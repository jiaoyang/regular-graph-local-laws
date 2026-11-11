import LocalLaw.ExcessCutset
import LocalLaw.GraphBallCounting

/-!
# Excess bounds for an actual graph-ball annulus

Both connectedness hypotheses in the cutset theorem are proved for the actual
outer and inner balls. The resulting multiplicities count cut edges, and the
deficit is the actual degree loss on deleting the inner ball. This is the
ball geometry behind Lemma 5.4 and Proposition 5.3, before the additional
distance argument in Proposition 5.2.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000

namespace LocalLaw

local instance localExcessDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*}

/-- A short walk ending at the center stays in the induced ball. -/
theorem short_walk_reachable_in_ball (G : SimpleGraph V) (r : ℕ)
    {v o : V} (p : G.Walk v o) (hp : p.length ≤ r)
    (hv : v ∈ graphBallVertices G o r) :
    (graphBall G o r).Reachable ⟨v, hv⟩ ⟨o, center_mem_graphBall G o r⟩ := by
  induction p with
  | nil => exact SimpleGraph.Reachable.rfl
  | @cons v u o hvu p ih =>
      have hlen : p.length ≤ r := by
        simp only [SimpleGraph.Walk.length_cons] at hp
        omega
      have hu : u ∈ graphBallVertices G o r := by
        exact (SimpleGraph.edist_le p.reverse).trans
          (by simpa only [SimpleGraph.Walk.length_reverse] using
            (ENat.coe_le_coe.mpr hlen))
      exact (show (graphBall G o r).Adj ⟨v, hv⟩ ⟨u, hu⟩ from hvu).reachable.trans
        (ih hlen hu)

/-- Every finite-radius induced ball is connected, including radius zero. -/
theorem graphBall_connected (G : SimpleGraph V) (o : V) (r : ℕ) :
    (graphBall G o r).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨o, center_mem_graphBall G o r⟩, ?_⟩
  intro v
  have hv : v.val ∈ graphSetBall G {o} r := by
    rw [graphSetBall_singleton]
    exact v.property
  obtain ⟨s, hs, p, hp⟩ := (mem_graphSetBall_iff_walk G {o} r v.val).mp hv
  have hso : s = o := Set.mem_singleton_iff.mp hs
  subst s
  exact (short_walk_reachable_in_ball G r p.reverse
    (by simpa only [SimpleGraph.Walk.length_reverse] using hp) v.property).symm

/-- The inner-ball vertex set, viewed as vertices of the outer induced ball. -/
def ballCutInner (G : SimpleGraph V) (o : V) (ell R : ℕ) :
    Set (graphBallVertices G o R) := {v | v.val ∈ graphBallVertices G o ell}

/-- Nested induction is precisely the original inner-ball graph. -/
def nestedBallIso (G : SimpleGraph V) (o : V) {ell R : ℕ} (h : ell ≤ R) :
    (graphBall G o R).induce (ballCutInner G o ell R) ≃g graphBall G o ell where
  toEquiv :=
    { toFun := fun v => ⟨v.val.val, v.property⟩
      invFun := fun v => ⟨⟨v.val, graphBallVertices_mono G o h v.property⟩, v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := Iff.rfl

theorem ballCutInner_connected (G : SimpleGraph V) (o : V) {ell R : ℕ}
    (h : ell ≤ R) :
    ((graphBall G o R).induce (ballCutInner G o ell R)).Connected :=
  (nestedBallIso G o h).connected_iff.mpr (graphBall_connected G o ell)

theorem ballCutInner_nonempty (G : SimpleGraph V) (o : V) (ell R : ℕ) :
    (ballCutInner G o ell R).Nonempty :=
  ⟨⟨o, center_mem_graphBall G o R⟩, center_mem_graphBall G o ell⟩

/-- Actual connected components of the annulus B_R(o) minus B_ell(o). -/
abbrev BallAnnulusComponent (G : SimpleGraph V) (o : V) (ell R : ℕ) :=
  CutComponent (graphBall G o R) (ballCutInner G o ell R)

/-- All neighbors of the inner ball belong to the outer ball once R≥ell+1. -/
theorem adjacent_inner_mem_outer_ball (G : SimpleGraph V) (o : V) {ell R : ℕ}
    (h : ell + 1 ≤ R) {x y : V} (hx : x ∈ graphBallVertices G o ell)
    (hxy : G.Adj x y) : y ∈ graphBallVertices G o R := by
  change G.edist o y ≤ (R : ℕ∞)
  calc
    G.edist o y ≤ G.edist o x + G.edist x y := G.edist_triangle
    _ ≤ (ell : ℕ∞) + 1 := add_le_add hx
      (le_of_eq (SimpleGraph.edist_eq_one_iff_adj.mpr hxy))
    _ ≤ (R : ℕ∞) := by exact_mod_cast h

/-- The cut boundary inside B_R is exactly the ambient boundary of B_ell.
Thus its multiplicities count the paper's actual boundary labels. -/
def ballBoundaryEquiv (G : SimpleGraph V) (o : V) {ell R : ℕ} (h : ell + 1 ≤ R) :
    BoundaryOrientedEdge G (graphBallVertices G o ell) ≃
      BoundaryOrientedEdge (graphBall G o R) (ballCutInner G o ell R) where
  toFun e := ⟨(⟨e.val.1, graphBallVertices_mono G o (by omega) e.property.2.1⟩,
    ⟨e.val.2, adjacent_inner_mem_outer_ball G o h e.property.2.1 e.property.1⟩),
    e.property.1, e.property.2.1, e.property.2.2⟩
  invFun e := ⟨(e.val.1.val, e.val.2.val), e.property.1, e.property.2.1, e.property.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Annulus component containing an ambient boundary edge's outside endpoint. -/
def ambientBoundaryComponent (G : SimpleGraph V) (o : V) {ell R : ℕ}
    (h : ell + 1 ≤ R) (e : BoundaryOrientedEdge G (graphBallVertices G o ell)) :
    BallAnnulusComponent G o ell R :=
  (outsideGraph (graphBall G o R) (ballCutInner G o ell R)).connectedComponentMk
    ⟨(ballBoundaryEquiv G o h e).val.2, (ballBoundaryEquiv G o h e).property.2.2⟩

/-- Actual ambient boundary labels attached to a given annulus component. -/
def AmbientBallBoundaryFiber (G : SimpleGraph V) (o : V) {ell R : ℕ}
    (h : ell + 1 ≤ R) (C : BallAnnulusComponent G o ell R) :=
  {e : BoundaryOrientedEdge G (graphBallVertices G o ell) |
    ambientBoundaryComponent G o h e = C}

def ambientBallBoundaryFiberEquiv (G : SimpleGraph V) (o : V) {ell R : ℕ}
    (h : ell + 1 ≤ R) (C : BallAnnulusComponent G o ell R) :
    AmbientBallBoundaryFiber G o h C ≃
      CutBoundaryEdge (graphBall G o R) (ballCutInner G o ell R) C where
  toFun e := ⟨ballBoundaryEquiv G o h e.val, e.property⟩
  invFun e := ⟨(ballBoundaryEquiv G o h).symm e.val, by
    change ambientBoundaryComponent G o h ((ballBoundaryEquiv G o h).symm e.val) = C
    simpa only [ambientBoundaryComponent, Equiv.apply_symm_apply] using e.property⟩
  left_inv e := by apply Subtype.ext; exact (ballBoundaryEquiv G o h).symm_apply_apply e.val
  right_inv e := by apply Subtype.ext; exact (ballBoundaryEquiv G o h).apply_symm_apply e.val

theorem ambientBallBoundaryFiber_card (G : SimpleGraph V) (o : V) {ell R : ℕ}
    (h : ell + 1 ≤ R) (C : BallAnnulusComponent G o ell R) :
    Nat.card (AmbientBallBoundaryFiber G o h C) =
      cutMultiplicity (graphBall G o R) (ballCutInner G o ell R) C :=
  Nat.card_congr (ambientBallBoundaryFiberEquiv G o h C)

section Finite

variable [Fintype V]

/-- Exact Euler accounting for the actual nested graph balls. -/
theorem ball_annulus_excess_identity (G : SimpleGraph V) (o : V) {ell R : ℕ}
    (h : ell ≤ R) :
    graphBallExcess G o R =
      graphExcess ((graphBall G o R).induce (ballCutInner G o ell R)) +
        ∑ C : BallAnnulusComponent G o ell R,
          cutExcessCharge (graphBall G o R) (ballCutInner G o ell R) C := by
  have hEuler := connected_cutset_excess_identity (graphBall G o R)
    (ballCutInner G o ell R) (graphBall_connected G o R) (ballCutInner_connected G o h)
  -- Nat.card and finsum remove irrelevant choices of nested finite enumerations.
  simp only [graphBallExcess, graphExcess, SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card, ← finsum_eq_sum_of_fintype] at hEuler ⊢
  exact hEuler

/-- Lemma 5.4: at most 2 omega boundary edges belong to annulus components
with two or more attachments. No connectedness hypothesis is assumed. -/
theorem ball_multiple_attachment_sum_bound (G : SimpleGraph V) (o : V)
    {ell R ω : ℕ} (h : ell ≤ R) (hbudget : graphBallExcess G o R ≤ ω) :
    (∑ C ∈ (Finset.univ : Finset (BallAnnulusComponent G o ell R)).filter
      (fun C => 2 ≤ cutMultiplicity (graphBall G o R) (ballCutInner G o ell R) C),
      cutMultiplicity (graphBall G o R) (ballCutInner G o ell R) C) ≤ 2 * ω := by
  have hsum := multiple_attachment_sum_bound (graphBall G o R) (ballCutInner G o ell R)
    (graphBall_connected G o R) (ballCutInner_connected G o h)
  simp only [graphBallExcess, graphExcess, SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card, Finset.sum_filter, ← finsum_eq_sum_of_fintype]
    at hsum hbudget ⊢
  exact hsum.trans (Nat.mul_le_mul_left 2 hbudget)

/-- Each actual annulus component has at most omega+1 attachments. -/
theorem ball_component_cut_multiplicity_bound (G : SimpleGraph V) (o : V)
    {ell R ω : ℕ} (h : ell ≤ R) (hbudget : graphBallExcess G o R ≤ ω)
    (C : BallAnnulusComponent G o ell R) :
    cutMultiplicity (graphBall G o R) (ballCutInner G o ell R) C ≤ ω + 1 :=
  component_cut_multiplicity_bound (graphBall G o R) (ballCutInner G o ell R) (graphBall_connected G o R)
    (ballCutInner_connected G o h) ω hbudget C

/-- The annulus fibers partition the actual ambient boundary labels. -/
theorem ambient_boundary_annulus_partition (G : SimpleGraph V) (o : V) {ell R : ℕ}
    (h : ell + 1 ≤ R) :
    Nat.card (BoundaryOrientedEdge G (graphBallVertices G o ell)) =
      ∑ C : BallAnnulusComponent G o ell R, Nat.card (AmbientBallBoundaryFiber G o h C) := by
  have hcount := cut_boundary_partition (graphBall G o R) (ballCutInner G o ell R)
  have hequiv := Nat.card_congr (ballBoundaryEquiv G o h)
  simp only [ambientBallBoundaryFiber_card, ← finsum_eq_sum_of_fintype] at hcount ⊢
  exact hequiv.trans hcount

/-- Lemma 5.4 phrased directly with the actual ambient boundary labels. -/
theorem ambient_boundary_multiple_attachment_bound (G : SimpleGraph V) (o : V)
    {ell R ω : ℕ} (h : ell + 1 ≤ R) (hbudget : graphBallExcess G o R ≤ ω) :
    (∑ C ∈ (Finset.univ : Finset (BallAnnulusComponent G o ell R)).filter
      (fun C => 2 ≤ Nat.card (AmbientBallBoundaryFiber G o h C)),
      Nat.card (AmbientBallBoundaryFiber G o h C)) ≤ 2 * ω := by
  simp only [ambientBallBoundaryFiber_card]
  exact ball_multiple_attachment_sum_bound G o (by omega) hbudget

theorem ambient_boundary_component_count_bound (G : SimpleGraph V) (o : V)
    {ell R ω : ℕ} (h : ell + 1 ≤ R) (hbudget : graphBallExcess G o R ≤ ω)
    (C : BallAnnulusComponent G o ell R) :
    Nat.card (AmbientBallBoundaryFiber G o h C) ≤ ω + 1 := by
  rw [ambientBallBoundaryFiber_card]
  exact ball_component_cut_multiplicity_bound G o (by omega) hbudget C

/-- Proposition 5.3 with the deficit defined by actual lost neighbors. -/
theorem ball_component_deficit_excess_bound (G : SimpleGraph V) (o : V)
    {ell R ω : ℕ} (h : ell ≤ R) (hbudget : graphBallExcess G o R ≤ ω)
    (C : BallAnnulusComponent G o ell R) :
    (∃ v : C.supp, 0 < cutDeficit (graphBall G o R) (ballCutInner G o ell R) C v) ∧
      graphExcess (cutComponentGraph (graphBall G o R) (ballCutInner G o ell R) C) +
        (∑ v : C.supp, cutDeficit (graphBall G o R) (ballCutInner G o ell R) C v) ≤ ω + 1 := by
  have hcomponent := component_deficit_excess_bound (graphBall G o R)
    (ballCutInner G o ell R) (graphBall_connected G o R) (ballCutInner_connected G o h)
    ω hbudget C
  simp only [graphExcess, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
    ← finsum_eq_sum_of_fintype] at hcomponent ⊢
  exact hcomponent

def ballAnnulusDegreeDeficit (G : SimpleGraph V) (o : V) {ell R : ℕ}
    (C : BallAnnulusComponent G o ell R) (v : C.supp) : ℕ :=
  (graphBall G o R).degree v.val.val -
    (cutComponentGraph (graphBall G o R) (ballCutInner G o ell R) C).degree v

theorem ballAnnulusDegreeDeficit_eq (G : SimpleGraph V) (o : V) {ell R : ℕ}
    (C : BallAnnulusComponent G o ell R) (v : C.supp) :
    ballAnnulusDegreeDeficit G o C v =
      cutDeficit (graphBall G o R) (ballCutInner G o ell R) C v := by
  have hdef := cutDeficit_degree_loss (graphBall G o R) (ballCutInner G o ell R) C v
  simp only [ballAnnulusDegreeDeficit, ← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] at hdef ⊢
  exact hdef.symm

/-- The same conclusion in the paper's degree-loss notation. -/
theorem ball_component_degree_loss_excess_bound (G : SimpleGraph V) (o : V)
    {ell R ω : ℕ} (h : ell ≤ R) (hbudget : graphBallExcess G o R ≤ ω)
    (C : BallAnnulusComponent G o ell R) :
    (∃ v : C.supp, 0 < ballAnnulusDegreeDeficit G o C v) ∧
      graphExcess (cutComponentGraph (graphBall G o R) (ballCutInner G o ell R) C) +
        (∑ v : C.supp, ballAnnulusDegreeDeficit G o C v) ≤ ω + 1 := by
  simpa only [ballAnnulusDegreeDeficit_eq] using
    ball_component_deficit_excess_bound G o h hbudget C

/-- Structural-event specialization; its ball-excess clause is the only input. -/
theorem structural_ball_component_deficit_excess_bound (G : SimpleGraph V) (o : V)
    {ell R ω badCount : ℕ} (h : ell ≤ R) (hstruct : GraphTreeLike G R ω badCount)
    (C : BallAnnulusComponent G o ell R) :
    (∃ v : C.supp, 0 < cutDeficit (graphBall G o R) (ballCutInner G o ell R) C v) ∧
      graphExcess (cutComponentGraph (graphBall G o R) (ballCutInner G o ell R) C) +
        (∑ v : C.supp, cutDeficit (graphBall G o R) (ballCutInner G o ell R) C v) ≤ ω + 1 :=
  ball_component_deficit_excess_bound G o h (hstruct.1 o) C

end Finite

namespace RegularGraph

variable {N d : ℕ}

/-- Exact boundary-size formula for any connected induced vertex set in a
regular graph; this natural-number form has no truncated subtraction. -/
theorem boundary_excess_count (g : RegularGraph N d) (hd : 2 ≤ d)
    (T : Set (Fin N)) (hT : (g.graph.induce T).Connected) :
    Nat.card (BoundaryOrientedEdge g.graph T) + 2 * graphExcess (g.graph.induce T) =
      (d - 2) * Nat.card T + 2 := by
  have hboundary := g.boundary_interior_count T
  have hinterior := interior_count_induced g.graph T
  have hdarts := graph_dart_count (g.graph.induce T)
  have hEuler := connected_graph_excess_euler (g.graph.induce T) hT
  rw [hinterior, hdarts] at hboundary
  have hmul : d * Nat.card T = (d - 2) * Nat.card T + 2 * Nat.card T := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hd]
  simp only [graphExcess, graphEdgeCount, SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card] at hEuler hboundary ⊢
  omega

/-- Actual radius-ell boundary size, with connectedness proved for the ball. -/
theorem ball_boundary_excess_count (g : RegularGraph N d) (hd : 2 ≤ d)
    (o : Fin N) (ell : ℕ) :
    Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) +
      2 * graphBallExcess g.graph o ell =
        (d - 2) * Nat.card (graphBallVertices g.graph o ell) + 2 := by
  have hcount := g.boundary_excess_count hd (graphBallVertices g.graph o ell)
    (graphBall_connected g.graph o ell)
  simp only [graphBallExcess, graphBall, graphExcess, SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card] at hcount ⊢
  exact hcount

end RegularGraph

end LocalLaw
