import LocalLaw.CutSelfEnergy

/-!
# Actual exceptional attachment edge count

Exceptional boundary edges are classified by the actual positive Euler
charge of their outside component. Exact finite equivalences transfer the
proved charge bound to edge and port incidences.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance exceptionalCutDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) exceptionalComponentMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _

variable {V : Type} [Fintype V] [DecidableEq V]

def ExceptionalBoundaryEdge (G : SimpleGraph V) (S : Set V) :=
  {e : BoundaryOrientedEdge G S // ¬ordinaryCutVertex G S ⟨e.val.2, e.property.2.2⟩}

instance exceptionalBoundaryEdgeFintype (G : SimpleGraph V) (S : Set V) :
    Fintype (ExceptionalBoundaryEdge G S) := by unfold ExceptionalBoundaryEdge; infer_instance

def exceptionalBoundaryComponentEquiv (G : SimpleGraph V) (S : Set V) :
    ExceptionalBoundaryEdge G S ≃
      Σ c : {c : CutComponent G S // 0 < cutExcessCharge G S c}, CutBoundaryEdge G S c.val where
  toFun e :=
    ⟨⟨(outsideGraph G S).connectedComponentMk ⟨e.val.val.2, e.val.property.2.2⟩,
      Nat.pos_of_ne_zero e.property⟩, ⟨e.val, rfl⟩⟩
  invFun p := ⟨p.2.val, by
    change cutExcessCharge G S ((outsideGraph G S).connectedComponentMk
      ⟨p.2.val.val.2, p.2.val.property.2.2⟩) ≠ 0
    rw [p.2.property]
    exact Nat.ne_of_gt p.1.property⟩
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨⟨c, hc⟩, e⟩
    rcases e with ⟨e, he⟩
    cases he
    rfl

/-- A bounded-excess connected cut has at most twice the excess many
literal exceptional attachment edges, including cyclic single attachments. -/
theorem exceptionalBoundaryEdge_card_bound (G : SimpleGraph V) (S : Set V)
    (hG : G.Connected) (hS : (G.induce S).Connected) (ω : ℕ) (hω : graphExcess G ≤ ω) :
    Nat.card (ExceptionalBoundaryEdge G S) ≤ 2 * ω := by
  have hcard := Nat.card_congr (exceptionalBoundaryComponentEquiv G S)
  have hsigma := Nat.card_sigma (β := fun c : {c : CutComponent G S // 0 < cutExcessCharge G S c} =>
    CutBoundaryEdge G S c.val)
  have hsub : (∑ c : {c : CutComponent G S // 0 < cutExcessCharge G S c}, cutMultiplicity G S c.val) =
      ∑ c : CutComponent G S, if 0 < cutExcessCharge G S c then cutMultiplicity G S c else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) _).symm
  change Nat.card (Σ c : {c : CutComponent G S // 0 < cutExcessCharge G S c}, CutBoundaryEdge G S c.val) =
    ∑ c : {c : CutComponent G S // 0 < cutExcessCharge G S c}, cutMultiplicity G S c.val at hsigma
  simp only [← finsum_eq_sum_of_fintype] at hsigma hsub
  exact (hcard.trans (hsigma.trans hsub)).le.trans (exceptional_cut_attachment_sum G S hG hS ω hω)

def ExceptionalPortFiber (G : SimpleGraph V) (S : Set V) (u : S) :=
  {a : (Sᶜ : Set V) // ¬ordinaryCutVertex G S a ∧ G.Adj u.val a.val}

instance exceptionalPortFiberFintype (G : SimpleGraph V) (S : Set V) (u : S) :
    Fintype (ExceptionalPortFiber G S u) := by unfold ExceptionalPortFiber; infer_instance

def exceptionalBoundaryPortEquiv (G : SimpleGraph V) (S : Set V) :
    ExceptionalBoundaryEdge G S ≃ Σ u : S, ExceptionalPortFiber G S u where
  toFun e := ⟨⟨e.val.val.1, e.val.property.2.1⟩,
    ⟨⟨e.val.val.2, e.val.property.2.2⟩, e.property, e.val.property.1⟩⟩
  invFun p := ⟨⟨(p.1.val, p.2.val.val), p.2.property.2, p.1.property, p.2.val.property⟩, p.2.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem indicator_sum_card {I : Type*} [Fintype I] (P : I → Prop) [DecidablePred P] (c : ℝ) :
    (∑ i, if P i then c else 0) = (Nat.card {i // P i} : ℝ) * c := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card, Fintype.card_subtype]

def exceptionalCutCharge (G : SimpleGraph V) (d : ℕ) (S : Set V) (u : S) : ℝ :=
  ∑ a : (Sᶜ : Set V), if ¬ordinaryCutVertex G S a ∧ G.Adj u.val a.val then
    1 / ((d : ℝ) - 1) else 0

omit [DecidableEq V] in
theorem exceptionalCutCharge_eq_card (G : SimpleGraph V) (d : ℕ) (S : Set V) (u : S) :
    exceptionalCutCharge G d S u = (Nat.card (ExceptionalPortFiber G S u) : ℝ) / ((d : ℝ) - 1) := by
  have h := indicator_sum_card (fun a : (Sᶜ : Set V) => ¬ordinaryCutVertex G S a ∧ G.Adj u.val a.val)
    (1 / ((d : ℝ) - 1))
  simpa only [exceptionalCutCharge, ExceptionalPortFiber, mul_one_div] using h

omit [DecidableEq V] in
theorem exceptionalCutCharge_sum (G : SimpleGraph V) (d : ℕ) (S : Set V) :
    (∑ u : S, exceptionalCutCharge G d S u) =
      (Nat.card (ExceptionalBoundaryEdge G S) : ℝ) / ((d : ℝ) - 1) := by
  simp only [exceptionalCutCharge_eq_card, ← Finset.sum_div]
  congr 1
  have hcard := Nat.card_congr (exceptionalBoundaryPortEquiv G S)
  rw [Nat.card_sigma] at hcard
  exact_mod_cast hcard.symm

namespace DeficientGraph
variable {d : ℕ}

omit [DecidableEq V] in
/-- The ordinary and exceptional incident charges partition the actual
missing-degree charge of the restriction. -/
theorem ordinary_add_exceptional_charge (g : DeficientGraph V d) (S : Set V) (u : S) :
    ordinaryCutCharge g.graph d S u + exceptionalCutCharge g.graph d S u = g.restrictionLoss S u := by
  have hsplit : ordinaryCutCharge g.graph d S u + exceptionalCutCharge g.graph d S u =
      ∑ a : (Sᶜ : Set V), if g.graph.Adj u.val a.val then 1 / ((d : ℝ) - 1) else 0 := by
    rw [ordinaryCutCharge, exceptionalCutCharge, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ho : ordinaryCutVertex g.graph S a <;> by_cases ha : g.graph.Adj u.val a.val <;> simp [ho, ha]
  let φ : {a : (Sᶜ : Set V) // g.graph.Adj u.val a.val} ≃
      {v : V // v ∉ S ∧ g.graph.Adj u.val v} :=
    { toFun := fun a => ⟨a.val.val, a.val.property, a.property⟩
      invFun := fun v => ⟨⟨v.val, v.property.1⟩, v.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard := Nat.card_congr φ
  have hdegree := core_neighbor_degree_partition g.graph S u
  have hdegreeR : (g.graph.degree u.val : ℝ) = ((g.graph.induce S).degree u : ℝ) +
      (outsideCoreNeighborCount g.graph S u : ℝ) := by exact_mod_cast hdegree
  rw [hsplit, indicator_sum_card, hcard]
  change (outsideCoreNeighborCount g.graph S u : ℝ) * (1 / ((d : ℝ) - 1)) = _
  unfold restrictionLoss
  rw [hdegreeR]
  ring

omit [DecidableEq V] in
/-- Unmatched boundary charge in the exceptional Schur matrix has total
mass controlled by the actual exceptional edge count. -/
theorem unmatched_boundary_charge_sum (g : DeficientGraph V d) (S : Set V) :
    (∑ u : S, (g.restrictionLoss S u - ordinaryCutCharge g.graph d S u)) =
      (Nat.card (ExceptionalBoundaryEdge g.graph S) : ℝ) / ((d : ℝ) - 1) := by
  have heq : ∀ u : S, g.restrictionLoss S u - ordinaryCutCharge g.graph d S u =
      exceptionalCutCharge g.graph d S u := by
    intro u
    rw [← g.ordinary_add_exceptional_charge S u]
    ring
  simp only [heq]
  exact exceptionalCutCharge_sum g.graph d S

end DeficientGraph

end LocalLaw
