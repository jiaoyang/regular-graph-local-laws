import LocalLaw.OutsideEdgeCounting

/-!
# Euler excess under removal of a connected vertex set

Actual vertex, dart, and boundary-edge equivalences give the cutset counting
identities. Connectivity makes every outside component incident to the removed
set. These are the combinatorial inputs behind Propositions 5.2 and 5.3.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000

namespace LocalLaw

local instance excessCutDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Finite-graph edge count, expressed independently of a finite enumeration. -/
def graphEdgeCount {W : Type*} (H : SimpleGraph W) : ℕ := Nat.card H.edgeSet

/-- The actual components after deleting T. -/
abbrev CutComponent {V : Type*} (G : SimpleGraph V) (T : Set V) :=
  (outsideGraph G T).ConnectedComponent

def cutComponentGraph {V : Type*} (G : SimpleGraph V) (T : Set V) (C : CutComponent G T) :
    SimpleGraph C.supp := (outsideGraph G T).induce C.supp

/-- T-to-component boundary edges, counted once in their T-to-outside orientation. -/
def CutBoundaryEdge {V : Type*} (G : SimpleGraph V) (T : Set V) (C : CutComponent G T) :=
  {e : BoundaryOrientedEdge G T //
    (outsideGraph G T).connectedComponentMk ⟨e.val.2, e.property.2.2⟩ = C}

def cutMultiplicity {V : Type*} (G : SimpleGraph V) (T : Set V) (C : CutComponent G T) : ℕ :=
  Nat.card (CutBoundaryEdge G T C)

instance cutBoundaryEdgeFintype {V : Type*} [Fintype V] (G : SimpleGraph V) (T : Set V)
    (C : CutComponent G T) : Fintype (CutBoundaryEdge G T C) := by
  unfold CutBoundaryEdge
  infer_instance

/-- A graph's vertices partition exactly into the supports of its components. -/
def componentVertexEquiv {W : Type*} (H : SimpleGraph W) :
    (Σ C : H.ConnectedComponent, C.supp) ≃ W where
  toFun p := p.2.val
  invFun v := ⟨H.connectedComponentMk v, v, rfl⟩
  left_inv p := by
    rcases p with ⟨C, ⟨v, hv⟩⟩
    change H.connectedComponentMk v = C at hv
    cases hv
    rfl
  right_inv _ := rfl

/-- A graph's oriented edges partition exactly into its component graphs. -/
def componentDartEquiv {W : Type*} (H : SimpleGraph W) :
    H.Dart ≃ Σ C : H.ConnectedComponent, (H.induce C.supp).Dart where
  toFun e := ⟨H.connectedComponentMk e.fst,
    ⟨(⟨e.fst, rfl⟩, ⟨e.snd, SimpleGraph.ConnectedComponent.sound e.adj.symm.reachable⟩), e.adj⟩⟩
  invFun p := ⟨(p.2.fst.val, p.2.snd.val), p.2.adj⟩
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨C, ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hxy⟩⟩
    change H.connectedComponentMk x = C at hx
    cases hx
    rfl

/-- Partition the actual boundary edges by the component of their outside endpoint. -/
def cutBoundaryEquiv {V : Type*} (G : SimpleGraph V) (T : Set V) :
    BoundaryOrientedEdge G T ≃ Σ C : CutComponent G T, CutBoundaryEdge G T C where
  toFun e := ⟨(outsideGraph G T).connectedComponentMk ⟨e.val.2, e.property.2.2⟩, e, rfl⟩
  invFun p := p.2.val
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨C, ⟨e, he⟩⟩
    cases he
    rfl

/-- Outside oriented edges are darts of the actual induced outside graph. -/
def outsideDartEquiv {V : Type*} (G : SimpleGraph V) (T : Set V) :
    OutsideOrientedEdge G T ≃ (outsideGraph G T).Dart :=
  interior_induced_dart_equiv G Tᶜ

/-- Deficit created by removal of T: the actual number of lost neighbors
inside T at a vertex of an outside component. -/
def cutDeficit {V : Type*} (G : SimpleGraph V) (T : Set V) (C : CutComponent G T)
    (v : C.supp) : ℕ := Nat.card {t : T // G.Adj t.val v.val.val}

/-- Boundary edges are exactly the lost-neighbor incidences over component
vertices. This makes the deficit sum an actual count, not an input identity. -/
def cutBoundaryDeficitEquiv {V : Type*} (G : SimpleGraph V) (T : Set V) (C : CutComponent G T) :
    CutBoundaryEdge G T C ≃ Σ v : C.supp, {t : T // G.Adj t.val v.val.val} where
  toFun e := ⟨⟨⟨e.val.val.2, e.val.property.2.2⟩, e.property⟩,
    ⟨⟨e.val.val.1, e.val.property.2.1⟩, e.val.property.1⟩⟩
  invFun p := ⟨⟨(p.2.val.val, p.1.val.val), p.2.property, p.2.val.property,
    p.1.val.property⟩, p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Ambient neighbors split into lost T-neighbors and retained outside
neighbors, with the lost edge orientation reversed for boundary counting. -/
def neighborCutEquiv {V : Type*} (G : SimpleGraph V) (T : Set V) (x : {v : V // v ∉ T}) :
    G.neighborSet x.val ≃ {t : T // G.Adj t.val x.val} ⊕ (outsideGraph G T).neighborSet x where
  toFun y := if hy : y.val ∈ T then Sum.inl ⟨⟨y.val, hy⟩, y.property.symm⟩
    else Sum.inr ⟨⟨y.val, hy⟩, y.property⟩
  invFun
    | Sum.inl t => ⟨t.val.val, t.property.symm⟩
    | Sum.inr y => ⟨y.val.val, y.property⟩
  left_inv y := by by_cases hy : y.val ∈ T <;> simp [hy]
  right_inv y := by
    rcases y with t | y
    · simp [t.val.property]
    · simp [y.val.property]

/-- A connected graph has exactly one connected component, with no finiteness
assumption needed for this quotient statement. -/
theorem connected_component_card {W : Type*} (H : SimpleGraph W) (hH : H.Connected) :
    Nat.card H.ConnectedComponent = 1 := by
  letI : Subsingleton H.ConnectedComponent := ⟨fun C D =>
    SimpleGraph.ConnectedComponent.ind₂
      (fun x y => SimpleGraph.ConnectedComponent.sound (hH x y)) C D⟩
  letI : Nonempty H.ConnectedComponent := ⟨H.connectedComponentMk (Classical.choice hH.nonempty)⟩
  exact Nat.card_unique

section FiniteCounts

variable {V : Type*} [Fintype V]

/-- Darts count each edge exactly twice. -/
theorem graph_dart_count (H : SimpleGraph V) : Nat.card H.Dart = 2 * graphEdgeCount H := by
  simpa only [graphEdgeCount, Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using
    H.dart_card_eq_twice_card_edges

/-- Vertex counting for the deletion and its actual connected components. -/
theorem cut_vertex_partition (G : SimpleGraph V) (T : Set V) :
    Nat.card V = Nat.card T + ∑ C : CutComponent G T, Nat.card C.supp := by
  have hsum := Nat.card_congr (Equiv.Set.sumCompl T)
  simp only [Nat.card_sum] at hsum
  change Nat.card T + Nat.card {v : V // v ∉ T} = Nat.card V at hsum
  have hcomponents : Nat.card {v : V // v ∉ T} =
      ∑ C : CutComponent G T, Nat.card C.supp := by
    calc
      Nat.card {v : V // v ∉ T} = Nat.card (Σ C : CutComponent G T, C.supp) :=
        (Nat.card_congr (componentVertexEquiv (outsideGraph G T))).symm
      _ = ∑ C : CutComponent G T, Nat.card C.supp := Nat.card_sigma
  omega

/-- The total cut boundary is the sum of the actual component multiplicities. -/
theorem cut_boundary_partition (G : SimpleGraph V) (T : Set V) :
    Nat.card (BoundaryOrientedEdge G T) = ∑ C : CutComponent G T, cutMultiplicity G T C := by
  have h := Nat.card_congr (cutBoundaryEquiv G T)
  rw [Nat.card_sigma] at h
  exact h

/-- Actual edge partition: internal T edges, internal outside-component edges,
and one copy of every cut boundary edge. -/
theorem cut_edge_partition (G : SimpleGraph V) (T : Set V) :
    graphEdgeCount G = graphEdgeCount (G.induce T) +
      (∑ C : CutComponent G T, graphEdgeCount (cutComponentGraph G T C)) +
      ∑ C : CutComponent G T, cutMultiplicity G T C := by
  have hO : Nat.card (OutsideOrientedEdge G T) =
      2 * ∑ C : CutComponent G T, graphEdgeCount (cutComponentGraph G T C) := by
    calc
      Nat.card (OutsideOrientedEdge G T) = Nat.card (outsideGraph G T).Dart :=
        Nat.card_congr (outsideDartEquiv G T)
      _ = ∑ C : CutComponent G T, Nat.card (cutComponentGraph G T C).Dart := by
        rw [Nat.card_congr (componentDartEquiv (outsideGraph G T)), Nat.card_sigma]
        rfl
      _ = ∑ C : CutComponent G T, 2 * graphEdgeCount (cutComponentGraph G T C) := by
        apply Finset.sum_congr rfl
        intro C _
        exact graph_dart_count _
      _ = 2 * ∑ C : CutComponent G T, graphEdgeCount (cutComponentGraph G T C) := by
        rw [Finset.mul_sum]
  have hI : Nat.card (InteriorOrientedEdge G T) = 2 * graphEdgeCount (G.induce T) := by
    rw [interior_count_induced, graph_dart_count]
  have h := outside_boundary_interior_count G T
  rw [graph_dart_count, hO, hI, cut_boundary_partition] at h
  omega

/-- Connectivity discharges the natural-subtraction guard in the Euler formula. -/
theorem connected_graph_excess_euler (G : SimpleGraph V) (hG : G.Connected) :
    graphExcess G + Nat.card V = graphEdgeCount G + 1 := by
  have hvertices := hG.card_vert_le_card_edgeSet_add_one
  unfold graphExcess graphEdgeCount
  rw [connected_component_card G hG]
  have hEdge : G.edgeFinset.card = Nat.card G.edgeSet := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]
  rw [hEdge, ← Nat.card_eq_fintype_card]
  exact Nat.sub_add_cancel hvertices

/- Walking from an outside vertex to T crosses a boundary edge in the same
outside component. This proves boundary nonemptiness, rather than assuming it. -/
omit [Fintype V] in
theorem cut_boundary_nonempty_of_walk (G : SimpleGraph V) (T : Set V) (C : CutComponent G T)
    {x t : V} (p : G.Walk x t) (ht : t ∈ T) :
    ∀ hx : x ∉ T, (outsideGraph G T).connectedComponentMk ⟨x, hx⟩ = C →
      Nonempty (CutBoundaryEdge G T C) := by
  induction p with
  | nil =>
      intro hx _
      exact False.elim (hx ht)
  | @cons x y t hadj p ih =>
      intro hx hC
      by_cases hy : y ∈ T
      · exact ⟨⟨⟨(y, x), hadj.symm, hy, hx⟩, hC⟩⟩
      · have hxy : (outsideGraph G T).Adj ⟨x, hx⟩ ⟨y, hy⟩ := hadj
        have hsame : (outsideGraph G T).connectedComponentMk ⟨x, hx⟩ =
            (outsideGraph G T).connectedComponentMk ⟨y, hy⟩ :=
          SimpleGraph.ConnectedComponent.sound hxy.reachable
        exact ih ht hy (hsame.symm.trans hC)

/-- Every outside component of a connected graph is incident to the nonempty
removed set. -/
theorem cutMultiplicity_positive (G : SimpleGraph V) (T : Set V)
    (hG : G.Connected) (hT : T.Nonempty) (C : CutComponent G T) :
    1 ≤ cutMultiplicity G T C := by
  obtain ⟨t, ht⟩ := hT
  let x := C.out
  obtain ⟨p⟩ := hG x.val t
  have hnonempty : Nonempty (CutBoundaryEdge G T C) :=
    cut_boundary_nonempty_of_walk G T C p ht x.property C.out_eq
  have hfinite : Finite (CutBoundaryEdge G T C) := inferInstance
  have hpos : 0 < Nat.card (CutBoundaryEdge G T C) := Nat.card_pos_iff.mpr ⟨hnonempty, hfinite⟩
  exact hpos

/-- The nonnegative Euler charge carried by one attached outside component. -/
def cutExcessCharge (G : SimpleGraph V) (T : Set V) (C : CutComponent G T) : ℕ :=
  graphExcess (cutComponentGraph G T C) + cutMultiplicity G T C - 1

theorem cutExcessCharge_add_one (G : SimpleGraph V) (T : Set V)
    (hG : G.Connected) (hT : T.Nonempty) (C : CutComponent G T) :
    cutExcessCharge G T C + 1 = graphExcess (cutComponentGraph G T C) + cutMultiplicity G T C := by
  unfold cutExcessCharge
  apply Nat.sub_add_cancel
  have h := cutMultiplicity_positive G T hG hT C
  omega

/-- Exact cutset Euler identity from the proved actual vertex/edge partitions
and connected-graph Euler formulas. -/
theorem connected_cutset_excess_identity (G : SimpleGraph V) (T : Set V)
    (hG : G.Connected) (hT : (G.induce T).Connected) :
    graphExcess G = graphExcess (G.induce T) +
      ∑ C : CutComponent G T, cutExcessCharge G T C := by
  have hTnonempty : T.Nonempty := by
    obtain ⟨t⟩ := hT.nonempty
    exact ⟨t.val, t.property⟩
  have hvertices := cut_vertex_partition G T
  have hedges := cut_edge_partition G T
  have hEulerG := connected_graph_excess_euler G hG
  have hEulerT := connected_graph_excess_euler (G.induce T) hT
  have hcomponentSum :
      (∑ C : CutComponent G T, graphExcess (cutComponentGraph G T C)) +
        (∑ C : CutComponent G T, Nat.card C.supp) =
      (∑ C : CutComponent G T, graphEdgeCount (cutComponentGraph G T C)) +
        Fintype.card (CutComponent G T) := by
    calc
      _ = ∑ C : CutComponent G T,
          (graphExcess (cutComponentGraph G T C) + Nat.card C.supp) :=
        Finset.sum_add_distrib.symm
      _ = ∑ C : CutComponent G T, (graphEdgeCount (cutComponentGraph G T C) + 1) := by
        apply Finset.sum_congr rfl
        intro C _
        exact connected_graph_excess_euler _ (SimpleGraph.ConnectedComponent.connected_induce_supp C)
      _ = _ := by simp [Finset.sum_add_distrib]
  have hchargeSum :
      (∑ C : CutComponent G T, cutExcessCharge G T C) + Fintype.card (CutComponent G T) =
      (∑ C : CutComponent G T, graphExcess (cutComponentGraph G T C)) +
        ∑ C : CutComponent G T, cutMultiplicity G T C := by
    calc
      _ = ∑ C : CutComponent G T, (cutExcessCharge G T C + 1) := by simp [Finset.sum_add_distrib]
      _ = ∑ C : CutComponent G T,
          (graphExcess (cutComponentGraph G T C) + cutMultiplicity G T C) := by
        apply Finset.sum_congr rfl
        intro C _
        exact cutExcessCharge_add_one G T hG hTnonempty C
      _ = _ := Finset.sum_add_distrib
  omega

/-- One outside component cannot use more than the total available Euler excess. -/
theorem cutExcessCharge_le_total (G : SimpleGraph V) (T : Set V)
    (hG : G.Connected) (hT : (G.induce T).Connected) (C : CutComponent G T) :
    cutExcessCharge G T C ≤ graphExcess G := by
  have hEuler := connected_cutset_excess_identity G T hG hT
  have hsingle : cutExcessCharge G T C ≤ ∑ D : CutComponent G T, cutExcessCharge G T D :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ C)
  omega

/-- The deficit-plus-excess bound before introducing an external omega budget. -/
theorem component_excess_plus_cut_le (G : SimpleGraph V) (T : Set V)
    (hG : G.Connected) (hT : (G.induce T).Connected) (C : CutComponent G T) :
    graphExcess (cutComponentGraph G T C) + cutMultiplicity G T C ≤ graphExcess G + 1 := by
  have hTnonempty : T.Nonempty := by
    obtain ⟨t⟩ := hT.nonempty
    exact ⟨t.val, t.property⟩
  have hcharge := cutExcessCharge_le_total G T hG hT C
  have hidentity := cutExcessCharge_add_one G T hG hTnonempty C
  omega

/-- Component multiplicity and component excess consume the same omega+1
budget, as needed for Proposition 5.3. -/
theorem component_excess_plus_cut_bound (G : SimpleGraph V) (T : Set V)
    (hG : G.Connected) (hT : (G.induce T).Connected) (ω : ℕ)
    (hbudget : graphExcess G ≤ ω) (C : CutComponent G T) :
    graphExcess (cutComponentGraph G T C) + cutMultiplicity G T C ≤ ω + 1 :=
  (component_excess_plus_cut_le G T hG hT C).trans (Nat.add_le_add_right hbudget 1)

theorem component_cut_multiplicity_bound (G : SimpleGraph V) (T : Set V)
    (hG : G.Connected) (hT : (G.induce T).Connected) (ω : ℕ)
    (hbudget : graphExcess G ≤ ω) (C : CutComponent G T) :
    cutMultiplicity G T C ≤ ω + 1 := by
  have h := component_excess_plus_cut_bound G T hG hT ω hbudget C
  omega

/-- The number of boundary edges belonging to components with at least two
attachments is at most twice the original excess (the core of Proposition 5.2). -/
theorem multiple_attachment_sum_bound (G : SimpleGraph V) (T : Set V)
    (hG : G.Connected) (hT : (G.induce T).Connected) :
    (∑ C ∈ (Finset.univ : Finset (CutComponent G T)).filter
      (fun C => 2 ≤ cutMultiplicity G T C), cutMultiplicity G T C) ≤ 2 * graphExcess G := by
  have hTnonempty : T.Nonempty := by
    obtain ⟨t⟩ := hT.nonempty
    exact ⟨t.val, t.property⟩
  have hpoint : ∀ C : CutComponent G T,
      (if 2 ≤ cutMultiplicity G T C then cutMultiplicity G T C else 0) ≤
        2 * cutExcessCharge G T C := by
    intro C
    have hcharge := cutExcessCharge_add_one G T hG hTnonempty C
    split_ifs <;> omega
  have hsum : (∑ C : CutComponent G T, cutExcessCharge G T C) ≤ graphExcess G := by
    have h := connected_cutset_excess_identity G T hG hT
    omega
  rw [Finset.sum_filter]
  calc
    _ ≤ ∑ C : CutComponent G T, 2 * cutExcessCharge G T C :=
      Finset.sum_le_sum (fun C _ => hpoint C)
    _ = 2 * ∑ C : CutComponent G T, cutExcessCharge G T C := by rw [Finset.mul_sum]
    _ ≤ 2 * graphExcess G := Nat.mul_le_mul_left 2 hsum

/-- The actual deficit sum is exactly the number of cut edges incident to
this component. -/
theorem cutMultiplicity_eq_sum_deficit (G : SimpleGraph V) (T : Set V) (C : CutComponent G T) :
    cutMultiplicity G T C = ∑ v : C.supp, cutDeficit G T C v := by
  unfold cutMultiplicity
  calc
    Nat.card (CutBoundaryEdge G T C) =
        Nat.card (Σ v : C.supp, {t : T // G.Adj t.val v.val.val}) :=
      Nat.card_congr (cutBoundaryDeficitEquiv G T C)
    _ = ∑ v : C.supp, cutDeficit G T C v := Nat.card_sigma

/-- There are no edges from one outside component to another, so passing
from the outside graph to its component does not change vertex degree. -/
theorem cutComponent_degree_eq (G : SimpleGraph V) (T : Set V) (C : CutComponent G T)
    (v : C.supp) :
    (cutComponentGraph G T C).degree v = (outsideGraph G T).degree v.val := by
  apply SimpleGraph.degree_induce_of_neighborSet_subset
  intro y hy
  exact (C.mem_supp_congr_adj hy).mp v.property

/-- The cut deficit agrees with the paper's degree-loss deletion convention. -/
theorem cutDeficit_degree_loss (G : SimpleGraph V) (T : Set V) (C : CutComponent G T)
    (v : C.supp) :
    cutDeficit G T C v = G.degree v.val.val - (cutComponentGraph G T C).degree v := by
  have h := Nat.card_congr (neighborCutEquiv G T v.val)
  rw [Nat.card_sum] at h
  have hG : Nat.card (G.neighborSet v.val.val) = G.degree v.val.val := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
  have hD : Nat.card ((outsideGraph G T).neighborSet v.val) = (outsideGraph G T).degree v.val := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
  rw [hG, hD] at h
  rw [cutComponent_degree_eq]
  change G.degree v.val.val = cutDeficit G T C v + (outsideGraph G T).degree v.val at h
  omega

/-- The deficit in each outside component is not identically zero. -/
theorem cutDeficit_nonzero (G : SimpleGraph V) (T : Set V)
    (hG : G.Connected) (hT : T.Nonempty) (C : CutComponent G T) :
    ∃ v : C.supp, 0 < cutDeficit G T C v := by
  by_contra hnone
  have hall : ∀ v : C.supp, cutDeficit G T C v = 0 := by
    intro v
    by_contra hv
    exact hnone ⟨v, Nat.pos_of_ne_zero hv⟩
  have hsum := cutMultiplicity_eq_sum_deficit G T C
  simp only [hall, Finset.sum_const_zero] at hsum
  have hpos := cutMultiplicity_positive G T hG hT C
  omega

/-- Actual Proposition-5.3 cutset conclusion: lost-degree deficit plus
component excess is bounded by omega+1, with nonzero deficit. -/
theorem component_deficit_excess_bound (G : SimpleGraph V) (T : Set V)
    (hG : G.Connected) (hT : (G.induce T).Connected) (ω : ℕ)
    (hbudget : graphExcess G ≤ ω) (C : CutComponent G T) :
    (∃ v : C.supp, 0 < cutDeficit G T C v) ∧
      graphExcess (cutComponentGraph G T C) + (∑ v : C.supp, cutDeficit G T C v) ≤ ω + 1 := by
  have hTnonempty : T.Nonempty := by
    obtain ⟨t⟩ := hT.nonempty
    exact ⟨t.val, t.property⟩
  refine ⟨cutDeficit_nonzero G T hG hTnonempty C, ?_⟩
  rw [← cutMultiplicity_eq_sum_deficit]
  exact component_excess_plus_cut_bound G T hG hT ω hbudget C

end FiniteCounts

end LocalLaw
