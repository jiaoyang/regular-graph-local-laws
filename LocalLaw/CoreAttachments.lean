import LocalLaw.CoreLayerCounting

/-!
# The actual forest attachments outside the spanning core

The core is connected in the chosen tree because its defining paths all
share their initial vertex. Tree cutset counting then gives exactly one
attachment for each outside component. The G and T boundaries are identified
by an actual edge equivalence; their outside induced graphs are already equal.
-/

noncomputable section
namespace LocalLaw

local instance coreAttachmentDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual path-union core is connected in T, without a convexity premise. -/
theorem spanningCore_tree_connected (G T : SimpleGraph V) (hT : T.IsTree) (i j : V) :
    (T.induce (spanningCore G T hT i j : Set V)).Connected := by
  have hi : i ∈ spanningCore G T hT i j :=
    spanningCoreTerminals_subset G T hT i j (Finset.mem_insert_self _ _)
  apply T.induce_connected_of_patches i hi
  intro x hx
  obtain ⟨s, hs, hxs⟩ := Finset.mem_biUnion.mp hx
  let p := spanningTreePath hT i s
  refine ⟨{v | v ∈ p.support}, ?_, p.start_mem_support, List.mem_toFinset.mp hxs, ?_⟩
  · intro v hv
    exact Finset.mem_biUnion.mpr ⟨s, hs, List.mem_toFinset.mpr hv⟩
  · exact p.connected_induce_support _ _

theorem spanningCore_tree_isTree (G T : SimpleGraph V) (hT : T.IsTree) (i j : V) :
    (T.induce (spanningCore G T hT i j : Set V)).IsTree :=
  ⟨spanningCore_tree_connected G T hT i j,
    graph_acyclic_induce T _ hT.IsAcyclic⟩

omit [DecidableEq V] in
theorem tree_graphExcess_zero (T : SimpleGraph V) (hT : T.IsTree) : graphExcess T = 0 := by
  have heuler := connected_graph_excess_euler T hT.isConnected
  have htree := (SimpleGraph.isTree_iff_connected_and_card.mp hT).2
  unfold graphEdgeCount at heuler
  omega

/-- Every outside T component has exactly one actual boundary edge into
the connected core, by the proved cutset count and zero tree excess. -/
theorem spanningCore_tree_cutMultiplicity_one (G T : SimpleGraph V) (hT : T.IsTree)
    (i j : V) (A : CutComponent T (spanningCore G T hT i j : Set V)) :
    cutMultiplicity T (spanningCore G T hT i j : Set V) A = 1 := by
  have hi : i ∈ spanningCore G T hT i j :=
    spanningCoreTerminals_subset G T hT i j (Finset.mem_insert_self _ _)
  have hlo := cutMultiplicity_positive T (spanningCore G T hT i j : Set V)
    hT.isConnected ⟨i, hi⟩ A
  have hupper := component_cut_multiplicity_bound T (spanningCore G T hT i j : Set V)
    hT.isConnected (spanningCore_tree_connected G T hT i j) 0
    (by rw [tree_graphExcess_zero T hT]) A
  omega

/-- Each actual outside component is a finite tree. -/
theorem spanningCore_component_isTree (G T : SimpleGraph V) (hT : T.IsTree) (i j : V)
    (A : CutComponent T (spanningCore G T hT i j : Set V)) :
    (cutComponentGraph T (spanningCore G T hT i j : Set V) A).IsTree := by
  refine ⟨A.connected_induce_supp, ?_⟩
  apply graph_acyclic_induce
  exact graph_acyclic_induce T _ hT.IsAcyclic

/-- The unique attachment creates deficit one at exactly one vertex of the
outside tree, and zero at all others. -/
theorem spanningCore_component_root_deficit (G T : SimpleGraph V) (hT : T.IsTree)
    (i j : V) (A : CutComponent T (spanningCore G T hT i j : Set V)) :
    ∃ root : A.supp, cutDeficit T (spanningCore G T hT i j : Set V) A root = 1 ∧
      ∀ v : A.supp, v ≠ root → cutDeficit T (spanningCore G T hT i j : Set V) A v = 0 := by
  let C : Set V := (spanningCore G T hT i j : Set V)
  let δ := cutDeficit T C A
  have hi : i ∈ C := spanningCoreTerminals_subset G T hT i j (Finset.mem_insert_self _ _)
  have hsum : (∑ v : A.supp, δ v) = 1 := by
    have hsum₀ := cutMultiplicity_eq_sum_deficit T C A
    rw [spanningCore_tree_cutMultiplicity_one G T hT i j A] at hsum₀
    simp only [← finsum_eq_sum_of_fintype] at hsum₀ ⊢
    exact hsum₀.symm
  obtain ⟨root, hroot⟩ := cutDeficit_nonzero T C hT.isConnected ⟨i, hi⟩ A
  have hrootle : δ root ≤ 1 := by
    calc
      _ ≤ ∑ v : A.supp, δ v := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ root)
      _ = 1 := hsum
  have hrootone : δ root = 1 := by change 0 < δ root at hroot; omega
  refine ⟨root, hrootone, ?_⟩
  intro v hv
  have hpair : δ root + δ v ≤ 1 := by
    calc
      _ = ∑ x ∈ ({root, v} : Finset A.supp), δ x := by simp [hv, hv.symm]
      _ ≤ ∑ x : A.supp, δ x := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
      _ = 1 := hsum
  change δ v = 0
  omega

/-- The actual G boundary and the tree boundary agree, since every edge
touching an outside vertex was proved to belong to T. -/
def spanningCoreBoundaryEquiv (G T : SimpleGraph V) (hTG : T ≤ G)
    (hT : T.IsTree) (i j : V) :
    BoundaryOrientedEdge G (spanningCore G T hT i j : Set V) ≃
      BoundaryOrientedEdge T (spanningCore G T hT i j : Set V) where
  toFun e := ⟨e.val,
    (spanningCore_outside_adj G T hT i j e.val.2 e.val.1 e.property.2.2 e.property.1.symm).symm,
    e.property.2⟩
  invFun e := ⟨e.val, hTG e.property.1, e.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Actual G boundary edges entering an outside component. Components are
indexed in T, canonically the same outside graph by spanningCore_outside_graph_eq. -/
def CoreAttachmentFiber (G T : SimpleGraph V) (hT : T.IsTree) (i j : V)
    (A : CutComponent T (spanningCore G T hT i j : Set V)) :=
  {e : BoundaryOrientedEdge G (spanningCore G T hT i j : Set V) //
    (outsideGraph T (spanningCore G T hT i j : Set V)).connectedComponentMk
      ⟨e.val.2, e.property.2.2⟩ = A}

def coreAttachmentFiberEquiv (G T : SimpleGraph V) (hTG : T ≤ G) (hT : T.IsTree)
    (i j : V) (A : CutComponent T (spanningCore G T hT i j : Set V)) :
    CoreAttachmentFiber G T hT i j A ≃
      CutBoundaryEdge T (spanningCore G T hT i j : Set V) A where
  toFun e := ⟨spanningCoreBoundaryEquiv G T hTG hT i j e.val, e.property⟩
  invFun e := ⟨(spanningCoreBoundaryEquiv G T hTG hT i j).symm e.val, e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Each actual outside forest component has exactly one actual G attachment
to the core. There is no assumed attachment bound in this statement. -/
theorem spanningCore_attachment_card_one (G T : SimpleGraph V) (hTG : T ≤ G)
    (hT : T.IsTree) (i j : V)
    (A : CutComponent T (spanningCore G T hT i j : Set V)) :
    Nat.card (CoreAttachmentFiber G T hT i j A) = 1 := by
  calc
    _ = Nat.card (CutBoundaryEdge T (spanningCore G T hT i j : Set V) A) :=
      Nat.card_congr (coreAttachmentFiberEquiv G T hTG hT i j A)
    _ = 1 := spanningCore_tree_cutMultiplicity_one G T hT i j A

/-- Canonical identification of the actual G and T outside components. -/
def spanningCoreOutsideIso (G T : SimpleGraph V) (hTG : T ≤ G) (hT : T.IsTree)
    (i j : V) : outsideGraph G (spanningCore G T hT i j : Set V) ≃g
      outsideGraph T (spanningCore G T hT i j : Set V) where
  toEquiv := Equiv.refl _
  map_rel_iff' := by
    intro u v
    change T.Adj u.val v.val ↔ G.Adj u.val v.val
    exact ⟨fun h => hTG h,
      spanningCore_outside_adj G T hT i j u.val v.val u.property⟩

def spanningCoreCutBoundaryEquiv (G T : SimpleGraph V) (hTG : T ≤ G) (hT : T.IsTree)
    (i j : V) (A : CutComponent G (spanningCore G T hT i j : Set V)) :
    CutBoundaryEdge G (spanningCore G T hT i j : Set V) A ≃
      CoreAttachmentFiber G T hT i j ((spanningCoreOutsideIso G T hTG hT i j).connectedComponentEquiv A) where
  toFun e := ⟨e.val, congrArg (spanningCoreOutsideIso G T hTG hT i j).connectedComponentEquiv e.property⟩
  invFun e := ⟨e.val, by
    apply (spanningCoreOutsideIso G T hTG hT i j).connectedComponentEquiv.injective
    exact e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The unique attachment conclusion in the literal actual-G component and
cutMultiplicity identifiers, with no component-identification premise. -/
theorem spanningCore_cutMultiplicity_one (G T : SimpleGraph V) (hTG : T ≤ G)
    (hT : T.IsTree) (i j : V)
    (A : CutComponent G (spanningCore G T hT i j : Set V)) :
    cutMultiplicity G (spanningCore G T hT i j : Set V) A = 1 := by
  calc
    _ = Nat.card (CoreAttachmentFiber G T hT i j
        ((spanningCoreOutsideIso G T hTG hT i j).connectedComponentEquiv A)) :=
      Nat.card_congr (spanningCoreCutBoundaryEquiv G T hTG hT i j A)
    _ = 1 := spanningCore_attachment_card_one G T hTG hT i j _

theorem spanningCore_actual_component_isTree (G T : SimpleGraph V) (hTG : T ≤ G)
    (hT : T.IsTree) (i j : V)
    (A : CutComponent G (spanningCore G T hT i j : Set V)) :
    (cutComponentGraph G (spanningCore G T hT i j : Set V) A).IsTree := by
  refine ⟨A.connected_induce_supp, ?_⟩
  apply graph_acyclic_induce
  exact spanningCore_outside_acyclic G T hTG hT i j

/-- The literal actual-G deletion deficit is one at one outside-tree root
and zero elsewhere. This supplies the physical cavity-tree deficit data. -/
theorem spanningCore_actual_root_deficit (G T : SimpleGraph V) (hTG : T ≤ G)
    (hT : T.IsTree) (i j : V)
    (A : CutComponent G (spanningCore G T hT i j : Set V)) :
    ∃ root : A.supp, cutDeficit G (spanningCore G T hT i j : Set V) A root = 1 ∧
      ∀ v : A.supp, v ≠ root → cutDeficit G (spanningCore G T hT i j : Set V) A v = 0 := by
  let C : Set V := (spanningCore G T hT i j : Set V)
  let δ := cutDeficit G C A
  have hi : i ∈ C := spanningCoreTerminals_subset G T hT i j (Finset.mem_insert_self _ _)
  have hsum : (∑ v : A.supp, δ v) = 1 := by
    have hsum₀ := cutMultiplicity_eq_sum_deficit G C A
    rw [spanningCore_cutMultiplicity_one G T hTG hT i j A] at hsum₀
    simp only [← finsum_eq_sum_of_fintype] at hsum₀ ⊢
    exact hsum₀.symm
  obtain ⟨root, hroot⟩ := cutDeficit_nonzero G C (hT.isConnected.mono hTG) ⟨i, hi⟩ A
  have hrootle : δ root ≤ 1 := by
    calc
      _ ≤ ∑ v : A.supp, δ v := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ root)
      _ = 1 := hsum
  have hrootone : δ root = 1 := by change 0 < δ root at hroot; omega
  refine ⟨root, hrootone, ?_⟩
  intro v hv
  have hpair : δ root + δ v ≤ 1 := by
    calc
      _ = ∑ x ∈ ({root, v} : Finset A.supp), δ x := by simp [hv, hv.symm]
      _ ≤ ∑ x : A.supp, δ x := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
      _ = 1 := hsum
  change δ v = 0
  omega

end LocalLaw
