import LocalLaw.BallEvenPatternGeometry

/-!
# Actual parent-tree components outside accepted triples

Remove the actual eligible exterior vertices from the shortest-distance
parent tree of a ball. Any remaining component that does not meet the
interior set T is contained in one accepted I-neighborhood, hence its
ambient induced graph is acyclic. This is the tree-attachment step used
when a switched small ball crosses T.
-/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw

local instance resamplingParentComponentsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace HeightParentData
variable {V : Type*} [Fintype V] (D : HeightParentData V)

theorem path_length_le_twice_height (R : ℕ) (hheight : ∀ v, D.height v ≤ R)
    {a b : V} (p : D.tree.Walk a b) (hp : p.IsPath) : p.length ≤ 2 * R := by
  obtain ⟨pa, hpa⟩ := D.walk_to_root a
  obtain ⟨pb, hpb⟩ := D.walk_to_root b
  let q₀ := pa.append pb.reverse
  let q := q₀.bypass
  have hq : q.IsPath := q₀.bypass_isPath
  have heq : p = q := congrArg Subtype.val (D.tree_isTree.IsAcyclic.path_unique ⟨p, hp⟩ ⟨q, hq⟩)
  have hlen : q₀.length ≤ 2 * R := by
    simp only [q₀, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse, hpa, hpb]
    have ha := hheight a
    have hb := hheight b
    omega
  rw [heq]
  exact q₀.length_bypass_le.trans hlen

end HeightParentData

namespace LabelledResamplingState
variable {V : Type*} [Fintype V] {T : Set V} {ι : Type*}

/-- The removed parent vertices are actual exterior vertices of eligible
coordinates, rather than an arbitrary surgery certificate. -/
def eligibleExteriorInBall (s : LabelledResamplingState V T ι) (selector : ℕ) (o : V) (r : ℕ) :
    Set (graphBallVertices s.graph o r) :=
  {v | ∃ i, s.Eligible selector i ∧ v.val ∈ (s.quad i).exterior}

abbrev ParentExteriorComponent (s : LabelledResamplingState V T ι) (selector : ℕ) (o : V) (r : ℕ) :=
  CutComponent (ballHeightParentData s.graph o r).tree (s.eligibleExteriorInBall selector o r)

/-- All ambient edges on an actual outside parent component. -/
def parentComponentAmbientGraph (s : LabelledResamplingState V T ι)
    (selector : ℕ) (o : V) (r : ℕ) (C : s.ParentExteriorComponent selector o r) : SimpleGraph C.supp :=
  (graphBall s.graph o r).comap (fun y : C.supp => y.val.val)

theorem parent_component_acyclic_away_interior (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (hsmall : 2 * r ≤ selector) (o : V)
    (hremoved : (s.eligibleExteriorInBall selector o r).Nonempty)
    (C : s.ParentExteriorComponent selector o r)
    (haway : ∀ y : C.supp, y.val.val.val ∉ T) :
    (s.parentComponentAmbientGraph selector o r C).IsAcyclic := by
  let D := ballHeightParentData s.graph o r
  let A := s.eligibleExteriorInBall selector o r
  have hDB : D.tree ≤ graphBall s.graph o r :=
    D.tree_le _ (ballHeightParentData_parent_adj s.graph o r)
  have hpositive := cutMultiplicity_positive D.tree A D.tree_isTree.isConnected hremoved C
  have hnonempty : Nonempty (CutBoundaryEdge D.tree A C) := by
    apply (Nat.card_pos_iff.mp (show 0 < Nat.card (CutBoundaryEdge D.tree A C) from hpositive)).1
  obtain ⟨e⟩ := hnonempty
  let a := e.val.val.1
  let b : C.supp := ⟨⟨e.val.val.2, e.val.property.2.2⟩, e.property⟩
  obtain ⟨i, hi, hai⟩ := e.val.property.2.1
  have haOut : a.val ∉ T := fun ht => Set.disjoint_left.mp
    (sampledSwitching_exterior_disjoint s.graph T s.samples (s.boundary i)) hai ht
  let aOut : {v : V // v ∉ T} := ⟨a.val, haOut⟩
  have hmember : ∀ y : C.supp,
      (⟨y.val.val.val, haway y⟩ : {v : V // v ∉ T}) ∈ s.tripleBall selector i := by
    intro y
    obtain ⟨p, hp⟩ := C.connected_induce_supp.exists_isPath b y
    let fTree : cutComponentGraph D.tree A C →g D.tree :=
      { toFun := fun v => v.val.val
        map_rel' := fun h => h }
    have hfTree : Function.Injective fTree := by
      intro v w h
      apply Subtype.ext
      apply Subtype.ext
      exact h
    let pTree := p.map fTree
    have hpTree : pTree.IsPath := SimpleGraph.Walk.map_isPath_of_injective hfTree hp
    have hnot : a ∉ pTree.support := by
      intro ha
      obtain ⟨v, _, hva⟩ := List.mem_map.mp (show a ∈ p.support.map fTree from by
        simpa only [pTree, SimpleGraph.Walk.support_map] using ha)
      have hnotA := v.val.property
      have hvEq : v.val.val = a := hva
      have haA : a ∈ A := e.val.property.2.1
      rw [← hvEq] at haA
      exact hnotA haA
    let pFull := pTree.cons e.val.property.1
    have hpFull : pFull.IsPath := hpTree.cons hnot
    have hlen : pFull.length ≤ 2 * r :=
      D.path_length_le_twice_height r (ballVertexHeight_le s.graph o r) pFull hpFull
    let fOut : cutComponentGraph D.tree A C →g outsideGraph s.graph T :=
      { toFun := fun v => ⟨v.val.val.val, haway v⟩
        map_rel' := fun h => hDB h }
    have hab : (outsideGraph s.graph T).Adj aOut (fOut b) := hDB e.val.property.1
    let pOut := (p.map fOut).cons hab
    refine ⟨aOut, hai, ?_⟩
    have hd := (outsideGraph s.graph T).edist_le pOut
    apply hd.trans
    apply ENat.coe_le_coe.mpr
    have hlenOut : pOut.length = pFull.length := by
      simp only [pOut, pFull, pTree, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_map]
    rw [hlenOut]
    exact hlen.trans hsmall
  let f : s.parentComponentAmbientGraph selector o r C →g
      ((outsideGraph s.graph T ⊔ SimpleGraph.edge
        (boundaryOutsideVertex s.graph T (s.boundary i))
        (sampledFirstOutsideVertex s.graph T s.samples (s.boundary i))).induce (s.tripleBall selector i)) :=
    { toFun := fun y => ⟨⟨y.val.val.val, haway y⟩, hmember y⟩
      map_rel' := fun h => Or.inl h }
  have hf : Function.Injective f := by
    intro y z h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : s.tripleBall selector i => w.val.val) h
  intro y p hp
  exact hi.1.tree.IsAcyclic (p.map f) (hp.map hf)

end LabelledResamplingState
end LocalLaw
