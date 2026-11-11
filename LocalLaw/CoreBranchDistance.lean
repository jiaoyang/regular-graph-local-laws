import LocalLaw.CoreAttachments

/-!
# Distances through an actual unique forest attachment

A walk ending in a pendant induced component has a last entry across its
unique attachment edge. Comparing genuine shortest walks on both sides gives
the exact distance factorization, rather than assuming a metric gluing rule.
-/

noncomputable section
namespace LocalLaw

local instance branchDistanceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} {G : SimpleGraph V}

def inducedVertexHom (G : SimpleGraph V) (S : Set V) : G.induce S →g G where
  toFun := Subtype.val
  map_rel' := fun h => h

/-- A walk is entirely in S, or has a last entry across the unique boundary
edge and then a genuine walk in the induced graph on S. -/
theorem walk_last_pendant_entry (S : Set V) (root : S) (port : V)
    (_hport : port ∉ S) (hedge : G.Adj port root.val)
    (boundary : ∀ u ∉ S, ∀ v ∈ S, G.Adj u v → u = port ∧ v = root.val)
    {i x : V} (p : G.Walk i x) (hx : x ∈ S) :
    (∃ hi : i ∈ S, ∃ q : (G.induce S).Walk ⟨i, hi⟩ ⟨x, hx⟩,
      p = q.map (inducedVertexHom G S)) ∨
    ∃ headWalk : G.Walk i port, ∃ tailWalk : (G.induce S).Walk root ⟨x, hx⟩,
      p = headWalk.append ((tailWalk.map (inducedVertexHom G S)).cons hedge) := by
  induction p with
  | nil => exact Or.inl ⟨hx, SimpleGraph.Walk.nil, rfl⟩
  | @cons i u x hiu p ih =>
    rcases ih hx with ⟨hu, q, hq⟩ | ⟨headWalk, tailWalk, hsplit⟩
    · by_cases hi : i ∈ S
      · left
        refine ⟨hi, q.cons (show (G.induce S).Adj ⟨i, hi⟩ ⟨u, hu⟩ from hiu), ?_⟩
        rw [hq]
        rfl
      · obtain ⟨hiport, huroot⟩ := boundary i hi u hu hiu
        subst i
        subst u
        right
        refine ⟨SimpleGraph.Walk.nil, q, ?_⟩
        rw [hq]
        rfl
    · right
      refine ⟨headWalk.cons hiu, tailWalk, ?_⟩
      rw [hsplit]
      rfl

/-- Exact distance through the unique attachment edge, derived by lower
shortest-walk decomposition and upper shortest-walk concatenation. -/
theorem pendant_component_distance (hG : G.Connected) (S : Set V)
    (hS : (G.induce S).Connected) (root : S) (port : V)
    (hport : port ∉ S) (hedge : G.Adj port root.val)
    (boundary : ∀ u ∉ S, ∀ v ∈ S, G.Adj u v → u = port ∧ v = root.val)
    (i : V) (hi : i ∉ S) (y : S) :
    G.dist i y.val = G.dist i port + 1 + (G.induce S).dist root y := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist i y.val
  obtain ⟨headWalk, tailWalk, hsplit⟩ :
      ∃ headWalk : G.Walk i port, ∃ tailWalk : (G.induce S).Walk root y,
        p = headWalk.append ((tailWalk.map (inducedVertexHom G S)).cons hedge) := by
    rcases walk_last_pendant_entry S root port hport hedge boundary p y.property with
      ⟨hi', q, hq⟩ | h
    · exact False.elim (hi hi')
    · exact h
  have hhead := G.dist_le headWalk
  have htail := (G.induce S).dist_le tailWalk
  rw [hsplit, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
    SimpleGraph.Walk.length_map] at hp
  obtain ⟨a, ha⟩ := hG.exists_walk_length_eq_dist i port
  obtain ⟨b, hb⟩ := hS.exists_walk_length_eq_dist root y
  have hupper := G.dist_le (a.append ((b.map (inducedVertexHom G S)).cons hedge))
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
    SimpleGraph.Walk.length_map, ha, hb] at hupper
  change G.dist i y.val ≤ G.dist i port + ((G.induce S).dist root y + 1) at hupper
  omega

/-- An actual outside connected component, viewed as an ambient vertex set. -/
def cutComponentVertices (G : SimpleGraph V) (C : Set V) (A : CutComponent G C) : Set V :=
  {v | ∃ hv : v ∉ C, (outsideGraph G C).connectedComponentMk ⟨v, hv⟩ = A}

/-- Flattening the two subtypes changes no edges. -/
def cutComponentFlatIso (G : SimpleGraph V) (C : Set V) (A : CutComponent G C) :
    cutComponentGraph G C A ≃g G.induce (cutComponentVertices G C A) where
  toEquiv :=
    { toFun := fun v => ⟨v.val.val, v.val.property, v.property⟩
      invFun := fun v => ⟨⟨v.val, by obtain ⟨h, _⟩ := v.property; exact h⟩,
        by obtain ⟨h, hh⟩ := v.property; exact hh⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  map_rel_iff' := Iff.rfl

private theorem componentIso_distance {W : Type*} {H : SimpleGraph W}
    (φ : H ≃g G) (hH : H.Connected) (a b : W) :
    H.dist a b = G.dist (φ a) (φ b) := by
  have hG := φ.connected_iff.mp hH
  obtain ⟨p, hp⟩ := hH.exists_walk_length_eq_dist a b
  have h₁ := G.dist_le (p.map φ.toHom)
  rw [SimpleGraph.Walk.length_map, hp] at h₁
  obtain ⟨q, hq⟩ := hG.exists_walk_length_eq_dist (φ a) (φ b)
  have h₂ := H.dist_le (q.map φ.symm.toHom)
  have h₂' : H.dist a b ≤ G.dist (φ a) (φ b) := by
    change H.dist (φ.symm (φ a)) (φ.symm (φ b)) ≤ (q.map φ.symm.toHom).length at h₂
    simpa only [SimpleGraph.Walk.length_map, hq, φ.symm_apply_apply] using h₂
  exact le_antisymm h₂' h₁

/-- An outside-component vertex cannot be adjacent to another outside
vertex of a different outside component. -/
theorem cutComponentVertices_adj_closed (G : SimpleGraph V) (C : Set V)
    (A : CutComponent G C) {u v : V} (hu : u ∉ C)
    (hv : v ∈ cutComponentVertices G C A) (huv : G.Adj u v) :
    u ∈ cutComponentVertices G C A := by
  obtain ⟨hvC, hvA⟩ := hv
  refine ⟨hu, ?_⟩
  have hadj : (outsideGraph G C).Adj ⟨u, hu⟩ ⟨v, hvC⟩ := huv
  exact (SimpleGraph.ConnectedComponent.sound hadj.reachable).trans hvA

/-- Unique actual cut boundary implies the unique pendant-entry condition;
no boundary uniqueness is assumed beyond the genuine cutMultiplicity count. -/
theorem unique_cut_boundary_entry (G : SimpleGraph V) (C : Set V) (A : CutComponent G C)
    (hcount : cutMultiplicity G C A = 1) (e : CutBoundaryEdge G C A) :
    ∀ u ∉ cutComponentVertices G C A, ∀ v ∈ cutComponentVertices G C A,
      G.Adj u v → u = e.val.val.1 ∧ v = e.val.val.2 := by
  letI : Subsingleton (CutBoundaryEdge G C A) := (Nat.card_eq_one_iff_unique.mp hcount).1
  intro u hu v hv huv
  obtain ⟨hvC, hvA⟩ := hv
  have huC : u ∈ C := by
    by_contra hnot
    exact hu (cutComponentVertices_adj_closed G C A hnot ⟨hvC, hvA⟩ huv)
  let e' : CutBoundaryEdge G C A := ⟨⟨(u, v), huv, huC, hvC⟩, hvA⟩
  have heq : e' = e := Subsingleton.elim _ _
  exact ⟨congrArg (fun f : CutBoundaryEdge G C A => f.val.val.1) heq,
    congrArg (fun f : CutBoundaryEdge G C A => f.val.val.2) heq⟩

/-- The outside root of the actual unique attachment edge. -/
def cutAttachmentRoot (G : SimpleGraph V) (C : Set V) (A : CutComponent G C)
    (e : CutBoundaryEdge G C A) : A.supp :=
  ⟨⟨e.val.val.2, e.val.property.2.2⟩, e.property⟩

/-- Exact physical distance in any genuine singly attached outside component. -/
theorem unique_cut_attachment_distance (G : SimpleGraph V) (hG : G.Connected)
    (C : Set V) (A : CutComponent G C) (hcount : cutMultiplicity G C A = 1)
    (e : CutBoundaryEdge G C A) (i : V) (hi : i ∈ C) (y : A.supp) :
    G.dist i y.val.val = G.dist i e.val.val.1 + 1 +
      (cutComponentGraph G C A).dist (cutAttachmentRoot G C A e) y := by
  let S := cutComponentVertices G C A
  let φ := cutComponentFlatIso G C A
  let root := cutAttachmentRoot G C A e
  have hS : (G.induce S).Connected := φ.connected_iff.mp A.connected_induce_supp
  have hport : e.val.val.1 ∉ S := by
    rintro ⟨hnot, _⟩
    exact hnot e.val.property.2.1
  have hiS : i ∉ S := by rintro ⟨hnot, _⟩; exact hnot hi
  have hdist := pendant_component_distance hG S hS (φ root) e.val.val.1 hport
    e.val.property.1 (unique_cut_boundary_entry G C A hcount e) i hiS (φ y)
  have hiso := componentIso_distance φ A.connected_induce_supp root y
  change G.dist i y.val.val = G.dist i e.val.val.1 + 1 +
    (G.induce S).dist (φ root) (φ y) at hdist
  rw [← hiso] at hdist
  exact hdist

section ActualCore

variable [Fintype V] [DecidableEq V]

/-- The source distance identity at the actual constructed core. Attachment
multiplicity and component geometry are discharged by CoreAttachments. -/
theorem spanningCore_branch_distance (G T : SimpleGraph V) (hTG : T ≤ G)
    (hT : T.IsTree) (i j : V)
    (A : CutComponent G (spanningCore G T hT i j : Set V))
    (e : CutBoundaryEdge G (spanningCore G T hT i j : Set V) A)
    (v : V) (hv : v ∈ spanningCore G T hT i j) (y : A.supp) :
    G.dist v y.val.val = G.dist v e.val.val.1 + 1 +
      (cutComponentGraph G (spanningCore G T hT i j : Set V) A).dist
        (cutAttachmentRoot G (spanningCore G T hT i j : Set V) A e) y :=
  unique_cut_attachment_distance G (hT.isConnected.mono hTG) _ A
    (spanningCore_cutMultiplicity_one G T hTG hT i j A) e v hv y

end ActualCore

end LocalLaw
