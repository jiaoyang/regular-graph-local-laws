import LocalLaw.PostComponentClassifier
import LocalLaw.ExcessCutset

/-!
# Recover actual cut components from a partition into attached trees

The connected-component and cut-multiplicity conclusions are proved from
literal branch sets, connected internal graphs, and their actual sole cut
edges. They are not supplied as hypotheses to the tree-attachment budget.
-/

noncomputable section
namespace LocalLaw
local instance postBranchComponentsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A walk cannot leave a set closed under actual edges. -/
theorem reachable_mem_of_edge_closed {V : Type*} (G : SimpleGraph V) (S : Set V)
    (hclosed : ∀ {u v}, u ∈ S → G.Adj u v → v ∈ S)
    {u v : V} (h : G.Reachable u v) (hu : u ∈ S) : v ∈ S := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | cons h p ih => exact ih (hclosed hu h)

namespace BranchAttachmentData
variable {V I : Type*} {old post : SimpleGraph V}

theorem branch_family_index (D : BranchAttachmentData V I old post) {i j : I} {v : V}
    (hi : v ∈ D.B i ∨ v ∈ D.C i) (hj : v ∈ D.B j ∨ v ∈ D.C j) : i = j := by
  have hc := D.not_core_of_branch i v hi
  exact (D.branchIndex_eq v hc i hi).symm.trans (D.branchIndex_eq v hc j hj)

theorem B_closed_outside_core (D : BranchAttachmentData V I old post) (i : I)
    {u v : V} (hu : u ∈ D.B i) (hv : v ∉ D.core) (h : post.Adj u v) : v ∈ D.B i := by
  rcases D.edge_cover h with h | ⟨j,huj,hvj⟩ | ⟨j,huj,_⟩ | ⟨j,h | h⟩
  · exact (D.not_core_of_branch i u (Or.inl hu) h.1).elim
  · have hij := D.branch_family_index (Or.inl hu) (Or.inl huj)
    exact hij.symm ▸ hvj
  · have hij := D.branch_family_index (Or.inl hu) (Or.inr huj)
    exact (Set.disjoint_left.mp (D.branch_disjoint i) hu (hij.symm ▸ huj)).elim
  · exact (D.not_core_of_branch i u (Or.inl hu) (h.1 ▸ D.attach_mem j)).elim
  · exact (hv (h.1 ▸ D.attach_mem j)).elim

theorem C_closed_outside_core (D : BranchAttachmentData V I old post) (i : I)
    {u v : V} (hu : u ∈ D.C i) (hv : v ∉ D.core) (h : post.Adj u v) : v ∈ D.C i := by
  rcases D.edge_cover h with h | ⟨j,huj,_⟩ | ⟨j,huj,hvj⟩ | ⟨j,h | h⟩
  · exact (D.not_core_of_branch i u (Or.inr hu) h.1).elim
  · have hij := D.branch_family_index (Or.inr hu) (Or.inl huj)
    exact (Set.disjoint_left.mp (D.branch_disjoint i) (hij.symm ▸ huj) hu).elim
  · have hij := D.branch_family_index (Or.inr hu) (Or.inr huj)
    exact hij.symm ▸ hvj
  · exact (D.not_core_of_branch i u (Or.inr hu) (h.1 ▸ D.attach_mem j)).elim
  · exact (hv (h.1 ▸ D.attach_mem j)).elim

theorem core_B_cut_iff (D : BranchAttachmentData V I old post) (i : I)
    {u v : V} (hu : u ∈ D.core) (hv : v ∈ D.B i) :
    post.Adj u v ↔ u = D.attach i ∧ v = D.base i := by
  refine ⟨?_, fun h => h.1 ▸ h.2 ▸ D.attach_edge i⟩
  intro h
  rcases D.edge_cover h with h | ⟨j,huj,_⟩ | ⟨j,huj,_⟩ | ⟨j,h | h⟩
  · exact (D.not_core_of_branch i v (Or.inl hv) h.2.1).elim
  · exact (D.not_core_of_branch j u (Or.inl huj) hu).elim
  · exact (D.not_core_of_branch j u (Or.inr huj) hu).elim
  · have hij : i = j := D.branch_family_index (Or.inl hv) (Or.inl (h.2 ▸ D.base_mem j))
    simpa only [hij] using h
  · exact (D.not_core_of_branch i v (Or.inl hv) (h.1 ▸ D.attach_mem j)).elim

theorem core_C_no_cut (D : BranchAttachmentData V I old post) (i : I)
    {u v : V} (hu : u ∈ D.core) (hv : v ∈ D.C i) : ¬post.Adj u v := by
  intro h
  rcases D.edge_cover h with h | ⟨j,huj,_⟩ | ⟨j,huj,_⟩ | ⟨j,h | h⟩
  · exact D.not_core_of_branch i v (Or.inr hv) h.2.1
  · exact D.not_core_of_branch j u (Or.inl huj) hu
  · exact D.not_core_of_branch j u (Or.inr huj) hu
  · have hij : i = j := D.branch_family_index (Or.inr hv) (Or.inl (h.2 ▸ D.base_mem j))
    exact Set.disjoint_left.mp (D.branch_disjoint i) (hij.symm ▸ (h.2 ▸ D.base_mem j)) hv
  · exact D.not_core_of_branch i v (Or.inr hv) (h.1 ▸ D.attach_mem j)

end BranchAttachmentData

/-- Each actual outside component is one of the connected branch sets. -/
theorem attached_tree_cut_components {V I : Type*} (G : SimpleGraph V) (S : Set V)
    (branch : I → Set V) (port root : I → V)
    (hport : ∀ i, port i ∈ S) (hroot : ∀ i, root i ∈ branch i)
    (hout : ∀ i v, v ∈ branch i → v ∉ S)
    (hcover : ∀ v, v ∉ S → ∃ i, v ∈ branch i)
    (hclosed : ∀ i {u v}, u ∈ branch i → v ∉ S → G.Adj u v → v ∈ branch i)
    (htree : ∀ i, (G.induce (branch i)).IsTree)
    (hcut : ∀ i u v, u ∈ S → v ∈ branch i →
      (G.Adj u v ↔ u = port i ∧ v = root i)) :
    (∀ c : CutComponent G S, (cutComponentGraph G S c).IsTree) ∧
      (∀ c : CutComponent G S, cutMultiplicity G S c = 1) := by
  have hcomponent (c : CutComponent G S) : ∃ i,
      ∀ v : {v : V // v ∉ S}, v ∈ c.supp ↔ v.val ∈ branch i := by
    obtain ⟨x, hx⟩ := c.exists_rep
    obtain ⟨i, hi⟩ := hcover x.val x.property
    refine ⟨i, fun v => ⟨?_, ?_⟩⟩
    · intro hv
      have hr : (outsideGraph G S).Reachable x v :=
        SimpleGraph.ConnectedComponent.exact (hx.trans hv.symm)
      exact reachable_mem_of_edge_closed (outsideGraph G S)
        {v | v.val ∈ branch i} (fun {_ v} hu huv => hclosed i hu v.property huv) hr hi
    · intro hv
      let f : (G.induce (branch i)) →g outsideGraph G S :=
        ⟨fun y => ⟨y.val,hout i y.val y.property⟩, fun {_ _} h => h⟩
      have hr : (outsideGraph G S).Reachable v x :=
        ((htree i).isConnected ⟨v.val,hv⟩ ⟨x.val,hi⟩).map f
      exact (SimpleGraph.ConnectedComponent.sound hr).trans hx
  constructor
  · intro c
    obtain ⟨i,hi⟩ := hcomponent c
    let e : cutComponentGraph G S c ≃g G.induce (branch i) :=
      { toEquiv :=
          { toFun := fun v => ⟨v.val.val, (hi v.val).mp v.property⟩
            invFun := fun v => ⟨⟨v.val,hout i v.val v.property⟩,
              (hi ⟨v.val,hout i v.val v.property⟩).mpr v.property⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        map_rel_iff' := Iff.rfl }
    constructor
    · exact e.connected_iff.mpr (htree i).isConnected
    · intro v p hp
      exact (htree i).IsAcyclic (p.map e.toHom) (hp.map e.injective)
  · intro c
    obtain ⟨i,hi⟩ := hcomponent c
    have hr : (⟨root i,hout i (root i) (hroot i)⟩ : {v : V // v ∉ S}) ∈ c.supp :=
      (hi _).mpr (hroot i)
    have hadj : G.Adj (port i) (root i) :=
      (hcut i _ _ (hport i) (hroot i)).mpr ⟨rfl,rfl⟩
    let canonical : CutBoundaryEdge G S c :=
      ⟨⟨(port i,root i),hadj,hport i,hout i _ (hroot i)⟩,hr⟩
    have heq (e : CutBoundaryEdge G S c) : e = canonical := by
      apply Subtype.ext
      apply Subtype.ext
      have h := (hcut i e.val.val.1 e.val.val.2 e.val.property.2.1
        ((hi _).mp e.property)).mp e.val.property.1
      exact Prod.ext h.1 h.2
    let e : CutBoundaryEdge G S c ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => canonical
        left_inv := fun e => (heq e).symm
        right_inv := fun u => by cases u; rfl }
    exact (Nat.card_congr e).trans (by simp)

end LocalLaw
