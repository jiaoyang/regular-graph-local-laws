import LocalLaw.PostBranchComponents
import LocalLaw.EndpointBranchTrees

/-! # Genuine connected fibers of the constructed surgery labels -/

noncomputable section
namespace LocalLaw
local instance branchLabelFibersDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace BranchAttachmentData
variable {V I : Type*} {old post : SimpleGraph V}

def labelFiber (D : BranchAttachmentData V I old post)
    (l : (old.induce D.core).ConnectedComponent ⊕ I) : Set V := {v | D.vertexLabel v = l}

def centralFiber (D : BranchAttachmentData V I old post)
    (c : (old.induce D.core).ConnectedComponent) : Set V := D.labelFiber (Sum.inl c)

def centralFiberCore (D : BranchAttachmentData V I old post)
    (c : (old.induce D.core).ConnectedComponent) : Set (D.centralFiber c) := {v | v.val ∈ D.core}

theorem core_edge_persists (D : BranchAttachmentData V I old post)
    (hcore : post.induce D.core = old.induce D.core)
    {u v : V} (hu : u ∈ D.core) (hv : v ∈ D.core) (h : old.Adj u v) : post.Adj u v := by
  have he := congrArg (fun G => G.Adj (⟨u, hu⟩ : D.core) (⟨v, hv⟩ : D.core)) hcore
  exact he.mpr h

theorem labelFiber_connected (D : BranchAttachmentData V I old post)
    (hcore : post.induce D.core = old.induce D.core)
    (hB : ∀ i, (post.induce (D.B i)).IsTree) (hC : ∀ i, (post.induce (D.C i)).IsTree)
    (l : (old.induce D.core).ConnectedComponent ⊕ I) (hne : Nonempty (D.labelFiber l)) :
    (post.induce (D.labelFiber l)).Connected := by
  obtain ⟨x⟩ := hne
  let c := post.connectedComponentMk x.val
  have heq : D.labelFiber l = c.supp := by
    ext v
    constructor
    · intro hv
      have hr := (D.reachable_iff_vertexLabel_eq (D.core_edge_persists hcore)
        (fun i => (hB i).isConnected.preconnected) (fun i => (hC i).isConnected.preconnected) x.val v).mpr
          (x.property.trans hv.symm)
      exact (SimpleGraph.ConnectedComponent.sound hr).symm
    · intro hv
      have hr : post.Reachable x.val v := SimpleGraph.ConnectedComponent.exact hv.symm
      exact (D.vertexLabel_eq_of_reachable hr).symm.trans x.property
  rw [heq]
  exact c.connected_induce_supp

theorem centralFiber_nonempty (D : BranchAttachmentData V I old post)
    (c : (old.induce D.core).ConnectedComponent) : Nonempty (D.centralFiber c) := by
  obtain ⟨v, hv⟩ := c.exists_rep
  refine ⟨⟨v.val, ?_⟩⟩
  exact (D.vertexLabel_core v.val v.property).trans (congrArg Sum.inl hv)

theorem centralFiber_connected (D : BranchAttachmentData V I old post)
    (hcore : post.induce D.core = old.induce D.core)
    (hB : ∀ i, (post.induce (D.B i)).IsTree) (hC : ∀ i, (post.induce (D.C i)).IsTree)
    (c : (old.induce D.core).ConnectedComponent) : (post.induce (D.centralFiber c)).Connected :=
  D.labelFiber_connected hcore hB hC (Sum.inl c) (D.centralFiber_nonempty c)

def centralFiberCoreIso (D : BranchAttachmentData V I old post)
    (hcore : post.induce D.core = old.induce D.core)
    (c : (old.induce D.core).ConnectedComponent) :
    ((old.induce D.core).induce c.supp) ≃g
      ((post.induce (D.centralFiber c)).induce (D.centralFiberCore c)) where
  toEquiv :=
    { toFun := fun v => ⟨⟨v.val.val, (D.vertexLabel_core v.val.val v.val.property).trans
          (congrArg Sum.inl v.property)⟩, v.val.property⟩
      invFun := fun v => ⟨⟨v.val.val, v.property⟩, by
        have h := v.val.property
        change D.vertexLabel v.val.val = Sum.inl c at h
        rw [D.vertexLabel_core v.val.val v.property] at h
        exact Sum.inl.inj h⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := by
    intro u v
    exact Iff.of_eq (congrArg (fun G => G.Adj u.val v.val) hcore)

theorem centralFiberCore_connected (D : BranchAttachmentData V I old post)
    (hcore : post.induce D.core = old.induce D.core)
    (c : (old.induce D.core).ConnectedComponent) :
    ((post.induce (D.centralFiber c)).induce (D.centralFiberCore c)).Connected :=
  (D.centralFiberCoreIso hcore c).connected_iff.mp c.connected_induce_supp

theorem centralFiber_B_subset (D : BranchAttachmentData V I old post)
    (c : (old.induce D.core).ConnectedComponent) (i : I) (hi : D.centralLabel i = c) :
    D.B i ⊆ D.centralFiber c := by
  intro v hv
  exact (D.vertexLabel_B i v hv).trans (congrArg Sum.inl hi)

theorem labelFiber_inr_eq_C (D : BranchAttachmentData V I old post) (i : I) :
    D.labelFiber (Sum.inr i) = D.C i := by
  ext v
  constructor
  · intro hv
    by_cases hc : v ∈ D.core
    · have h := D.vertexLabel_core v hc
      exact Sum.noConfusion (h.symm.trans hv)
    · rcases D.branchIndex_mem v hc with hB | hC
      · have h := D.vertexLabel_B _ v hB
        exact Sum.noConfusion (h.symm.trans hv)
      · have h := (D.vertexLabel_C _ v hC).symm.trans hv
        exact (Sum.inr.inj h) ▸ hC
  · exact fun hv => D.vertexLabel_C i v hv

def centralFiberPort (D : BranchAttachmentData V I old post)
    (c : (old.induce D.core).ConnectedComponent) (i : {i : I // D.centralLabel i = c}) : D.centralFiber c :=
  ⟨D.attach i.val, (D.vertexLabel_core _ (D.attach_mem i.val)).trans (congrArg Sum.inl i.property)⟩

def centralFiberBase (D : BranchAttachmentData V I old post)
    (c : (old.induce D.core).ConnectedComponent) (i : {i : I // D.centralLabel i = c}) : D.centralFiber c :=
  ⟨D.base i.val, (D.vertexLabel_B i.val _ (D.base_mem i.val)).trans (congrArg Sum.inl i.property)⟩

theorem centralFiber_tree_cut_components (D : BranchAttachmentData V I old post)
    (hB : ∀ i, (post.induce (D.B i)).IsTree)
    (c : (old.induce D.core).ConnectedComponent) :
    (∀ e : CutComponent (post.induce (D.centralFiber c)) (D.centralFiberCore c),
      (cutComponentGraph (post.induce (D.centralFiber c)) (D.centralFiberCore c) e).IsTree) ∧
    (∀ e : CutComponent (post.induce (D.centralFiber c)) (D.centralFiberCore c),
      cutMultiplicity (post.induce (D.centralFiber c)) (D.centralFiberCore c) e = 1) := by
  let branch : {i : I // D.centralLabel i = c} → Set (D.centralFiber c) := fun i => {v | v.val ∈ D.B i.val}
  apply attached_tree_cut_components (post.induce (D.centralFiber c)) (D.centralFiberCore c)
    branch (D.centralFiberPort c) (D.centralFiberBase c)
  · exact fun i => D.attach_mem i.val
  · exact fun i => D.base_mem i.val
  · intro i v hv hc
    exact D.not_core_of_branch i.val v.val (Or.inl hv) hc
  · intro v hv
    rcases D.cover v.val hv with ⟨i, hi | hi⟩
    · have hh := (D.vertexLabel_B i v.val hi).symm.trans v.property
      exact ⟨⟨i, Sum.inl.inj hh⟩, hi⟩
    · have hh := (D.vertexLabel_C i v.val hi).symm.trans v.property
      exact Sum.noConfusion hh
  · intro i u v hu hv huv
    exact D.B_closed_outside_core i.val hu hv huv
  · intro i
    exact induce_preimage_isTree post (D.centralFiber c) (D.B i.val)
      (D.centralFiber_B_subset c i.val i.property) (hB i.val)
  · intro i u v hu hv
    simpa only [centralFiberPort, centralFiberBase, Subtype.ext_iff] using D.core_B_cut_iff i.val hu hv

end BranchAttachmentData
end LocalLaw
