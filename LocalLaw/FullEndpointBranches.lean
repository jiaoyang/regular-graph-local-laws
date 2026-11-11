import LocalLaw.SwitchedRetainedReference
import LocalLaw.EndpointBranchTrees
import LocalLaw.PostBranchComponents

/-! # Literal pendant branches after filling the retained vertices -/

noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance fullEndpointBranchesDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type} [Fintype ι]

def fullEndpointEmbedding (s : LabelledResamplingState V T ι) (selector r : ℕ) :
    s.endpointModelVertices selector r ↪ filledExteriorVertices T (s.endpointModelVertices selector r) where
  toFun x := ⟨x.val.val,Or.inr ⟨x.val,x.property,rfl⟩⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : filledExteriorVertices T (s.endpointModelVertices selector r) => x.val) h

def fullEndpointCore (s : LabelledResamplingState V T ι) (selector r : ℕ) :
    Set (filledExteriorVertices T (s.endpointModelVertices selector r)) :=
  {x | x.val ∈ filledExteriorVertices T (s.centralEndpointPatch r)}

def fullEndpointBranch (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2*r+2≤selector) (i : s.AdmissibleSampleIndex selector ⊕ s.AdmissibleSampleIndex selector) :
    Set (filledExteriorVertices T (s.endpointModelVertices selector r)) :=
  let D := s.endpointBranchAttachmentData selector r hsep
  s.fullEndpointEmbedding selector r '' (match i with | Sum.inl i => D.B i | Sum.inr i => D.C i)

theorem endpoint_final_not_B (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2*r+2≤selector) (i : s.AdmissibleSampleIndex selector) (j : ι) :
    s.endpointModelKernelEmbedding selector r (s.endpointFinalBoundaryRoot selector j) ∉
      (s.endpointBranchAttachmentData selector r hsep).B i := by
  let D := s.endpointBranchAttachmentData selector r hsep
  by_cases hj : s.Eligible selector j
  · let k : s.AdmissibleSampleIndex selector := ⟨j,hj⟩
    have heq : s.endpointModelKernelEmbedding selector r (s.endpointFinalBoundaryRoot selector j) = D.tip k := by
      simp only [endpointFinalBoundaryRoot,dif_pos hj]
      rfl
    rw [heq]
    intro hB
    have hik := D.branch_family_index (Or.inl hB) (Or.inr (D.tip_mem k))
    rw [← hik] at hB
    exact Set.disjoint_left.mp (D.branch_disjoint i) hB (D.tip_mem i)
  · have hcore : s.endpointModelKernelEmbedding selector r (s.endpointFinalBoundaryRoot selector j) ∈ D.core := by
      simp only [endpointFinalBoundaryRoot,dif_neg hj]
      exact ⟨_,⟨s.boundary j,rfl⟩,center_mem_graphBall _ _ r⟩
    exact D.core_not_mem_B i _ hcore

theorem endpoint_final_mem_C (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2*r+2≤selector) (i : s.AdmissibleSampleIndex selector) (j : ι)
    (h : s.endpointModelKernelEmbedding selector r (s.endpointFinalBoundaryRoot selector j) ∈
      (s.endpointBranchAttachmentData selector r hsep).C i) : j=i.val := by
  let D := s.endpointBranchAttachmentData selector r hsep
  by_cases hj : s.Eligible selector j
  · let k : s.AdmissibleSampleIndex selector := ⟨j,hj⟩
    have heq : s.endpointModelKernelEmbedding selector r (s.endpointFinalBoundaryRoot selector j) = D.tip k := by
      simp only [endpointFinalBoundaryRoot,dif_pos hj]
      rfl
    rw [heq] at h
    exact congrArg Subtype.val (D.branch_family_index (Or.inr (D.tip_mem k)) (Or.inr h))
  · have hcore : s.endpointModelKernelEmbedding selector r (s.endpointFinalBoundaryRoot selector j) ∈ D.core := by
      simp only [endpointFinalBoundaryRoot,dif_neg hj]
      exact ⟨_,⟨s.boundary j,rfl⟩,center_mem_graphBall _ _ r⟩
    exact False.elim (D.core_not_mem_C i _ hcore h)


def fullEndpointOutsidePoint (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (x : filledExteriorVertices T (s.endpointModelVertices selector r)) (hx : x.val ∉ T) :
    s.endpointModelVertices selector r :=
  ⟨⟨x.val,hx⟩,(filledExterior_outside_mem T (s.endpointModelVertices selector r) ⟨x.val,hx⟩).mp x.property⟩

omit [Fintype ι] in
theorem fullEndpointEmbedding_outsidePoint (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (x : filledExteriorVertices T (s.endpointModelVertices selector r)) (hx : x.val ∉ T) :
    s.fullEndpointEmbedding selector r (s.fullEndpointOutsidePoint selector r x hx) = x := rfl

theorem fullEndpointEmbedding_core (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2*r+2≤selector) (x : s.endpointModelVertices selector r) :
    s.fullEndpointEmbedding selector r x ∈ s.fullEndpointCore selector r ↔
      x ∈ (s.endpointBranchAttachmentData selector r hsep).core := by
  change x.val.val ∈ filledExteriorVertices T (s.centralEndpointPatch r) ↔ _
  rw [filledExterior_outside_mem]
  rfl

theorem fullEndpointBranch_not_inner (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2*r+2≤selector) (i : s.AdmissibleSampleIndex selector ⊕ s.AdmissibleSampleIndex selector)
    {x : filledExteriorVertices T (s.endpointModelVertices selector r)}
    (hx : x ∈ s.fullEndpointBranch selector r hsep i) : x.val ∉ T := by
  obtain ⟨y,hy,rfl⟩ := hx
  exact y.val.property

def fullEndpointBranchIso (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2*r+2≤selector) (i : s.AdmissibleSampleIndex selector ⊕ s.AdmissibleSampleIndex selector) :
    (((s.fullResample selector).graph.induce (filledExteriorVertices T (s.endpointModelVertices selector r))).induce
      (s.fullEndpointBranch selector r hsep i)) ≃g
    (s.endpointPostGraph selector r).induce
      (match i with | Sum.inl i => (s.endpointBranchAttachmentData selector r hsep).B i
                    | Sum.inr i => (s.endpointBranchAttachmentData selector r hsep).C i) where
  toEquiv :=
    { toFun := fun x => ⟨s.fullEndpointOutsidePoint selector r x.val
          (s.fullEndpointBranch_not_inner selector r hsep i x.property),by
        obtain ⟨y,hy,heq⟩ := x.property
        have hh : s.fullEndpointOutsidePoint selector r x.val
            (s.fullEndpointBranch_not_inner selector r hsep i x.property) = y := by
          apply (s.fullEndpointEmbedding selector r).injective
          exact (s.fullEndpointEmbedding_outsidePoint selector r x.val _).trans heq.symm
        exact hh ▸ hy⟩
      invFun := fun x => ⟨s.fullEndpointEmbedding selector r x.val,⟨x.val,x.property,rfl⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := Iff.rfl

theorem fullEndpointBranch_isTree (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2*r+2≤selector) (i : s.AdmissibleSampleIndex selector ⊕ s.AdmissibleSampleIndex selector) :
    (((s.fullResample selector).graph.induce (filledExteriorVertices T (s.endpointModelVertices selector r))).induce
      (s.fullEndpointBranch selector r hsep i)).IsTree := by
  let e := s.fullEndpointBranchIso selector r hsep i
  have htree : ((s.endpointPostGraph selector r).induce
      (match i with | Sum.inl i => (s.endpointBranchAttachmentData selector r hsep).B i
                    | Sum.inr i => (s.endpointBranchAttachmentData selector r hsep).C i)).IsTree := by
    cases i with
    | inl i => exact s.endpoint_B_isTree selector r hsep i
    | inr i => exact s.endpoint_C_isTree selector r hsep i
  constructor
  · exact e.connected_iff.mpr htree.isConnected
  · intro v p hp
    exact htree.IsAcyclic (p.map e.toHom) (hp.map e.injective)


def fullEndpointPort (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (_hsep : 2*r+2≤selector) (i : s.AdmissibleSampleIndex selector ⊕ s.AdmissibleSampleIndex selector) :
    filledExteriorVertices T (s.endpointModelVertices selector r) :=
  match i with
  | Sum.inl i => s.fullEndpointEmbedding selector r (s.endpointAttachmentVertex selector r i)
  | Sum.inr i => ⟨(s.boundary i.val).val.1,Or.inl (s.boundary i.val).property.2.1⟩

def fullEndpointBranchRoot (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (_hsep : 2*r+2≤selector) (i : s.AdmissibleSampleIndex selector ⊕ s.AdmissibleSampleIndex selector) :
    filledExteriorVertices T (s.endpointModelVertices selector r) :=
  s.fullEndpointEmbedding selector r (match i with
    | Sum.inl i => s.endpointBaseVertex selector r i | Sum.inr i => s.endpointTipVertex selector r i)

theorem endpoint_new_boundary_point (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (u : filledExteriorVertices T (s.endpointModelVertices selector r)) (hu : u.val∈T)
    (v : s.endpointModelVertices selector r)
    (h : (s.fullResample selector).graph.Adj u.val v.val.val) :
    ∃ j, s.endpointModelKernelEmbedding selector r (s.endpointFinalBoundaryRoot selector j) = v ∧
      (s.boundary j).val.1=u.val := by
  let e : BoundaryOrientedEdge (s.fullResample selector).graph T := ⟨(u.val,v.val.val),h,hu,v.val.property⟩
  obtain ⟨j,hj⟩ := (s.fullResample selector).boundary.surjective e
  refine ⟨j,?_,?_⟩
  · apply Subtype.ext
    exact (s.endpointFinalBoundaryRoot_outer selector j).trans (congrArg (boundaryOutsideVertex _ T) hj)
  · exact (s.fullResample_boundary_inner_endpoint selector j).symm.trans
      (congrArg (fun e : BoundaryOrientedEdge (s.fullResample selector).graph T => e.val.1) hj)

theorem fullEndpoint_core_B_cut (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2*r+2≤selector) (i : s.AdmissibleSampleIndex selector)
    (u v : filledExteriorVertices T (s.endpointModelVertices selector r))
    (hu : u∈s.fullEndpointCore selector r) (hv : v∈s.fullEndpointBranch selector r hsep (Sum.inl i)) :
    (s.fullResample selector).graph.Adj u.val v.val ↔
      u=s.fullEndpointPort selector r hsep (Sum.inl i) ∧
      v=s.fullEndpointBranchRoot selector r hsep (Sum.inl i) := by
  let D := s.endpointBranchAttachmentData selector r hsep
  obtain ⟨v0,hv0,rfl⟩ := hv
  constructor
  · intro h
    by_cases huT : u.val∈T
    · obtain ⟨j,hj,_⟩ := s.endpoint_new_boundary_point selector r u huT v0 h
      exact False.elim (s.endpoint_final_not_B selector r hsep i j (hj ▸ hv0))
    · let u0 := s.fullEndpointOutsidePoint selector r u huT
      have hu0 : u0∈D.core := (s.fullEndpointEmbedding_core selector r hsep u0).mp hu
      have hh := (D.core_B_cut_iff i hu0 hv0).mp h
      exact ⟨(congrArg (s.fullEndpointEmbedding selector r) hh.1).trans rfl,
        congrArg (s.fullEndpointEmbedding selector r) hh.2⟩
  · rintro ⟨hu,hv⟩
    rw [hu,hv]
    exact D.attach_edge i

theorem fullEndpoint_core_C_cut (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2*r+2≤selector) (i : s.AdmissibleSampleIndex selector)
    (u v : filledExteriorVertices T (s.endpointModelVertices selector r))
    (hu : u∈s.fullEndpointCore selector r) (hv : v∈s.fullEndpointBranch selector r hsep (Sum.inr i)) :
    (s.fullResample selector).graph.Adj u.val v.val ↔
      u=s.fullEndpointPort selector r hsep (Sum.inr i) ∧
      v=s.fullEndpointBranchRoot selector r hsep (Sum.inr i) := by
  let D := s.endpointBranchAttachmentData selector r hsep
  obtain ⟨v0,hv0,rfl⟩ := hv
  constructor
  · intro h
    by_cases huT : u.val∈T
    · obtain ⟨j,hj,hinner⟩ := s.endpoint_new_boundary_point selector r u huT v0 h
      have hji := s.endpoint_final_mem_C selector r hsep i j (hj ▸ hv0)
      subst j
      have hpoint : s.endpointModelKernelEmbedding selector r (s.endpointFinalBoundaryRoot selector i.val)=D.tip i := by
        simp only [endpointFinalBoundaryRoot,dif_pos i.property]
        rfl
      exact ⟨Subtype.ext hinner.symm,congrArg (s.fullEndpointEmbedding selector r) (hj.symm.trans hpoint)⟩
    · let u0 := s.fullEndpointOutsidePoint selector r u huT
      have hu0 : u0∈D.core := (s.fullEndpointEmbedding_core selector r hsep u0).mp hu
      exact False.elim (D.core_C_no_cut i hu0 hv0 h)
  · rintro ⟨hu,hv⟩
    rw [hu,hv]
    have hh := ((s.fullResample selector).boundary i.val).property.1
    rw [s.fullResample_boundary_inner_endpoint,s.fullResample_boundary_outer,if_pos i.property] at hh
    exact hh


theorem fullEndpoint_tree_cut_components (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2*r+2≤selector) :
    let G := (s.fullResample selector).graph.induce (filledExteriorVertices T (s.endpointModelVertices selector r))
    (∀ C : CutComponent G (s.fullEndpointCore selector r), (cutComponentGraph G (s.fullEndpointCore selector r) C).IsTree) ∧
    (∀ C : CutComponent G (s.fullEndpointCore selector r), cutMultiplicity G (s.fullEndpointCore selector r) C=1) := by
  let D := s.endpointBranchAttachmentData selector r hsep
  let S := s.fullEndpointCore selector r
  let G := (s.fullResample selector).graph.induce (filledExteriorVertices T (s.endpointModelVertices selector r))
  apply attached_tree_cut_components G S (s.fullEndpointBranch selector r hsep)
    (s.fullEndpointPort selector r hsep) (s.fullEndpointBranchRoot selector r hsep)
  · intro i
    cases i with
    | inl i => exact (s.fullEndpointEmbedding_core selector r hsep (D.attach i)).mpr (D.attach_mem i)
    | inr i => exact Or.inl (s.boundary i.val).property.2.1
  · intro i
    cases i with
    | inl i => exact ⟨D.base i,D.base_mem i,rfl⟩
    | inr i => exact ⟨D.tip i,D.tip_mem i,rfl⟩
  · intro i v hv hcore
    obtain ⟨u,hu,rfl⟩ := hv
    have hc : u∈D.core := (s.fullEndpointEmbedding_core selector r hsep u).mp hcore
    cases i with
    | inl i => exact D.not_core_of_branch i u (Or.inl hu) hc
    | inr i => exact D.not_core_of_branch i u (Or.inr hu) hc
  · intro v hv
    have hvT : v.val∉T := fun h => hv (Or.inl h)
    let v0 := s.fullEndpointOutsidePoint selector r v hvT
    have hv0 : v0∉D.core := fun h => hv ((s.fullEndpointEmbedding_core selector r hsep v0).mpr h)
    obtain ⟨i,hi | hi⟩ := D.cover v0 hv0
    · exact ⟨Sum.inl i,v0,hi,rfl⟩
    · exact ⟨Sum.inr i,v0,hi,rfl⟩
  · intro i u v hu hv huv
    obtain ⟨u0,hu0,rfl⟩ := hu
    have hvT : v.val∉T := fun h => hv (Or.inl h)
    let v0 := s.fullEndpointOutsidePoint selector r v hvT
    have hv0 : v0∉D.core := fun h => hv ((s.fullEndpointEmbedding_core selector r hsep v0).mpr h)
    cases i with
    | inl i => exact ⟨v0,D.B_closed_outside_core i hu0 hv0 huv,rfl⟩
    | inr i => exact ⟨v0,D.C_closed_outside_core i hu0 hv0 huv,rfl⟩
  · exact s.fullEndpointBranch_isTree selector r hsep
  · intro i u v hu hv
    cases i with
    | inl i => exact s.fullEndpoint_core_B_cut selector r hsep i u v hu hv
    | inr i => exact s.fullEndpoint_core_C_cut selector r hsep i u v hu hv


theorem fullEndpoint_core_edge_from_inner (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2*r+2≤selector)
    (u v : filledExteriorVertices T (s.endpointModelVertices selector r))
    (hu : u.val∈T) (hv : v∈s.fullEndpointCore selector r) (hvT : v.val∉T)
    (h : (s.fullResample selector).graph.Adj u.val v.val) : s.graph.Adj u.val v.val := by
  let D := s.endpointBranchAttachmentData selector r hsep
  let v0 := s.fullEndpointOutsidePoint selector r v hvT
  have hc : v0∈D.core := (s.fullEndpointEmbedding_core selector r hsep v0).mp hv
  obtain ⟨j,hj,hinner⟩ := s.endpoint_new_boundary_point selector r u hu v0 h
  by_cases hjE : s.Eligible selector j
  · let k : s.AdmissibleSampleIndex selector := ⟨j,hjE⟩
    have heq : s.endpointModelKernelEmbedding selector r (s.endpointFinalBoundaryRoot selector j)=D.tip k := by
      simp only [endpointFinalBoundaryRoot,dif_pos hjE]
      rfl
    have htip : D.tip k∈D.core := (hj.symm.trans heq) ▸ hc
    exact False.elim (D.not_core_of_branch k _ (Or.inr (D.tip_mem k)) htip)
  · have hyraw : v.val=(s.boundary j).val.2 := by
      have hh := congrArg (fun x : s.endpointModelVertices selector r => x.val.val) hj.symm
      simpa only [endpointFinalBoundaryRoot,dif_neg hjE,endpointModelKernelEmbedding,
        endpointRootLabel,setBallRoot] using hh
    rw [hyraw,←hinner]
    exact (s.boundary j).property.1

theorem fullEndpoint_core_edges_old (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2*r+2≤selector)
    (u v : filledExteriorVertices T (s.endpointModelVertices selector r))
    (hu : u∈s.fullEndpointCore selector r) (hv : v∈s.fullEndpointCore selector r)
    (h : (s.fullResample selector).graph.Adj u.val v.val) : s.graph.Adj u.val v.val := by
  by_cases huT : u.val∈T
  · by_cases hvT : v.val∈T
    · change ((s.fullResample selector).graph.induce T).Adj ⟨u.val,huT⟩ ⟨v.val,hvT⟩ at h
      rw [s.fullResample_induce selector] at h
      exact h
    · exact s.fullEndpoint_core_edge_from_inner selector r hsep u v huT hv hvT h
  · by_cases hvT : v.val∈T
    · exact (s.fullEndpoint_core_edge_from_inner selector r hsep v u hvT hu huT h.symm).symm
    · let D := s.endpointBranchAttachmentData selector r hsep
      let u0 := s.fullEndpointOutsidePoint selector r u huT
      let v0 := s.fullEndpointOutsidePoint selector r v hvT
      have hu0 : u0∈D.core := (s.fullEndpointEmbedding_core selector r hsep u0).mp hu
      have hv0 : v0∈D.core := (s.fullEndpointEmbedding_core selector r hsep v0).mp hv
      have heq := congrArg (fun G => G.Adj (⟨u0,hu0⟩ : D.core) (⟨v0,hv0⟩ : D.core))
        (s.endpoint_core_graph_eq selector r hsep)
      exact (Iff.of_eq heq).mp h

end LabelledResamplingState
end LocalLaw
