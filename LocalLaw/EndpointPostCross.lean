import LocalLaw.DetachedEndpointModel
import LocalLaw.SourceEndpointCorrelations
import LocalLaw.EndpointSurgerySupport
import LocalLaw.CentralUniqueAttachment

/-! # Actual post-model zero entries needed by isolated-pair surgery -/

noncomputable section
namespace LocalLaw
local instance endpointPostCrossDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem extensionGreen_zero_of_label_ne {L : Type*} (g : DeficientGraph V d) (hd : 3 ≤ d)
    (label : V → L) (hedge : ∀ {u v}, g.graph.Adj u v → label u=label v)
    (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) (u v : V) (hne : label u ≠ label v) :
    g.extensionGreen q z u v = 0 := by
  apply g.extensionGreen_zero_across_cut hd {x | label x=label u} _ q z hz hq u rfl v
    (fun h => hne h.symm)
  intro a ha b hb hab
  exact hb ((hedge hab).symm.trans ha)

end DeficientGraph

namespace LabelledResamplingState
variable {V : Type*} {T : Set V} {ι : Type*} [Fintype ι]

def endpointOwnTripleFinset (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i : s.AdmissibleSampleIndex selector) : Finset (s.endpointModelRoots selector) :=
  {s.endpointRootLabel selector (Sum.inl (s.boundary i.val)),
    s.endpointRootLabel selector (Sum.inr (i,0)),s.endpointRootLabel selector (Sum.inr (i,1))}

def endpointFinalBoundaryRoot (s : LabelledResamplingState V T ι) (selector : ℕ) (j : ι) :
    s.endpointModelRoots selector :=
  if hj : s.Eligible selector j then s.endpointRootLabel selector (Sum.inr (⟨j,hj⟩,1))
  else s.endpointRootLabel selector (Sum.inl (s.boundary j))

omit [Fintype ι] in
theorem endpointFinalBoundaryRoot_mem_triple (s : LabelledResamplingState V T ι)
    (selector : ℕ) (j : ι) :
    (s.endpointFinalBoundaryRoot selector j).val.val ∈ (s.quad j).exterior := by
  unfold endpointFinalBoundaryRoot
  split_ifs
  · exact Or.inr (Or.inr rfl)
  · exact Or.inl rfl

omit [Fintype ι] in
theorem endpointFinalBoundaryRoot_not_pair (s : LabelledResamplingState V T ι)
    (selector : ℕ) (i : s.AdmissibleSampleIndex selector) (j : ι) (hji : j ≠ i.val) :
    s.endpointFinalBoundaryRoot selector j ∉ s.endpointPairFinset selector i := by
  intro h
  have hpair := (s.mem_endpointPairFinset_iff selector i _).mp h
  have hown := s.admissiblePairRoots_subset_triple selector i hpair
  exact hji (s.eligible_triple_index_unique selector i _ hown j
    (s.endpointFinalBoundaryRoot_mem_triple selector j))

end LabelledResamplingState

namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

/-- Among actual endpoint roots, a detached model row has only its own tip. -/
theorem switchedEndpointModel_tip_root_zero (g : RegularGraph N d) (hd : 3≤d)
    (T : Set (Fin N)) (selector r : ℕ) (hsep : 2*r+2≤selector)
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (i : (g.admissibleState T labels S).AdmissibleSampleIndex selector)
    (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im)
    (v : (g.admissibleState T labels S).endpointModelRoots selector)
    (hv : v ≠ (g.admissibleState T labels S).endpointRootLabel selector (Sum.inr (i,1))) :
    let s := g.admissibleState T labels S
    (g.switchedEndpointModel T labels S selector r).extensionGreen q z
      (s.endpointRootVertex selector r (s.endpointRootLabel selector (Sum.inr (i,1))))
      (s.endpointRootVertex selector r v)=0 := by
  dsimp only
  let s := g.admissibleState T labels S
  let D := s.endpointBranchAttachmentData selector r hsep
  let M := g.switchedEndpointModel T labels S selector r
  apply M.extensionGreen_zero_of_label_ne hd D.vertexLabel (fun h => D.vertexLabel_eq_of_adj h) q z hz hq
  intro h
  have htip : D.vertexLabel (s.endpointRootVertex selector r
      (s.endpointRootLabel selector (Sum.inr (i,1)))) = Sum.inr i :=
    (congrArg D.vertexLabel (s.endpointRootVertex_label selector r hsep (Sum.inr (i,1)))).trans
      (D.fullEndpoint_label_right (s.endpointBoundaryRoot selector r) i 1)
  obtain ⟨p,hp⟩ := s.endpointRootLabel_surjective selector v
  have hvlabel : D.vertexLabel (D.fullEndpoint (s.endpointBoundaryRoot selector r) p) = Sum.inr i := by
    rw [←s.endpointRootVertex_label selector r hsep p,hp]
    exact h.symm.trans htip
  have hpeq := D.detachedEndpointFiber_unique (s.endpointBoundaryRoot selector r)
    (s.endpointBoundaryRoot_mem_central selector r) i p hvlabel
  exact hv (hp.symm.trans (congrArg (s.endpointRootLabel selector) hpeq))

theorem endpoint_central_label_unique (g : RegularGraph N d) (o : Fin N)
    (ell selector r R : ℕ) (hsep : 2*r+2≤selector) (hmargin : ell+r+1≤R)
    (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (i : (g.admissibleState (graphBallVertices g.graph o ell) labels S).AdmissibleSampleIndex selector)
    (hnot : labels i.val ∉ multiattachmentBoundaryLabels g.graph o (by omega : ell+1≤R))
    (a : BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (heq : ((g.admissibleState (graphBallVertices g.graph o ell) labels S).endpointBranchAttachmentData selector r hsep).rootLabel ((g.admissibleState (graphBallVertices g.graph o ell) labels S).endpointBoundaryRoot selector r)
        ((g.admissibleState (graphBallVertices g.graph o ell) labels S).endpointBoundaryRoot_mem_central selector r) a =
      ((g.admissibleState (graphBallVertices g.graph o ell) labels S).endpointBranchAttachmentData selector r hsep).centralLabel i) :
    a=labels i.val := by
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T labels S
  let e := s.endpointCentralIso selector r hsep
  have hh := congrArg e.connectedComponentEquiv heq
  let c := (centralBoundaryGraph g.graph T r).connectedComponentMk
    (centralBoundaryCenter g.graph T r (labels i.val))
  have ha : centralBoundaryCenter g.graph T r a ∈ c.supp := hh
  exact central_boundary_label_eq_of_not_bad g.graph o ell r R hmargin c (labels i.val) a rfl ha hnot

/-- A good uniquely attached sample triple is model-disconnected from every
other final boundary root, accepted or rejected. -/
theorem switchedEndpointModel_own_triple_cross_zero (g : RegularGraph N d) (hd : 3≤d)
    (o : Fin N) (ell selector r R : ℕ) (hsep : 2*r+2≤selector) (hmargin : ell+r+1≤R)
    (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (i : (g.admissibleState (graphBallVertices g.graph o ell) labels S).AdmissibleSampleIndex selector)
    (hnot : labels i.val ∉ multiattachmentBoundaryLabels g.graph o (by omega : ell+1≤R))
    (j : ι) (hji : j ≠ i.val) (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) :
    let s := g.admissibleState (graphBallVertices g.graph o ell) labels S
    ∀ k ∈ s.endpointOwnTripleFinset selector i,
      (g.switchedEndpointModel (graphBallVertices g.graph o ell) labels S selector r).extensionGreen q z
        (s.endpointRootVertex selector r k) (s.endpointRootVertex selector r (s.endpointFinalBoundaryRoot selector j))=0 := by
  dsimp only
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T labels S
  let D := s.endpointBranchAttachmentData selector r hsep
  let M := g.switchedEndpointModel T labels S selector r
  intro k hk
  apply M.extensionGreen_zero_of_label_ne hd D.vertexLabel (fun h => D.vertexLabel_eq_of_adj h) q z hz hq
  intro heq
  have hvertex (p : BoundaryOrientedEdge g.graph T ⊕ (s.AdmissibleSampleIndex selector × Fin 2)) :
      D.vertexLabel (s.endpointRootVertex selector r (s.endpointRootLabel selector p)) =
        D.vertexLabel (D.fullEndpoint (s.endpointBoundaryRoot selector r) p) :=
    congrArg D.vertexLabel (s.endpointRootVertex_label selector r hsep p)
  have hleft (a : BoundaryOrientedEdge g.graph T) :=
    (hvertex (Sum.inl a)).trans (D.fullEndpoint_label_left _ (s.endpointBoundaryRoot_mem_central selector r) a)
  have hbase (a : s.AdmissibleSampleIndex selector) := (hvertex (Sum.inr (a,0))).trans
    (D.fullEndpoint_label_right (s.endpointBoundaryRoot selector r) a 0)
  have htip (a : s.AdmissibleSampleIndex selector) := (hvertex (Sum.inr (a,1))).trans
    (D.fullEndpoint_label_right (s.endpointBoundaryRoot selector r) a 1)
  have hown : D.rootLabel (s.endpointBoundaryRoot selector r)
      (s.endpointBoundaryRoot_mem_central selector r) (s.boundary i.val) = D.centralLabel i := rfl
  simp only [LabelledResamplingState.endpointOwnTripleFinset,Finset.mem_insert,Finset.mem_singleton] at hk
  unfold LabelledResamplingState.endpointFinalBoundaryRoot at heq
  split_ifs at heq with hj
  · rcases hk with rfl | rfl | rfl
    · rw [hleft,hown,htip] at heq
      exact Sum.noConfusion heq
    · rw [hbase,htip] at heq
      simp only [if_pos rfl,if_neg (by decide : (1:Fin 2)≠0)] at heq
      exact Sum.noConfusion heq
    · rw [htip,htip] at heq
      simp only [if_neg (by decide : (1:Fin 2)≠0)] at heq
      exact hji (congrArg Subtype.val (Sum.inr.inj heq)).symm
  · rcases hk with rfl | rfl | rfl
    · rw [hleft,hown,hleft] at heq
      exact hji (labels.injective (g.endpoint_central_label_unique o ell selector r R hsep hmargin labels S i hnot
        (labels j) (Sum.inl.inj heq).symm))
    · rw [hbase,hleft] at heq
      simp only [if_pos rfl] at heq
      exact hji (labels.injective (g.endpoint_central_label_unique o ell selector r R hsep hmargin labels S i hnot
        (labels j) (Sum.inl.inj heq).symm))
    · rw [htip,hleft] at heq
      simp only [if_neg (by decide : (1:Fin 2)≠0)] at heq
      exact Sum.noConfusion heq

end RegularGraph
end LocalLaw
