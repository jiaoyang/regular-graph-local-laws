import LocalLaw.EndpointPostCross
import LocalLaw.PairSurgeryMatrixSupport
import LocalLaw.SourceEndpointMatrices

/-! # Derive both actual endpoint comparison-matrix supports -/

noncomputable section
namespace LocalLaw
local instance actualEndpointComparisonSupportDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type*} {T : Set V} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem mem_endpointOwnTripleFinset_iff (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i : s.AdmissibleSampleIndex selector) (v : s.endpointModelRoots selector) :
    v ∈ s.endpointOwnTripleFinset selector i ↔ v.val.val ∈ (s.quad i.val).exterior := by
  simp only [endpointOwnTripleFinset,Finset.mem_insert,Finset.mem_singleton,
    SwitchingQuad.exterior,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (h | h | h)
    · exact Or.inl (Subtype.ext (Subtype.ext h))
    · exact Or.inr (Or.inl (Subtype.ext (Subtype.ext h)))
    · exact Or.inr (Or.inr (Subtype.ext (Subtype.ext h)))

end LabelledResamplingState

namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

/-- Literal physical coupling rows vanish outside their own selected triple. -/
theorem sourceEndpointW_pair_row_zero (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector : ℕ) (i : (g.admissibleState T labels S).AdmissibleSampleIndex selector) :
    let s := g.admissibleState T labels S
    ∀ u ∈ s.endpointPairFinset selector i, ∀ v ∉ s.endpointOwnTripleFinset selector i,
      g.sourceEndpointW T labels S selector u v=0 := by
  dsimp only
  let s := g.admissibleState T labels S
  intro u hu v hv
  have hown := s.admissiblePairRoots_subset_triple selector i
    ((s.mem_endpointPairFinset_iff selector i u).mp hu)
  have hvraw : v.val.val ∉ (s.quad i.val).exterior :=
    fun h => hv ((s.mem_endpointOwnTripleFinset_iff selector i v).mpr h)
  have heq := s.fullResample_outside_row_unchanged_away_triple selector i u.val v.val hown hvraw
  change (normalizedAdjacency (outsideGraph (s.fullResample selector).graph T) d -
    normalizedAdjacency (outsideGraph s.graph T) d) u.val v.val=0
  simp only [normalizedAdjacency,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,SimpleGraph.adjMatrix_apply]
  rw [heq,sub_self]

/-- The actual Q/W matrices provide every support condition used by paired
surgery; none of those conditions is an assumption of this wrapper. -/
theorem source_endpoint_comparison_support (g : RegularGraph N d) (hd : 3≤d) (o : Fin N)
    (ell selector r R : ℕ) (hsep : 2*r+2≤selector) (hmargin : ell+r+1≤R)
    (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (i : (g.admissibleState (graphBallVertices g.graph o ell) labels S).AdmissibleSampleIndex selector)
    (hnot : labels i.val ∉ multiattachmentBoundaryLabels g.graph o (by omega : ell+1≤R))
    (j : ι) (hji : j≠i.val) (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) :
    let T := graphBallVertices g.graph o ell
    let s := g.admissibleState T labels S
    let Q := g.sourceEndpointQ T labels S selector r q z
    let W := g.sourceEndpointW T labels S selector
    let tip := s.endpointRootLabel selector (Sum.inr (i,1))
    let target := s.endpointFinalBoundaryRoot selector j
    (∀ k, k ∉ s.endpointPairFinset selector i → (1-Q*W) tip k=0) ∧
      (∀ l ∈ s.endpointPairFinset selector i, (1-W*Q) l target=0) := by
  dsimp only
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T labels S
  let a := s.endpointRootLabel selector (Sum.inl (s.boundary i.val))
  let b := s.endpointRootLabel selector (Sum.inr (i,0))
  let c := s.endpointRootLabel selector (Sum.inr (i,1))
  let target := s.endpointFinalBoundaryRoot selector j
  have hpair : s.endpointPairFinset selector i = {b,c} := by
    ext k
    simp only [LabelledResamplingState.endpointPairFinset,Finset.mem_insert,Finset.mem_singleton,b,c]
  have htriple : s.endpointOwnTripleFinset selector i = {a,b,c} := by
    ext k
    simp only [LabelledResamplingState.endpointOwnTripleFinset,Finset.mem_insert,Finset.mem_singleton,a,b,c]
  rw [hpair]
  apply pair_comparison_matrix_support (g.sourceEndpointQ T labels S selector r q z)
    (g.sourceEndpointW T labels S selector) a b c target
  · intro k hk
    exact g.switchedEndpointModel_tip_root_zero hd T selector r hsep labels S i q z hz hq k hk
  · intro k hk
    apply s.outside_perturbation_tip_row_zero selector d i k.val
    intro heq
    exact hk (Subtype.ext heq)
  · intro l hl k hk
    exact g.sourceEndpointW_pair_row_zero T labels S selector i l (hpair.symm ▸ hl) k (htriple.symm ▸ hk)
  · exact hpair ▸ s.endpointFinalBoundaryRoot_not_pair selector i j hji
  · intro k hk
    exact g.switchedEndpointModel_own_triple_cross_zero hd o ell selector r R hsep hmargin
      labels S i hnot j hji q z hz hq k (htriple.symm ▸ hk)

end RegularGraph
end LocalLaw
