import LocalLaw.PartialInnerRestoration
import LocalLaw.PartialInnerCovariance
import LocalLaw.PartialLMaskRows

/-! Actual new partial-inner-deletion rows from old covariance and restoration. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance actualPartialInnerRowsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
set_option maxHeartbeats 3000000
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

theorem partial_inner_model_row_caps (g:RegularGraph N d)(hd:3≤d)
    (T:Set (Fin N))(labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Fin N))(q p z:ℂ)(hz:0<z.im)(hq:0≤q.im)
    (hq0:q≠0)(hp0:p≠0)(hrel:p⁻¹=q⁻¹-q*treeEdgeWeight d^2)
    (P K δ:ℝ)(hP:0≤P)(hK:0≤K)(hδ:0≤δ)(hqnorm:‖q‖≤P)(hpnorm:‖p‖≤P)
    (ha:‖treeEdgeWeight d*q‖≤1):
    let s:=g.admissibleState T labels samples
    let Tm:=s.retainedInnerSet S
    let e:=s.partialInnerDeletedEmbedding selector S
    let G:=((g.deficient.restrict S).delete Tm).extensionGreen q z
    let H:=(((g.labelledResampledGraph T labels samples selector).deficient.restrict S).delete Tm).extensionGreen q z
    let AM:=s.partialBoundaryMask selector (s.fullSliceOutside S)
    let A:=G.submatrix (s.partialInnerBoundaryEmbedding selector S) (s.partialInnerBoundaryEmbedding selector S)
    let cut:=A⁻¹-partialLMaskRestoration AM (s.retainedInnerLabels selector S) q (treeEdgeWeight d)
    IsUnit cut→(∀i,∑j,‖cut⁻¹ i j‖≤K)→
    (∀i j,‖(G.submatrix e e-s.partialInnerOldCovariance selector S G q p (treeEdgeWeight d)) i j‖≤δ)→
    ((Fintype.card (s.PartialEndpointIndex selector (s.fullSliceOutside S)):ℝ)*
      (1+(P+2*K)*(2*‖treeEdgeWeight d‖+‖q‖*‖treeEdgeWeight d‖^2))*
        (2*‖treeEdgeWeight d‖+‖q‖*‖treeEdgeWeight d‖^2)*δ≤1/2)→
    ((Fintype.card (s.PartialEndpointIndex selector (s.fullSliceOutside S)):ℝ)*
      (2*(1+(P+2*K)*(2*‖treeEdgeWeight d‖+‖q‖*‖treeEdgeWeight d‖^2))^2*δ)≤1)→
    (∀i,∑j,‖H (e i) (e j)‖≤P+2*K+1)∧(∀j,∑i,‖H (e i) (e j)‖≤P+2*K+1):=by
  dsimp only
  let s:=g.admissibleState T labels samples
  let Tm:=s.retainedInnerSet S
  let M:=(g.deficient.restrict S).delete Tm
  let Mnew:=((g.labelledResampledGraph T labels samples selector).deficient.restrict S).delete Tm
  let e:=s.partialInnerDeletedEmbedding selector S
  let G:=M.extensionGreen q z
  let H:=Mnew.extensionGreen q z
  let AM:=s.partialBoundaryMask selector (s.fullSliceOutside S)
  let BM:=s.partialFirstMask selector (s.fullSliceOutside S)
  let CM:=s.partialSecondMask selector (s.fullSliceOutside S)
  let LM:=s.retainedInnerLabels selector S
  let A:=G.submatrix (s.partialInnerBoundaryEmbedding selector S) (s.partialInnerBoundaryEmbedding selector S)
  let J:=AM⊕(BM⊕CM)
  let I:=s.PartialEndpointIndex selector (s.fullSliceOutside S)
  let φ:I≃J:=Equiv.refl _
  intro hrestored hrows herror hsmall hmass
  have hA:IsUnit A:=M.extensionGreen_submatrix_isUnit hd (s.partialInnerBoundaryEmbedding selector S) q z hz hq
  have hA0:IsUnit A⁻¹:=Matrix.isUnit_nonsing_inv_iff.mpr hA
  have hAsym:A⁻¹.IsSymm:=by
    have hs:A.IsSymm:=by
      ext i j
      exact (M.extensionGreen_isSymm q z).apply _ _
    change (A⁻¹).transpose=A⁻¹
    rw [Matrix.transpose_nonsing_inv,hs.eq]
  have hOldInv:(partialTripleOldPrecision AM BM CM A⁻¹ q p (treeEdgeWeight d))⁻¹=
      s.partialInnerOldCovariance selector S G q p (treeEdgeWeight d):=by
    rw [(partialTripleOldPrecision_inverse AM BM CM A⁻¹ q p (treeEdgeWeight d) hA0 hq0 hp0 hrel).2]
    rw [Matrix.nonsing_inv_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA)]
    rfl
  let R0:Matrix J J ℂ:=G.submatrix e e
  let T0:Matrix J J ℂ:=H.submatrix e e
  have hup:=g.partial_inner_model_endpoint_updates hd T labels samples selector S q z hz hq
  dsimp only at hup
  have herr:∀i j:J,‖(R0-(partialTripleOldPrecision AM BM CM A⁻¹ q p (treeEdgeWeight d))⁻¹) i j‖≤δ:=by
    rw [hOldInv]
    exact herror
  have hg:=partialLMask_surgery_rows AM BM CM LM A⁻¹ q p (treeEdgeWeight d) hA0 hAsym
    hq0 hp0 hrel P K δ hP hK hδ hqnorm hpnorm ha hrestored hrows R0 T0 hup.1 herr hsmall hmass
  constructor
  · intro i
    have heq:(∑j:I,‖H (e i) (e j)‖)=∑j:J,‖T0 (φ i) j‖:=φ.sum_comp (fun j=>‖T0 (φ i) j‖)
    rw [heq]
    exact hg.1 (φ i)
  · intro j
    have heq:(∑i:I,‖H (e i) (e j)‖)=∑i:J,‖T0 i (φ j)‖:=φ.sum_comp (fun i=>‖T0 i (φ j)‖)
    rw [heq]
    exact hg.2 (φ j)

end RegularGraph
end LocalLaw
