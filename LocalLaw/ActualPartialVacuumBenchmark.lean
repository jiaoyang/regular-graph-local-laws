import LocalLaw.ActualPartialModelUpdate
import LocalLaw.PartialVacuumSurgeryStability
import LocalLaw.PartialEndpointCovariance
import LocalLaw.EmbeddedDeficitRestoration

/-! # Actual partial-model stability against the restored vacuum benchmark

All inverse updates, diagonal crossing charges and principal block units
are derived for the actual old and switched restrictions. Only estimates
on the old covariance and restored old boundary block remain as inputs.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 3000000
namespace LocalLaw
local instance actualPartialVacuumBenchmarkDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type} {T:Set V} {ι:Type}

def partialVacuumNewPrecision (s:LabelledResamplingState V T ι) (selector:ℕ)
    (S:Set (Tᶜ:Set V)) (A₀:Matrix (s.partialBoundaryMask selector S) (s.partialBoundaryMask selector S) ℂ)
    (q p α:ℂ) : Matrix (s.PartialEndpointIndex selector S) (s.PartialEndpointIndex selector S) ℂ :=
  partialTripleNewPrecision (s.partialBoundaryMask selector S) (s.partialFirstMask selector S)
    (s.partialSecondMask selector S) A₀ q p α

def partialVacuumNewCovariance [Fintype ι] (s:LabelledResamplingState V T ι) (selector:ℕ)
    (S:Set (Tᶜ:Set V)) (A₀:Matrix (s.partialBoundaryMask selector S) (s.partialBoundaryMask selector S) ℂ)
    (q p α:ℂ) : Matrix (s.PartialEndpointIndex selector S) (s.PartialEndpointIndex selector S) ℂ :=
  (partialTripleNewPrecision (s.partialBoundaryMask selector S) (s.partialFirstMask selector S)
    (s.partialSecondMask selector S) A₀ q p α)⁻¹

end LabelledResamplingState
namespace RegularGraph
variable {N d:ℕ} {ι:Type} [Fintype ι]

theorem partial_boundary_precision_units (g:RegularGraph N d) (hd:3≤d)
    (T:Set (Fin N)) (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector:ℕ) (S:Set (Tᶜ:Set (Fin N))) (q z:ℂ) (hz:0<z.im) (hq:0≤q.im) :
    let s:=g.admissibleState T labels samples
    let e:=s.partialBoundaryEmbedding selector S
    let R:=(((g.deficient.delete T).restrict S).extensionGreen q z).submatrix e e
    IsUnit R∧IsUnit (R⁻¹-Matrix.diagonal (fun _:s.partialBoundaryMask selector S=>q*treeEdgeWeight d^2)) := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let M:=(g.deficient.delete T).restrict S
  let e:=s.partialBoundaryEmbedding selector S
  have hpos:∀v∈Set.range e,0<M.deficit v:=by
    intro v hv
    have hi:v∈s.includedEligibleBoundary selector S:=s.partialBoundaryEmbedding_range selector S ▸ hv
    rw [g.includedEligibleBoundary_deficit_one T labels samples selector S v hi]
    norm_num
  have hu:=M.restoreOneDeficit_embedding_inverse hd e hpos q z hz hq
  have hshift:IsUnit ((((M.extensionGreen q z).submatrix e e)⁻¹)-
      q • Matrix.diagonal (fun _:s.partialBoundaryMask selector S=>((1/((d:ℝ)-1):ℝ):ℂ))) := by
    rw [←hu.2.2]
    exact Matrix.isUnit_nonsing_inv_iff.mpr hu.2.1
  have hD:Matrix.diagonal (fun _:s.partialBoundaryMask selector S=>q*treeEdgeWeight d^2)=
      q • Matrix.diagonal (fun _:s.partialBoundaryMask selector S=>((1/((d:ℝ)-1):ℝ):ℂ)):=by
    have hcast:((1/((d:ℝ)-1):ℝ):ℂ)=1/((d:ℂ)-1):=by push_cast;rfl
    ext i j
    by_cases hij:i=j
    · subst j
      simp only [Matrix.diagonal_apply_eq,Matrix.smul_apply,smul_eq_mul,treeEdgeWeight_sq d hd,hcast]
    · simp [Matrix.diagonal_apply,hij]
  exact ⟨hu.1,by rw [hD];exact hshift⟩

theorem partial_model_vacuum_stability (g:RegularGraph N d) (hd:3≤d)
    (T:Set (Fin N)) (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector:ℕ) (S:Set (Tᶜ:Set (Fin N))) (q p z:ℂ) (hz:0<z.im) (hq:0≤q.im)
    (hq0:q≠0) (hp0:p≠0) (hrel:p⁻¹=q⁻¹-q*treeEdgeWeight d^2)
    (P K δ:ℝ) (hP:0≤P) (hK:0≤K) (hδ:0≤δ)
    (hqnorm:‖q‖≤P) (hpnorm:‖p‖≤P) (ha:‖treeEdgeWeight d*q‖≤1) :
    let s:=g.admissibleState T labels samples
    let e:=s.partialEndpointEmbedding selector S
    let G:=((g.deficient.delete T).restrict S).extensionGreen q z
    let H:=(((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S).extensionGreen q z
    let A:=G.submatrix (s.partialBoundaryEmbedding selector S) (s.partialBoundaryEmbedding selector S)
    (∀ i,∑ j,‖(A⁻¹-Matrix.diagonal (fun _:s.partialBoundaryMask selector S=>q*treeEdgeWeight d^2))⁻¹ i j‖≤K)→
    (∀ i j,‖(G.submatrix e e-s.partialOldCovariance selector S G q p (treeEdgeWeight d)) i j‖≤δ)→
    ((Fintype.card (s.PartialEndpointIndex selector S):ℝ)*
      (1+(P+2*K)*(2*‖treeEdgeWeight d‖+‖q‖*‖treeEdgeWeight d‖^2))*
        (2*‖treeEdgeWeight d‖+‖q‖*‖treeEdgeWeight d‖^2)*δ≤1/2)→
    ∀ (i j:s.PartialEndpointIndex selector S),‖H (e i) (e j)-
      (partialTripleNewPrecision (s.partialBoundaryMask selector S) (s.partialFirstMask selector S)
        (s.partialSecondMask selector S) A⁻¹ q p (treeEdgeWeight d))⁻¹ i j‖≤
      2*(1+(P+2*K)*(2*‖treeEdgeWeight d‖+‖q‖*‖treeEdgeWeight d‖^2))^2*δ := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let e:=s.partialEndpointEmbedding selector S
  let G:=((g.deficient.delete T).restrict S).extensionGreen q z
  let H:=(((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S).extensionGreen q z
  let A:=G.submatrix (s.partialBoundaryEmbedding selector S) (s.partialBoundaryEmbedding selector S)
  let AM:=s.partialBoundaryMask selector S
  let BM:=s.partialFirstMask selector S
  let CM:=s.partialSecondMask selector S
  intro hrows herr hsmall
  have hUnits:=g.partial_boundary_precision_units hd T labels samples selector S q z hz hq
  have hA0:IsUnit A⁻¹:=Matrix.isUnit_nonsing_inv_iff.mpr hUnits.1
  have hAsym:A⁻¹.IsSymm:=by
    have hS:A.IsSymm:=by
      ext i j
      exact (DeficientGraph.extensionGreen_isSymm _ q z).apply _ _
    change (A⁻¹).transpose=A⁻¹
    rw [Matrix.transpose_nonsing_inv,hS.eq]
  have hOldInv: (partialTripleOldPrecision AM BM CM A⁻¹ q p (treeEdgeWeight d))⁻¹=
      s.partialOldCovariance selector S G q p (treeEdgeWeight d):=by
    rw [(partialTripleOldPrecision_inverse AM BM CM A⁻¹ q p (treeEdgeWeight d) hA0 hq0 hp0 hrel).2]
    rw [Matrix.nonsing_inv_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hUnits.1)]
    rfl
  have hUpdate:=g.partial_model_endpoint_updates hd T labels samples selector S q z hz hq
  dsimp only at hUpdate
  rw [s.partialActualCoupling_eq selector S q (treeEdgeWeight d)] at hUpdate
  let R0:Matrix (AM⊕(BM⊕CM)) (AM⊕(BM⊕CM)) ℂ:=G.submatrix e e
  let T0:Matrix (AM⊕(BM⊕CM)) (AM⊕(BM⊕CM)) ℂ:=H.submatrix e e
  have he : ∀ i j:AM⊕(BM⊕CM),
      ‖(R0-(partialTripleOldPrecision AM BM CM A⁻¹ q p (treeEdgeWeight d))⁻¹) i j‖≤δ := by
    rw [hOldInv]
    exact herr
  have hg:=partialVacuum_surgery_stability AM BM CM A⁻¹ q p (treeEdgeWeight d)
    hA0 hAsym hq0 hp0 hrel P K δ hP hK hδ hqnorm hpnorm ha hUnits.2 hrows
    R0 T0 hUpdate.1 he hsmall
  intro i j
  exact hg i j

end RegularGraph
end LocalLaw
