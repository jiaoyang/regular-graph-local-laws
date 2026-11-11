import LocalLaw.ActualPartialModelUpdate
import LocalLaw.PartialTripleRows
import LocalLaw.AugmentedRowTransfer
import LocalLaw.PartialSamplePhysical

/-! # Actual target-to-partial-endpoint rows after switching -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance partialTargetRowTransferDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ} {ι:Type} [Fintype ι]

theorem partial_model_endpoint_mass (g:RegularGraph N d) (hd:3≤d)
    (T:Set (Fin N)) (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector:ℕ) (S:Set (Tᶜ:Set (Fin N))) (q z:ℂ) (hq:‖q‖≤2) :
    let s:=g.admissibleState T labels samples
    let e:=s.partialEndpointEmbedding selector S
    let A:=((g.deficient.delete T).restrict S).extensionMatrix q z
    let B:=(((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S).extensionMatrix q z
    (∀i,∑j,‖(B-A) (e i) (e j)‖≤4)∧(∀j,∑i,‖(B-A) (e i) (e j)‖≤4) := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let e:=s.partialEndpointEmbedding selector S
  let A:=((g.deficient.delete T).restrict S).extensionMatrix q z
  let B:=(((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S).extensionMatrix q z
  let J:=s.partialBoundaryMask selector S⊕(s.partialFirstMask selector S⊕s.partialSecondMask selector S)
  let φ:s.PartialEndpointIndex selector S≃J:=Equiv.refl _
  let W:Matrix J J ℂ:=partialTripleEdgeUpdate (s.partialBoundaryMask selector S)
    (s.partialFirstMask selector S) (s.partialSecondMask selector S) (treeEdgeWeight d)+
    partialTripleCharge (s.partialBoundaryMask selector S)
      (s.partialFirstMask selector S) (s.partialSecondMask selector S) q (treeEdgeWeight d)
  have hW:(B-A).submatrix e e=W:=
    (g.partial_model_difference_coupling hd T labels samples selector S q z).trans
      (s.partialActualCoupling_eq selector S q (treeEdgeWeight d))
  have hαsq:‖treeEdgeWeight d‖^2≤1:=by
    rw [treeEdgeWeight_norm_sq d hd]
    have hD:(3:ℝ)≤d:=Nat.cast_le.mpr hd
    exact (div_le_one (by linarith)).mpr (by linarith)
  have hα:‖treeEdgeWeight d‖≤1:=by nlinarith [norm_nonneg (treeEdgeWeight d)]
  have hw:2*‖treeEdgeWeight d‖+‖q‖*‖treeEdgeWeight d‖^2≤4:=by
    have hh:=mul_le_mul hq hαsq (sq_nonneg ‖treeEdgeWeight d‖) (by norm_num:(0:ℝ)≤2)
    nlinarith
  have hm:=partialTripleCoupling_mass (s.partialBoundaryMask selector S)
    (s.partialFirstMask selector S) (s.partialSecondMask selector S) q (treeEdgeWeight d)
  have hrow (i:s.PartialEndpointIndex selector S) : (∑j,‖(B-A) (e i) (e j)‖)≤4:=by
    have heq:(∑j,‖(B-A) (e i) (e j)‖)=∑j:J,‖W (φ i) j‖:=by
      calc
        _=∑j,‖W (φ i) (φ j)‖:=by
          apply Finset.sum_congr rfl
          intro j _
          exact congrArg norm (congrArg (fun M=>M i j) hW)
        _=_:=φ.sum_comp (fun j=>‖W (φ i) j‖)
    rw [heq]
    exact (hm.1 (φ i)).trans hw
  have hsym:((B-A).submatrix e e).IsSymm:=by
    rw [hW]
    exact partialTripleCoupling_isSymm (s.partialBoundaryMask selector S)
      (s.partialFirstMask selector S) (s.partialSecondMask selector S) q (treeEdgeWeight d)
  refine ⟨hrow,fun j=>?_⟩
  have heq:(∑i,‖(B-A) (e i) (e j)‖)=∑i,‖(B-A) (e j) (e i)‖:=
    Finset.sum_congr rfl (fun i _=>congrArg norm (hsym.apply _ _))
  rw [heq]
  exact hrow j

theorem partial_new_target_endpoint_row (g:RegularGraph N d) (hd:3≤d)
    (T:Set (Fin N)) (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector:ℕ) (S:Set (Tᶜ:Set (Fin N))) (q z:ℂ) (hz:0<z.im) (hqim:0≤q.im) (hq:‖q‖≤2)
    (a C:ℝ) (ha:0≤a) (hC:0≤C) :
    let s:=g.admissibleState T labels samples
    let e:=s.partialEndpointEmbedding selector S
    let G:=((g.deficient.delete T).restrict S).extensionGreen q z
    let H:=(((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S).extensionGreen q z
    ∀x:S,(∑i,‖G x (e i)‖)≤a→(∀i,∑j,‖H (e i) (e j)‖≤C)→
      (∑i,‖H x (e i)‖)≤a*(1+4*C) := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let old:=(g.deficient.delete T).restrict S
  let new:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S
  let e:=s.partialEndpointEmbedding selector S
  intro x hOld hNew
  exact inverse_supported_endpoint_row_sum (old.extensionMatrix q z) (new.extensionMatrix q z)
    (old.extensionMatrix_isUnit hd q z hz hqim) (new.extensionMatrix_isUnit hd q z hz hqim) e
    (g.partial_model_difference_supported T labels samples selector S q z)
    a C 4 ha hC (by norm_num) x hOld hNew
    (g.partial_model_endpoint_mass hd T labels samples selector S q z hq).1

end RegularGraph
end LocalLaw
