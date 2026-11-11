import LocalLaw.PartialFirstInverseParameters
import LocalLaw.SourcePartialGenericInputs
import LocalLaw.SourcePartialGeometry
import LocalLaw.SourceObservationGeneralCap
import LocalLaw.FormalVacuumDiagonalBounds

/-! # Actual sampled-first block inverse caps for every weak boundary value

The old strong-radius geometry and arbitrary-q weak prior derive both
restoration inverses, covariance, true switched B-block nonsingularity and
all numerical contraction conditions. No switched reference class or pivot
bound is assumed.
-/

open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance sourcePartialFirstInverseDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourcePartialFirstInverseCap (d : ℕ) (B : ℝ) : ℝ :=
  2*(2*|B|+3+4*finiteExtraReferenceConstant d)

namespace RegularGraph

theorem eventually_source_partial_first_inverse_caps (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in atTop,∀(g : RegularGraph N d)(o : Fin N)(z q : ℂ),
      0<z.im→‖z‖≤B→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→0≤q.im→
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z)→
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d)→
      ∀{ι : Type}[Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y : ((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      ∀S:Set (Tᶜ:Set (Fin N)),S⊆s.twoTargetEndpointVertices selector r x y→
      let H:=(((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S).extensionGreen q z
      let U:=H.submatrix (s.partialFirstEmbedding selector S) (s.partialFirstEmbedding selector S)
      IsUnit U ∧ (∀i,∑j,‖U⁻¹ i j‖≤sourcePartialFirstInverseCap d B) ∧
        (∀j,∑i,‖U⁻¹ i j‖≤sourcePartialFirstInverseCap d B) := by
  let Acap:=sourcePartialObservationLogCap d β
  let F:=2*(finiteOmega d:ℝ)+5
  let PInv:=2*|B|+3
  have hF : 1≤F := by dsimp only [F]; have hh:=Nat.cast_nonneg (α:=ℝ) (finiteOmega d); linarith
  have hAobs : 0≤sourceObservationLogCap d β := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hAcap : sourceObservationLogCap d β≤Acap := le_mul_of_one_le_left hAobs hF
  have hAcap0 : 0≤Acap := hAobs.trans hAcap
  have hPInv : 0≤PInv := by dsimp only [PInv]; positivity
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_source_partial_generic_inputs a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_partial_geometry a d c β (by omega) hd hc hβ hβc,
    eventually_sourceObservationBounds_of_cap a b d c β B C1 Acap ha hb hd hc hβ hβc hC1 hAcap,
    eventually_source_formal_kernel_bounds a b d c β B C1 Acap ha hb hd hc hβ hβc hC1 hAcap0,
    eventually_source_formal_kernel_inverse_bound a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_formal_diagonal_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_partial_first_inverse_of_covariance a b d β PInv (sourcePartialCovarianceConstant d β B C1)
      ha hb hd hβ hPInv,
    eventually_endpoint_far_tail_small a d 1 ha hd (by norm_num),
    eventually_source_radius_hierarchy a d c β hd hc hβ hβc,hdepth]
    with N hinputs hgeometry hnum hformal hinverse hdiagonal hcaps htail hradii hdepthN
  intro g o z q hz hzB hfloor hqim hprior hballs ι _ labels samples x y
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let R:=hereditaryReferenceRadius d (augmentedObservationDiameter d r)
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let p:=rationalTreeReference (d-1) q
  have hell : ell≤doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepthN).2
  have num:=hnum z hz hfloor
  have hf:=hformal z q hz hzB hfloor hprior
  have hinv:=hinverse z q hz hzB hfloor hprior
  have hdiag:=hdiagonal z q hz hzB hfloor hprior
  have hprior' := hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative hC1)
  have hscaled : 0≤C1^2*ε := mul_nonneg (sq_nonneg C1) num.error_nonnegative
  have hεone : ε≤1 :=
    ((le_mul_of_one_le_left num.error_nonnegative (show (1:ℝ)≤C1^2 by nlinarith)).trans
      (le_mul_of_one_le_right hscaled (one_le_pow₀ num.log_one))).trans num.error_scaled
  have ht:=htail g o ell hell labels samples selector (logarithmicRadius β d N) selector hradii.2.2.1 z hz.le
  simp only [one_mul] at ht
  have htailOne : (Nat.card (s.endpointModelRoots selector):ℝ)*physicalTransfer d z^selector≤1 :=
    ht.trans ((div_le_self num.error_nonnegative (one_le_pow₀ num.log_one)).trans hεone)
  have hqInvCap : ‖q⁻¹‖≤PInv := hinv.2.trans (by dsimp only [PInv]; linarith [le_abs_self B])
  have hi:=hinputs g o z q hz hzB hfloor hqim hprior hballs labels samples x y
  have hgeo:=hgeometry g o z hballs labels samples x y
  intro S hS
  let G:=((g.deficient.delete T).restrict S).extensionGreen q z
  let A:=G.submatrix (s.partialBoundaryEmbedding selector S) (s.partialBoundaryEmbedding selector S)
  let AM:=s.partialBoundaryMask selector S
  let BM:=s.partialFirstMask selector S
  obtain ⟨hbudget,hR,hRlog⟩:=hgeo S hS
  have hsmall:=(DeficientGraph.weak_localization_feedback_budgets d hd z q hz B (C1^2*ε) L Acap
    hscaled num.log_one num.log_cap_nonnegative num.error_scaled hprior'
    R (4*r+1) hRlog num.pair_log num.localization_large).1
  have hcard:=Nat.cast_le (α:=ℝ).mpr (s.partialBoundaryMask_card_le_roots selector S)
  have hmask : (Fintype.card AM:ℝ)*physicalTransfer d z^selector≤1 := by
    have hh:=(mul_le_mul_of_nonneg_right hcard (pow_nonneg (physicalTransfer_pos d hd z).le _)).trans htailOne
    simpa only [Nat.card_eq_fintype_card,AM] using hh
  have hmissing:=g.partial_first_missing_restoration_rows hd T labels samples selector S hbudget q z hz hqim
    R hR hsmall hmask
  have hSinputs:=hi S hS
  have hout:=hcaps g o ell hell labels samples selector z q p hz hfloor hqim hf.1 hf.2.1
    hf.2.2.2.1 hdiag.2.2.1 hf.2.2.1 hdiag.2.2.2.2.1 hqInvCap hdiag.2.2.2.2.2 S
    hSinputs.2.2.1 hmissing.1 hmissing.2.1 hSinputs.1
  exact hout

end RegularGraph
end LocalLaw
