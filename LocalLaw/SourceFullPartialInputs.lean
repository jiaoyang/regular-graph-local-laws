import LocalLaw.SourceFullRestrictionGeometry
import LocalLaw.FullCoreLogRows
import LocalLaw.FullEndpointWeakCovariance
import LocalLaw.SourceFormalKernelInverse
import LocalLaw.SourceObservationGeneralCap

/-! # Actual old full covariance and cut-core rows at every weak boundary q

Every full retained subset of the actual old two-target augmentation is
allowed. All graph classes, diameters, separation, scalar normalization and
kernel feedback conditions are derived from the source radius and prior.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceFullPartialInputsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 2500000

def sourceFullCutRowConstant (d : ℕ) (β : ℝ) : ℝ :=
  fullEndpointCountConstant d*(8*finiteExtraReferenceConstant d^2*fullRestrictionLogCap d β)+1

def sourceFullCovarianceConstant (d : ℕ) (β B C1 : ℝ) : ℝ :=
  (|treePatchWeakConstant d B (fullRestrictionLogCap d β)|+2*finiteExtraReferenceConstant d+1)*C1^2

namespace RegularGraph

theorem eventually_source_full_partial_inputs (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop,∀ (g : RegularGraph N d) (o : Fin N) (z q : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → 0≤q.im →
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) →
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀{ι : Type}[Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y : Fin N),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector := logarithmicRadius (c/4) d N/4
      let r := effectiveModelRadius a d N β
      let s := g.admissibleState T labels samples
      ∀ (hs : 1≤selector) (S : Set (Fin N)),S⊆s.fullTwoTargetVertices selector r x y →
      let G := (g.deficient.restrict S).extensionGreen q z
      let p := rationalTreeReference (d-1) q
      (∀i j,‖(G.submatrix (s.fullPartialEmbedding selector S hs) (s.fullPartialEmbedding selector S hs)-
        s.fullOldCovariance selector S G q p (treeEdgeWeight d)) i j‖≤
        sourceFullCovarianceConstant d β B C1*Real.log (N:ℝ)*graphPaperError a d N (logarithmicRadius β d N) z) ∧
      (∀i,∑j,‖(g.fullCoreEdgeCutModel T labels samples selector S).extensionGreen q z
        (s.fullCoreEmbedding S i) (s.fullCoreEmbedding S j)‖≤
        sourceFullCutRowConstant d β*Real.log (N:ℝ)^(a-1)) := by
  let A := fullRestrictionLogCap d β
  let U := fullEndpointCountConstant d
  have hAcaps := fullRestrictionLogCap_properties d β
  have hA : 0≤A := hAcaps.1
  have hAobs : sourceObservationLogCap d β≤A := hAcaps.2.1
  have hU : 0≤U := by dsimp only [U,fullEndpointCountConstant]; positivity
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_source_fullRestriction_geometry a b d c β B ha hb hd hc hβ hβc,
    eventually_sourceObservationBounds_of_cap a b d c β B C1 A ha hb hd hc hβ hβc hC1 hAobs,
    eventually_source_formal_kernel_bounds a b d c β B C1 A ha hb hd hc hβ hβc hC1 hA,
    eventually_source_formal_kernel_inverse_bound a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_fullPartialIndex_count a d ha hd,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,hdepth]
    with N hgeo hnum hformal hinverse hcount hcommon hdepth
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let T := graphBallVertices g.graph o ell
  let selector := logarithmicRadius (c/4) d N/4
  let r := effectiveModelRadius a d N β
  let s := g.admissibleState T labels samples
  let D := fullTwoTargetDiameter d ell r
  let R := hereditaryReferenceRadius d D
  let Rc := hereditaryReferenceRadius d R
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let p := rationalTreeReference (d-1) q
  have num := hnum z hz hfloor
  have hf := hformal z q hz hzB hfloor hprior
  have hi := hinverse z q hz hzB hfloor hprior
  have hp : p*(q⁻¹-q/((d:ℂ)-1))=1 := by
    have hrel : p⁻¹=q⁻¹-q/((d:ℂ)-1) := by
      rw [hf.2.2.2.1,treeEdgeWeight_sq d hd]
      simp only [mul_one_div]
    rw [←hrel]
    exact mul_inv_cancel₀ hf.2.1
  have hqpow : ∀n≤4*r+1,‖q‖^n≤2 := by
    intro n hn
    have hh : (n:ℝ)≤((4*r+1:ℕ):ℝ)+1 := by exact_mod_cast Nat.le_succ_of_le hn
    exact hf.2.2.2.2 n (hh.trans num.pair_log)
  have hsep : 2*r+2≤selector := by
    have hh := Nat.mul_le_mul_left 2 hcommon
    dsimp only [r,selector]
    omega
  intro hs S hSS
  have hg := hgeo g o z hz hfloor hballs labels samples x y S hSS
  have hscaled : 0≤C1^2*ε := mul_nonneg (sq_nonneg C1) num.error_nonnegative
  have hprior' := hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative hC1)
  have hsmall := (DeficientGraph.weak_localization_feedback_budgets d hd z q hz B (C1^2*ε) L A
    hscaled num.log_one hA num.error_scaled hprior' Rc (4*r+1) hg.2.2.2 num.pair_log num.localization_large).1
  have hcov := g.full_endpoint_old_weak_covariance hd T labels samples selector r hsep hs S hg.1
    z q p hz hq hf.1 hp B C1 ε L A hzB num hprior R hg.2.1 hg.2.2.1 hf.2.2.1 hi.2 hqpow
  have hI := hcount g o z labels samples selector hs S
  have hCoreNat : Nat.card (s.fullCoreMask S)≤Nat.card (s.FullEndpointIndex selector S) :=
    Nat.card_le_card_of_injective (fun k:s.fullCoreMask S => (Sum.inl k:s.FullEndpointIndex selector S))
      (fun _ _ h => Sum.inl.inj h)
  have hCore : (Nat.card (s.fullCoreMask S):ℝ)≤U*L^(2*a-4) :=
    (Nat.cast_le.mpr hCoreNat).trans hI
  have hrow := g.fullCoreEdgeCut_log_rows hd T labels samples selector S hg.1 R hg.2.1 q z hz hq
    a L U A (by omega) num.log_one hU hA hCore hg.2.2.2 hsmall
  refine ⟨?_,hrow⟩
  intro i j
  have hh := hcov i j
  have hcoeff : treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d≤
      |treePatchWeakConstant d B A|+2*finiteExtraReferenceConstant d+1 := by
    linarith [le_abs_self (treePatchWeakConstant d B A)]
  have hbnd := mul_le_mul_of_nonneg_right hcoeff
    (show 0≤C1^2*L*ε by exact mul_nonneg (mul_nonneg (sq_nonneg C1) (by linarith [num.log_one])) num.error_nonnegative)
  dsimp only [sourceFullCovarianceConstant]
  nlinarith only [hh,hbnd]

end RegularGraph
end LocalLaw
