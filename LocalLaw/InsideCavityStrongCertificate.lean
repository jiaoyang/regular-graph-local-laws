import LocalLaw.SourceInsideCavityKernel
import LocalLaw.StrongCertificateClosure

/-! # The actual inside/cavity improvement extends to a strong certificate

Only the still-separate outside-row estimate is needed. The inside estimate
and absolute cavity average are consumed from the proved common kernel good
event; no extra cavity norm or strict closure conclusion is assumed.
-/

noncomputable section
namespace LocalLaw
local instance insideCavityStrongCertificateDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem strong_certificate_of_inside_cavity_and_outside {N d : ℕ}
    (a q Cq : ℕ) (c β B C1 : ℝ) (o : Fin N) (z : ℂ) (ξ : BallLabelledSpace N d)
    (hd : 0<d)
    (D : StrongClosureBudget z (semicircleRoot z) (spectralScale z)
      (graphPaperError a d N (logarithmicRadius β d N) z))
    (hdepth : D.depth=actualCavityDepth a d N z) (hlog : D.L=Real.log (N:ℝ))
    (hbase : D.rowBase=D.U*graphPaperError a d N (logarithmicRadius β d N) z/D.L)
    (hfeedback : D.rowFeedback=D.V*D.L^2)
    (hcavity : D.cavityError=D.residualConstant*graphPaperError a d N (logarithmicRadius β d N) z/(2*D.L^4))
    (hU : sourceInsideBaseConstant d (sourceRejectionConstant Cq q) β C1≤D.U)
    (hV : sourceInsideFeedbackConstant d β B≤D.V)
    (hM : sourceCavityAverageConstant d (sourceRejectionConstant Cq q) β C1≤D.residualConstant/2)
    (hgood : ballSourceInsideCavityGood a q Cq c β B C1 o z ξ)
    (houtside :
      let R := logarithmicRadius (c/4) d N
      let gnew := ballLabelledProject (ballLabelledResample N d (R/4) ξ)
      ∀ j∉ξ.1, ‖gnew.G z o j-gnew.P (effectiveModelRadius a d N β) z (gnew.Q z) o j‖≤
        D.rowBase+D.rowFeedback*gnew.sourceFeedback z) :
    let R := logarithmicRadius (c/4) d N
    let r := effectiveModelRadius a d N β
    let gnew := ballLabelledProject (ballLabelledResample N d (R/4) ξ)
    StrongCavityRowCertificate (gnew.Q z) (semicircleRoot z) z (spectralScale z)
      (graphPaperError a d N (logarithmicRadius β d N) z) D (gnew.G z) (fun w => gnew.P r z w)
      (cavityAtVertex gnew.graph d z) (nonTreeCenters gnew.graph R) o := by
  dsimp only
  let R := logarithmicRadius (c/4) d N
  let r := effectiveModelRadius a d N β
  let ell := actualCavityDepth a d N z-1
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let gnew := ballLabelledProject (ballLabelledResample N d (R/4) ξ)
  have hLp : 0<D.L := by have hh := D.large; linarith
  have hL1 : 1≤D.L := by have hh := D.large; linarith
  have hε : 0≤ε := D.errorPositive.le
  have hpositive : 1≤D.depth := by
    by_contra h
    have hz0 : D.depth=0 := by omega
    have hh := D.nonresonant
    simp only [hz0,cavitySum,Finset.range_zero,Finset.sum_empty,norm_zero] at hh
    linarith
  have hdepth' : D.depth=ell+1 := by dsimp only [ell]; omega
  constructor
  · intro hnotbad
    have htree : (graphBall gnew.graph o R).IsTree := by
      by_contra ht
      exact hnotbad ((nonTreeCenters_membership gnew.graph R o).mpr ht)
    have habs := hgood.2 htree
    change gnew.sourceCavityAbsoluteResidual ell o z≤
      sourceCavityAverageConstant d (sourceRejectionConstant Cq q) β C1*(ε/Real.log (N:ℝ)^4) at habs
    rw [←hlog] at habs
    have hscale := mul_le_mul_of_nonneg_right hM (div_nonneg hε (pow_nonneg hLp.le 4))
    rw [hdepth',hcavity]
    exact (gnew.sourceCavityResidual_norm_bound hd ell o z).trans
      (habs.trans (hscale.trans_eq (by ring)))
  · intro j
    change ‖gnew.G z o j-gnew.P r z (gnew.Q z) o j‖≤D.rowBase+D.rowFeedback*gnew.sourceFeedback z
    by_cases hj : j∈ξ.1
    · have hrow := hgood.1 ⟨j,hj⟩
      change ‖gnew.G z o j-gnew.P r z (gnew.Q z) o j‖≤
        sourceInsideBaseConstant d (sourceRejectionConstant Cq q) β C1*(ε/Real.log (N:ℝ)^2)+
          sourceInsideFeedbackConstant d β B*Real.log (N:ℝ)^2*gnew.sourceFeedback z at hrow
      rw [←hlog] at hrow
      have hdiv : ε/D.L^2≤ε/D.L := div_le_div_of_nonneg_left hε hLp (by nlinarith only [hL1])
      have hbaseBound : sourceInsideBaseConstant d (sourceRejectionConstant Cq q) β C1*(ε/D.L^2)≤D.rowBase := by
        calc
          _ ≤ D.U*(ε/D.L^2) := mul_le_mul_of_nonneg_right hU (div_nonneg hε (sq_nonneg _))
          _ ≤ D.U*(ε/D.L) := mul_le_mul_of_nonneg_left hdiv D.UNonnegative
          _ = _ := by rw [hbase]; ring
      have hF : 0≤gnew.sourceFeedback z := by dsimp only [RegularGraph.sourceFeedback]; positivity
      have hfeedbackBound : sourceInsideFeedbackConstant d β B*D.L^2*gnew.sourceFeedback z≤
          D.rowFeedback*gnew.sourceFeedback z := by
        rw [hfeedback]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hV (sq_nonneg _)) hF
      exact hrow.trans (add_le_add hbaseBound hfeedbackBound)
    · exact houtside j hj

end LocalLaw
