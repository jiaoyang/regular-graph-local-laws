import LocalLaw.IndependentRadiusEvents
import LocalLaw.SourceLocalCertificate

/-!
# Scalar closure certificates with separate model and error radii

The local row and cavity event at an internal model radius supplies the same
proved closure certificate, with every scalar/error tolerance kept at the
nominal radius. No comparison of inflated errors at different radii occurs.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance independentRadiusCertificateDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}
namespace SourceOmegaMinusLocalWithRadii
theorem certificate {a rModel rError R : ℕ} {C2 : ℝ} {o : Fin N} {z : ℂ} {g : RegularGraph N d}
    (h : g.SourceOmegaMinusLocalWithRadii a rModel rError R (actualCavityDepth a d N z - 1) C2 o z)
    (ha : 12 ≤ a) (hd : 3 ≤ d) (hC2 : 0 ≤ C2)
    (hlog : 1 ≤ Real.log (N : ℝ)) (hconstant : 2 * C2 ≤ Real.log (N : ℝ) ^ 3)
    (hz : 0 < z.im) (D : ClosureBudget z (semicircleRoot z) (spectralScale z) (graphPaperError a d N rError z))
    (hdepth : D.depth = actualCavityDepth a d N z)
    (hbase : D.rowBase = graphPaperError a d N rError z / Real.log (N : ℝ))
    (hfeedback : D.rowFeedback = C2 * Real.log (N : ℝ))
    (hcavity : D.cavityError = graphPaperError a d N rError z / (2 * Real.log (N : ℝ) ^ 2)) :
    CavityRowCertificate (g.Q z) (semicircleRoot z) z (spectralScale z)
      (graphPaperError a d N rError z) D (g.G z) (fun w => g.P rModel z w)
      (cavityAtVertex g.graph d z) (nonTreeCenters g.graph R) o := by
  let ell := actualCavityDepth a d N z - 1
  let L := Real.log (N : ℝ)
  let ε := graphPaperError a d N rError z
  have hN : 1 ≤ N := by have := o.isLt; omega
  have hnums := local_improvement_error_budgets L ε C2 (resamplingDecayDenominator d ell)
    hlog D.errorPositive.le hC2 (selected_radius_decay_gain a d N z ha hd hlog) hconstant
  have hn := (nonresonantDepth_bounds (semicircleRoot z) (baselineCavityDepth a d N)).1
  have hnpos : 1 ≤ actualCavityDepth a d N z := by
    change baselineCavityDepth a d N ≤ actualCavityDepth a d N z at hn
    unfold baselineCavityDepth at hn
    omega
  have hdepth' : D.depth = ell + 1 := by dsimp [ell]; omega
  constructor
  · intro hgood
    have htree : (graphBall g.graph o R).IsTree := by
      by_contra htree
      exact hgood ((nonTreeCenters_membership g.graph R o).mpr htree)
    rw [hcavity, hdepth']
    exact (g.sourceCavityResidual_norm_bound (by omega) ell o z).trans
      ((h.localCavity htree).trans hnums.2.2)
  · intro i
    rw [hbase, hfeedback]
    change ‖g.G z o i - g.P rModel z (g.Q z) o i‖ ≤ ε / L + (C2 * L) * g.sourceFeedback z
    by_cases hi : i ∈ graphBallVertices g.graph o ell
    · have hcommon := (h.rowInside i hi).trans
        (g.sourceInsideRowBudget_le_common hd a rError ell C2 hC2 o i z
          hN hz.le hi)
      calc
        _ ≤ C2 * (((L / resamplingDecayDenominator d ell + L ^ 2 / resamplingDecayDenominator d ell) *
            g.sourcePrime a rError z) + L * g.sourceFeedback z) := hcommon
        _ = C2 * ((L / resamplingDecayDenominator d ell + L ^ 2 / resamplingDecayDenominator d ell) *
            inflatedPrime L ε) + (C2 * L) * g.sourceFeedback z := by
              unfold sourcePrime
              ring
        _ ≤ _ := add_le_add_right hnums.1 _
    · have hrow := h.rowOutside i hi
      calc
        _ ≤ C2 * (L ^ 2 * g.sourcePrime a rError z / resamplingDecayDenominator d ell +
            L * g.sourceFeedback z) := hrow
        _ = C2 * (L ^ 2 * inflatedPrime L ε / resamplingDecayDenominator d ell) +
            (C2 * L) * g.sourceFeedback z := by unfold sourcePrime; ring
        _ ≤ _ := add_le_add_right hnums.2.1 _

end SourceOmegaMinusLocalWithRadii
end RegularGraph
end LocalLaw
