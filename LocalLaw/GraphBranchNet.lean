import LocalLaw.GraphAnalyticTransport
import LocalLaw.BaseErrorContinuity
import LocalLaw.SpectralScaleContinuity

/-!
# Actual same-branch graph transport from numerical mesh inequalities

The base-error modulus, regularized edge-distance continuity, and physical
resolvent continuity are now combined. The remaining hypotheses are explicit
mesh inequalities, rather than unproved analytic-continuity or event-inclusion
statements.
-/

namespace LocalLaw

noncomputable def graphBaseError (a d N r : ℕ) (z : ℂ) : ℝ :=
  paperBaseError a d N r z.im (graphKestenMcKayReference d z).im

noncomputable def graphErrorBranch (a d N r : ℕ) (z : ℂ) : Bool :=
  errorBranch (Real.log (N : ℝ)) (graphBaseError a d N r z) (spectralScale z)

noncomputable def baseErrorModulus (a N : ℕ) (η h : ℝ) : ℝ :=
  Real.log (N : ℝ) ^ (8 * a + 4) *
    (Real.sqrt ((8 / ((N : ℝ) * η ^ 2)) * h) +
      ((2 / 3 : ℝ) * ((N : ℝ) * η) ^ (- (5 / 3 : ℝ)) * (N : ℝ)) * h)

/-- An actual graph transport step in a single error branch. Every analytic
estimate is supplied by a proved source-specific lemma. -/
noncomputable def graphSameBranchStep (N d a r : ℕ) (hN : 0 < N) (hd : 3 ≤ d)
    (structural : RegularGraph N d → Prop) (z w : ℂ) (η₀ : ℝ)
    (hη : 0 < η₀) (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im)
    (hlog : 1 ≤ Real.log (N : ℝ))
    (branch : graphErrorBranch a d N r w = graphErrorBranch a d N r z)
    (baseMesh : baseErrorModulus a N η₀ (dist z w) ≤ graphBaseError a d N r z / 8)
    (scaleMesh : 2 * dist z w ≤ spectralScale z / 8)
    (cavityMesh : (1 / η₀ ^ 2 + 1 / η₀) * dist z w ≤
      scalarScale (spectralScale z) (graphPaperError a d N r z) / 4)
    (entryMesh : (1 / η₀ ^ 2 + ((1 + 2 / η₀ ^ 2) / η₀ ^ 2)) * dist z w ≤
      graphPaperError a d N r z / 4) :
    LocalLawTransportStep (graphLocalLawFamily N d a r) structural w z := by
  have hLp : 0 < Real.log (N : ℝ) := by linarith
  have hzp := hη.trans_le hz
  have hbasep : 0 < graphBaseError a d N r z :=
    baseError_positive (Real.log (N : ℝ)) a d N r z.im _ hLp (by omega) hN hzp
  have herrorp : 0 < graphPaperError a d N r z :=
    inflateError_positive hLp hbasep
  have hbasevar : Real.log (N : ℝ) ^ 4 *
      |graphBaseError a d N r w - graphBaseError a d N r z| ≤ graphBaseError a d N r z / 8 := by
    have hm := paperBaseError_modulus a d N r hd hN w z η₀ hη hw hz
    rw [dist_comm] at hm
    calc
      _ ≤ Real.log (N : ℝ) ^ 4 * (Real.log (N : ℝ) ^ (8 * a) *
        (Real.sqrt ((8 / ((N : ℝ) * η₀ ^ 2)) * dist z w) +
          ((2 / 3 : ℝ) * ((N : ℝ) * η₀) ^ (- (5 / 3 : ℝ)) * (N : ℝ)) * dist z w)) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ = baseErrorModulus a N η₀ (dist z w) := by
        unfold baseErrorModulus
        rw [show 8 * a + 4 = 4 + 8 * a by omega, pow_add]
        ring
      _ ≤ graphBaseError a d N r z / 8 := baseMesh
  have herrorvar : |graphPaperError a d N r w - graphPaperError a d N r z| ≤
      graphPaperError a d N r z / 8 :=
    inflatedError_relative_variation _ _ _ _ _ hlog hbasep.le branch hbasevar
  have hscale : |spectralScale w - spectralScale z| ≤ spectralScale z / 8 := by
    have hs0 : |spectralScale w - spectralScale z| ≤ 2 * dist z w := by
      simpa only [abs_sub_comm] using spectralScale_lipschitz z w
    exact hs0.trans scaleMesh
  have hbudget := local_budget_comparison (spectralScale z) (spectralScale w)
    (graphPaperError a d N r z) (graphPaperError a d N r w)
    (1 / η₀ ^ 2 + 1 / η₀) (1 / η₀ ^ 2 + ((1 + 2 / η₀ ^ 2) / η₀ ^ 2)) (dist z w)
    (spectralScale_pos hzp) herrorp hscale herrorvar cavityMesh entryMesh
  exact graphTransportStep N d a r hN hd structural z w η₀ hη hz hw hbudget.1 hbudget.2

end LocalLaw
