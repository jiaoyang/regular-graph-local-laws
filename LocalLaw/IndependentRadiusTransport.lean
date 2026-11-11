import LocalLaw.IndependentRadiusEvents
import LocalLaw.GraphBranchNet

/-!
# Actual spectral transport with independent model and error radii

The physical Green/Q/model continuity is evaluated at the internal model
radius; all scalar and inflated-error comparisons use the nominal error
radius. Their proved continuity constants do not depend on the model radius.
-/

noncomputable section
namespace LocalLaw
local instance independentRadiusTransportDecidable (p : Prop) : Decidable p := Classical.propDecidable p
noncomputable def graphTransportStepWithRadii (N d a rModel rError : ℕ) (hN : 0 < N) (hd : 3 ≤ d)
    (structural : RegularGraph N d → Prop) (z w : ℂ) (η₀ : ℝ)
    (hη : 0 < η₀) (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im)
    (cavityBudget : scalarScale (spectralScale w) (graphPaperError a d N rError w) / 2 +
      (1 / η₀ ^ 2 + 1 / η₀) * dist z w ≤
        scalarScale (spectralScale z) (graphPaperError a d N rError z))
    (entryBudget : graphPaperError a d N rError w / 2 +
      (1 / η₀ ^ 2 + ((1 + 2 / η₀ ^ 2) / η₀ ^ 2)) * dist z w ≤
        graphPaperError a d N rError z) :
    LocalLawTransportStep (graphLocalLawFamilyWithRadii N d a rModel rError) structural w z := by
  apply LocalLawTransportStep.ofComponents (graphLocalLawFamilyWithRadii N d a rModel rError) structural w z
    (1 / η₀ ^ 2) (1 / η₀) (1 / η₀ ^ 2) ((1 + 2 / η₀ ^ 2) / η₀ ^ 2)
    (by positivity) (by positivity) (by positivity) (by positivity)
  · intro g _
    exact g.Q_lipschitz hN (by omega) z w η₀ hη hz hw
  · have hm := semicircleRoot_lipschitz (z := z) (w := w) η₀ hη hz hw
    change ‖semicircleRoot z - semicircleRoot w‖ ≤ _
    calc
      _ ≤ ‖z - w‖ / η₀ := hm
      _ = (1 / η₀) * dist z w := by rw [dist_eq_norm]; ring
  · intro g _ i j
    exact green_entry_lipschitz_universal g.H g.H_hermitian z w η₀ hη hz hw i j
  · intro g _ i j
    exact g.P_Q_lipschitz hN hd rModel z w η₀ hη hz hw i j
  · exact cavityBudget
  · exact entryBudget


noncomputable def graphSameBranchStepWithRadii (N d a rModel rError : ℕ) (hN : 0 < N) (hd : 3 ≤ d)
    (structural : RegularGraph N d → Prop) (z w : ℂ) (η₀ : ℝ)
    (hη : 0 < η₀) (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im)
    (hlog : 1 ≤ Real.log (N : ℝ))
    (branch : graphErrorBranch a d N rError w = graphErrorBranch a d N rError z)
    (baseMesh : baseErrorModulus a N η₀ (dist z w) ≤ graphBaseError a d N rError z / 8)
    (scaleMesh : 2 * dist z w ≤ spectralScale z / 8)
    (cavityMesh : (1 / η₀ ^ 2 + 1 / η₀) * dist z w ≤
      scalarScale (spectralScale z) (graphPaperError a d N rError z) / 4)
    (entryMesh : (1 / η₀ ^ 2 + ((1 + 2 / η₀ ^ 2) / η₀ ^ 2)) * dist z w ≤
      graphPaperError a d N rError z / 4) :
    LocalLawTransportStep (graphLocalLawFamilyWithRadii N d a rModel rError) structural w z := by
  have hLp : 0 < Real.log (N : ℝ) := by linarith
  have hzp := hη.trans_le hz
  have hbasep : 0 < graphBaseError a d N rError z :=
    baseError_positive (Real.log (N : ℝ)) a d N rError z.im _ hLp (by omega) hN hzp
  have herrorp : 0 < graphPaperError a d N rError z :=
    inflateError_positive hLp hbasep
  have hbasevar : Real.log (N : ℝ) ^ 4 *
      |graphBaseError a d N rError w - graphBaseError a d N rError z| ≤ graphBaseError a d N rError z / 8 := by
    have hm := paperBaseError_modulus a d N rError hd hN w z η₀ hη hw hz
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
      _ ≤ graphBaseError a d N rError z / 8 := baseMesh
  have herrorvar : |graphPaperError a d N rError w - graphPaperError a d N rError z| ≤
      graphPaperError a d N rError z / 8 :=
    inflatedError_relative_variation _ _ _ _ _ hlog hbasep.le branch hbasevar
  have hscale : |spectralScale w - spectralScale z| ≤ spectralScale z / 8 := by
    have hs0 : |spectralScale w - spectralScale z| ≤ 2 * dist z w := by
      simpa only [abs_sub_comm] using spectralScale_lipschitz z w
    exact hs0.trans scaleMesh
  have hbudget := local_budget_comparison (spectralScale z) (spectralScale w)
    (graphPaperError a d N rError z) (graphPaperError a d N rError w)
    (1 / η₀ ^ 2 + 1 / η₀) (1 / η₀ ^ 2 + ((1 + 2 / η₀ ^ 2) / η₀ ^ 2)) (dist z w)
    (spectralScale_pos hzp) herrorp hscale herrorvar cavityMesh entryMesh
  exact graphTransportStepWithRadii N d a rModel rError hN hd structural z w η₀ hη hz hw hbudget.1 hbudget.2

end LocalLaw
