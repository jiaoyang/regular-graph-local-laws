import LocalLaw.IndependentRadiusTransport
import LocalLaw.GraphVerticalTransport

/-!
# Nominal numerical meshes for an independent finite-model radius

All mesh and monotonicity budgets use the nominal error radius. The actual
model radius enters only the proved physical continuity bounds. Both
same-branch and threshold-crossing downward transport are preserved.
-/

namespace LocalLaw
namespace UniformGraphMesh
variable {N d a rError : ℕ} {domain : Set ℂ} {radius : ℝ}
noncomputable def stepWithRadii (M : UniformGraphMesh N d a rError domain radius) (rModel : ℕ)
    (structural : RegularGraph N d → Prop) (z w : ℂ) (hz : z ∈ domain) (hw : w ∈ domain)
    (branch : graphErrorBranch a d N rError w = graphErrorBranch a d N rError z)
    (hdist : dist z w ≤ radius) :
    LocalLawTransportStep (graphLocalLawFamilyWithRadii N d a rModel rError) structural w z := by
  have hEta := M.etaPositive
  have hzp := M.etaPositive.trans_le (M.lowerImaginary z hz)
  have hεlower := graphPaperError_lower a d N rError z M.logLarge hzp.le
  have hbaselower := graphBaseError_lower a d N rError z (by linarith [M.logLarge]) hzp.le
  have hslower : M.etaFloor ≤ spectralScale z := by
    unfold spectralScale
    linarith [edgeDistance_nonneg z, M.lowerImaginary z hz]
  apply graphSameBranchStepWithRadii N d a rModel rError M.vertexPositive M.degreeAtLeastThree structural z w
    M.etaFloor M.etaPositive (M.lowerImaginary z hz) (M.lowerImaginary w hw) M.logLarge branch
  · exact (baseErrorModulus_mono a N M.etaFloor _ _ M.etaPositive
      (by linarith [M.logLarge]) hdist).trans (M.baseMesh.trans (by linarith))
  · linarith [M.scaleMesh]
  · have hC : 0 ≤ 1 / M.etaFloor ^ 2 + 1 / M.etaFloor := by positivity
    have hmul := mul_le_mul_of_nonneg_left hdist hC
    exact hmul.trans (M.cavityMesh.trans (by linarith [M.scale_budget_lower z hz]))
  · have hC : 0 ≤ 1 / M.etaFloor ^ 2 + ((1 + 2 / M.etaFloor ^ 2) / M.etaFloor ^ 2) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hdist hC
    exact hmul.trans (M.entryMesh.trans (by linarith))

noncomputable def verticalStepWithRadii (M : UniformGraphMesh N d a rError domain radius) (rModel : ℕ)
    (structural : RegularGraph N d → Prop) (z w : ℂ) (hz : z ∈ domain) (hw : w ∈ domain)
    (hreal : z.re = w.re) (him : z.im ≤ w.im) (hdist : dist z w ≤ radius) :
    LocalLawTransportStep (graphLocalLawFamilyWithRadii N d a rModel rError) structural w z := by
  have hη := M.etaPositive
  have hzp := hη.trans_le (M.lowerImaginary z hz)
  have hwp := hη.trans_le (M.lowerImaginary w hw)
  have hv := paperError_vertical_budgets a d N rError M.degreeAtLeastThree M.vertexPositive
    z w hzp hwp hreal him M.logLarge
  change graphPaperError a d N rError w ≤ graphPaperError a d N rError z ∧
    scalarScale (spectralScale w) (graphPaperError a d N rError w) ≤
      scalarScale (spectralScale z) (graphPaperError a d N rError z) at hv
  have hεnonneg := graphPaperError_nonnegative a d N rError z (Nat.succ_le_of_lt M.vertexPositive) hzp.le
  have hΨnonneg := scalarScale_nonneg (s := spectralScale z) hεnonneg
  have hεlower := graphPaperError_lower a d N rError z M.logLarge hzp.le
  have hc : (1 / M.etaFloor ^ 2 + 1 / M.etaFloor) * dist z w ≤
      scalarScale (spectralScale z) (graphPaperError a d N rError z) / 4 := by
    have hC : 0 ≤ 1 / M.etaFloor ^ 2 + 1 / M.etaFloor := by positivity
    exact (mul_le_mul_of_nonneg_left hdist hC).trans
      (M.cavityMesh.trans (by linarith [M.scale_budget_lower z hz]))
  have he : (1 / M.etaFloor ^ 2 + ((1 + 2 / M.etaFloor ^ 2) / M.etaFloor ^ 2)) * dist z w ≤
      graphPaperError a d N rError z / 4 := by
    have hC : 0 ≤ 1 / M.etaFloor ^ 2 + ((1 + 2 / M.etaFloor ^ 2) / M.etaFloor ^ 2) := by positivity
    exact (mul_le_mul_of_nonneg_left hdist hC).trans (M.entryMesh.trans (by linarith))
  apply graphTransportStepWithRadii N d a rModel rError M.vertexPositive M.degreeAtLeastThree structural z w M.etaFloor
    M.etaPositive (M.lowerImaginary z hz) (M.lowerImaginary w hw)
  · linarith [hv.2]
  · linarith [hv.1]

end UniformGraphMesh

theorem actual_vertical_chain_transportWithRadii {N d a rModel rError K : ℕ} {domain : Set ℂ} {radius : ℝ}
    (M : UniformGraphMesh N d a rError domain radius) (structural : RegularGraph N d → Prop)
    (E top bottom h : ℝ) (hh : 0 ≤ h) (hstep : h ≤ radius)
    (inside : ∀ k ≤ K, verticalSpectralPoint E top bottom h k ∈ domain)
    (anchor : ∀ g, structural g → (graphLocalLawFamilyWithRadii N d a rModel rError).weak
      (verticalSpectralPoint E top bottom h 0) g) :
    ∀ t : Fin (K + 1), ∀ g, structural g →
      (∀ p : Fin (K + 1), p < t → (graphLocalLawFamilyWithRadii N d a rModel rError).strict
        (verticalSpectralPoint E top bottom h p.val) g) →
      (graphLocalLawFamilyWithRadii N d a rModel rError).weak (verticalSpectralPoint E top bottom h t.val) g := by
  intro t g hg previous
  rcases t with ⟨n, hn⟩
  cases n with
  | zero => exact anchor g hg
  | succ n =>
      have hnK : n + 1 ≤ K := by omega
      have hp : n < K + 1 := by omega
      have hs := verticalSpectralPoint_step E top bottom h n hh
      let S := M.verticalStepWithRadii rModel structural (verticalSpectralPoint E top bottom h (n + 1))
        (verticalSpectralPoint E top bottom h n) (inside _ hnK) (inside _ (by omega)) rfl
        hs.1 (hs.2.trans hstep)
      exact S.strict_to_weak g hg (previous ⟨n, hp⟩ (by exact Nat.lt_succ_self n))

end LocalLaw
