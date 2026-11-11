import LocalLaw.UniformGraphNet
import LocalLaw.MdVerticalMonotonic

/-!
# Actual downward spectral transport, including threshold crossings

The physical variance monotonicity proves monotonicity of both epsilon and
its square-root stability budget. Uniform numerical mesh margins therefore
produce actual graph weak/strict transport without a same-branch premise.
-/

namespace LocalLaw

namespace UniformGraphMesh

variable {N d a r : ℕ} {domain : Set ℂ} {radius : ℝ}

noncomputable def verticalStep (M : UniformGraphMesh N d a r domain radius)
    (structural : RegularGraph N d → Prop) (z w : ℂ) (hz : z ∈ domain) (hw : w ∈ domain)
    (hreal : z.re = w.re) (him : z.im ≤ w.im) (hdist : dist z w ≤ radius) :
    LocalLawTransportStep (graphLocalLawFamily N d a r) structural w z := by
  have hη := M.etaPositive
  have hzp := hη.trans_le (M.lowerImaginary z hz)
  have hwp := hη.trans_le (M.lowerImaginary w hw)
  have hv := paperError_vertical_budgets a d N r M.degreeAtLeastThree M.vertexPositive
    z w hzp hwp hreal him M.logLarge
  change graphPaperError a d N r w ≤ graphPaperError a d N r z ∧
    scalarScale (spectralScale w) (graphPaperError a d N r w) ≤
      scalarScale (spectralScale z) (graphPaperError a d N r z) at hv
  have hεnonneg := graphPaperError_nonnegative a d N r z (Nat.succ_le_of_lt M.vertexPositive) hzp.le
  have hΨnonneg := scalarScale_nonneg (s := spectralScale z) hεnonneg
  have hεlower := graphPaperError_lower a d N r z M.logLarge hzp.le
  have hc : (1 / M.etaFloor ^ 2 + 1 / M.etaFloor) * dist z w ≤
      scalarScale (spectralScale z) (graphPaperError a d N r z) / 4 := by
    have hC : 0 ≤ 1 / M.etaFloor ^ 2 + 1 / M.etaFloor := by positivity
    exact (mul_le_mul_of_nonneg_left hdist hC).trans
      (M.cavityMesh.trans (by linarith [M.scale_budget_lower z hz]))
  have he : (1 / M.etaFloor ^ 2 + ((1 + 2 / M.etaFloor ^ 2) / M.etaFloor ^ 2)) * dist z w ≤
      graphPaperError a d N r z / 4 := by
    have hC : 0 ≤ 1 / M.etaFloor ^ 2 + ((1 + 2 / M.etaFloor ^ 2) / M.etaFloor ^ 2) := by positivity
    exact (mul_le_mul_of_nonneg_left hdist hC).trans (M.entryMesh.trans (by linarith))
  apply graphTransportStep N d a r M.vertexPositive M.degreeAtLeastThree structural z w M.etaFloor
    M.etaPositive (M.lowerImaginary z hz) (M.lowerImaginary w hw)
  · linarith [hv.2]
  · linarith [hv.1]

end UniformGraphMesh

/-- The spectral chain retains a fixed real coordinate and caps the last
height at the selected target. -/
def verticalSpectralPoint (E top bottom h : ℝ) (k : ℕ) : ℂ :=
  ⟨E, verticalHeight top bottom h k⟩

theorem verticalSpectralPoint_step (E top bottom h : ℝ) (k : ℕ) (hh : 0 ≤ h) :
    (verticalSpectralPoint E top bottom h (k + 1)).im ≤
      (verticalSpectralPoint E top bottom h k).im ∧
    dist (verticalSpectralPoint E top bottom h (k + 1))
      (verticalSpectralPoint E top bottom h k) ≤ h := by
  have hs := verticalHeight_step top bottom h k hh
  constructor
  · exact sub_nonneg.mp hs.1
  · have hd : verticalSpectralPoint E top bottom h (k + 1) - verticalSpectralPoint E top bottom h k =
        (↑(verticalHeight top bottom h (k + 1) - verticalHeight top bottom h k) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [verticalSpectralPoint, Complex.mul_re, Complex.mul_im]
    rw [dist_eq_norm, hd, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_sub_comm, abs_of_nonneg hs.1]
    exact hs.2

/-- The actual ordered transport inclusion for a finite downward chain.
Only the initial weak anchor remains as a separate source estimate. -/
theorem actual_vertical_chain_transport {N d a r K : ℕ} {domain : Set ℂ} {radius : ℝ}
    (M : UniformGraphMesh N d a r domain radius) (structural : RegularGraph N d → Prop)
    (E top bottom h : ℝ) (hh : 0 ≤ h) (hstep : h ≤ radius)
    (inside : ∀ k ≤ K, verticalSpectralPoint E top bottom h k ∈ domain)
    (anchor : ∀ g, structural g → (graphLocalLawFamily N d a r).weak
      (verticalSpectralPoint E top bottom h 0) g) :
    ∀ t : Fin (K + 1), ∀ g, structural g →
      (∀ p : Fin (K + 1), p < t → (graphLocalLawFamily N d a r).strict
        (verticalSpectralPoint E top bottom h p.val) g) →
      (graphLocalLawFamily N d a r).weak (verticalSpectralPoint E top bottom h t.val) g := by
  intro t g hg previous
  rcases t with ⟨n, hn⟩
  cases n with
  | zero => exact anchor g hg
  | succ n =>
      have hnK : n + 1 ≤ K := by omega
      have hp : n < K + 1 := by omega
      have hs := verticalSpectralPoint_step E top bottom h n hh
      let S := M.verticalStep structural (verticalSpectralPoint E top bottom h (n + 1))
        (verticalSpectralPoint E top bottom h n) (inside _ hnK) (inside _ (by omega)) rfl
        hs.1 (hs.2.trans hstep)
      exact S.strict_to_weak g hg (previous ⟨n, hp⟩ (by exact Nat.lt_succ_self n))

end LocalLaw
