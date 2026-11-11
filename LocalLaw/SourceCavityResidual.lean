import LocalLaw.FiniteCavityResidual
import LocalLaw.SourceObservationParameters
import LocalLaw.BoundaryPerturbationParameters

/-! # Actual weak-prior control of the finite cavity residual -/

noncomputable section
namespace LocalLaw

def sourceCavityResidualConstant (d : ℕ) (β B C1 : ℝ) : ℝ :=
  2 * sourceObservationLogCap d β * (C1 ^ 2 + Real.sqrt (B + 2) * C1)

/-- All depth-smallness and logarithmic bounds are realized. The internal
radius is effective while the residual is paid by the nominal source prime. -/
theorem eventually_cavity_residual_le_sourcePrime (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ z q : ℂ, 0 < z.im → ‖z‖ ≤ B →
      Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ‖q - semicircleRoot z‖ ≤ C1 * scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) →
      ‖q - cavityIterate z q (effectiveModelRadius a d N β + 1)‖ ≤
        inflatedPrime (Real.log (N : ℝ)) (graphPaperError a d N (logarithmicRadius β d N) z) := by
  let A := sourceObservationLogCap d β
  let K := C1 ^ 2 + Real.sqrt (B + 2) * C1
  have hA : 0 ≤ A := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hC : 0 ≤ C1 := (by norm_num : (0 : ℝ) ≤ 1).trans hC1
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  filter_upwards [eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_kernel_feedback a b d β C1 1 1 ha hb hd hβ hC (by norm_num) (by norm_num),
    eventually_log_ge_nat (2 * A * K)] with N hnum hfeedback hlarge
  intro z q hz hzB hfloor hprior
  let L := Real.log (N : ℝ)
  let r := effectiveModelRadius a d N β
  let rn := logarithmicRadius β d N
  let ε := graphPaperError a d N rn z
  have num := hnum z hz hfloor
  have hε : 0 ≤ ε := num.error_nonnegative
  have hL : 1 ≤ L := num.log_one
  have hr : r + 1 ≤ 2 * rn + 1 := by
    have hh : r ≤ rn := Nat.sub_le _ _
    omega
  have hrR : (r + 1 : ℕ) ≤ (2 * rn + 1 : ℕ) := hr
  have hrCast : ((r + 1 : ℕ) : ℝ) ≤ 2 * (rn : ℝ) + 1 := by exact_mod_cast hrR
  have hsmall : ((r + 1 : ℕ) : ℝ) * ‖q - semicircleRoot z‖ ≤ 1 / 2 := by
    have hh := hfeedback z q hz hfloor hprior
    simp only [mul_one] at hh
    exact (mul_le_mul_of_nonneg_right hrCast (norm_nonneg _)).trans (by simpa only [mul_comm] using hh)
  have hlength : ((r + 1 : ℕ) : ℝ) ≤ A * L := by
    have hnat : r + 1 ≤ (4 * r + 1) + 1 := by omega
    have hh : (((4 * r + 1) + 1 : ℕ) : ℝ) ≤ A * L := by
      simpa only [Nat.cast_add, Nat.cast_one] using num.pair_log
    exact (Nat.cast_le.mpr hnat).trans hh
  have hres := cavity_residual_of_weak_prior z q hz B ε C1 hzB hε hC hprior (r + 1) hsmall
  have hfirst : ‖q - cavityIterate z q (r + 1)‖ ≤ (2 * A * K) * L * ε := by
    apply hres.trans
    have hh := mul_le_mul_of_nonneg_right hlength (show 0 ≤ 2 * K * ε by positivity)
    convert hh using 1 <;> dsimp only [K] <;> ring
  apply hfirst.trans
  change (2 * A * K) * L * ε ≤ L ^ 3 * ε
  have hh := mul_le_mul_of_nonneg_right hlarge (show 0 ≤ L * ε by positivity)
  have hp : L ^ 2 ≤ L ^ 3 := pow_le_pow_right₀ hL (by omega)
  have hp := mul_le_mul_of_nonneg_right hp hε
  nlinarith only [hh, hp]

end LocalLaw
