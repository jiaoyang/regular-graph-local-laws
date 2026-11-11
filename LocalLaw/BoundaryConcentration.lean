import Mathlib

/-!
# Bounded-variable concentration for local boundary sampling

The bounded-centered sub-Gaussian MGF constructor is proved here from the
exponential secant inequality and the cosh bound. In particular, boundedness
is not replaced by an assumed tail estimate. This is the concentration input
in the independent-sampling step of Lemma 6.2 / equation (6.3).
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal

namespace LocalLaw

section BoundedMGF

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Hoeffding's MGF lemma for a centered variable in the symmetric interval
[-b,b]. The variance proxy is b². -/
theorem bounded_centered_subgaussian (X : Ω → ℝ) (b : ℝ≥0)
    (hX : AEStronglyMeasurable X μ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ (b : ℝ))
    (hmean : ∫ ω, X ω ∂μ = 0) : HasSubgaussianMGF X (b ^ 2) μ := by
  by_cases hbzero : b = 0
  · have hzero : X =ᵐ[μ] fun _ => 0 := by
      filter_upwards [hbound] with ω hω
      simp only [hbzero, NNReal.coe_zero] at hω
      exact abs_eq_zero.mp (le_antisymm hω (abs_nonneg _))
    have hz : HasSubgaussianMGF (fun _ : Ω => 0) 0 μ := HasSubgaussianMGF.fun_zero
    simpa only [hbzero, zero_pow (by decide : 2 ≠ 0)] using hz.congr hzero.symm
  have hbpos : (0 : ℝ) < b := by
    exact_mod_cast (pos_iff_ne_zero.mpr hbzero : 0 < b)
  have hIntX : Integrable X μ := by
    apply (integrable_const (b : ℝ)).mono' hX
    simpa only [Real.norm_eq_abs] using hbound
  have hExp : ∀ t : ℝ, Integrable (fun ω => exp (t * X ω)) μ := by
    intro t
    apply (integrable_const (exp (|t| * b))).mono' (aemeasurable_exp_mul t hX.aemeasurable)
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    calc
      t * X ω ≤ |t * X ω| := le_abs_self _
      _ = |t| * |X ω| := abs_mul _ _
      _ ≤ |t| * b := mul_le_mul_of_nonneg_left hω (abs_nonneg t)
  refine ⟨hExp, ?_⟩
  intro t
  have hAffine : Integrable (fun ω => cosh (t * b) + (X ω / b) * sinh (t * b)) μ :=
    (integrable_const _).add ((hIntX.div_const (b : ℝ)).mul_const _)
  have hsecant : ∀ᵐ ω ∂μ, exp (t * X ω) ≤
      cosh (t * b) + (X ω / b) * sinh (t * b) := by
    filter_upwards [hbound] with ω hω
    have hnormalized : |X ω / (b : ℝ)| ≤ 1 := by
      rw [abs_div, abs_of_pos hbpos]
      exact (div_le_iff₀ hbpos).2 (by simpa using hω)
    have h := exp_mul_le_cosh_add_mul_sinh hnormalized (t * b)
    have harg : (X ω / (b : ℝ)) * (t * b) = t * X ω := by
      field_simp
      ring
    simpa only [harg] using h
  change (∫ ω, exp (t * X ω) ∂μ) ≤ exp ((↑(b ^ 2) : ℝ) * t ^ 2 / 2)
  calc
    (∫ ω, exp (t * X ω) ∂μ) ≤
        ∫ ω, (cosh (t * b) + (X ω / b) * sinh (t * b)) ∂μ :=
      integral_mono_ae (hExp t) hAffine hsecant
    _ = cosh (t * b) := by
      rw [integral_add (integrable_const _) ((hIntX.div_const (b : ℝ)).mul_const _),
        integral_mul_const, integral_div, hmean]
      simp
    _ ≤ exp ((t * b) ^ 2 / 2) := cosh_le_exp_half_sq _
    _ = exp ((↑(b ^ 2) : ℝ) * t ^ 2 / 2) := by
      congr 1
      simp only [NNReal.coe_pow]
      ring

/-- One-sided concentration for a finite independent family of genuinely
bounded, centered real variables. -/
theorem bounded_independent_sum_tail {ι : Type*} (X : ι → Ω → ℝ)
    (b : ι → ℝ≥0) (s : Finset ι) (hindep : iIndepFun X μ)
    (hX : ∀ i ∈ s, AEStronglyMeasurable (X i) μ)
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ (b i : ℝ))
    (hmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i ∈ s, X i ω} ≤
      exp (-t ^ 2 / (2 * ∑ i ∈ s, ((b i : ℝ) ^ 2))) := by
  have hsub : ∀ i ∈ s, HasSubgaussianMGF (X i) (b i ^ 2) μ := by
    intro i hi
    exact bounded_centered_subgaussian (X i) (b i) (hX i hi) (hbound i hi) (hmean i hi)
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindep hsub ht
  simpa only [NNReal.coe_sum, NNReal.coe_pow] using h

/-- Two-sided Hoeffding concentration for bounded centered real variables. -/
theorem bounded_independent_abs_sum_tail {ι : Type*} (X : ι → Ω → ℝ)
    (b : ι → ℝ≥0) (s : Finset ι) (hindep : iIndepFun X μ)
    (hX : ∀ i ∈ s, AEStronglyMeasurable (X i) μ)
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ (b i : ℝ))
    (hmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i ∈ s, X i ω|} ≤
      2 * exp (-t ^ 2 / (2 * ∑ i ∈ s, ((b i : ℝ) ^ 2))) := by
  have hpositive := bounded_independent_sum_tail X b s hindep hX hbound hmean t ht
  have hnegativeIndependent : iIndepFun (fun i ω => -X i ω) μ := by
    simpa only [Function.comp_def] using
      hindep.comp (fun _i (x : ℝ) => -x) (fun _ => measurable_neg)
  have hnegative := bounded_independent_sum_tail (fun i ω => -X i ω) b s
    hnegativeIndependent (fun i hi => (hX i hi).neg)
    (fun i hi => by simpa only [abs_neg] using hbound i hi)
    (fun i hi => by simp only [integral_neg, hmean i hi, neg_zero]) t ht
  have hcover : {ω | t ≤ |∑ i ∈ s, X i ω|} ⊆
      {ω | t ≤ ∑ i ∈ s, X i ω} ∪ {ω | t ≤ ∑ i ∈ s, -X i ω} := by
    intro ω hω
    by_cases hsum : 0 ≤ ∑ i ∈ s, X i ω
    · exact Or.inl (by simpa only [Set.mem_setOf_eq, abs_of_nonneg hsum] using hω)
    · exact Or.inr (by simpa only [Set.mem_setOf_eq, abs_of_neg (lt_of_not_ge hsum),
        Finset.sum_neg_distrib] using hω)
  calc
    μ.real {ω | t ≤ |∑ i ∈ s, X i ω|} ≤
        μ.real ({ω | t ≤ ∑ i ∈ s, X i ω} ∪ {ω | t ≤ ∑ i ∈ s, -X i ω}) :=
      measureReal_mono hcover
    _ ≤ μ.real {ω | t ≤ ∑ i ∈ s, X i ω} + μ.real {ω | t ≤ ∑ i ∈ s, -X i ω} :=
      measureReal_union_le _ _
    _ ≤ 2 * exp (-t ^ 2 / (2 * ∑ i ∈ s, ((b i : ℝ) ^ 2))) := by
      linarith

/-- Deterministic complex weights preserve sub-Gaussian boundary
concentration. The weighted squared bounds appear with the correct ℓ² sum.
The explicit constant eight comes from splitting real and imaginary parts. -/
theorem bounded_independent_complex_weighted_tail {ι : Type*} (Z : ι → Ω → ℂ)
    (b : ι → ℝ≥0) (w : ι → ℂ) (s : Finset ι) (hindep : iIndepFun Z μ)
    (hZ : ∀ i ∈ s, AEStronglyMeasurable (Z i) μ)
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂μ, ‖Z i ω‖ ≤ (b i : ℝ))
    (hmean : ∀ i ∈ s, ∫ ω, Z i ω ∂μ = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ‖∑ i ∈ s, w i * Z i ω‖} ≤
      4 * exp (-t ^ 2 / (8 * ∑ i ∈ s, (‖w i‖ ^ 2 * (b i : ℝ) ^ 2))) := by
  let Xr : ι → Ω → ℝ := fun i ω => (w i * Z i ω).re
  let Xi : ι → Ω → ℝ := fun i ω => (w i * Z i ω).im
  let bw : ι → ℝ≥0 := fun i => ‖w i‖₊ * b i
  have hrIndependent : iIndepFun Xr μ := by
    simpa only [Xr, Function.comp_def] using
      hindep.comp (fun i (x : ℂ) => (w i * x).re) (fun _ => by fun_prop)
  have hiIndependent : iIndepFun Xi μ := by
    simpa only [Xi, Function.comp_def] using
      hindep.comp (fun i (x : ℂ) => (w i * x).im) (fun _ => by fun_prop)
  have hIntZ : ∀ i ∈ s, Integrable (Z i) μ := by
    intro i hi
    exact (integrable_const (b i : ℝ)).mono' (hZ i hi) (hbound i hi)
  have hrMeas : ∀ i ∈ s, AEStronglyMeasurable (Xr i) μ := by
    intro i hi
    exact (Complex.measurable_re.comp_aemeasurable
      ((hZ i hi).aemeasurable.const_mul (w i))).aestronglyMeasurable
  have hiMeas : ∀ i ∈ s, AEStronglyMeasurable (Xi i) μ := by
    intro i hi
    exact (Complex.measurable_im.comp_aemeasurable
      ((hZ i hi).aemeasurable.const_mul (w i))).aestronglyMeasurable
  have hrBound : ∀ i ∈ s, ∀ᵐ ω ∂μ, |Xr i ω| ≤ (bw i : ℝ) := by
    intro i hi
    filter_upwards [hbound i hi] with ω hω
    calc
      |Xr i ω| ≤ ‖w i * Z i ω‖ := Complex.abs_re_le_norm _
      _ = ‖w i‖ * ‖Z i ω‖ := norm_mul _ _
      _ ≤ ‖w i‖ * b i := mul_le_mul_of_nonneg_left hω (norm_nonneg _)
      _ = (bw i : ℝ) := by simp only [bw, NNReal.coe_mul, coe_nnnorm]
  have hiBound : ∀ i ∈ s, ∀ᵐ ω ∂μ, |Xi i ω| ≤ (bw i : ℝ) := by
    intro i hi
    filter_upwards [hbound i hi] with ω hω
    calc
      |Xi i ω| ≤ ‖w i * Z i ω‖ := Complex.abs_im_le_norm _
      _ = ‖w i‖ * ‖Z i ω‖ := norm_mul _ _
      _ ≤ ‖w i‖ * b i := mul_le_mul_of_nonneg_left hω (norm_nonneg _)
      _ = (bw i : ℝ) := by simp only [bw, NNReal.coe_mul, coe_nnnorm]
  have hrMean : ∀ i ∈ s, ∫ ω, Xr i ω ∂μ = 0 := by
    intro i hi
    have hc : (∫ ω, w i * Z i ω ∂μ) = 0 := by
      rw [integral_const_mul, hmean i hi, mul_zero]
    have hr := integral_re ((hIntZ i hi).const_mul (w i))
    simpa only [Xr, RCLike.re_eq_complex_re, hc, Complex.zero_re] using hr
  have hiMean : ∀ i ∈ s, ∫ ω, Xi i ω ∂μ = 0 := by
    intro i hi
    have hc : (∫ ω, w i * Z i ω ∂μ) = 0 := by
      rw [integral_const_mul, hmean i hi, mul_zero]
    have hi' := integral_im ((hIntZ i hi).const_mul (w i))
    simpa only [Xi, RCLike.im_eq_complex_im, hc, Complex.zero_im] using hi'
  have hrTail := bounded_independent_abs_sum_tail Xr bw s hrIndependent hrMeas hrBound
    hrMean (t / 2) (by positivity)
  have hiTail := bounded_independent_abs_sum_tail Xi bw s hiIndependent hiMeas hiBound
    hiMean (t / 2) (by positivity)
  have hre (ω : Ω) : (∑ i ∈ s, w i * Z i ω).re = ∑ i ∈ s, Xr i ω := by
    simp only [Complex.re_sum, Xr]
  have him (ω : Ω) : (∑ i ∈ s, w i * Z i ω).im = ∑ i ∈ s, Xi i ω := by
    simp only [Complex.im_sum, Xi]
  have hcover : {ω | t ≤ ‖∑ i ∈ s, w i * Z i ω‖} ⊆
      {ω | t / 2 ≤ |∑ i ∈ s, Xr i ω|} ∪ {ω | t / 2 ≤ |∑ i ∈ s, Xi i ω|} := by
    intro ω hω
    change t ≤ ‖∑ i ∈ s, w i * Z i ω‖ at hω
    by_cases hr : t / 2 ≤ |∑ i ∈ s, Xr i ω|
    · exact Or.inl hr
    by_cases hi : t / 2 ≤ |∑ i ∈ s, Xi i ω|
    · exact Or.inr hi
    have hnorm := Complex.norm_le_abs_re_add_abs_im (∑ i ∈ s, w i * Z i ω)
    rw [hre, him] at hnorm
    exact False.elim (by linarith [lt_of_not_ge hr, lt_of_not_ge hi])
  have hprob : μ.real {ω | t ≤ ‖∑ i ∈ s, w i * Z i ω‖} ≤
      4 * exp (-(t / 2) ^ 2 / (2 * ∑ i ∈ s, ((bw i : ℝ) ^ 2))) := by
    calc
      μ.real {ω | t ≤ ‖∑ i ∈ s, w i * Z i ω‖} ≤
          μ.real ({ω | t / 2 ≤ |∑ i ∈ s, Xr i ω|} ∪
            {ω | t / 2 ≤ |∑ i ∈ s, Xi i ω|}) := measureReal_mono hcover
      _ ≤ μ.real {ω | t / 2 ≤ |∑ i ∈ s, Xr i ω|} +
          μ.real {ω | t / 2 ≤ |∑ i ∈ s, Xi i ω|} := measureReal_union_le _ _
      _ ≤ 4 * exp (-(t / 2) ^ 2 / (2 * ∑ i ∈ s, ((bw i : ℝ) ^ 2))) := by
        linarith
  have hsum : (∑ i ∈ s, ((bw i : ℝ) ^ 2)) =
      ∑ i ∈ s, (‖w i‖ ^ 2 * (b i : ℝ) ^ 2) := by
    simp only [bw, NNReal.coe_mul, coe_nnnorm, mul_pow]
  rw [hsum] at hprob
  have hexponent : -(t / 2) ^ 2 /
      (2 * ∑ i ∈ s, (‖w i‖ ^ 2 * (b i : ℝ) ^ 2)) =
      -t ^ 2 / (8 * ∑ i ∈ s, (‖w i‖ ^ 2 * (b i : ℝ) ^ 2)) := by
    ring
  simpa only [hexponent] using hprob

/-- Bounded complex variables are integrable, their means have the same bound,
and centering increases the norm bound by at most a factor two. -/
theorem bounded_complex_centering (Z : Ω → ℂ) (b : ℝ≥0)
    (hZ : AEStronglyMeasurable Z μ) (hbound : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ (b : ℝ)) :
    Integrable Z μ ∧ ‖∫ ω, Z ω ∂μ‖ ≤ (b : ℝ) ∧
      (∀ᵐ ω ∂μ, ‖Z ω - ∫ η, Z η ∂μ‖ ≤ 2 * (b : ℝ)) ∧
      (∫ ω, (Z ω - ∫ η, Z η ∂μ) ∂μ) = 0 := by
  have hInt : Integrable Z μ := (integrable_const (b : ℝ)).mono' hZ hbound
  have hMeanNorm : ‖∫ ω, Z ω ∂μ‖ ≤ (b : ℝ) := by
    calc
      ‖∫ ω, Z ω ∂μ‖ ≤ ∫ ω, ‖Z ω‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ _ω : Ω, (b : ℝ) ∂μ := integral_mono_ae hInt.norm (integrable_const _) hbound
      _ = (b : ℝ) := by simp
  refine ⟨hInt, hMeanNorm, ?_, ?_⟩
  · filter_upwards [hbound] with ω hω
    exact (norm_sub_le _ _).trans (by linarith)
  · rw [integral_sub hInt (integrable_const _)]
    simp

/-- The concentration step in equation (6.3), with centering and its variance
proxy derived from bounded original complex observations. -/
theorem bounded_complex_centered_weighted_tail {ι : Type*} (Z : ι → Ω → ℂ)
    (b : ι → ℝ≥0) (w : ι → ℂ) (s : Finset ι) (hindep : iIndepFun Z μ)
    (hZ : ∀ i ∈ s, AEStronglyMeasurable (Z i) μ)
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂μ, ‖Z i ω‖ ≤ (b i : ℝ))
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ‖∑ i ∈ s, w i * (Z i ω - ∫ η, Z i η ∂μ)‖} ≤
      4 * exp (-t ^ 2 / (32 * ∑ i ∈ s, (‖w i‖ ^ 2 * (b i : ℝ) ^ 2))) := by
  let Y : ι → Ω → ℂ := fun i ω => Z i ω - ∫ η, Z i η ∂μ
  have hcentering : ∀ i ∈ s,
      Integrable (Z i) μ ∧ ‖∫ ω, Z i ω ∂μ‖ ≤ (b i : ℝ) ∧
      (∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ 2 * (b i : ℝ)) ∧
      (∫ ω, Y i ω ∂μ) = 0 := by
    intro i hi
    exact bounded_complex_centering (Z i) (b i) (hZ i hi) (hbound i hi)
  have hIndependent : iIndepFun Y μ := by
    simpa only [Y, Function.comp_def] using
      hindep.comp (fun i (x : ℂ) => x - ∫ η, Z i η ∂μ) (fun _ => by fun_prop)
  have h := bounded_independent_complex_weighted_tail Y (fun i => 2 * b i) w s
    hIndependent (fun i hi => (hZ i hi).sub aestronglyMeasurable_const)
    (fun i hi => by simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using
      (hcentering i hi).2.2.1)
    (fun i hi => (hcentering i hi).2.2.2) t ht
  have hsum : (∑ i ∈ s, (‖w i‖ ^ 2 * ((↑(2 * b i) : ℝ) ^ 2))) =
      4 * ∑ i ∈ s, (‖w i‖ ^ 2 * (b i : ℝ) ^ 2) := by
    calc
      (∑ i ∈ s, (‖w i‖ ^ 2 * ((↑(2 * b i) : ℝ) ^ 2))) =
          ∑ i ∈ s, 4 * (‖w i‖ ^ 2 * (b i : ℝ) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [NNReal.coe_mul, NNReal.coe_ofNat]
        ring
      _ = 4 * ∑ i ∈ s, (‖w i‖ ^ 2 * (b i : ℝ) ^ 2) := by rw [Finset.mul_sum]
  change μ.real {ω | t ≤ ‖∑ i ∈ s, w i * Y i ω‖} ≤ _
  rw [hsum] at h
  have hden : (8 : ℝ) * (4 * ∑ i ∈ s, (‖w i‖ ^ 2 * (b i : ℝ) ^ 2)) =
      32 * ∑ i ∈ s, (‖w i‖ ^ 2 * (b i : ℝ) ^ 2) := by ring
  simpa only [hden] using h

/-- Homogeneous-bound normalization of the paper's boundary concentration.
The positive weighted variance assumption excludes the degenerate zero
threshold, where a nontrivial exponential bound with a ≥ event is impossible. -/
theorem boundary_sampling_concentration {ι : Type*} (Z : ι → Ω → ℂ)
    (b : ℝ≥0) (hb : 0 < b) (w : ι → ℂ) (s : Finset ι)
    (hweights : 0 < ∑ i ∈ s, ‖w i‖ ^ 2) (hindep : iIndepFun Z μ)
    (hZ : ∀ i ∈ s, AEStronglyMeasurable (Z i) μ)
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂μ, ‖Z i ω‖ ≤ (b : ℝ))
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t * b * Real.sqrt (∑ i ∈ s, ‖w i‖ ^ 2) ≤
      ‖∑ i ∈ s, w i * (Z i ω - ∫ η, Z i η ∂μ)‖} ≤
      4 * exp (-t ^ 2 / 32) := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have h := bounded_complex_centered_weighted_tail Z (fun _ => b) w s hindep hZ hbound
    (t * b * Real.sqrt (∑ i ∈ s, ‖w i‖ ^ 2)) (by positivity)
  have hsum : (∑ i ∈ s, ‖w i‖ ^ 2 * (b : ℝ) ^ 2) =
      (∑ i ∈ s, ‖w i‖ ^ 2) * (b : ℝ) ^ 2 := by rw [Finset.sum_mul]
  rw [hsum] at h
  have heq : -(t * b * Real.sqrt (∑ i ∈ s, ‖w i‖ ^ 2)) ^ 2 /
      (32 * ((∑ i ∈ s, ‖w i‖ ^ 2) * (b : ℝ) ^ 2)) = -t ^ 2 / 32 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hweights.le]
    field_simp [ne_of_gt hweights, ne_of_gt hbpos]
    ring
  simpa only [heq] using h

end BoundedMGF

section ProductSampling

variable {ι A : Type*} [Fintype ι] [MeasurableSpace A]

/-- Every coordinate of a finite product probability measure has its stated
marginal. This supplies the independence bridge for actual sampled edges. -/
theorem product_coordinate_map (ν : ι → Measure A) [∀ i, IsProbabilityMeasure (ν i)] (i : ι) :
    (Measure.pi ν).map (fun ω : ι → A => ω i) = ν i := by
  classical
  ext E hE
  rw [Measure.map_apply (measurable_pi_apply i) hE]
  have hset : (fun ω : ι → A => ω i) ⁻¹' E =
      Set.univ.pi (fun j => if j = i then E else Set.univ) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h j
      by_cases hj : j = i
      · simpa only [hj, if_pos rfl] using h
      · simp only [if_neg hj, Set.mem_univ]
    · intro h
      simpa only [if_pos rfl] using h i
  rw [hset, Measure.pi_pi]
  simp [apply_ite, Finset.prod_ite_eq]

/-- Coordinate independence is proved from the product measure, not assumed
as a property of uniform sampling. -/
theorem product_coordinates_independent (ν : ι → Measure A)
    [∀ i, IsProbabilityMeasure (ν i)] :
    iIndepFun (fun i (ω : ι → A) => ω i) (Measure.pi ν) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (measurable_pi_apply i).aemeasurable)).2
  change (Measure.pi ν).map id = Measure.pi (fun i =>
    (Measure.pi ν).map (fun ω : ι → A => ω i))
  rw [Measure.map_id]
  congr 1
  funext i
  exact (product_coordinate_map ν i).symm

/-- Product expectations of one-coordinate observables equal their original
one-edge expectations. -/
theorem product_coordinate_integral (ν : ι → Measure A)
    [∀ i, IsProbabilityMeasure (ν i)] (i : ι) (f : A → ℂ) (hf : Measurable f) :
    (∫ ω : ι → A, f (ω i) ∂Measure.pi ν) = ∫ a, f a ∂ν i := by
  have h := integral_map_of_stronglyMeasurable (μ := Measure.pi ν)
    (measurable_pi_apply i) hf.stronglyMeasurable
  rw [product_coordinate_map ν i] at h
  exact h.symm

variable [Fintype A] [Nonempty A]

/-- Independent uniform sampling with replacement from a finite nonempty
edge set. The index type ι records the boundary labels. -/
noncomputable def uniformBoundarySampling : Measure (ι → A) :=
  Measure.pi (fun _i : ι => (PMF.uniformOfFintype A).toMeasure)

instance uniformBoundarySampling_probability :
    IsProbabilityMeasure (uniformBoundarySampling (ι := ι) (A := A)) := by
  unfold uniformBoundarySampling
  infer_instance

/-- Genuine bounded-observation concentration under the finite uniform
product sampling used for local resampling. The centering is the actual
one-edge uniform expectation. -/
theorem uniform_finite_boundary_concentration (Z : ι → A → ℂ)
    (hZ : ∀ i, Measurable (Z i)) (b : ℝ≥0) (hb : 0 < b)
    (w : ι → ℂ) (s : Finset ι) (hweights : 0 < ∑ i ∈ s, ‖w i‖ ^ 2)
    (hbound : ∀ i ∈ s, ∀ a, ‖Z i a‖ ≤ (b : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    (uniformBoundarySampling (ι := ι) (A := A)).real
      {ω | t * b * Real.sqrt (∑ i ∈ s, ‖w i‖ ^ 2) ≤
        ‖∑ i ∈ s, w i * (Z i (ω i) - ∫ a, Z i a ∂(PMF.uniformOfFintype A).toMeasure)‖} ≤
      4 * exp (-t ^ 2 / 32) := by
  let ν : ι → Measure A := fun _ => (PMF.uniformOfFintype A).toMeasure
  have hIndependent : iIndepFun (fun i (ω : ι → A) => Z i (ω i)) (Measure.pi ν) := by
    simpa only [Function.comp_def] using (product_coordinates_independent ν).comp Z hZ
  have h := boundary_sampling_concentration (μ := Measure.pi ν)
    (fun i (ω : ι → A) => Z i (ω i)) b hb w s hweights hIndependent
    (fun i _ => ((hZ i).comp (measurable_pi_apply i)).aestronglyMeasurable)
    (fun i hi => ae_of_all _ (fun ω => hbound i hi (ω i))) t ht
  have hmean : ∀ i, (∫ ω : ι → A, Z i (ω i) ∂Measure.pi ν) =
      ∫ a, Z i a ∂(PMF.uniformOfFintype A).toMeasure := by
    intro i
    exact product_coordinate_integral ν i (Z i) (hZ i)
  simp_rw [hmean] at h
  exact h

end ProductSampling

end LocalLaw
