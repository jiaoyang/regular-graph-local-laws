import LocalLaw.PolynomialGraphMesh
import LocalLaw.ParameterSmallness

/-!
# The actual bounded spectral domain eventually has a polynomial mesh

The paper's N-dependent error, integer logarithmic radius and logarithmic eta
floor are used directly. No final error cap, numerical mesh inequality, or
continuum event inclusion is supplied as a hypothesis.
-/

open Filter

namespace LocalLaw

/-- The bounded part of the actual local-law spectral domain. -/
noncomputable def boundedLocalLawDomain (N b : ℕ) (B : ℝ) : Set ℂ :=
  {z | ‖z‖ ≤ B ∧ Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im}

/-- The regularized edge scale has an explicit bounded-domain cap. -/
theorem spectralScale_le_twice_norm_add_two (z : ℂ) : spectralScale z ≤ 2 * ‖z‖ + 2 := by
  have hzero : spectralScale (0 : ℂ) = 2 := by norm_num [spectralScale, edgeDistance]
  have h := spectralScale_lipschitz z 0
  rw [hzero, dist_zero_right] at h
  have h' := (le_abs_self (spectralScale z - 2)).trans h
  linarith

/-- For all sufficiently large N, the actual source error and logarithmic
radius admit a mesh of radius 2/N^12 throughout the bounded source domain. -/
theorem eventually_polynomial_graph_mesh (a b d : ℕ) (β B : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d)
    (hβ : 0 < β) (hβ₁ : β ≤ 1) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in atTop,
      Nonempty (UniformGraphMesh N d a (logarithmicRadius β d N)
        (boundedLocalLawDomain N b B) (2 / (N : ℝ) ^ 12)) := by
  have hlarge : ∀ᶠ N : ℕ in atTop, 16 * Real.sqrt (2 * B + 3) ≤ (N : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (16 * Real.sqrt (2 * B + 3)))
  filter_upwards [eventually_ge_atTop 4, eventually_log_ge_nat 3,
    eventually_log_pow_le_nat (8 * a + 4), hlarge,
    eventually_paperError_small a b d β ha hb hd hβ] with N hN hlog hweight hsize herror
  have hNpos : 0 < N := by omega
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hlog₁ : 1 ≤ Real.log (N : ℝ) := by linarith
  have hpower : 1 ≤ Real.log (N : ℝ) ^ b := one_le_pow₀ hlog₁
  have hheight : 1 / (N : ℝ) ≤ Real.log (N : ℝ) ^ b / (N : ℝ) :=
    div_le_div_of_nonneg_right hpower hn.le
  have hImaginary : ∀ z ∈ boundedLocalLawDomain N b B, 1 / (N : ℝ) ≤ z.im := by
    intro z hz
    exact hheight.trans hz.2
  have hCap : ∀ z ∈ boundedLocalLawDomain N b B,
      spectralScale z + graphPaperError a d N (logarithmicRadius β d N) z ≤ 2 * B + 3 := by
    intro z hz
    have hzp : 0 < z.im := (div_pos (by norm_num) hn).trans_le (hImaginary z hz)
    have hsmall := herror z hzp hz.2
    have hinv : (Real.log (N : ℝ) ^ (4 * a))⁻¹ ≤ 1 := by
      have hpow : 1 ≤ Real.log (N : ℝ) ^ (4 * a) := one_le_pow₀ hlog₁
      have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hpow
      simpa only [one_div, inv_one] using h
    have hε : graphPaperError a d N (logarithmicRadius β d N) z ≤ 1 := hsmall.trans hinv
    have hs := spectralScale_le_twice_norm_add_two z
    linarith [hz.1]
  have hradius := logarithmicRadius_power_le_N β d N hβ.le hβ₁ hd (by omega)
  exact ⟨polynomialGraphMesh N d a (logarithmicRadius β d N) (boundedLocalLawDomain N b B)
    (1 / (N : ℝ)) (2 * B + 3) hN hd hlog₁ hweight hradius le_rfl hImaginary
    (by linarith) hCap hsize⟩

end LocalLaw
