import LocalLaw.ErrorParameters

/-!
# The actual correlation-threshold smallness in (4.5)

The estimate is derived from the variance/fractional components of the base
error and the two actual inflation branches. The final phi inequality is not
an assumption, nor is a sub-Gaussian or self-consistency estimate substituted
for the finite parameter arithmetic.
-/

namespace LocalLaw

private theorem rpow_two_thirds_cube (X : ℝ) (hX : 0 < X) :
    (X ^ (2 / 3 : ℝ)) ^ 3 = X ^ 2 := by
  calc
    (X ^ (2 / 3 : ℝ)) ^ 3 = (X ^ (2 / 3 : ℝ)) ^ (3 : ℝ) := (Real.rpow_natCast _ 3).symm
    _ = X ^ ((2 / 3 : ℝ) * 3) := (Real.rpow_mul hX.le _ _).symm
    _ = X ^ 2 := by norm_num

private theorem fractional_component_cube (L X e : ℝ) (a : ℕ)
    (hL : 0 ≤ L) (hX : 0 < X) (_he : 0 ≤ e)
    (fraction : L ^ (8 * a) / X ^ (2 / 3 : ℝ) ≤ e) :
    L ^ (24 * a) ≤ e ^ 3 * X ^ 2 := by
  have hroot : 0 < X ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hX _
  have hmul := (div_le_iff₀ hroot).mp fraction
  have hcube := pow_le_pow_left₀ (pow_nonneg hL _) hmul 3
  calc
    L ^ (24 * a) = (L ^ (8 * a)) ^ 3 := by rw [← pow_mul]; congr 1; omega
    _ ≤ (e * X ^ (2 / 3 : ℝ)) ^ 3 := hcube
    _ = e ^ 3 * X ^ 2 := by rw [mul_pow, rpow_two_thirds_cube X hX]

/-- The 2/3 fractional component implies the mixed epsilon-sqrt(epsilon)
control used in the correlation parameter. -/
theorem fractional_component_mixed_bound (L X e : ℝ) (a : ℕ)
    (hL : 0 ≤ L) (hX : 0 < X) (he : 0 ≤ e)
    (fraction : L ^ (8 * a) / X ^ (2 / 3 : ℝ) ≤ e) :
    L ^ (12 * a) / X ≤ e * Real.sqrt e := by
  apply (div_le_iff₀ hX).2
  apply (sq_le_sq₀ (pow_nonneg hL _) (by positivity)).mp
  calc
    (L ^ (12 * a)) ^ 2 = L ^ (24 * a) := by rw [← pow_mul]; congr 1; omega
    _ ≤ e ^ 3 * X ^ 2 := fractional_component_cube L X e a hL hX he fraction
    _ = (e * Real.sqrt e * X) ^ 2 := by rw [mul_pow, mul_pow, Real.sq_sqrt he]; ring

/-- The same component and the source N*eta lower bound control epsilon*X
without assuming the desired correlation estimate. -/
theorem fractional_component_sample_lower (L X e : ℝ) (a b : ℕ)
    (hL : 1 ≤ L) (hX : 0 < X) (he : 0 ≤ e)
    (fraction : L ^ (8 * a) / X ^ (2 / 3 : ℝ) ≤ e)
    (sample : L ^ b ≤ X) (exponent : 12 * a + 12 ≤ b) :
    L ^ (12 * a + 4) ≤ e * X := by
  apply (pow_le_pow_iff_left₀ (pow_nonneg (by linarith : 0 ≤ L) _)
    (mul_nonneg he hX.le) (by decide : (3 : ℕ) ≠ 0)).mp
  calc
    (L ^ (12 * a + 4)) ^ 3 = L ^ (36 * a + 12) := by rw [← pow_mul]; congr 1; omega
    _ ≤ L ^ (24 * a + b) := pow_le_pow_right₀ hL (by omega)
    _ = L ^ (24 * a) * L ^ b := pow_add ..
    _ ≤ L ^ (24 * a) * X := mul_le_mul_of_nonneg_left sample (pow_nonneg (by linarith) _)
    _ ≤ (e ^ 3 * X ^ 2) * X := mul_le_mul_of_nonneg_right
      (fractional_component_cube L X e a (by linarith) hX he fraction) hX.le
    _ = (e * X) ^ 3 := by ring

/-- In the separated regime the scalar budget has the extra factor one
third required to sum the three correlation numerator contributions. -/
theorem scalarScale_le_third_sqrt (s e L : ℝ) (hs : 0 < s) (he : 0 ≤ e)
    (hL : 9 ≤ L) (separated : e ≤ s / L) :
    scalarScale s e ≤ Real.sqrt e / 3 := by
  have hLp : 0 < L := by linarith
  have hroot : 0 < Real.sqrt (s + e) := Real.sqrt_pos.mpr (by linarith)
  have hse := (le_div_iff₀ hLp).mp separated
  have hlarge : 9 * e ≤ s + e := by
    have h := mul_le_mul_of_nonneg_right hL he
    nlinarith
  have hsq : (3 * e) ^ 2 ≤ (Real.sqrt e * Real.sqrt (s + e)) ^ 2 := by
    simp only [mul_pow, Real.sq_sqrt he, Real.sq_sqrt (by linarith : 0 ≤ s + e)]
    nlinarith [mul_le_mul_of_nonneg_left hlarge he]
  have hlinear := (sq_le_sq₀ (by positivity : 0 ≤ 3 * e)
    (mul_nonneg (Real.sqrt_nonneg e) (Real.sqrt_nonneg (s + e)))).mp hsq
  unfold scalarScale
  apply (div_le_iff₀ hroot).2
  nlinarith



/-- The three numerator terms of phi are controlled from the actual error
components and the actual inflation branch, not a final phi hypothesis. -/
theorem correlationThreshold_component_bound (L X v s e₀ ε : ℝ) (a b : ℕ)
    (hL : 9 ≤ L) (ha : 12 ≤ a) (hb : 25 * a ≤ b) (sample : L ^ b ≤ X)
    (hv : 0 ≤ v) (hs : 0 < s) (he₀ : 0 ≤ e₀)
    (inflation : ε = inflateError L e₀ s)
    (variance : L ^ (8 * a) * Real.sqrt (v / X) ≤ e₀)
    (fraction : L ^ (8 * a) / X ^ (2 / 3 : ℝ) ≤ e₀) :
    L ^ (2 * a) * Real.sqrt ((v + L ^ 3 * ε + scalarScale s ε) / X) ≤ ε / L ^ (4 * a) := by
  have hLp : 0 < L := by linarith
  have hL₁ : 1 ≤ L := by linarith
  have hXone : 1 ≤ X := (one_le_pow₀ hL₁).trans sample
  have hXp : 0 < X := by linarith
  have hε : 0 ≤ ε := by rw [inflation]; exact inflateError_nonnegative he₀
  have he₀ε : e₀ ≤ ε := by rw [inflation]; exact (inflateError_bounds hL₁ he₀).1
  have hvariance := variance.trans he₀ε
  have hfraction := fraction.trans he₀ε
  have hLfourA : 3 ≤ L ^ (4 * a) := by
    have h := pow_le_pow_right₀ hL₁ (show 1 ≤ 4 * a by omega)
    simp only [pow_one] at h
    linarith
  have hprod : L ^ (4 * a) * L ^ (12 * a) = L ^ (16 * a) := by
    rw [← pow_add]
    congr 1
    omega
  have hvX : 0 ≤ v / X := div_nonneg hv hXp.le
  have hvarianceSq : L ^ (16 * a) * (v / X) ≤ ε ^ 2 := by
    have h := pow_le_pow_left₀ (mul_nonneg (pow_nonneg hLp.le _) (Real.sqrt_nonneg _)) hvariance 2
    have hpow : (L ^ (8 * a)) ^ 2 = L ^ (16 * a) := by rw [← pow_mul]; congr 1; omega
    simpa only [mul_pow, Real.sq_sqrt hvX, hpow] using h
  have hA : L ^ (12 * a) * v / X ≤ ε ^ 2 / 3 := by
    have hthree := mul_le_mul_of_nonneg_right hLfourA (mul_nonneg (pow_nonneg hLp.le (12 * a)) hvX)
    have hbound : 3 * (L ^ (12 * a) * v / X) ≤ ε ^ 2 := by
      calc
        3 * (L ^ (12 * a) * v / X) = 3 * (L ^ (12 * a) * (v / X)) := by ring
        _ ≤ L ^ (4 * a) * (L ^ (12 * a) * (v / X)) := hthree
        _ = L ^ (16 * a) * (v / X) := by rw [← mul_assoc, hprod]
        _ ≤ ε ^ 2 := hvarianceSq
    linarith
  have hsample := fractional_component_sample_lower L X ε a b hL₁ hXp hε hfraction sample (by omega)
  have hB : L ^ (12 * a + 3) * ε / X ≤ ε ^ 2 / 3 := by
    have hthree : 3 * L ^ (12 * a + 3) ≤ ε * X := by
      calc
        3 * L ^ (12 * a + 3) ≤ L ^ (12 * a + 3) * L := by
          nlinarith [mul_le_mul_of_nonneg_right (show 3 ≤ L by linarith) (pow_nonneg hLp.le (12 * a + 3))]
        _ = L ^ (12 * a + 4) := by rw [← pow_succ]
        _ ≤ ε * X := hsample
    apply (div_le_iff₀ hXp).2
    nlinarith [mul_le_mul_of_nonneg_left hthree hε]
  have hC : L ^ (12 * a) * scalarScale s ε / X ≤ ε ^ 2 / 3 := by
    have hΨ : 0 ≤ scalarScale s ε := scalarScale_nonneg hε
    by_cases hsmall : e₀ ≤ s / L
    · have hεeq : ε = e₀ := inflation.trans (inflateError_of_small hsmall)
      have hmixed : L ^ (12 * a) / X ≤ ε * Real.sqrt ε := by
        rw [hεeq]
        exact fractional_component_mixed_bound L X e₀ a hLp.le hXp he₀ fraction
      have hscale : scalarScale s ε ≤ Real.sqrt ε / 3 :=
        scalarScale_le_third_sqrt s ε L hs hε hL (by simpa only [hεeq] using hsmall)
      calc
        L ^ (12 * a) * scalarScale s ε / X = (L ^ (12 * a) / X) * scalarScale s ε := by ring
        _ ≤ (ε * Real.sqrt ε) * (Real.sqrt ε / 3) := mul_le_mul hmixed hscale hΨ (by positivity)
        _ = ε * (Real.sqrt ε) ^ 2 / 3 := by ring
        _ = ε ^ 2 / 3 := by rw [Real.sq_sqrt hε]; ring
    · have hεeq : ε = L ^ 4 * e₀ := by rw [inflation, inflateError, if_neg hsmall]
      have hLfour : 3 ≤ L ^ 4 := by
        have h := pow_le_pow_right₀ hL₁ (show 1 ≤ (4 : ℕ) by decide)
        simp only [pow_one] at h
        linarith
      have hthree : 3 * e₀ ≤ ε := by
        rw [hεeq]
        exact mul_le_mul_of_nonneg_right hLfour he₀
      have hroot := Real.sqrt_le_sqrt he₀ε
      have hmixed₀ := fractional_component_mixed_bound L X e₀ a hLp.le hXp he₀ fraction
      have hmixed : L ^ (12 * a) / X ≤ (ε * Real.sqrt ε) / 3 := by
        have hbound : 3 * (L ^ (12 * a) / X) ≤ ε * Real.sqrt ε := by
          calc
            3 * (L ^ (12 * a) / X) ≤ 3 * (e₀ * Real.sqrt e₀) :=
              mul_le_mul_of_nonneg_left hmixed₀ (by norm_num)
            _ = (3 * e₀) * Real.sqrt e₀ := by ring
            _ ≤ ε * Real.sqrt e₀ := mul_le_mul_of_nonneg_right hthree (Real.sqrt_nonneg _)
            _ ≤ ε * Real.sqrt ε := mul_le_mul_of_nonneg_left hroot hε
        linarith
      have hscale := scalarScale_le_sqrt hs hε
      calc
        L ^ (12 * a) * scalarScale s ε / X = (L ^ (12 * a) / X) * scalarScale s ε := by ring
        _ ≤ ((ε * Real.sqrt ε) / 3) * Real.sqrt ε := mul_le_mul hmixed hscale hΨ (by positivity)
        _ = ε * (Real.sqrt ε) ^ 2 / 3 := by ring
        _ = ε ^ 2 / 3 := by rw [Real.sq_sqrt hε]; ring
  have hsum : L ^ (12 * a) * ((v + L ^ 3 * ε + scalarScale s ε) / X) ≤ ε ^ 2 := by
    have hpow : L ^ (12 * a) * L ^ 3 = L ^ (12 * a + 3) := (pow_add ..).symm
    calc
      _ = L ^ (12 * a) * v / X + L ^ (12 * a + 3) * ε / X +
          L ^ (12 * a) * scalarScale s ε / X := by rw [← hpow]; ring
      _ ≤ ε ^ 2 / 3 + ε ^ 2 / 3 + ε ^ 2 / 3 := add_le_add (add_le_add hA hB) hC
      _ = ε ^ 2 := by ring
  have hnum : 0 ≤ (v + L ^ 3 * ε + scalarScale s ε) / X := by
    have hΨ : 0 ≤ scalarScale s ε := scalarScale_nonneg hε
    positivity
  apply (le_div_iff₀ (pow_pos hLp (4 * a))).2
  apply (sq_le_sq₀ (by positivity) hε).mp
  have hpow : (L ^ (2 * a) * L ^ (4 * a)) ^ 2 = L ^ (12 * a) := by
    rw [← pow_add, ← pow_mul]
    congr 1
    omega
  calc
    (L ^ (2 * a) * Real.sqrt ((v + L ^ 3 * ε + scalarScale s ε) / X) * L ^ (4 * a)) ^ 2 =
        (L ^ (2 * a) * L ^ (4 * a)) ^ 2 *
          (Real.sqrt ((v + L ^ 3 * ε + scalarScale s ε) / X)) ^ 2 := by ring
    _ = L ^ (12 * a) * ((v + L ^ 3 * ε + scalarScale s ε) / X) := by rw [hpow, Real.sq_sqrt hnum]
    _ ≤ ε ^ 2 := hsum

/-- The second estimate of (4.5), for the actual base error and actual phi
formula in (4.4). All needed component inequalities are derived from (4.2). -/
theorem correlationThreshold_le_inflated_base (L : ℝ) (a b d N r : ℕ) (η v s : ℝ)
    (hL : 9 ≤ L) (ha : 12 ≤ a) (hb : 25 * a ≤ b)
    (_hN : 0 < N) (hη : 0 < η) (hv : 0 ≤ v) (hs : 0 < s)
    (sample : L ^ b ≤ (N : ℝ) * η) :
    correlationThreshold L a N η v s (inflateError L (baseError L a d N r η v) s) ≤
      inflateError L (baseError L a d N r η v) s / L ^ (4 * a) := by
  have hL0 : 0 ≤ L := by linarith
  have hbase : 0 ≤ baseError L a d N r η v := baseError_nonnegative L a d N r η v hL0 hη.le
  have hcomponents := baseError_component_bounds L a d N r η v hL0 hη.le
  have hfraction : L ^ (8 * a) / (((N : ℝ) * η) ^ (2 / 3 : ℝ)) ≤ baseError L a d N r η v := by
    simpa only [div_eq_mul_inv] using hcomponents.2.2
  simpa only [correlationThreshold, inflatedPrime] using
    correlationThreshold_component_bound L ((N : ℝ) * η) v s (baseError L a d N r η v)
      (inflateError L (baseError L a d N r η v) s) a b hL ha hb sample hv hs hbase rfl
      hcomponents.2.1 hfraction

end LocalLaw
