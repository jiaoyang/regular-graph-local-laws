import LocalLaw.UniformGraphNet

/-!
# An explicit polynomial spectral mesh

The numerical mesh inequalities are proved for radius 2/N^12 from concrete
finite conditions. They are not supplied as final mesh hypotheses. Passing
from fixed d,a,r(N) to these finite conditions is an asymptotic task.
-/

namespace LocalLaw

private theorem mesh_fraction_margin (n : ℝ) (hn : 4 ≤ n) (p : ℕ) (hp : 4 ≤ p)
    (c b : ℝ) (hb : 0 < b) (hcb : c * b ≤ 64) :
    c / n ^ p ≤ 1 / (b * n) := by
  have hnp : 0 < n := by linarith
  have hn1 : 1 ≤ n := by linarith
  have hn3 : (64 : ℝ) ≤ n ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hn 3
    norm_num at h
    exact h
  have hp₁ : 3 ≤ p - 1 := by omega
  have hpower : 64 ≤ n ^ (p - 1) := hn3.trans (pow_le_pow_right₀ hn1 hp₁)
  apply (div_le_div_iff₀ (pow_pos hnp _) (mul_pos hb hnp)).2
  have hpn : p = (p - 1) + 1 := by omega
  rw [hpn, pow_succ]
  calc
    c * (b * n) = (c * b) * n := by ring
    _ ≤ 64 * n := mul_le_mul_of_nonneg_right hcb hnp.le
    _ ≤ n ^ (p - 1) * n := mul_le_mul_of_nonneg_right hpower hnp.le
    _ = 1 * (n ^ (p - 1) * n) := by simp

/-- Coarse observable continuity constants at eta>=1/N. -/
theorem polynomial_mesh_observable_coefficients (n η : ℝ) (hn : 4 ≤ n)
    (hη : 1 / n ≤ η) :
    (1 / η ^ 2 + 1 / η) ≤ 2 * n ^ 2 ∧
    (1 / η ^ 2 + ((1 + 2 / η ^ 2) / η ^ 2)) ≤ 4 * n ^ 4 := by
  have hnp : 0 < n := by linarith
  have hηp : 0 < η := (div_pos (by norm_num) hnp).trans_le hη
  have hprod : 1 ≤ n * η := by
    have h := (div_le_iff₀ hnp).mp hη
    nlinarith
  have hinv : 1 / η ≤ n := (div_le_iff₀ hηp).2 (by nlinarith)
  have hinvnonneg : 0 ≤ 1 / η := by positivity
  have hinv2 : 1 / η ^ 2 ≤ n ^ 2 := by
    simpa only [one_div_pow] using pow_le_pow_left₀ hinvnonneg hinv 2
  have hn1 : 1 ≤ n := by linarith
  have hn2 : n ≤ n ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hn1) hnp.le]
  have hn24 : n ^ 2 ≤ n ^ 4 := pow_le_pow_right₀ hn1 (by decide)
  have hsq : (1 / η ^ 2) ^ 2 ≤ n ^ 4 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / η ^ 2) hinv2 2
    convert h using 1
    ring
  constructor
  · linarith
  · have heq : 1 / η ^ 2 + ((1 + 2 / η ^ 2) / η ^ 2) =
        2 * (1 / η ^ 2) + 2 * (1 / η ^ 2) ^ 2 := by ring
    rw [heq]
    nlinarith

/-- The actual base-error modulus at radius 2/N^12 is bounded by 1/(8N). -/
theorem polynomial_mesh_base_modulus (a N : ℕ) (η : ℝ) (hN : 4 ≤ N)
    (hη : 1 / (N : ℝ) ≤ η)
    (_hlog : 1 ≤ Real.log (N : ℝ))
    (hweight : Real.log (N : ℝ) ^ (8 * a + 4) ≤ (N : ℝ)) :
    baseErrorModulus a N η (2 / (N : ℝ) ^ 12) ≤ 1 / (8 * (N : ℝ)) := by
  let n : ℝ := N
  have hn4 : (4 : ℝ) ≤ n := by
    change (4 : ℝ) ≤ (N : ℝ)
    exact_mod_cast hN
  have hnp : 0 < n := by linarith
  have hn0 : n ≠ 0 := ne_of_gt hnp
  have hn1 : 1 ≤ n := by linarith
  have hηp : 0 < η := (div_pos (by norm_num) hnp).trans_le hη
  have hprod : 1 ≤ n * η := by
    have h := (div_le_iff₀ hnp).mp hη
    nlinarith
  have hvariance : 8 / (n * η ^ 2) ≤ 8 * n := by
    apply (div_le_iff₀ (mul_pos hnp (sq_pos_of_pos hηp))).2
    have hsq := one_le_pow₀ hprod (n := 2)
    nlinarith
  have hnegative : (n * η) ^ (-(5 / 3 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hprod (by norm_num)
  have hfractional : (2 / 3 : ℝ) * (n * η) ^ (-(5 / 3 : ℝ)) * n ≤ n := by
    have h := mul_le_mul_of_nonneg_right hnegative hnp.le
    nlinarith [Real.rpow_nonneg (mul_nonneg hnp.le hηp.le) (-(5 / 3 : ℝ))]
  have hsqrt : Real.sqrt ((8 / (n * η ^ 2)) * (2 / n ^ 12)) ≤ 4 / n ^ 5 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · calc
        (8 / (n * η ^ 2)) * (2 / n ^ 12) ≤ (8 * n) * (2 / n ^ 12) :=
          mul_le_mul_of_nonneg_right hvariance (by positivity)
        _ = 16 / n ^ 11 := by field_simp; ring
        _ ≤ 16 / n ^ 10 := by
          have h := one_div_le_one_div_of_le (pow_pos hnp 10)
            (pow_le_pow_right₀ hn1 (by decide : 10 ≤ 11))
          convert mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 16) using 1 <;> ring
        _ = (4 / n ^ 5) ^ 2 := by field_simp; ring
  have hlinear : ((2 / 3 : ℝ) * (n * η) ^ (-(5 / 3 : ℝ)) * n) * (2 / n ^ 12) ≤ 2 / n ^ 11 := by
    calc
      _ ≤ n * (2 / n ^ 12) := mul_le_mul_of_nonneg_right hfractional (by positivity)
      _ = 2 / n ^ 11 := by field_simp; ring
  have hsum : Real.sqrt ((8 / (n * η ^ 2)) * (2 / n ^ 12)) +
      ((2 / 3 : ℝ) * (n * η) ^ (-(5 / 3 : ℝ)) * n) * (2 / n ^ 12) ≤
      4 / n ^ 5 + 2 / n ^ 11 := add_le_add hsqrt hlinear
  have hsum0 : 0 ≤ Real.sqrt ((8 / (n * η ^ 2)) * (2 / n ^ 12)) +
      ((2 / 3 : ℝ) * (n * η) ^ (-(5 / 3 : ℝ)) * n) * (2 / n ^ 12) := by positivity
  change Real.log n ^ (8 * a + 4) *
    (Real.sqrt ((8 / (n * η ^ 2)) * (2 / n ^ 12)) +
      ((2 / 3 : ℝ) * (n * η) ^ (-(5 / 3 : ℝ)) * n) * (2 / n ^ 12)) ≤ 1 / (8 * n)
  calc
    _ ≤ n * (4 / n ^ 5 + 2 / n ^ 11) := mul_le_mul hweight hsum hsum0 hnp.le
    _ ≤ n * (6 / n ^ 5) := by
      apply mul_le_mul_of_nonneg_left _ hnp.le
      have h := one_div_le_one_div_of_le (pow_pos hnp 5)
        (pow_le_pow_right₀ hn1 (by decide : 5 ≤ 11))
      have hh : 2 / n ^ 11 ≤ 2 / n ^ 5 := by
        convert mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
      calc
        4 / n ^ 5 + 2 / n ^ 11 ≤ 4 / n ^ 5 + 2 / n ^ 5 := add_le_add_left hh _
        _ = 6 / n ^ 5 := by ring
    _ = 6 / n ^ 4 := by field_simp; ring
    _ ≤ 1 / (8 * n) := mesh_fraction_margin n hn4 4 (by decide) 6 8 (by norm_num) (by norm_num)

/-- The raw localization contribution supplies a uniform positive error floor. -/
theorem localizationErrorFloor_ge_inverse_vertex (a d N r : ℕ)
    (_hN : 0 < N) (hd : 3 ≤ d) (hlog : 1 ≤ Real.log (N : ℝ))
    (hradius : (((d - 1 : ℕ) : ℝ) ^ r) ≤ (N : ℝ)) :
    1 / (N : ℝ) ≤ localizationErrorFloor a d N r := by
  have hdp : (0 : ℝ) < (d - 1 : ℕ) := Nat.cast_pos.mpr (by omega)
  have hden : 0 < (((d - 1 : ℕ) : ℝ) ^ r) := pow_pos hdp _
  have hinv := one_div_le_one_div_of_le hden hradius
  have hw : 1 ≤ Real.log (N : ℝ) ^ (8 * a) := one_le_pow₀ hlog
  unfold localizationErrorFloor
  calc
    1 / (N : ℝ) ≤ (((d - 1 : ℕ) : ℝ) ^ r)⁻¹ := by simpa only [one_div] using hinv
    _ ≤ Real.log (N : ℝ) ^ (8 * a) * (((d - 1 : ℕ) : ℝ) ^ r)⁻¹ := by
      nlinarith [mul_le_mul_of_nonneg_right hw (inv_nonneg.mpr hden.le)]

/-- A concrete UniformGraphMesh at radius 2/N^12. All four numerical mesh
fields are proved from finite source-parameter inequalities. -/
noncomputable def polynomialGraphMesh (N d a r : ℕ) (domain : Set ℂ) (η A : ℝ)
    (hN : 4 ≤ N) (hd : 3 ≤ d) (hlog : 1 ≤ Real.log (N : ℝ))
    (hweight : Real.log (N : ℝ) ^ (8 * a + 4) ≤ (N : ℝ))
    (hradius : (((d - 1 : ℕ) : ℝ) ^ r) ≤ (N : ℝ))
    (hη : 1 / (N : ℝ) ≤ η) (hImaginary : ∀ z ∈ domain, η ≤ z.im)
    (hA : 0 < A) (hCap : ∀ z ∈ domain, spectralScale z + graphPaperError a d N r z ≤ A)
    (hLarge : 16 * Real.sqrt A ≤ (N : ℝ)) :
    UniformGraphMesh N d a r domain (2 / (N : ℝ) ^ 12) := by
  have hNpos : 0 < N := by omega
  have hn4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hn0 : (N : ℝ) ≠ 0 := ne_of_gt hn
  have hn1 : (1 : ℝ) ≤ N := by linarith
  have hηp : 0 < η := (div_pos (by norm_num) hn).trans_le hη
  have hfloor := localizationErrorFloor_ge_inverse_vertex a d N r hNpos hd hlog hradius
  have hcoeff := polynomial_mesh_observable_coefficients (N : ℝ) η hn4 hη
  refine {
    vertexPositive := hNpos
    degreeAtLeastThree := hd
    logLarge := hlog
    etaFloor := η
    etaPositive := hηp
    lowerImaginary := hImaginary
    cap := A
    capPositive := hA
    totalCap := hCap
    baseMesh := ?_
    scaleMesh := ?_
    cavityMesh := ?_
    entryMesh := ?_ }
  · have hbase := polynomial_mesh_base_modulus a N η hN hη hlog hweight
    apply hbase.trans
    have h := div_le_div_of_nonneg_right hfloor (by norm_num : (0 : ℝ) ≤ 8)
    convert h using 1
    ring
  · have hmargin := mesh_fraction_margin (N : ℝ) hn4 12 (by decide) 4 8 (by norm_num) (by norm_num)
    have heta := div_le_div_of_nonneg_right hη (by norm_num : (0 : ℝ) ≤ 8)
    calc
      2 * (2 / (N : ℝ) ^ 12) = 4 / (N : ℝ) ^ 12 := by ring
      _ ≤ 1 / (8 * (N : ℝ)) := hmargin
      _ = (1 / (N : ℝ)) / 8 := by ring
      _ ≤ η / 8 := heta
  · have hsqrt : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
    have hnum : 4 / (N : ℝ) ^ 10 ≤ ((1 / (N : ℝ)) / Real.sqrt A) / 4 := by
      have hpow : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 10 := pow_le_pow_right₀ hn1 (by decide)
      have hmul := mul_le_mul_of_nonneg_right hLarge hn.le
      have htarget : 4 / (N : ℝ) ^ 10 ≤ 1 / (4 * (N : ℝ) * Real.sqrt A) := by
        apply (div_le_div_iff₀ (pow_pos hn 10) (by positivity : 0 < 4 * (N : ℝ) * Real.sqrt A)).2
        nlinarith
      convert htarget using 1
      field_simp
      ring
    calc
      _ ≤ (2 * (N : ℝ) ^ 2) * (2 / (N : ℝ) ^ 12) :=
        mul_le_mul_of_nonneg_right hcoeff.1 (by positivity)
      _ = 4 / (N : ℝ) ^ 10 := by field_simp; ring
      _ ≤ ((1 / (N : ℝ)) / Real.sqrt A) / 4 := hnum
      _ ≤ (localizationErrorFloor a d N r / Real.sqrt A) / 4 :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hfloor hsqrt.le) (by norm_num)
  · have hmargin := mesh_fraction_margin (N : ℝ) hn4 8 (by decide) 8 4 (by norm_num) (by norm_num)
    calc
      _ ≤ (4 * (N : ℝ) ^ 4) * (2 / (N : ℝ) ^ 12) :=
        mul_le_mul_of_nonneg_right hcoeff.2 (by positivity)
      _ = 8 / (N : ℝ) ^ 8 := by field_simp; ring
      _ ≤ 1 / (4 * (N : ℝ)) := hmargin
      _ ≤ localizationErrorFloor a d N r / 4 := by
        have h := div_le_div_of_nonneg_right hfloor (by norm_num : (0 : ℝ) ≤ 4)
        convert h using 1
        ring

end LocalLaw
