import LocalLaw.ClosureParameters

/-!
# Integer radius hierarchy for the source parameters

The logarithmic localization radius, the larger structural radius and the
selected log-log resampling radius are compared with their actual integer
rounding. Fixed multiples and additive margins are realized eventually;
these scale separations are not left as qualitative asymptotic assumptions.
-/

open Filter

namespace LocalLaw

/-- Integer flooring preserves the exact source separation 8r<=R. -/
theorem logarithmic_radius_eight_le (c β : ℝ) (d N : ℕ)
    (hd : 3 ≤ d) (hN : 1 ≤ N) (hβ : 0 ≤ β) (hc : 0 ≤ c) (hβc : β ≤ c / 32) :
    8 * logarithmicRadius β d N ≤ logarithmicRadius (c / 4) d N := by
  have hk : (1 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < d - 1 by omega)
  have hlogk : 0 < Real.log ((d - 1 : ℕ) : ℝ) := Real.log_pos hk
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hcoord : 0 ≤ β * Real.log (N : ℝ) / Real.log ((d - 1 : ℕ) : ℝ) := by positivity
  have hf := Nat.floor_le hcoord
  have hx : 8 * (logarithmicRadius β d N : ℝ) ≤
      (c / 4) * Real.log (N : ℝ) / Real.log ((d - 1 : ℕ) : ℝ) := by
    change (logarithmicRadius β d N : ℝ) ≤ _ at hf
    have hmul := mul_le_mul_of_nonneg_right (show 8 * β ≤ c / 4 by linarith)
      (div_nonneg hlog hlogk.le)
    calc
      8 * (logarithmicRadius β d N : ℝ) ≤
          8 * (β * Real.log (N : ℝ) / Real.log ((d - 1 : ℕ) : ℝ)) := by linarith
      _ ≤ (c / 4) * Real.log (N : ℝ) / Real.log ((d - 1 : ℕ) : ℝ) := by
        convert hmul using 1 <;> ring
  unfold logarithmicRadius
  apply (Nat.le_floor_iff (show 0 ≤ (c / 4) * Real.log (N : ℝ) /
    Real.log ((d - 1 : ℕ) : ℝ) by positivity)).mpr
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hx

/-- Any fixed multiple of the log-log radius, with any fixed additive margin,
is eventually dominated by a positive logarithmic radius. -/
theorem eventually_resampling_radius_margin (a d K A : ℕ) (β : ℝ)
    (hd : 3 ≤ d) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop,
      K * doubleLogRadius a d N + A ≤ logarithmicRadius β d N := by
  let k : ℝ := ((d - 1 : ℕ) : ℝ)
  let C : ℝ := (K : ℝ) * (2 * a : ℕ) / β
  have hk : 1 < k := by dsimp [k]; exact_mod_cast (show 1 < d - 1 by omega)
  have hlogk : 0 < Real.log k := Real.log_pos hk
  have ht := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hlittle := ((Real.isLittleO_pow_log_id_atTop (n := 1)).const_mul_left C).comp_tendsto ht
  have hbound := hlittle.bound (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hbound, eventually_log_ge_nat 1,
    eventually_log_ge_nat (2 * (A : ℝ) * Real.log k / β)] with N hbound hlog hmargin
  let L := Real.log (N : ℝ)
  have hLp : 0 < L := by dsimp [L]; linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hlog
  have hexp : 0 ≤ ((2 * a : ℕ) : ℝ) * Real.log L / Real.log k := by positivity
  have hell := Nat.floor_le hexp
  change (doubleLogRadius a d N : ℝ) ≤ _ at hell
  simp only [Function.comp_apply, pow_one, id_eq, Real.norm_eq_abs,
    abs_of_nonneg hLp.le] at hbound
  change |C * Real.log L| ≤ (1 / 2) * |L| at hbound
  rw [abs_of_pos hLp] at hbound
  have hsmall : (K : ℝ) * ((2 * a : ℕ) : ℝ) * Real.log L ≤ β * L / 2 := by
    have h := mul_le_mul_of_nonneg_left ((le_abs_self (C * Real.log L)).trans hbound) hβ.le
    dsimp [C] at h
    field_simp [ne_of_gt hβ] at h
    push_cast
    nlinarith
  have hAmargin : (A : ℝ) * Real.log k ≤ β * L / 2 := by
    have h := (div_le_iff₀ hβ).mp hmargin
    change 2 * (A : ℝ) * Real.log k ≤ L * β at h
    linarith
  have hcoord : 0 ≤ β * L / Real.log k := by positivity
  apply (Nat.le_floor_iff hcoord).mpr
  rw [Nat.cast_add, Nat.cast_mul]
  have hfloorMul := mul_le_mul_of_nonneg_left hell (Nat.cast_nonneg K)
  apply (le_div_iff₀ hlogk).mpr
  have hscaled := mul_le_mul_of_nonneg_right hfloorMul hlogk.le
  have hcancel : ((K : ℝ) * (((2 * a : ℕ) : ℝ) * Real.log L / Real.log k)) * Real.log k =
      (K : ℝ) * ((2 * a : ℕ) : ℝ) * Real.log L := by field_simp; ring
  rw [hcancel] at hscaled
  nlinarith

/-- A convenient set of concrete margins for ball containment, isolation and
cutset applications in Sections 5 and 6. The maximal printed r exponent is
allowed; no strict beta<c/32 assumption is used. -/
theorem eventually_source_radius_hierarchy (a d : ℕ) (c β : ℝ)
    (hd : 3 ≤ d) (hc : 0 < c) (hβ : 0 < β) (hβc : β ≤ c / 32) :
    ∀ᶠ N : ℕ in atTop,
      let r := logarithmicRadius β d N
      let R := logarithmicRadius (c / 4) d N
      let ell := doubleLogRadius a d N
      8 * r ≤ R ∧ 64 * ell + 64 ≤ r ∧ 2 * r ≤ R / 4 ∧ r + ell + 1 ≤ R / 4 := by
  filter_upwards [eventually_resampling_radius_margin a d 64 64 β hd hβ,
    eventually_ge_atTop 1] with N hmargin hN
  have he := logarithmic_radius_eight_le c β d N hd hN hβ.le hc.le hβc
  have hdiv : 2 * logarithmicRadius β d N ≤ logarithmicRadius (c / 4) d N / 4 := by omega
  exact ⟨he, hmargin, hdiv, by omega⟩

end LocalLaw
