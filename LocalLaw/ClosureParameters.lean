import LocalLaw.Theorem42
import LocalLaw.GraphBranchNet
import LocalLaw.ParameterSmallness
import LocalLaw.ResamplingRadiusGrowth

/-!
# Actual log-log depth selection and scalar closure parameters

A nonresonant depth is selected from two adjacent integers. For the paper's
logarithmic parameters the chosen resampling radius lies in its allowed
log-log interval, its recursion is small, and all fixed scalar-closure
large-log requirements hold eventually. No nonresonance or final smallness
condition is supplied as an asymptotic hypothesis.
-/

open Filter

namespace LocalLaw

noncomputable def nonresonantDepth (m : ℂ) (n : ℕ) : ℕ :=
  if 1 / 2 ≤ ‖cavitySum m n‖ then n else n + 1

theorem nonresonantDepth_bounds (m : ℂ) (n : ℕ) :
    n ≤ nonresonantDepth m n ∧ nonresonantDepth m n ≤ n + 1 := by
  unfold nonresonantDepth
  split_ifs <;> omega

theorem nonresonantDepth_valid (m : ℂ) (n : ℕ) (hm : ‖m‖ ≤ 1) :
    1 / 2 ≤ ‖cavitySum m (nonresonantDepth m n)‖ := by
  unfold nonresonantDepth
  split_ifs with h
  · exact h
  · exact (cavitySum_adjacent_nonresonance hm n).resolve_left h

noncomputable def lowerLogLogRadius (a d N : ℕ) : ℝ :=
  (a : ℝ) * Real.log (Real.log (N : ℝ)) / Real.log ((d - 1 : ℕ) : ℝ)

noncomputable def baselineCavityDepth (a d N : ℕ) : ℕ :=
  ⌊(3 / 2 : ℝ) * lowerLogLogRadius a d N⌋₊ + 2

noncomputable def actualCavityDepth (a d N : ℕ) (z : ℂ) : ℕ :=
  nonresonantDepth (semicircleRoot z) (baselineCavityDepth a d N)

/-- Integer rounding and the adjacent-depth choice stay within the actual
allowed resampling-radius interval once its lower endpoint exceeds four. -/
theorem actualCavityDepth_radius_bounds (a d N : ℕ) (z : ℂ)
    (hlarge : 4 ≤ lowerLogLogRadius a d N) :
    lowerLogLogRadius a d N ≤ ((actualCavityDepth a d N z - 1 : ℕ) : ℝ) ∧
      actualCavityDepth a d N z - 1 ≤ doubleLogRadius a d N := by
  have hdepth := nonresonantDepth_bounds (semicircleRoot z) (baselineCavityDepth a d N)
  change baselineCavityDepth a d N ≤ actualCavityDepth a d N z ∧
    actualCavityDepth a d N z ≤ baselineCavityDepth a d N + 1 at hdepth
  have hfloor := Nat.floor_le (show 0 ≤ (3 / 2 : ℝ) * lowerLogLogRadius a d N by linarith)
  have hfloorlt := Nat.lt_floor_add_one ((3 / 2 : ℝ) * lowerLogLogRadius a d N)
  have hdpos : 1 ≤ actualCavityDepth a d N z := by
    dsimp [baselineCavityDepth] at hdepth
    omega
  have hdcast : ((actualCavityDepth a d N z - 1 : ℕ) : ℝ) =
      (actualCavityDepth a d N z : ℝ) - 1 := by
    rw [Nat.cast_sub hdpos, Nat.cast_one]
  have hlo : lowerLogLogRadius a d N ≤ ((actualCavityDepth a d N z - 1 : ℕ) : ℝ) := by
    have hh : (⌊(3 / 2 : ℝ) * lowerLogLogRadius a d N⌋₊ : ℝ) + 2 ≤ (actualCavityDepth a d N z : ℝ) := by
      exact_mod_cast hdepth.1
    rw [hdcast]
    linarith
  have hhi : ((actualCavityDepth a d N z - 1 : ℕ) : ℝ) ≤ 2 * lowerLogLogRadius a d N := by
    have hh : (actualCavityDepth a d N z : ℝ) ≤ (⌊(3 / 2 : ℝ) * lowerLogLogRadius a d N⌋₊ : ℝ) + 3 := by
      exact_mod_cast hdepth.2
    rw [hdcast]
    linarith
  refine ⟨hlo, ?_⟩
  have heq : doubleLogRadius a d N = ⌊2 * lowerLogLogRadius a d N⌋₊ := by
    unfold doubleLogRadius lowerLogLogRadius
    congr 1
    push_cast
    ring
  rw [heq]
  exact (Nat.le_floor_iff (by linarith : 0 ≤ 2 * lowerLogLogRadius a d N)).mpr hhi

/-- The chosen depth is in the interior of the allowed log-log interval,
leaving a polynomial logarithmic gain for the local improvement errors. -/
theorem actualCavityDepth_strong_lower (a d N : ℕ) (z : ℂ) :
    (3 / 2 : ℝ) * lowerLogLogRadius a d N ≤
      ((actualCavityDepth a d N z - 1 : ℕ) : ℝ) := by
  have hdepth := (nonresonantDepth_bounds (semicircleRoot z) (baselineCavityDepth a d N)).1
  have hdepth' : baselineCavityDepth a d N ≤ actualCavityDepth a d N z := hdepth
  have hdpos : 1 ≤ actualCavityDepth a d N z := by
    dsimp [baselineCavityDepth] at hdepth'
    omega
  have hh : (⌊(3 / 2 : ℝ) * lowerLogLogRadius a d N⌋₊ : ℝ) + 2 ≤
      (actualCavityDepth a d N z : ℝ) := by exact_mod_cast hdepth'
  have hf := Nat.lt_floor_add_one ((3 / 2 : ℝ) * lowerLogLogRadius a d N)
  rw [Nat.cast_sub hdpos, Nat.cast_one]
  linarith

/-- The lower log-log endpoint tends to infinity for every positive a. -/
theorem lowerLogLogRadius_tendsto (a d : ℕ) (ha : 0 < a) (hd : 3 ≤ d) :
    Tendsto (lowerLogLogRadius a d) atTop atTop := by
  have hk : (1 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < d - 1 by omega)
  have hden := Real.log_pos hk
  have hcoeff : 0 < (a : ℝ) / Real.log ((d - 1 : ℕ) : ℝ) :=
    div_pos (Nat.cast_pos.mpr ha) hden
  have ht := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop))
  have hmul := ht.const_mul_atTop hcoeff
  convert hmul using 1
  funext N
  simp only [lowerLogLogRadius, Function.comp_apply]
  ring

/-- Even the larger adjacent depth is eventually at most log N. -/
theorem eventually_actualCavityDepth_le_log (a d : ℕ) (hd : 3 ≤ d) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, (actualCavityDepth a d N z : ℝ) ≤ Real.log (N : ℝ) := by
  let C : ℝ := (3 / 2 : ℝ) * (a : ℝ) / Real.log ((d - 1 : ℕ) : ℝ)
  have hk : (1 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < d - 1 by omega)
  have hC : 0 ≤ C := div_nonneg (by positivity) (Real.log_pos hk).le
  have ht := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hlittle := ((Real.isLittleO_pow_log_id_atTop (n := 1)).const_mul_left C).comp_tendsto ht
  have hbound := hlittle.bound (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hbound, eventually_log_ge_nat 6] with N hbound hlog
  intro z
  have hlogpos : 0 ≤ Real.log (N : ℝ) := by linarith
  simp only [Function.comp_apply, pow_one, id_eq, Real.norm_eq_abs, abs_of_nonneg hlogpos] at hbound
  have hx : (3 / 2 : ℝ) * lowerLogLogRadius a d N ≤ Real.log (N : ℝ) / 2 := by
    have h := (le_abs_self (C * Real.log (Real.log (N : ℝ)))).trans hbound
    have hid : (3 / 2 : ℝ) * lowerLogLogRadius a d N = C * Real.log (Real.log (N : ℝ)) := by
      unfold lowerLogLogRadius C
      ring
    rw [hid]
    linarith
  have hx0 : 0 ≤ lowerLogLogRadius a d N := by
    unfold lowerLogLogRadius
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith)))
      (Real.log_pos hk).le
  have hf := Nat.floor_le (show 0 ≤ (3 / 2 : ℝ) * lowerLogLogRadius a d N by positivity)
  have hd := (nonresonantDepth_bounds (semicircleRoot z) (baselineCavityDepth a d N)).2
  have hd' : (actualCavityDepth a d N z : ℝ) ≤ (⌊(3 / 2 : ℝ) * lowerLogLogRadius a d N⌋₊ : ℝ) + 3 := by
    exact_mod_cast hd
  linarith

/-- The actual small epsilon and a depth at most log N validate the exact
cavity formula throughout the weak event. -/
theorem depth_scalarScale_small (L s ε : ℝ) (n a : ℕ)
    (hL : 2 ≤ L) (hs : 0 < s) (hε : 0 ≤ ε) (ha : 1 ≤ a)
    (herror : ε ≤ (L ^ (4 * a))⁻¹) (hdepth : (n : ℝ) ≤ L) :
    (n : ℝ) * scalarScale s ε ≤ 1 / 2 := by
  have hLp : 0 < L := by linarith
  have hp := pow_le_pow_right₀ (by linarith : 1 ≤ L) (show 4 ≤ 4 * a by omega)
  have hi : (L ^ (4 * a))⁻¹ ≤ (L ^ 4)⁻¹ := inv_anti₀ (by positivity) hp
  have hsq : ε ≤ (1 / L ^ 2) ^ 2 := by
    calc
      ε ≤ (L ^ 4)⁻¹ := herror.trans hi
      _ = (1 / L ^ 2) ^ 2 := by field_simp; ring
  have hroot : Real.sqrt ε ≤ 1 / L ^ 2 := Real.sqrt_le_iff.mpr ⟨by positivity, hsq⟩
  calc
    (n : ℝ) * scalarScale s ε ≤ L * (1 / L ^ 2) :=
      mul_le_mul hdepth ((scalarScale_le_sqrt hs hε).trans hroot)
        (scalarScale_nonneg hε) hLp.le
    _ = 1 / L := by field_simp; ring
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hL

/-- All radius, nonresonance, and recursion-smallness requirements are
simultaneously realized by the actual source parameters. -/
theorem eventually_actual_cavity_parameters (a b d : ℕ) (β : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, 0 < z.im →
      Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      lowerLogLogRadius a d N ≤ ((actualCavityDepth a d N z - 1 : ℕ) : ℝ) ∧
      actualCavityDepth a d N z - 1 ≤ doubleLogRadius a d N ∧
      1 / 2 ≤ ‖cavitySum (semicircleRoot z) (actualCavityDepth a d N z)‖ ∧
      (actualCavityDepth a d N z : ℝ) * scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) ≤ 1 / 2 := by
  have hradius := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [hradius, eventually_actualCavityDepth_le_log a d hd,
    eventually_paperError_small a b d β ha hb hd hβ, eventually_log_ge_nat 2,
    eventually_ge_atTop 1] with N hradius hdepth herror hlog hN
  intro z hz hscale
  have hbound := actualCavityDepth_radius_bounds a d N z hradius
  refine ⟨hbound.1, hbound.2,
    nonresonantDepth_valid _ _ (semicircleRoot_norm_le_one z), ?_⟩
  apply depth_scalarScale_small (Real.log (N : ℝ)) (spectralScale z) _ _ a hlog
    (spectralScale_pos hz) (graphPaperError_nonnegative _ _ _ _ _ hN hz.le) (by omega)
  · exact herror z hz hscale
  · exact hdepth z

/-- The scalar closure certificate is now constructed for the actual source
parameters. Its row and cavity tolerances are explicit; proving that actual
resampling supplies those local tolerances is a separate graph estimate. -/
theorem eventually_actual_closure_budget (a b d : ℕ) (β B U V M₀ : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hβ : 0 < β)
    (hU : 0 ≤ U) (hV : 0 ≤ V) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, 0 < z.im →
      Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ‖z‖ ≤ B →
      ∃ D : ClosureBudget z (semicircleRoot z) (spectralScale z)
          (graphPaperError a d N (logarithmicRadius β d N) z),
        D.depth = actualCavityDepth a d N z ∧ D.L = Real.log (N : ℝ) ∧
        D.rowBase = U * graphPaperError a d N (logarithmicRadius β d N) z / Real.log (N : ℝ) ∧
        D.rowFeedback = V * Real.log (N : ℝ) ∧
        D.cavityError = graphPaperError a d N (logarithmicRadius β d N) z /
          (2 * Real.log (N : ℝ) ^ 2) ∧ D.exceptionalCavity = M₀ := by
  let C := localClosureConstant B (Real.sqrt (B + 2))
  filter_upwards [eventually_actual_cavity_parameters a b d β ha hb hd hβ,
    eventually_log_ge_nat 2, eventually_log_ge_nat (2 * C),
    eventually_log_ge_nat (2 * (U + V * (C + C ^ 2))),
    eventually_ge_atTop 1] with N hparameters hlog hscalar hrow hN
  intro z hz hscale hB
  have hp := hparameters z hz hscale
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let L := Real.log (N : ℝ)
  have hLp : 0 < L := by dsimp [L]; linarith
  have hε : 0 < ε := by
    exact inflateError_positive hLp (baseError_positive L a d N _ z.im _ hLp
      (by omega) (by omega) hz)
  let D := ClosureBudget.ofSemicircle z ε (actualCavityDepth a d N z) L B U V
    (U * ε / L) (V * L) (ε / (2 * L ^ 2)) M₀ hz hB hp.2.2.2 hp.2.2.1
    hε hU hV hlog (paperError_dichotomy a d N _ z _ hLp)
    (by positivity) le_rfl le_rfl hscalar hrow
  exact ⟨D, rfl, rfl, rfl, rfl, rfl, rfl⟩

end LocalLaw
