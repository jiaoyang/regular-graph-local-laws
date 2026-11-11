import LocalLaw.BoundaryRowBootstrap

/-!
# Explicit paper-error absorption for the finite nonlinear row bootstrap

The actual source range a>=12 leaves enough logarithmic gain even for a
coarser boundary-error SUM bootstrap. Counts, root decay, squared-column
bounds and the genuine D column sum give the contraction and the nonlinear
remainder budget. No bound on the boundary row error is an input.
-/

namespace LocalLaw

private theorem scaled_monomial_small (a p : ℕ) (L ε H : ℝ)
    (hL : 1 ≤ L) (hε : 0 ≤ ε) (hH : 0 ≤ H)
    (hcap : ε * L ^ (4 * a) ≤ 1) (hp : p + 1 ≤ 4 * a) (hlarge : 2 * H ≤ L) :
    H * ε * L ^ p ≤ 1 / 2 := by
  have hLp : 0 < L := by linarith
  have hscale := (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hp) hε).trans hcap
  apply (mul_le_mul_right hLp).mp
  have hh := mul_le_mul_of_nonneg_left hscale hH
  rw [pow_succ] at hh
  nlinarith only [hh, hlarge]

/-- The explicit second-order remainder has one full logarithmic spare gain
when a>=12, including a=12. -/
theorem source_nonlinear_remainder_absorption (a : ℕ) (L ε H : ℝ)
    (ha : 12 ≤ a) (hL : 1 ≤ L) (hε : 0 ≤ ε) (hH : 0 ≤ H)
    (hcap : ε * L ^ (4 * a) ≤ 1) (hlarge : 2 * H ≤ L) :
    H * ε ^ 2 * L ^ (3 * a + 9) ≤ ε / (2 * L ^ 2) := by
  have hLp : 0 < L := by linarith
  have hpow : L ^ (3 * a + 12) ≤ L ^ (4 * a) := pow_le_pow_right₀ hL (by omega)
  have hscale := (mul_le_mul_of_nonneg_left hpow hε).trans hcap
  have hfirst := mul_le_mul_of_nonneg_left hscale (mul_nonneg hH hε)
  have hsecond := mul_le_mul_of_nonneg_right hlarge hε
  apply (le_div_iff₀ (show 0 < 2 * L ^ 2 by positivity)).mpr
  apply (mul_le_mul_right hLp).mp
  have hid : (H * ε ^ 2 * L ^ (3 * a + 9) * (2 * L ^ 2)) * L =
      2 * H * ε ^ 2 * L ^ (3 * a + 12) := by
    have he : 3 * a + 12 = (3 * a + 9) + 2 + 1 := by omega
    rw [he, pow_add, pow_add, pow_one]
    ring
  rw [hid]
  nlinarith only [hfirst, hsecond]

private theorem sqrt_count_bound (a : ℕ) (n U L : ℝ) (_hn : 0 ≤ n) (hU : 0 ≤ U) (hL : 0 ≤ L)
    (hcount : n ≤ U * L ^ (2 * a)) : Real.sqrt n ≤ (U + 1) * L ^ a := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hUbound : U ≤ (U + 1) ^ 2 := by nlinarith only [hU]
  have hh := mul_le_mul_of_nonneg_right hUbound (pow_nonneg hL (2 * a))
  have he : (2 * a) = a * 2 := by omega
  rw [he, pow_mul] at hcount hh
  exact hcount.trans (hh.trans_eq (by ring))

/-- Source parameter realization for the coarser finite boundary-row
contraction. `n` is the actual boundary-label count, `W` a squared model-row
budget, and `M*sqrt(n)` the actual root-decay/count cancellation. -/
theorem boundary_row_parameter_budgets (a : ℕ) (L ε n M e S W U M0 E W0 : ℝ)
    (ha : 12 ≤ a) (hL : 1 ≤ L) (hε : 0 ≤ ε)
    (hn : 0 ≤ n) (hM : 0 ≤ M) (he : 0 ≤ e) (hS : 0 ≤ S) (hW : 0 ≤ W)
    (hU : 0 ≤ U) (hM0 : 0 ≤ M0) (hE : 0 ≤ E) (hW0 : 0 ≤ W0)
    (hcap : ε * L ^ (4 * a) ≤ 1)
    (hcount : n ≤ U * L ^ (2 * a)) (hroot : M * Real.sqrt n ≤ M0)
    (herror : e ≤ E * L ^ 4 * ε) (hsquare : S ^ 2 ≤ n * W) (hrow : W ≤ W0 * L)
    (hlargeFeedback : 2 * (U * E * (U + W0 + 1)) ≤ L)
    (hlargeRemainder : 2 * (2 * M0 * U * (U + 1) * E ^ 2 * W0) ≤ L) :
    n * e * S ≤ 1 / 2 ∧ 2 * n * M * e ^ 2 * S ^ 2 ≤ ε / (2 * L ^ 2) := by
  have hL0 : 0 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  let V := U + W0 + 1
  let H := 2 * M0 * U * (U + 1) * E ^ 2 * W0
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hnW := mul_le_mul hcount hrow hW (by positivity : 0 ≤ U * L ^ (2 * a))
  have hpower : L ^ (2 * a + 1) ≤ L ^ (2 * a + 2) := pow_le_pow_right₀ hL (by omega)
  have hUV : U * W0 ≤ V ^ 2 := by dsimp only [V]; nlinarith only [hU, hW0]
  have hSsq : S ^ 2 ≤ (V * L ^ (a + 1)) ^ 2 := by
    calc
      _ ≤ (U * L ^ (2 * a)) * (W0 * L) := hsquare.trans hnW
      _ = (U * W0) * L ^ (2 * a + 1) := by rw [pow_succ]; ring
      _ ≤ (U * W0) * L ^ (2 * a + 2) := mul_le_mul_of_nonneg_left hpower (mul_nonneg hU hW0)
      _ ≤ V ^ 2 * L ^ (2 * a + 2) := mul_le_mul_of_nonneg_right hUV (pow_nonneg hL0 _)
      _ = _ := by
        have heq : 2 * a + 2 = (a + 1) * 2 := by omega
        rw [heq, pow_mul]
        ring
  have hSbound : S ≤ V * L ^ (a + 1) := by
    have hp : 0 ≤ V * L ^ (a + 1) := by positivity
    nlinarith only [hSsq, hp, hS]
  have hfeedback : n * e * S ≤ (U * E * V) * ε * L ^ (3 * a + 5) := by
    have h1 := mul_le_mul hcount herror he (by positivity : 0 ≤ U * L ^ (2 * a))
    have h2 := mul_le_mul h1 hSbound hS (by positivity : 0 ≤ (U * L ^ (2 * a)) * (E * L ^ 4 * ε))
    apply h2.trans_eq
    have heq : 3 * a + 5 = 2 * a + 4 + (a + 1) := by omega
    rw [heq, pow_add, pow_add]
    ring
  refine ⟨hfeedback.trans (scaled_monomial_small a (3 * a + 5) L ε (U * E * V)
    hL hε (by positivity) hcap (by omega) hlargeFeedback), ?_⟩
  have hsqrtn := sqrt_count_bound a n U L hn hU hL0 hcount
  have hnroot : n * Real.sqrt n ≤ U * (U + 1) * L ^ (3 * a) := by
    have hh := mul_le_mul hcount hsqrtn (Real.sqrt_nonneg n) (by positivity : 0 ≤ U * L ^ (2 * a))
    apply hh.trans_eq
    have heq : 3 * a = 2 * a + a := by omega
    rw [heq, pow_add]
    ring
  have hMn : M * n ^ 2 ≤ M0 * (U * (U + 1) * L ^ (3 * a)) := by
    calc
      _ = M * n * (Real.sqrt n) ^ 2 := by rw [Real.sq_sqrt hn]; ring
      _ = (M * Real.sqrt n) * (n * Real.sqrt n) := by ring
      _ ≤ _ := mul_le_mul hroot hnroot (by positivity) hM0
  have he2 := pow_le_pow_left₀ he herror 2
  have hrem : 2 * n * M * e ^ 2 * S ^ 2 ≤ H * ε ^ 2 * L ^ (3 * a + 9) := by
    calc
      _ ≤ 2 * n * M * e ^ 2 * (n * W) := mul_le_mul_of_nonneg_left hsquare (by positivity)
      _ = 2 * (M * n ^ 2) * e ^ 2 * W := by ring
      _ ≤ 2 * (M0 * (U * (U + 1) * L ^ (3 * a))) * (E * L ^ 4 * ε) ^ 2 * (W0 * L) := by
        exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hMn (by norm_num)) he2
          (sq_nonneg e) (by positivity)) hrow hW (by positivity)
      _ = H * ε ^ 2 * L ^ (3 * a + 9) := by
        have heq : 3 * a + 9 = 3 * a + 8 + 1 := by omega
        rw [heq, pow_add, pow_add, pow_one]
        dsimp only [H]
        ring
  exact hrem.trans (source_nonlinear_remainder_absorption a L ε H ha hL hε hH hcap hlargeRemainder)

end LocalLaw
