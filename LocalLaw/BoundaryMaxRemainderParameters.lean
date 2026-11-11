import LocalLaw.BoundaryMaxBootstrap
import LocalLaw.BoundaryRemainderParameters

/-!
# Realize the maximum bootstrap with O(log^2 N) exceptional labels

A genuine D column budget of order log^5(N)*epsilon still contracts, and
its nonlinear remainder fits epsilon/(2 log^2 N), for the source a>=12.
Unlike a sum bootstrap, the maximum bootstrap pays no extra boundary count
in its feedback coefficient.
-/

namespace LocalLaw

private theorem max_scaled_monomial_small (a p : ℕ) (L ε H : ℝ)
    (hL : 1 ≤ L) (hε : 0 ≤ ε) (hH : 0 ≤ H)
    (hcap : ε * L ^ (4 * a) ≤ 1) (hp : p + 1 ≤ 4 * a) (hlarge : 2 * H ≤ L) :
    H * ε * L ^ p ≤ 1 / 2 := by
  have hLp : 0 < L := by linarith
  have hh := (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hp) hε).trans hcap
  have hh := mul_le_mul_of_nonneg_left hh hH
  rw [pow_succ] at hh
  apply (mul_le_mul_right hLp).mp
  nlinarith only [hh,hlarge]

/-- All actual finite row quantities remain visible. Only numerical source
bounds are inputs; neither contraction nor remainder size is assumed. -/
theorem boundary_max_parameter_budgets (a : ℕ) (L ε n M e S W U M0 E W0 : ℝ)
    (ha : 12 ≤ a) (hL : 1 ≤ L) (hε : 0 ≤ ε)
    (hn : 0 ≤ n) (hM : 0 ≤ M) (he : 0 ≤ e) (hS : 0 ≤ S) (hW : 0 ≤ W)
    (hU : 0 ≤ U) (hM0 : 0 ≤ M0) (hE : 0 ≤ E) (hW0 : 0 ≤ W0)
    (hcap : ε * L ^ (4 * a) ≤ 1)
    (hcount : n ≤ U * L ^ (2 * a)) (hroot : M * Real.sqrt n ≤ M0)
    (herror : e ≤ E * L ^ 5 * ε) (hsquare : S ^ 2 ≤ n * W) (hrow : W ≤ W0 * L)
    (hlargeFeedback : 2 * (E * (U + W0 + 1)) ≤ L)
    (hlargeRemainder : 2 * (2 * M0 * (U + 1) * E ^ 2 * W0) ≤ L) :
    e * S ≤ 1 / 2 ∧ 2 * M * e ^ 2 * S ^ 2 ≤ ε / (2 * L ^ 2) := by
  have hL0 : 0 ≤ L := by linarith
  let V := U + W0 + 1
  let H := 2 * M0 * (U + 1) * E ^ 2 * W0
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hSsq : S ^ 2 ≤ (V * L ^ (a + 1)) ^ 2 := by
    calc
      _ ≤ (U * L ^ (2 * a)) * (W0 * L) := hsquare.trans
        (mul_le_mul hcount hrow hW (by positivity))
      _ = (U * W0) * L ^ (2 * a + 1) := by rw [pow_succ]; ring
      _ ≤ (U * W0) * L ^ (2 * a + 2) := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hL (by omega)) (mul_nonneg hU hW0)
      _ ≤ V ^ 2 * L ^ (2 * a + 2) := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hL0 _)
        dsimp only [V]; nlinarith only [hU,hW0]
      _ = _ := by
        have hh : 2*a+2=(a+1)*2 := by omega
        rw [hh,pow_mul]; ring
  have hSbound : S ≤ V * L ^ (a + 1) := by
    have hh : 0 ≤ V * L ^ (a+1) := by positivity
    nlinarith only [hSsq,hS,hh]
  have hfeedback : e*S ≤ (E*V)*ε*L^(a+6) := by
    apply (mul_le_mul herror hSbound hS (by positivity)).trans_eq
    have hh : a+6=5+(a+1) := by omega
    rw [hh,pow_add]; ring
  refine ⟨hfeedback.trans (max_scaled_monomial_small a (a+6) L ε (E*V)
    hL hε (by positivity) hcap (by omega) hlargeFeedback), ?_⟩
  have hsqrtn : Real.sqrt n ≤ (U+1)*L^a := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hUbound : U ≤ (U+1)^2 := by nlinarith only [hU]
    have hh := mul_le_mul_of_nonneg_right hUbound (pow_nonneg hL0 (2*a))
    have hp : 2*a=a*2 := by omega
    rw [hp,pow_mul] at hcount hh
    exact hcount.trans (hh.trans_eq (by ring))
  have hMn : M*n ≤ M0*((U+1)*L^a) := by
    calc
      _ = (M*Real.sqrt n)*Real.sqrt n := by rw [mul_assoc,Real.mul_self_sqrt hn]
      _ ≤ _ := mul_le_mul hroot hsqrtn (Real.sqrt_nonneg n) hM0
  have he2 := pow_le_pow_left₀ he herror 2
  have hrem : 2*M*e^2*S^2 ≤ H*ε^2*L^(a+11) := by
    calc
      _ ≤ 2*M*e^2*(n*W) := mul_le_mul_of_nonneg_left hsquare (by positivity)
      _ = 2*(M*n)*e^2*W := by ring
      _ ≤ 2*(M0*((U+1)*L^a))*(E*L^5*ε)^2*(W0*L) := by
        exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hMn (by norm_num))
          he2 (sq_nonneg e) (by positivity)) hrow hW (by positivity)
      _ = _ := by
        have hh : a+11=a+10+1 := by omega
        rw [hh,pow_add,pow_add,pow_one]
        dsimp only [H]; ring
  have hpower : L^(a+11) ≤ L^(3*a+9) := pow_le_pow_right₀ hL (by omega)
  exact hrem.trans ((mul_le_mul_of_nonneg_left hpower (mul_nonneg hH (sq_nonneg ε))).trans
    (source_nonlinear_remainder_absorption a L ε H ha hL hε hH hcap hlargeRemainder))

end LocalLaw
