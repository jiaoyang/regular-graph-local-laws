import LocalLaw.ScalarStability

/-!
# Strong feedback from the original two-regime error dichotomy

A fourth-power residual improves the feedback to epsilon/L^3 without
changing either inflation branch. This permits a quadratic-log coefficient
in the row error while preserving strict tightening.
-/

namespace LocalLaw

def strongFeedbackConstant (G M : ℝ) : ℝ := 1+3*G^2+3*M

theorem scalar_strong_feedback (δ g : ℂ) (s ε L K G M : ℝ)
    (hs : 0<s) (hε : 0≤ε) (hK : 0≤K) (_hG : 0≤G) (hM : 0≤M)
    (hL : 2≤L) (hLK : 2*K≤L) (hgap₁ : Real.sqrt s≤‖g‖) (hgap₂ : ‖g‖≤G*Real.sqrt s)
    (hprior : ‖δ‖≤K*scalarScale s ε) (hres : ‖δ*(δ-g)‖≤M*ε/L^4)
    (hregime : ε≤s/L ∨ L^3*s≤ε) :
    Real.sqrt s*‖δ‖+‖δ‖^2≤strongFeedbackConstant G M*ε/L^3 := by
  have hL1 : 1≤L := by linarith
  have hLp : 0<L := by linarith
  let E := ε/L^3
  let R := M*ε/L^4
  have hE : 0≤E := by dsimp only [E]; positivity
  have hR : 0≤R := by dsimp only [R]; positivity
  have hRle : R≤M*E := by
    calc
      _ ≤ M*ε/L^3 := div_le_div_of_nonneg_left (mul_nonneg hM hε) (pow_pos hLp 3)
        (pow_le_pow_right₀ hL1 (by norm_num : 3≤4))
      _ = _ := by dsimp only [E]; ring
  have hconstant : 3*M≤strongFeedbackConstant G M := by unfold strongFeedbackConstant; nlinarith [sq_nonneg G]
  have hδ : 0≤‖δ‖ := norm_nonneg _
  rcases hregime with hsep | hedge
  · have hsmall := scalar_prior_separates δ g s ε L K hs hε hK hLp hLK hgap₁ hprior hsep
    have hstable := scalar_norm_stable δ g R hsmall hres
    have hlin : Real.sqrt s*‖δ‖≤2*R := by
      have hh := mul_le_mul_of_nonneg_left hgap₁ hδ
      nlinarith only [hh,hstable]
    have hrealgap : Real.sqrt s≤‖(Real.sqrt s:ℂ)‖ := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg s)]
    have hsmallS := scalar_prior_separates δ (Real.sqrt s:ℂ) s ε L K hs hε hK hLp hLK hrealgap hprior hsep
    have hsmallS' : ‖δ‖≤Real.sqrt s/2 := by
      simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg s)] using hsmallS
    have hsquare := mul_le_mul_of_nonneg_right hsmallS' hδ
    have hF : Real.sqrt s*‖δ‖+‖δ‖^2≤3*R := by nlinarith only [hlin,hsquare]
    exact hF.trans (calc
      3*R ≤ 3*(M*E) := mul_le_mul_of_nonneg_left hRle (by norm_num)
      _ = (3*M)*E := by ring
      _ ≤ strongFeedbackConstant G M*E := mul_le_mul_of_nonneg_right hconstant hE
      _ = strongFeedbackConstant G M*ε/L^3 := by dsimp only [E]; ring)
  · have hsE : s≤E := (le_div_iff₀ (pow_pos hLp 3)).mpr (by simpa only [mul_comm] using hedge)
    have hrev : ‖δ‖-‖g‖≤‖δ-g‖ := norm_sub_norm_le δ g
    have hmul := mul_le_mul_of_nonneg_left hrev hδ
    have hprod : ‖δ‖*‖δ-g‖≤R := by simpa only [norm_mul] using hres
    have hquad : ‖δ‖^2≤‖g‖*‖δ‖+R := by nlinarith only [hmul,hprod]
    have hgapSq : ‖g‖^2≤G^2*s := by
      have hh := pow_le_pow_left₀ (norm_nonneg g) hgap₂ 2
      simpa only [mul_pow,Real.sq_sqrt hs.le] using hh
    have hdeltaSq : ‖δ‖^2≤2*G^2*s+2*R := by
      nlinarith only [hquad,hgapSq,sq_nonneg (‖g‖-‖δ‖)]
    have hF : Real.sqrt s*‖δ‖+‖δ‖^2≤(1/2+3*G^2)*s+3*R := by
      nlinarith only [hdeltaSq,sq_nonneg (Real.sqrt s-‖δ‖),Real.sq_sqrt hs.le]
    have hscaled := mul_le_mul_of_nonneg_left hsE (show 0≤1/2+3*G^2 by positivity)
    have hscaledR := mul_le_mul_of_nonneg_left hRle (by norm_num : (0:ℝ)≤3)
    exact hF.trans (calc
      _ ≤ (1/2+3*G^2)*E+3*(M*E) := add_le_add hscaled hscaledR
      _ = (1/2+3*G^2+3*M)*E := by ring
      _ ≤ strongFeedbackConstant G M*E := mul_le_mul_of_nonneg_right (by
        unfold strongFeedbackConstant; linarith) hE
      _ = strongFeedbackConstant G M*ε/L^3 := by dsimp only [E]; ring)


end LocalLaw
