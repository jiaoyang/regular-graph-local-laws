import LocalLaw.LocalClosure
import LocalLaw.ScalarStrongFeedback

/-!
# Strict closure with quadratic-log row feedback

The original inflation dichotomy is retained. A fourth-power cavity residual
supplies a cubic feedback gain, which absorbs a quadratic-log row coefficient.
-/

namespace LocalLaw

noncomputable def strongLocalNormConstant (B G M0 : ℝ) : ℝ :=
  scalarConstant G (3*(B+1)*M0)

noncomputable def strongLocalFeedbackConstant (B G M0 : ℝ) : ℝ :=
  strongFeedbackConstant G (3*(B+1)*M0)

theorem local_certificate_strong_closure {I : Type*}
    (q m z : ℂ) (n : ℕ) (s ε L K G B M0 U V u v : ℝ) (rowError : I → ℝ)
    (hm : m^2+z*m+1=0) (hmnorm : ‖m‖≤1) (hz : ‖z‖≤B)
    (hsmall : (n:ℝ)*‖q-m‖≤1/2) (hnonresonant : 1/2≤‖cavitySum m n‖)
    (hs : 0<s) (hε : 0<ε) (hK : 0≤K) (hG : 0≤G) (hM0 : 0≤M0)
    (hV : 0≤V) (hL : 2≤L) (hLK : 2*K≤L)
    (hgap₁ : Real.sqrt s≤‖m⁻¹-m‖) (hgap₂ : ‖m⁻¹-m‖≤G*Real.sqrt s)
    (hprior : ‖q-m‖≤K*scalarScale s ε)
    (hresidual : ‖q-cavityIterate z q n‖≤M0*ε/L^4)
    (hregime : ε≤s/L ∨ L^3*s≤ε)
    (hrow : ∀ i,rowError i≤u+v*(Real.sqrt s*‖q-m‖+‖q-m‖^2))
    (hu : u≤U*ε/L) (hv : v≤V*L^2)
    (hLscalar : 2*strongLocalNormConstant B G M0≤L)
    (hLrow : 2*(U+V*strongLocalFeedbackConstant B G M0)≤L) :
    ‖q-m‖≤scalarScale s ε/2 ∧ ∀ i,rowError i≤ε/2 := by
  let M := 3*(B+1)*M0
  let C := strongLocalNormConstant B G M0
  let F := strongLocalFeedbackConstant B G M0
  have hB : 0≤B := (norm_nonneg z).trans hz
  have hM : 0≤M := by dsimp only [M]; positivity
  have hLp : 0<L := by linarith
  have hL1 : 1≤L := by linarith
  have hpoly : ‖(q-m)*((q-m)-(m⁻¹-m))‖≤M*ε/L^4 := by
    rw [←cavity_quadratic_factor hm]
    calc
      _ ≤ (3*(B+1))*‖q-cavityIterate z q n‖ :=
        cavity_polynomial_residual_bound_bounded hm hmnorm n hsmall hnonresonant hz
      _ ≤ (3*(B+1))*(M0*ε/L^4) := mul_le_mul_of_nonneg_left hresidual (by positivity)
      _ = _ := by dsimp only [M]; ring
  have hpolyWeak : ‖(q-m)*((q-m)-(m⁻¹-m))‖≤M*ε/L^2 := hpoly.trans
    (div_le_div_of_nonneg_left (mul_nonneg hM hε.le) (pow_pos hLp 2) (pow_le_pow_right₀ hL1 (by norm_num : 2≤4)))
  have hnorm := (scalar_two_regime (q-m) (m⁻¹-m) s ε L K G M hs hε hK hG hM hL hLK
    hgap₁ hgap₂ hprior hpolyWeak hregime).1
  have hfeedback := scalar_strong_feedback (q-m) (m⁻¹-m) s ε L K G M hs hε.le hK hG hM hL hLK
    hgap₁ hgap₂ hprior hpoly hregime
  have hhalfscalar : C*scalarScale s ε/L≤scalarScale s ε/2 := by
    apply (div_le_iff₀ hLp).mpr
    have hh := mul_le_mul_of_nonneg_right hLscalar (scalarScale_nonneg (s:=s) hε.le)
    change 2*C*scalarScale s ε≤L*scalarScale s ε at hh
    nlinarith only [hh]
  refine ⟨hnorm.trans hhalfscalar,?_⟩
  intro i
  have hfeedback0 : 0≤Real.sqrt s*‖q-m‖+‖q-m‖^2 := by positivity
  have hrowbound : rowError i≤(U+V*F)*ε/L := by
    calc
      _ ≤ u+v*(Real.sqrt s*‖q-m‖+‖q-m‖^2) := hrow i
      _ ≤ U*ε/L+(V*L^2)*(Real.sqrt s*‖q-m‖+‖q-m‖^2) :=
        add_le_add hu (mul_le_mul_of_nonneg_right hv hfeedback0)
      _ ≤ U*ε/L+(V*L^2)*(F*ε/L^3) :=
        add_le_add_left (mul_le_mul_of_nonneg_left hfeedback (mul_nonneg hV (sq_nonneg L))) _
      _ = _ := by field_simp [ne_of_gt hLp]; ring
  apply hrowbound.trans
  apply (div_le_iff₀ hLp).mpr
  have hh := mul_le_mul_of_nonneg_right hLrow hε.le
  change 2*(U+V*F)*ε≤L*ε at hh
  nlinarith only [hh]

end LocalLaw
