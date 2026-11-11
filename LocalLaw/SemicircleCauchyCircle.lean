import LocalLaw.Semicircle
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # The semicircle Cauchy integral on the unit circle

This is a genuine contour integral calculation, using Cauchy's formula and
the physical quadratic root. It is the analytic ingredient for identifying
the density Stieltjes integral; no density integral is assumed here.
-/

open Set Complex Metric
open scoped Real Topology
noncomputable section
namespace LocalLaw

theorem cavity_quadratic_linear_identity {m z : ℂ}
    (hm : m^2+z*m+1=0) : z= -m-m⁻¹ := by
  have hm0 := cavity_root_ne_zero hm
  apply (mul_right_cancel₀ hm0)
  calc
    z*m= -m^2-1 := by linear_combination hm
    _=(-m-m⁻¹)*m := by field_simp; ring

theorem cavity_circle_outer_denominator_ne_zero {m : ℂ} (hm0 : m≠0)
    (hm : ‖m‖<1) (w : ℂ) (hw : w∈closedBall (0:ℂ) 1) : w+m⁻¹≠0 := by
  intro hzero
  have hwNorm : ‖w‖≤1 := by simpa only [mem_closedBall,dist_zero_right] using hw
  have heq : w= -m⁻¹ := eq_neg_of_add_eq_zero_left hzero
  have hnorm : ‖w‖=‖m‖⁻¹ := by rw [heq,norm_neg,norm_inv]
  have hpos : 0<‖m‖ := norm_pos_iff.mpr hm0
  have hprod := mul_le_mul_of_nonneg_left hwNorm hpos.le
  rw [hnorm,mul_inv_cancel₀ hpos.ne'] at hprod
  linarith

/-- A direct Cauchy integral evaluation at the unique root in the disk. -/
theorem semicircle_unit_circle_integral (z : ℂ) (hz : 0<z.im) :
    (∮ w in C(0,1), (1-w^2)/(w^2-z*w+1))=
      (2*Real.pi*Complex.I:ℂ)*semicircleRoot z := by
  let m := semicircleRoot z
  have hm0 : m≠0 := semicircleRoot_ne_zero z
  have hm : ‖m‖<1 := semicircleRoot_norm_lt_one hz
  have hlinear : z= -m-m⁻¹ := cavity_quadratic_linear_identity (semicircleRoot_equation z)
  have hden : ∀w∈closedBall (0:ℂ) 1,w+m⁻¹≠0 :=
    fun w hw => cavity_circle_outer_denominator_ne_zero hm0 hm w hw
  let f : ℂ→ℂ := fun w => (1-w^2)/(w+m⁻¹)
  have hf : DifferentiableOn ℂ f (closedBall (0:ℂ) 1) := by
    intro w hw
    exact (((differentiableAt_const (1:ℂ)).sub (differentiableAt_id.pow 2)).div
      (differentiableAt_id.add_const (m⁻¹)) (hden w hw)).differentiableWithinAt
  have hmem : -m∈ball (0:ℂ) 1 := by simpa only [mem_ball,dist_zero_right,norm_neg] using hm
  have hcauchy := hf.circleIntegral_sub_inv_smul hmem
  have hfactor (w:ℂ) : w^2-z*w+1=(w+m)*(w+m⁻¹) := by
    rw [hlinear]
    field_simp
    ring
  have hsame : (fun w : ℂ => (w- -m)⁻¹ • f w)=fun w => (1-w^2)/(w^2-z*w+1) := by
    funext w
    rw [hfactor]
    simp only [f,sub_neg_eq_add,smul_eq_mul,div_eq_mul_inv,mul_inv_rev]
    ring
  have hfroot : f (-m)=m := by
    change (1-(-m)^2)/(-m+m⁻¹)=m
    apply (div_eq_iff (hden (-m) (ball_subset_closedBall hmem))).mpr
    field_simp
    ring
  rw [hsame,hfroot,smul_eq_mul] at hcauchy
  exact hcauchy

end LocalLaw
