import LocalLaw.RationalSemicircleStieltjes
import LocalLaw.RegularTree

/-! # The Kesten--McKay density Stieltjes transform

The density is exactly formula (1.1) of the article, in the normalization
A/sqrt(d-1). Its full-real-line Stieltjes integral is proved equal to the
algebraic tree transform, using actual semicircle integrals and partial
fractions at the two real exterior points d/sqrt(d-1) and -d/sqrt(d-1).
-/

open Set Complex MeasureTheory
open scoped Real Interval Topology
noncomputable section
namespace LocalLaw

def kestenMcKayDensity (d : ℕ) (x : ℝ) : ℝ :=
  (1+1/((d-1:ℕ):ℝ)-x^2/(d:ℝ))⁻¹*semicircleDensity x

def kestenMcKayExterior (d : ℕ) : ℝ := (d:ℝ)/Real.sqrt ((d-1:ℕ):ℝ)

def kestenMcKayExteriorRoot (d : ℕ) : ℝ := 1/Real.sqrt ((d-1:ℕ):ℝ)

theorem kestenMcKay_real_parameters (d : ℕ) (hd : 3≤d) :
    2<kestenMcKayExterior d ∧ 0<kestenMcKayExteriorRoot d ∧ kestenMcKayExteriorRoot d<1 ∧
      (kestenMcKayExteriorRoot d)^2-kestenMcKayExterior d*kestenMcKayExteriorRoot d+1=0 ∧
      kestenMcKayExteriorRoot d/kestenMcKayExterior d=1/(d:ℝ) ∧
      (kestenMcKayExterior d)^2=(d:ℝ)^2/((d-1:ℕ):ℝ) := by
  let k : ℝ := ((d-1:ℕ):ℝ)
  let r : ℝ := Real.sqrt k
  have hD : (3:ℝ)≤d := by exact_mod_cast hd
  have hk : k+1=(d:ℝ) := by
    dsimp only [k]
    exact_mod_cast Nat.sub_add_cancel (by omega : 1≤d)
  have hk1 : 1<k := by linarith
  have hr0 : 0≤r := Real.sqrt_nonneg k
  have hrsq : r^2=k := Real.sq_sqrt (by linarith)
  have hr1 : 1<r := by nlinarith
  have hr : 0<r := by linarith
  have hDpos : 0<(d:ℝ) := by linarith
  have hDgt : 2*r<(d:ℝ) := by
    by_contra h
    have hprod := mul_nonneg (show 0≤2*r-(d:ℝ) by linarith) (show 0≤2*r+(d:ℝ) by linarith)
    nlinarith [sq_nonneg ((d:ℝ)-2)]
  change 2<(d:ℝ)/r ∧ 0<1/r ∧ 1/r<1 ∧
    (1/r)^2-((d:ℝ)/r)*(1/r)+1=0 ∧ (1/r)/((d:ℝ)/r)=1/(d:ℝ) ∧
    ((d:ℝ)/r)^2=(d:ℝ)^2/k
  refine ⟨(lt_div_iff₀ hr).mpr hDgt,by positivity,(div_lt_one hr).mpr hr1,?_,?_,?_⟩
  · field_simp [hr.ne']
    nlinarith [hrsq,hk]
  · field_simp [hr.ne',hDpos.ne']
  · rw [div_pow,hrsq]

theorem kestenMcKayDensity_eq_rational (d : ℕ) (hd : 3≤d) (x : ℝ) :
    kestenMcKayDensity d x=(d:ℝ)*semicircleDensity x/((kestenMcKayExterior d)^2-x^2) := by
  have hp := kestenMcKay_real_parameters d hd
  have hD : (d:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have hk : (((d-1:ℕ):ℝ))≠0 := Nat.cast_ne_zero.mpr (by omega)
  have hkrel : (((d-1:ℕ):ℝ))+1=(d:ℝ) := by exact_mod_cast Nat.sub_add_cancel (by omega : 1≤d)
  have hscale : 1+1/((d-1:ℕ):ℝ)-x^2/(d:ℝ)=
      ((kestenMcKayExterior d)^2-x^2)/(d:ℝ) := by
    rw [hp.2.2.2.2.2]
    field_simp only [hD,hk]
    rw [←hkrel]
    ring
  unfold kestenMcKayDensity
  rw [hscale]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

theorem kestenMcKayDensity_eq_zero_of_not_mem (d : ℕ) (x : ℝ) (hx : x∉Icc (-2:ℝ) 2) :
    kestenMcKayDensity d x=0 := by
  rw [kestenMcKayDensity,semicircleDensity_eq_zero_of_not_mem x hx,mul_zero]

theorem kestenMcKay_density_interval_integral (d : ℕ) (hd : 3≤d) (z : ℂ) (hz : 0<z.im) :
    (∫x in (-2:ℝ)..2,(kestenMcKayDensity d x:ℂ)/((x:ℂ)-z))=
      kestenMcKayTransform d (semicircleRoot z) z := by
  let a := kestenMcKayExterior d
  let w := kestenMcKayExteriorRoot d
  have hp := kestenMcKay_real_parameters d hd
  have ha : 2<a := hp.1
  have hw : 0<w := hp.2.1
  have hw1 : w<1 := hp.2.2.1
  have hquad : w^2-a*w+1=0 := hp.2.2.2.1
  have hwa : w/a=1/(d:ℝ) := hp.2.2.2.2.1
  have ha2 : a^2=(d:ℝ)^2/((d-1:ℕ):ℝ) := hp.2.2.2.2.2
  have hi := rational_semicircle_density_interval_integral a w (d:ℝ) ha hw hw1 hquad z hz
  dsimp only [a,w] at hi
  simp_rw [←kestenMcKayDensity_eq_rational d hd] at hi
  rw [hi]
  let m := semicircleRoot z
  let k : ℂ := ((d-1:ℕ):ℂ)
  have hD : (d:ℂ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have hk : k≠0 := Nat.cast_ne_zero.mpr (by omega)
  have hDrel : (d:ℂ)=k+1 := by
    dsimp only [k]
    exact_mod_cast (Nat.sub_add_cancel (by omega : 1≤d)).symm
  have hwaC : (w:ℂ)/(a:ℂ)=1/(d:ℂ) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_natCast] using congrArg Complex.ofReal hwa
  have ha2C : (a:ℂ)^2=(d:ℂ)^2/k := by
    simpa only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast,k] using congrArg Complex.ofReal ha2
  have hden := kestenMcKay_denominator_ne_zero d m z hz (semicircleRoot_im_pos hz).le
  have hZden : (a:ℂ)^2-z^2≠0 := by
    have h1 := real_sub_upperHalfPlane_ne_zero a hz
    have h2 : (a:ℂ)+z≠0 := by
      intro h
      apply real_sub_upperHalfPlane_ne_zero (-a) hz
      simp only [Complex.ofReal_neg]
      linear_combination -h
    rw [sq_sub_sq]
    exact mul_ne_zero h2 h1
  have hquadratic : m^2+z*m= -1 := by linear_combination semicircleRoot_equation z
  have hid : ((d:ℂ)*m+z)*(-z-((d:ℂ)/k)*m)=(a:ℂ)^2-z^2 := by
    rw [ha2C]
    calc
      _= -z^2-((d:ℂ)^2/k)*(m^2+z*m) := by
        rw [hDrel]
        field_simp only [hk]
        ring
      _=_ := by rw [hquadratic]; ring
  have hnorm : (d:ℂ)/((a:ℂ)^2-z^2)*(m+z*(w:ℂ)/(a:ℂ))=
      ((d:ℂ)*m+z)/((a:ℂ)^2-z^2) := by
    rw [mul_div_assoc,hwaC]
    field_simp (maxDischargeDepth:=10) [hD,hZden]
    ring
  change (d:ℂ)/((a:ℂ)^2-z^2)*(m+z*(w:ℂ)/(a:ℂ))=_
  rw [hnorm]
  unfold kestenMcKayTransform
  change ((d:ℂ)*m+z)/((a:ℂ)^2-z^2)=(-z-((d:ℂ)/k)*m)⁻¹
  apply (div_eq_iff hZden).mpr
  rw [←hid]
  calc
    _=((d:ℂ)*m+z)*((-z-((d:ℂ)/k)*m)⁻¹*(-z-((d:ℂ)/k)*m)) := by
      rw [inv_mul_cancel₀ hden,mul_one]
    _=_ := by ring

def kestenMcKayStieltjes (d : ℕ) (z : ℂ) : ℂ :=
  ∫x : ℝ,(kestenMcKayDensity d x:ℂ)/((x:ℂ)-z)

/-- The explicit tree transform is exactly the density Stieltjes transform
from formula (1.1), with no integral or spectral-measure premise. -/
theorem kestenMcKayStieltjes_eq_transform (d : ℕ) (hd : 3≤d) (z : ℂ) (hz : 0<z.im) :
    kestenMcKayStieltjes d z=kestenMcKayTransform d (semicircleRoot z) z := by
  have hsupport : ∀x:ℝ,x∉Icc (-2:ℝ) 2→(kestenMcKayDensity d x:ℂ)/((x:ℂ)-z)=0 := by
    intro x hx
    rw [kestenMcKayDensity_eq_zero_of_not_mem d x hx,Complex.ofReal_zero,zero_div]
  have heq := setIntegral_eq_integral_of_forall_compl_eq_zero (μ:=volume) hsupport
  unfold kestenMcKayStieltjes
  rw [←heq,←Measure.restrict_congr_set Ioc_ae_eq_Icc,
    ←intervalIntegral.integral_of_le (by norm_num : (-2:ℝ)≤2)]
  exact kestenMcKay_density_interval_integral d hd z hz

end LocalLaw
