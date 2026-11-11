import SpectralConsequences.CancellationPolynomials
import LocalLaw.TreeBoundaryMass
import LocalLaw.SpectralGap

/-! Uniform cancellation of the constant-eigenvector pole in source (7.40). -/
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem treeEdgeWeight_norm_le_three_quarters (d:ℕ)(hd:3≤d):
    ‖treeEdgeWeight d‖≤3/4:=by
  have hs:=treeEdgeWeight_norm_sq d hd
  have hdR:(3:ℝ)≤d:=Nat.cast_le.mpr hd
  have hh:1/((d:ℝ)-1)≤1/2:=one_div_le_one_div_of_le (by norm_num) (by linarith)
  nlinarith [norm_nonneg (treeEdgeWeight d)]

theorem physical_root_trivial_pole_factor (d:ℕ)(hd:3≤d)(z:ℂ):
    treeEdgeWeight d*((d:ℂ)*treeEdgeWeight d-z)*semicircleRoot z=
      (semicircleRoot z+treeEdgeWeight d)*(1+treeEdgeWeight d*semicircleRoot z):=by
  have hm:=semicircleRoot_equation z
  have hn:((d:ℂ)-1)*(treeEdgeWeight d)^2=1:=by
    rw [treeEdgeWeight_sq d hd]
    have hk:((d-1:ℕ):ℂ)≠0:=Nat.cast_ne_zero.mpr (by omega)
    have hk':(d:ℂ)-1≠0:=by simpa only [Nat.cast_sub (by omega:1≤d),Nat.cast_one] using hk
    exact mul_one_div_cancel hk' 
  linear_combination -(treeEdgeWeight d)*hm+semicircleRoot z*hn

/-- The root displacement, multiplied by the actual pole, is uniformly O(1/N),
including points arbitrarily near the trivial eigenvalue. -/
theorem trivialPole_mul_root_displacement_bound (N d:ℕ)(hN:1≤N)(hd:3≤d)
    (z:ℂ)(hz:0<z.im):
    ‖trivialPole N d z*(semicircleRoot z+treeEdgeWeight d)‖≤3/(N:ℝ):=by
  let m:=semicircleRoot z
  let α:=treeEdgeWeight d
  let gap:=(d:ℂ)*α-z
  have hm:‖m‖≤1:=semicircleRoot_norm_le_one z
  have ha:‖α‖≤3/4:=treeEdgeWeight_norm_le_three_quarters d hd
  have hu:‖α*m‖≤3/4:=by rw [norm_mul];exact (mul_le_mul_of_nonneg_left hm (norm_nonneg α)).trans (by simpa only [mul_one] using ha)
  have hlower:1/4≤‖1+α*m‖:=by
    have hh:=norm_sub_norm_le (1:ℂ) (-α*m)
    simp only [neg_mul,norm_neg,sub_neg_eq_add,norm_one] at hh
    linarith
  have hgap:gap≠0:=by
    intro he
    have hh:=congrArg Complex.im he
    simp only [gap,α,treeEdgeWeight,Complex.sub_im,Complex.mul_im,Complex.ofReal_im,
      Complex.natCast_im,zero_mul,mul_zero,add_zero,zero_sub,Complex.zero_im] at hh
    linarith
  have hgp:0<‖gap‖:=norm_pos_iff.mpr hgap
  have hfac:=congrArg norm (physical_root_trivial_pole_factor d hd z)
  change ‖α*gap*m‖=‖(m+α)*(1+α*m)‖ at hfac
  simp only [norm_mul] at hfac
  have hnorm:‖m+α‖≤3*‖gap‖:=by
    have h1:=mul_le_mul_of_nonneg_left hlower (norm_nonneg (m+α))
    have h2:=mul_le_mul_of_nonneg_left hm (mul_nonneg (norm_nonneg α) (norm_nonneg gap))
    have h3:=mul_le_mul_of_nonneg_right ha (norm_nonneg gap)
    nlinarith
  have hNp:0<(N:ℝ):=Nat.cast_pos.mpr (by omega)
  simp only [trivialPole,norm_mul,norm_inv,Complex.norm_natCast]
  change (N:ℝ)⁻¹*‖gap‖⁻¹*‖m+α‖≤3/(N:ℝ)
  calc
    _≤(N:ℝ)⁻¹*‖gap‖⁻¹*(3*‖gap‖):=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _=3/(N:ℝ):=by field_simp;ring

def combinedCorrectionCoefficient (d ell:ℕ)(m md:ℂ):ℂ:=
  traceCorrectionCoefficient d ell m md+
    regularRootLinearCoefficient d ell m md/(1-m^(2*ell+2))*cavityCorrectionCoefficient d ell m

/-- The exact polynomial numerator whose zero cancels the pole. -/
theorem combinedCorrectionCoefficient_sub_one (d ell:ℕ)(hd:3≤d)(z:ℂ)(hz:0<z.im)
    (hT:1-(semicircleRoot z)^(2*ell+2)≠0):
    combinedCorrectionCoefficient d ell (semicircleRoot z) (kestenMcKayTransform d (semicircleRoot z) z)-1=
      correctionPolynomial
        ((d:ℂ)/((d-1:ℕ):ℂ)*((d:ℂ)*((d-1:ℕ):ℂ)^ell-1))
        ((d:ℂ)/((d-1:ℕ):ℂ)*((d-1:ℕ):ℂ)^ell)
        ((semicircleRoot z)^(2*ell+2)) (treeEdgeWeight d*semicircleRoot z)/
      ((1-treeEdgeWeight d*semicircleRoot z)^2*(1-(semicircleRoot z)^(2*ell+2))):=by
  let m:=semicircleRoot z
  let md:=kestenMcKayTransform d m z
  let α:=treeEdgeWeight d
  let k:ℂ:=((d-1:ℕ):ℂ)
  let u:=α*m
  have hkcast:k=(d:ℂ)-1:=by dsimp only [k];rw [Nat.cast_sub (by omega:1≤d),Nat.cast_one]
  have hu:‖u‖<1:=by
    dsimp only [u]
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (semicircleRoot_norm_le_one z) (norm_nonneg α)).trans_lt
      (by simpa only [mul_one] using (treeEdgeWeight_norm_le_three_quarters d hd).trans_lt (by norm_num:(3/4:ℝ)<1))
  have hminus:1-u≠0:=by
    intro hh
    have hh':u=1:=by linear_combination -hh
    rw [hh',norm_one] at hu
    exact (lt_irrefl _ hu)
  have hplus:1+u≠0:=by
    intro hh
    have hh':u= -1:=by linear_combination hh
    rw [hh',norm_neg,norm_one] at hu
    exact (lt_irrefl _ hu)
  have hu2:u^2=m^2/k:=by dsimp only [u];rw [mul_pow,treeEdgeWeight_sq d hd,←hkcast];ring
  have hden:1-m^2/k=(1-u)*(1+u):=by rw [show (1-u)*(1+u)=1-u^2 by ring,hu2]
  have hmd:md=m/((1-u)*(1+u)):=by
    dsimp only [md]
    rw [kestenMcKayTransform_eq d hd m z (semicircleRoot_equation z) hz (semicircleRoot_im_pos hz).le,hden]
  have hmul:md*(1+u)=m/(1-u):=by rw [hmd];field_simp [hminus,hplus];ring
  have hlinear:regularRootLinearCoefficient d ell m md*(1+m*α)^2=
      (d:ℂ)/k*m^(2*ell+2)/(1-u)^2:=by
    have he:1+m*α=1+u:=by dsimp only [u];ring
    rw [he]
    unfold regularRootLinearCoefficient
    change (d:ℂ)/k*md^2*m^(2*ell)*(1+u)^2=_
    rw [show (d:ℂ)/k*md^2*m^(2*ell)*(1+u)^2=(d:ℂ)/k*m^(2*ell)*(md*(1+u))^2 by ring,hmul,div_pow]
    rw [show 2*ell+2=2*ell+2 by rfl,pow_add]
    ring
  unfold combinedCorrectionCoefficient
  rw [correction_combination_coefficient d ell (by omega) _ _ hT]
  change regularRootLinearCoefficient d ell m md*(1+m*α)^2*
      ((k^ell*((d:ℂ)-m^(2*ell+2))-1)/(1-m^(2*ell+2)))-1=_
  rw [hlinear]
  change (d:ℂ)/k*m^(2*ell+2)/(1-u)^2*((k^ell*((d:ℂ)-m^(2*ell+2))-1)/(1-m^(2*ell+2)))-1=
    correctionPolynomial ((d:ℂ)/k*((d:ℂ)*k^ell-1)) ((d:ℂ)/k*k^ell) (m^(2*ell+2)) u/
      ((1-u)^2*(1-m^(2*ell+2)))
  have halg (c D K A u:ℂ)(hminus:1-u≠0)(hA:1-A≠0):
      c*A/(1-u)^2*((K*(D-A)-1)/(1-A))-1=
        correctionPolynomial (c*(D*K-1)) (c*K) A u/((1-u)^2*(1-A)):=by
    unfold correctionPolynomial
    field_simp [hminus,hA]
    ring
  exact halg _ _ _ _ _ hminus hT

end SpectralConsequences
#print axioms SpectralConsequences.trivialPole_mul_root_displacement_bound
#print axioms SpectralConsequences.combinedCorrectionCoefficient_sub_one
