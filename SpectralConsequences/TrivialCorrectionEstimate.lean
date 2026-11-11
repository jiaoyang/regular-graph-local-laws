import SpectralConsequences.TrivialPoleCancellation

/-! Quantitative global source-(7.40) cancellation. The harmless extra depth
factor is retained explicitly and can be absorbed into any N^e allowance. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw

def cancellationPolynomialBudget (d ell:ℕ):ℝ:=
  (((2*(d:ℝ)+4)*((d-1:ℕ):ℝ)^ell+6)*((2*ell+2:ℕ):ℝ)+8)

def trivialCancellationConstant (d:ℕ):ℝ:=48*(4*(d:ℝ)+32)

private theorem physical_correction_polynomial_bound (d ell:ℕ)(hd:3≤d)(z:ℂ):
    ‖correctionPolynomial
      ((d:ℂ)/((d-1:ℕ):ℂ)*((d:ℂ)*((d-1:ℕ):ℂ)^ell-1))
      ((d:ℂ)/((d-1:ℕ):ℂ)*((d-1:ℕ):ℂ)^ell)
      ((semicircleRoot z)^(2*ell+2)) (treeEdgeWeight d*semicircleRoot z)‖≤
        cancellationPolynomialBudget d ell*‖semicircleRoot z+treeEdgeWeight d‖:=by
  let k:ℂ:=((d-1:ℕ):ℂ)
  let K:=k^ell
  let Kr:=((d-1:ℕ):ℝ)^ell
  let m:=semicircleRoot z
  let α:=treeEdgeWeight d
  let a:ℂ:=(d:ℂ)/k*((d:ℂ)*K-1)
  let b:ℂ:=(d:ℂ)/k*K
  let n:=2*ell+2
  have hk:k≠0:=Nat.cast_ne_zero.mpr (by omega)
  have hK:K≠0:=pow_ne_zero ell hk
  have hkcast:k=(d:ℂ)-1:=by dsimp only [k];rw [Nat.cast_sub (by omega:1≤d),Nat.cast_one]
  have hdcast:(d:ℂ)=k+1:=by rw [hkcast];ring
  have hαsq:α^2=1/k:=by dsimp only [α];rw [treeEdgeWeight_sq d hd,←hkcast]
  have hα:‖α‖≤1:=(treeEdgeWeight_norm_le_three_quarters d hd).trans (by norm_num)
  have hm:‖m‖≤1:=semicircleRoot_norm_le_one z
  have hneg:‖-α‖≤1:=by simpa only [norm_neg] using hα
  have hA:‖m^n‖≤1:=by rw [norm_pow];exact pow_le_one₀ (norm_nonneg m) hm
  have hA0:‖(-α)^n‖≤1:=by rw [norm_pow];exact pow_le_one₀ (norm_nonneg _) hneg
  have hu:‖α*m‖≤1:=by rw [norm_mul];exact (mul_le_mul hα hm (norm_nonneg m) (by norm_num)).trans_eq (by ring)
  have hu0:‖α*(-α)‖≤1:=by rw [norm_mul];exact (mul_le_mul hα hneg (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  have hA0eq:(-α)^n=1/(k*K):=by
    change (-α)^(2*ell+2)=_
    rw [show 2*ell+2=2*(ell+1) by omega,pow_mul,neg_sq,hαsq,div_pow,one_pow,pow_succ]
    dsimp only [K]
    congr 1
    ring
  have hu0eq:α*(-α)= -1/k:=by
    calc
      α*(-α)= -α^2:=by ring
      _= -1/k:=by rw [hαsq];ring
  have hzero:correctionPolynomial a b ((-α)^n) (α*(-α))=0:=by
    dsimp only [a,b]
    rw [hA0eq,hu0eq,hdcast]
    exact correctionPolynomial_pole_zero k K hk hK
  have hnormK:‖K‖=Kr:=by dsimp only [K,k,Kr];rw [norm_pow,Complex.norm_natCast]
  have hkR:2≤((d-1:ℕ):ℝ):=by exact_mod_cast (show 2≤d-1 by omega)
  have hratio:‖(d:ℂ)/k‖≤2:=by
    dsimp only [k]
    rw [norm_div,Complex.norm_natCast,Complex.norm_natCast]
    apply (div_le_iff₀ (by linarith:0<((d-1:ℕ):ℝ))).2
    have hc:((d-1:ℕ):ℝ)=(d:ℝ)-1:=by rw [Nat.cast_sub (by omega:1≤d),Nat.cast_one]
    rw [hc]
    have hdR:(3:ℝ)≤d:=Nat.cast_le.mpr hd
    linarith
  have ha:‖a‖≤2*((d:ℝ)*Kr+1):=by
    dsimp only [a]
    rw [norm_mul]
    have hh:‖(d:ℂ)*K-1‖≤(d:ℝ)*Kr+1:=by
      exact (norm_sub_le _ _).trans_eq (by rw [norm_mul,Complex.norm_natCast,hnormK,norm_one])
    exact mul_le_mul hratio hh (norm_nonneg _) (by norm_num)
  have hb:‖b‖≤2*Kr:=by dsimp only [b];rw [norm_mul,hnormK];exact mul_le_mul_of_nonneg_right hratio (by dsimp only [Kr];positivity)
  have hcoeff:‖a‖+2*‖b‖+4≤(2*(d:ℝ)+4)*Kr+6:=by linarith
  have hdiffA:‖m^n-(-α)^n‖≤(n:ℝ)*‖m+α‖:=by
    simpa only [sub_neg_eq_add] using unit_disk_power_lipschitz m (-α) hm hneg n
  have hdiffu:‖α*m-α*(-α)‖≤‖m+α‖:=by
    rw [show α*m-α*(-α)=α*(m+α) by ring,norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hα (norm_nonneg (m+α))
  have hh:=correctionPolynomial_lipschitz a b (m^n) ((-α)^n) (α*m) (α*(-α)) hA hA0 hu hu0
  rw [hzero,sub_zero] at hh
  change ‖correctionPolynomial a b (m^n) (α*m)‖≤_
  calc
    _≤(‖a‖+2*‖b‖+4)*‖m^n-(-α)^n‖+8*‖α*m-α*(-α)‖:=hh
    _≤((2*(d:ℝ)+4)*Kr+6)*((n:ℝ)*‖m+α‖)+8*‖m+α‖:=by
      exact add_le_add (mul_le_mul hcoeff hdiffA (norm_nonneg _) (by dsimp only [Kr];positivity))
        (mul_le_mul_of_nonneg_left hdiffu (by norm_num))
    _=cancellationPolynomialBudget d ell*‖m+α‖:=by dsimp only [cancellationPolynomialBudget,n,Kr];ring

private theorem cancellationPolynomialBudget_bound (d ell:ℕ)(hd:3≤d):
    cancellationPolynomialBudget d ell≤(4*(d:ℝ)+32)*(ell+1)*((d-1:ℕ):ℝ)^ell:=by
  have hk:1≤((d-1:ℕ):ℝ)^ell:=one_le_pow₀ (by exact_mod_cast (show 1≤d-1 by omega))
  have he:1≤(ell:ℝ)+1:=by linarith [Nat.cast_nonneg (α:=ℝ) ell]
  have hprod:(ell:ℝ)+1≤((d-1:ℕ):ℝ)^ell*((ell:ℝ)+1):=by nlinarith
  unfold cancellationPolynomialBudget
  push_cast
  nlinarith

/-- Source (7.40), uniform across the genuine trivial eigenvalue. -/
theorem trivial_correction_cancellation_bound (N d ell:ℕ)(hN:1≤N)(hd:3≤d)(z:ℂ)(hz:0<z.im)
    (hT:1-(semicircleRoot z)^(2*ell+2)≠0):
    ‖trivialTraceCorrection N d ell z+
      regularRootLinearCoefficient d ell (semicircleRoot z) (kestenMcKayTransform d (semicircleRoot z) z)/
        (1-(semicircleRoot z)^(2*ell+2))*trivialCavityCorrection N d ell z-trivialPole N d z‖≤
      trivialCancellationConstant d*(ell+1)*((d-1:ℕ):ℝ)^ell/
        ((N:ℝ)*‖1-(semicircleRoot z)^(2*ell+2)‖):=by
  let m:=semicircleRoot z
  let u:=treeEdgeWeight d*m
  let T:=1-m^(2*ell+2)
  let P:=correctionPolynomial
      ((d:ℂ)/((d-1:ℕ):ℂ)*((d:ℂ)*((d-1:ℕ):ℂ)^ell-1))
      ((d:ℂ)/((d-1:ℕ):ℂ)*((d-1:ℕ):ℂ)^ell) (m^(2*ell+2)) u
  have ht:0<‖T‖:=norm_pos_iff.mpr hT
  have hu:‖u‖≤3/4:=by
    dsimp only [u];rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (semicircleRoot_norm_le_one z) (norm_nonneg _)).trans
      (by simpa only [mul_one] using treeEdgeWeight_norm_le_three_quarters d hd)
  have hlow:1/4≤‖1-u‖:=by have hh:=norm_sub_norm_le (1:ℂ) u;simp only [norm_one] at hh;linarith
  have hden:1/16*‖T‖≤‖1-u‖^2*‖T‖:=by
    exact mul_le_mul_of_nonneg_right (by nlinarith [norm_nonneg (1-u)]) (norm_nonneg T)
  have hB:0≤cancellationPolynomialBudget d ell:=by unfold cancellationPolynomialBudget;positivity
  have hnum:‖P‖*‖trivialPole N d z‖≤cancellationPolynomialBudget d ell*(3/(N:ℝ)):=by
    calc
      _≤(cancellationPolynomialBudget d ell*‖m+treeEdgeWeight d‖)*‖trivialPole N d z‖:=
        mul_le_mul_of_nonneg_right (physical_correction_polynomial_bound d ell hd z) (norm_nonneg _)
      _=cancellationPolynomialBudget d ell*‖trivialPole N d z*(m+treeEdgeWeight d)‖:=by rw [norm_mul];ring
      _≤_:=mul_le_mul_of_nonneg_left (trivialPole_mul_root_displacement_bound N d hN hd z hz) hB
  have he:trivialTraceCorrection N d ell z+
      regularRootLinearCoefficient d ell m (kestenMcKayTransform d m z)/T*trivialCavityCorrection N d ell z-trivialPole N d z=
      (combinedCorrectionCoefficient d ell m (kestenMcKayTransform d m z)-1)*trivialPole N d z:=by
    unfold trivialTraceCorrection trivialCavityCorrection combinedCorrectionCoefficient
    ring
  rw [he,combinedCorrectionCoefficient_sub_one d ell hd z hz hT]
  change ‖P/((1-u)^2*T)*trivialPole N d z‖≤_
  rw [norm_mul,norm_div,norm_mul,norm_pow]
  calc
    _=‖P‖*‖trivialPole N d z‖/(‖1-u‖^2*‖T‖):=by ring
    _≤(cancellationPolynomialBudget d ell*(3/(N:ℝ)))/(1/16*‖T‖):=
      div_le_div₀ (by positivity) hnum (by positivity) hden
    _=48*cancellationPolynomialBudget d ell/((N:ℝ)*‖T‖):=by field_simp;ring
    _≤trivialCancellationConstant d*(ell+1)*((d-1:ℕ):ℝ)^ell/((N:ℝ)*‖T‖):=by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact (mul_le_mul_of_nonneg_left (cancellationPolynomialBudget_bound d ell hd) (by norm_num)).trans_eq (by unfold trivialCancellationConstant;ring)

end SpectralConsequences
#print axioms SpectralConsequences.trivial_correction_cancellation_bound
