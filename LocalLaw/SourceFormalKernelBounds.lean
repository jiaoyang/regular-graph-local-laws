import LocalLaw.SourceObservationParameters
import LocalLaw.IndependentRadiusEvents
import LocalLaw.PartialSamplePhysical

/-! # Actual q-boundary normalization and logarithmic power bounds

The formal tree diagonal is q/(1-q^2/(d-1)). Its scalar vacuum identity is
exact for arbitrary nonzero q; the small quadratic residual is not set to
zero. The source weak prior supplies nonvanishing, a uniform diagonal bound
and norm(q)^R<=2 at every fixed logarithmic radius cap.
-/

open Filter
noncomputable section
namespace LocalLaw

theorem one_add_pow_times_one_sub_le_one (x : ℝ) (hx : 0≤x) (n : ℕ) :
    (1+x)^n*(1-(n:ℝ)*x)≤1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : (1+x)*(1-((n+1:ℕ):ℝ)*x)≤1-(n:ℝ)*x := by
      push_cast
      nlinarith [sq_nonneg x,Nat.cast_nonneg (α:=ℝ) n]
    calc
      _=(1+x)^n*((1+x)*(1-((n+1:ℕ):ℝ)*x)) := by rw [pow_succ]; ring
      _≤(1+x)^n*(1-(n:ℝ)*x) :=
        mul_le_mul_of_nonneg_left hs (pow_nonneg (by linarith) n)
      _≤1 := ih

theorem one_add_pow_le_two_of_mul_le_half (x : ℝ) (hx : 0≤x) (n : ℕ)
    (hsmall : (n:ℝ)*x≤1/2) : (1+x)^n≤2 := by
  have h:=one_add_pow_times_one_sub_le_one x hx n
  have hp:0≤(1+x)^n := pow_nonneg (by linarith) n
  nlinarith only [h,hsmall,hp]

theorem rationalTreeReference_bounds_near_unit (k : ℕ) (hk : 2≤k) (q : ℂ)
    (hq : ‖q‖≤9/8) :
    1-q^2/(k:ℂ)≠0 ∧ ‖rationalTreeReference k q‖≤4 := by
  have hkR : (2:ℝ)≤k := Nat.cast_le.mpr hk
  have hkpos : (0:ℝ)<k := by linarith
  have hcor : ‖q^2/(k:ℂ)‖≤2/3 := by
    rw [norm_div,norm_pow,Complex.norm_natCast]
    apply (div_le_iff₀ hkpos).mpr
    have hs:=pow_le_pow_left₀ (norm_nonneg q) hq 2
    nlinarith
  have hden : 1/3≤‖1-q^2/(k:ℂ)‖ := by
    have h:=norm_sub_norm_le (1:ℂ) (q^2/(k:ℂ))
    simp only [norm_one] at h
    linarith
  have hpos : 0<‖1-q^2/(k:ℂ)‖ := by linarith
  refine ⟨norm_pos_iff.mp hpos,?_⟩
  unfold rationalTreeReference
  rw [norm_div]
  apply (div_le_iff₀ hpos).mpr
  linarith

/-- Exact vacuum normalization for the formal q kernel. The quadratic
equation is deliberately absent from the hypotheses. -/
theorem rationalTreeReference_vacuum_relation (d : ℕ) (hd : 3≤d) (q : ℂ) (hq : q≠0) :
    (rationalTreeReference (d-1) q)⁻¹=q⁻¹-q*(treeEdgeWeight d)^2 := by
  have hkcast : ((d-1:ℕ):ℂ)=(d:ℂ)-1 := by
    exact_mod_cast (Nat.cast_sub (R:=ℝ) (by omega : 1≤d))
  have hk0 : (d:ℂ)-1≠0 := by
    rw [←hkcast]
    exact Nat.cast_ne_zero.mpr (by omega)
  unfold rationalTreeReference
  rw [inv_div,treeEdgeWeight_sq d hd,hkcast]
  field_simp [hq,hk0]
  ring

/-- Uniform scalar facts for every q obeying the source weak prior. -/
theorem eventually_source_formal_kernel_bounds (a b d : ℕ) (c β B C1 A : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) (hA : 0≤A) :
    ∀ᶠ N : ℕ in atTop,∀ z q : ℂ,0<z.im → ‖z‖≤B →
      Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) →
      q≠0 ∧ rationalTreeReference (d-1) q≠0 ∧
      ‖rationalTreeReference (d-1) q‖≤4 ∧
      (rationalTreeReference (d-1) q)⁻¹=q⁻¹-q*(treeEdgeWeight d)^2 ∧
      (∀ R : ℕ,(R:ℝ)≤A*Real.log (N:ℝ) → ‖q‖^R≤2) := by
  filter_upwards [eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_log_ge_nat 8,eventually_log_ge_nat (2*A),
    eventually_log_ge_nat (2*(|B|+1))] with N hnum hL8 hLA hLB
  intro z q hz hzB hfloor hprior
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let δ:=‖q-semicircleRoot z‖
  have num:=hnum z hz hfloor
  have hL : 1≤L := num.log_one
  have hLp : 0<L := by linarith
  have hδ : 0≤δ := norm_nonneg _
  have hprior' := hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative hC1)
  have hscaled := weak_prior_scaled_norm z q hz (C1^2*ε) L
    (mul_nonneg (sq_nonneg C1) num.error_nonnegative) num.error_scaled hprior'
  have hδ8 : δ≤1/8 := by
    have hh:=mul_le_mul_of_nonneg_left (show (8:ℝ)≤L^2 by nlinarith) hδ
    nlinarith only [hh,hscaled]
  have hδB : δ*(B+1)≤1/2 := by
    have hBL : 2*(B+1)≤L := (by linarith [le_abs_self B] : 2*(B+1)≤2*(|B|+1)).trans hLB
    have hh:=mul_le_mul_of_nonneg_left (show 2*(B+1)≤L^2 by nlinarith only [hBL,hL]) hδ
    nlinarith only [hh,hscaled]
  have hq0 : q≠0 := by
    intro hzero
    have hlo:=cavity_root_norm_lower_bound (semicircleRoot_equation z) (semicircleRoot_norm_le_one z) hzB
    have hB0:0≤B := (norm_nonneg z).trans hzB
    have hprod : 1≤‖semicircleRoot z‖*(B+1) := (div_le_iff₀ (by linarith : 0<B+1)).mp hlo
    have hδeq : δ=‖semicircleRoot z‖ := by simp only [δ,hzero,zero_sub,norm_neg]
    rw [hδeq] at hδB
    linarith
  have hnormq : ‖q‖≤1+δ := by
    have h:=norm_add_le (q-semicircleRoot z) (semicircleRoot z)
    rw [sub_add_cancel] at h
    linarith [semicircleRoot_norm_le_one z]
  have hqsmall : ‖q‖≤9/8 := by linarith
  have href:=rationalTreeReference_bounds_near_unit (d-1) (by omega) q hqsmall
  refine ⟨hq0,div_ne_zero hq0 href.1,href.2,rationalTreeReference_vacuum_relation d hd q hq0,?_⟩
  intro R hR
  have hbase:=scale_weight_small δ L A hδ hLp hA hscaled hLA
  have hRsmall : (R:ℝ)*δ≤1/2 :=
    (mul_le_mul_of_nonneg_right hR hδ).trans (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hbase)
  exact (pow_le_pow_left₀ (norm_nonneg q) hnormq R).trans
    (one_add_pow_le_two_of_mul_le_half δ hδ R hRsmall)

namespace RegularGraph

/-- In particular all scalar kernel facts hold for the actual old Q on
the enlarged source event, independently of its other geometric fields. -/
theorem eventually_source_Q_formal_kernel_bounds (a b d : ℕ) (c β B C1 A : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) (hA : 0≤A) :
    ∀ᶠ N : ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z:ℂ)(rModel R ell ω Cq badCount:ℕ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      g.SourceOmegaPlusWithRadii a rModel (logarithmicRadius β d N) R ell ω Cq badCount C1 o z →
      g.Q z≠0 ∧ rationalTreeReference (d-1) (g.Q z)≠0 ∧
      ‖rationalTreeReference (d-1) (g.Q z)‖≤4 ∧
      (rationalTreeReference (d-1) (g.Q z))⁻¹=(g.Q z)⁻¹-g.Q z*(treeEdgeWeight d)^2 ∧
      (∀ n : ℕ,(n:ℝ)≤A*Real.log (N:ℝ) → ‖g.Q z‖^n≤2) := by
  filter_upwards [eventually_source_formal_kernel_bounds a b d c β B C1 A ha hb hd hc hβ hβc hC1 hA]
    with N hN
  intro g o z rModel R ell ω Cq badCount hz hzB hfloor hplus
  exact hN z (g.Q z) hz hzB hfloor hplus.cavity

end RegularGraph
end LocalLaw
