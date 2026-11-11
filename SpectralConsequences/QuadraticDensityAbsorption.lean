import LocalLaw.PolynomialDensityAbsorption

/-! Every fixed polynomial-log sampling loss fits the genuine epsilon²
floor, provided its polynomial exponent exceeds twice the model exponent. -/
open Filter
namespace SpectralConsequences
open LocalLaw

theorem eventually_quadratic_density_absorbed (a d p q:ℕ)(β γ K:ℝ)
    (hd:3≤d)(hβ:0≤β)(hgap:2*β<γ):
    ∀ᶠ N:ℕ in atTop,∀z:ℂ,0≤z.im→
      K*Real.log (N:ℝ)^p/(N:ℝ)^γ≤
        (graphPaperError a d N (logarithmicRadius β d N) z)^2/Real.log (N:ℝ)^q:=by
  filter_upwards [eventually_const_mul_log_rpow_le K ((p+q:ℕ):ℝ) (γ-2*β) (by linarith),
    eventually_log_ge_nat 1,eventually_ge_atTop 1] with N hnum hlog hN
  intro z hz
  let L:=Real.log (N:ℝ)
  let X:ℝ:=(N:ℝ)^β
  have hn:0<(N:ℝ):=Nat.cast_pos.mpr (by omega)
  have hx:0<X:=Real.rpow_pos_of_pos hn β
  have hg:0<(N:ℝ)^γ:=Real.rpow_pos_of_pos hn γ
  have hL:0<L:=by dsimp only [L];linarith
  have hε:=graphPaperError_nominal_ge_inverse_power a d N β z hd hβ hN hlog hz
  have hε0:0≤graphPaperError a d N (logarithmicRadius β d N) z:=graphPaperError_nonnegative _ _ _ _ _ hN hz
  have hεsq:(X⁻¹)^2≤(graphPaperError a d N (logarithmicRadius β d N) z)^2:=
    pow_le_pow_left₀ (inv_nonneg.mpr hx.le) hε 2
  have hpow:(N:ℝ)^(γ-2*β)*X^2=(N:ℝ)^γ:=by
    have he:X^2=(N:ℝ)^(2*β):=by
      dsimp only [X]
      rw [show 2*β=β*(2:ℝ) by ring,Real.rpow_mul hn.le]
      norm_num
    rw [he,←Real.rpow_add hn]
    congr 1
    ring
  have hscaled:(K*L^p*L^q)*X^2≤(N:ℝ)^γ:=by
    have hh:=mul_le_mul_of_nonneg_right hnum (sq_nonneg X)
    rw [hpow] at hh
    simpa only [Real.rpow_natCast,pow_add,L,mul_assoc] using hh
  have hbase:K*L^p/(N:ℝ)^γ≤(X⁻¹)^2/L^q:=by
    apply (div_le_div_iff₀ hg (pow_pos hL q)).mpr
    apply (mul_le_mul_right (pow_pos hx 2)).mp
    calc
      _=(K*L^p*L^q)*X^2:=by ring
      _≤(N:ℝ)^γ:=hscaled
      _=((X⁻¹)^2*(N:ℝ)^γ)*X^2:=by field_simp
  exact hbase.trans (div_le_div_of_nonneg_right hεsq (pow_nonneg hL.le q))

/-- The protected-patch gap and the original work beta-margin imply the
strict exponent inequality required for all fixed logarithmic costs. -/
theorem protected_gap_exceeds_twice_beta (cAux β:ℝ)(hc:cAux≤1/4)(hβ:β≤(cAux/4)/32):
    2*β<(9/32:ℝ):=by linarith

theorem eventually_protected_and_density_quadratic (a d p q:ℕ)(cAux β K:ℝ)
    (hd:3≤d)(hβ:0≤β)(hc:cAux≤1/4)(hβc:β≤(cAux/4)/32):
    ∀ᶠ N:ℕ in atTop,∀z:ℂ,0≤z.im→
      K*Real.log (N:ℝ)^p/(N:ℝ)^(9/32:ℝ)≤
        (graphPaperError a d N (logarithmicRadius β d N) z)^2/Real.log (N:ℝ)^q ∧
      K*Real.log (N:ℝ)^p/(N:ℝ)≤
        (graphPaperError a d N (logarithmicRadius β d N) z)^2/Real.log (N:ℝ)^q:=by
  filter_upwards [eventually_quadratic_density_absorbed a d p q β (9/32) K hd hβ
      (protected_gap_exceeds_twice_beta cAux β hc hβc),
    eventually_quadratic_density_absorbed a d p q β 1 K hd hβ (by linarith)] with N hbad hdensity
  intro z hz
  exact ⟨hbad z hz,by simpa only [Real.rpow_one] using hdensity z hz⟩

end SpectralConsequences
#print axioms SpectralConsequences.eventually_protected_and_density_quadratic
