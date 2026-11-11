import LocalLaw.PolynomialDensityAbsorption

/-! Every prescribed power of the actual nominal epsilon absorbs an
all-polynomial exceptional-event contribution, including fixed log factors. -/
open Filter
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem eventually_moment_exception_absorbed (a d p q k:ℕ)(β γ K:ℝ)
    (hd:3≤d)(hβ:0≤β)(hgap:(k:ℝ)*β<γ):
    ∀ᶠ N:ℕ in atTop,∀z:ℂ,0≤z.im→
      K*Real.log (N:ℝ)^p/(N:ℝ)^γ≤
        (graphPaperError a d N (logarithmicRadius β d N) z)^k/Real.log (N:ℝ)^q:=by
  filter_upwards [eventually_const_mul_log_rpow_le K ((p+q:ℕ):ℝ) (γ-(k:ℝ)*β) (by linarith),
    eventually_log_ge_nat 1,eventually_ge_atTop 1] with N hnum hlog hN
  intro z hz
  let L:=Real.log (N:ℝ)
  let X:ℝ:=(N:ℝ)^β
  have hn:0<(N:ℝ):=Nat.cast_pos.mpr (by omega)
  have hx:0<X:=Real.rpow_pos_of_pos hn β
  have hg:0<(N:ℝ)^γ:=Real.rpow_pos_of_pos hn γ
  have hL:0<L:=by dsimp only [L];linarith
  have hε:=graphPaperError_nominal_ge_inverse_power a d N β z hd hβ hN hlog hz
  have hεpow:(X⁻¹)^k≤(graphPaperError a d N (logarithmicRadius β d N) z)^k:=
    pow_le_pow_left₀ (inv_nonneg.mpr hx.le) hε k
  have he:X^k=(N:ℝ)^((k:ℝ)*β):=by
    dsimp only [X]
    rw [←Real.rpow_natCast,←Real.rpow_mul hn.le]
    congr 1
    ring
  have hpow:(N:ℝ)^(γ-(k:ℝ)*β)*X^k=(N:ℝ)^γ:=by
    rw [he,←Real.rpow_add hn]
    congr 1
    ring
  have hscaled:(K*L^p*L^q)*X^k≤(N:ℝ)^γ:=by
    have hh:=mul_le_mul_of_nonneg_right hnum (pow_nonneg hx.le k)
    rw [hpow] at hh
    simpa only [Real.rpow_natCast,pow_add,L,mul_assoc] using hh
  have hcancel:(X⁻¹)^k*X^k=1:=by rw [←mul_pow,inv_mul_cancel₀ (ne_of_gt hx),one_pow]
  have hbase:K*L^p/(N:ℝ)^γ≤(X⁻¹)^k/L^q:=by
    apply (div_le_div_iff₀ hg (pow_pos hL q)).mpr
    apply (mul_le_mul_right (pow_pos hx k)).mp
    calc
      _=(K*L^p*L^q)*X^k:=by ring
      _≤(N:ℝ)^γ:=hscaled
      _=((X⁻¹)^k*(N:ℝ)^γ)*X^k:=by rw [mul_right_comm,hcancel,one_mul]
  exact hbase.trans (div_le_div_of_nonneg_right hεpow (pow_nonneg hL.le q))

end SpectralConsequences
