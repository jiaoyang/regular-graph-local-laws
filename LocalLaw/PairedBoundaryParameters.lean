import LocalLaw.ActualBoundaryColumn
import LocalLaw.SparseBoundaryParameters

/-! # Reduce the exact paired error to the sparse column parameter budget -/

namespace LocalLaw

def pairedBoundaryCoefficient (C w : ℝ) : ℝ := (1+C*w)^2+6*(1+C*w)^3*w

theorem pairedEndpointGoodError_monomial_bound (C w δold δ n φ : ℝ)
    (hC : 0≤C) (hw : 0≤w) (hδold : 0≤δold) (hδ : δold≤δ)
    (hn : 0≤n) (hφ : 0≤φ) :
    pairedEndpointGoodError C w δold n φ ≤
      pairedBoundaryCoefficient C w*(δ^2+n*φ*δ+φ) := by
  let M := 1+C*w
  have hM : 0≤M := by dsimp only [M]; positivity
  have hδ0 : 0≤δ := hδold.trans hδ
  have hs := pow_le_pow_left₀ hδold hδ 2
  have h₁ := mul_le_mul_of_nonneg_left hs (by positivity : 0≤4*M^3*w)
  have h₂ := mul_le_mul_of_nonneg_left hδ (by positivity : 0≤2*M^3*w*n*φ)
  have hγ : pairedEndpointGoodError C w δold n φ ≤
      M^2*φ+4*M^3*w*δ^2+2*M^3*w*(n*φ*δ) := by
    dsimp only [pairedEndpointGoodError,M] at *
    nlinarith only [h₁,h₂]
  let G := M^2+6*M^3*w
  have hG₁ : M^2≤G := by dsimp only [G]; exact le_add_of_nonneg_right (by positivity)
  have hG₂ : 4*M^3*w≤G := by dsimp only [G]; nlinarith [mul_nonneg (pow_nonneg hM 3) hw,sq_nonneg M]
  have hG₃ : 2*M^3*w≤G := by dsimp only [G]; nlinarith [mul_nonneg (pow_nonneg hM 3) hw,sq_nonneg M]
  have hx := add_le_add (add_le_add (mul_le_mul_of_nonneg_right hG₁ hφ)
    (mul_le_mul_of_nonneg_right hG₂ (sq_nonneg δ)))
    (mul_le_mul_of_nonneg_right hG₃ (by positivity : 0≤n*φ*δ))
  exact hγ.trans (hx.trans_eq (by dsimp only [G,M,pairedBoundaryCoefficient]; ring))

/-- Inflate the actual deduplicated endpoint count to a convenient label-count
budget; this also handles repeated original boundary endpoints. -/
theorem pairedEndpointGoodError_mono_count (C w δ n N φ : ℝ)
    (hC : 0≤C) (hw : 0≤w) (hδ : 0≤δ) (hn : n≤N) (hφ : 0≤φ) :
    pairedEndpointGoodError C w δ n φ≤pairedEndpointGoodError C w δ N φ := by
  have hh := mul_le_mul_of_nonneg_right hn hφ
  have hcoef : 0≤2*(1+C*w)^3*w*δ := by positivity
  have hbound := mul_le_mul_of_nonneg_left hh hcoef
  dsimp only [pairedEndpointGoodError]
  nlinarith only [hbound]

/-- The actual old endpoint error is dominated by the already derived global
new endpoint error coefficient. -/
theorem sourceEndpointOldErrorConstant_le (d : ℕ) (hd : 3≤d) (C1 : ℝ) (hC1 : 0≤C1) :
    2*C1≤sourceEndpointErrorConstant d C1 := by
  let C := endpointSurgeryModelRowCap d (2*(finiteOmega d+1))
  let w := endpointSurgeryCouplingCap d
  have hC : 0≤C := by
    dsimp only [C,endpointSurgeryModelRowCap]
    have hh := finiteExtraReferenceConstant_ge_one d hd
    positivity
  have hw : 0≤w := by dsimp only [w,endpointSurgeryCouplingCap]; positivity
  have hm : 1≤1+C*w := le_add_of_nonneg_right (mul_nonneg hC hw)
  have hs : 1≤(1+C*w)^2 := one_le_pow₀ hm
  have hh := mul_le_mul_of_nonneg_right hs hC1
  change 2*C1≤4*(1+C*w)^2*C1
  nlinarith only [hh,hC1]

/-- The literal ceiling-log count gives a fixed times log-squared budget. -/
theorem quadratic_log_exception_count (L : ℝ) (ω J Bbad : ℕ) (hL : 1≤L)
    (hcount : Bbad≤4*(Nat.ceil L)^2+3*Nat.ceil L+2*ω+J) :
    (Bbad:ℝ)≤(22+2*(ω:ℝ)+(J:ℝ))*L^2 := by
  have hL0 : 0≤L := by linarith
  have hk : (Nat.ceil L:ℝ)≤2*L := by linarith [Nat.ceil_lt_add_one hL0]
  have hk0 : 0≤(Nat.ceil L:ℝ) := Nat.cast_nonneg _
  have hksq : (Nat.ceil L:ℝ)^2≤4*L^2 := by nlinarith only [hk,hk0,hL0]
  have hreal : (Bbad:ℝ)≤4*(Nat.ceil L:ℝ)^2+3*(Nat.ceil L:ℝ)+2*(ω:ℝ)+(J:ℝ) := by exact_mod_cast hcount
  have hL2 : 1≤L^2 := one_le_pow₀ hL
  have hlin : L≤L^2 := by nlinarith only [hL]
  have hh := mul_le_mul_of_nonneg_left hL2 (show 0≤2*(ω:ℝ)+(J:ℝ) by positivity)
  nlinarith only [hreal,hksq,hk,hlin,hh]

end LocalLaw
