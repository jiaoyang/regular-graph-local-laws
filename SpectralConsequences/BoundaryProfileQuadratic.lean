import SpectralConsequences.BoundaryRowQuadratic
import LocalLaw.SourceSurgeryParameters

/-! # Explicit logarithmic size of the quadratic boundary remainder

The generic profile gives the contraction and a fixed logarithmic power.
The result stays quadratic in epsilon and does not weaken it to a linear
local-law tolerance before fluctuation averaging.
-/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw

def boundaryQuadraticConstant (U M0 W0 D:ℝ) : ℝ := 2*M0*(U+1)*U^2*W0*D^2

theorem model_column_mass_log_bound (a:ℕ) (n S W L U W0:ℝ)
    (_hn:0≤n) (_hS:0≤S) (hW:0≤W) (hL:1≤L) (hU:0≤U) (hW0:0≤W0)
    (hcount:n≤U*L^(2*a)) (hSsq:S^2≤n*W) (hWlog:W≤W0*L) :
    S≤(U+W0+1)*L^(a+1) := by
  have hL0:0≤L:=by linarith
  have hprod:=mul_le_mul hcount hWlog hW (by positivity)
  have hs:S^2≤U*W0*L^(2*a+1):=by
    apply hSsq.trans
    have he:(U*L^(2*a))*(W0*L)=U*W0*L^(2*a+1):=by rw [pow_succ];ring
    exact hprod.trans_eq he
  have hconst:U*W0≤(U+W0+1)^2:=by nlinarith [sq_nonneg (U-W0)]
  have hpow:L^(2*a+1)≤L^(2*a+2):=pow_le_pow_right₀ hL (by omega)
  have hb:=mul_le_mul hconst hpow (pow_nonneg hL0 _) (sq_nonneg _)
  have hex:((U+W0+1)*L^(a+1))^2=(U+W0+1)^2*L^(2*a+2):=by
    rw [mul_pow,←pow_mul]
    congr 2
    omega
  have hroot:0≤(U+W0+1)*L^(a+1):=by positivity
  rw [←hex] at hb
  nlinarith

theorem root_count_linear_bound (M n M0:ℝ) (_hM:0≤M) (hn:0≤n) (hM0:0≤M0)
    (hroot:M*Real.sqrt n≤M0) : M*n≤M0*(n+1) := by
  have hs:Real.sqrt n≤n+1:=Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith [sq_nonneg n]⟩
  calc
    M*n=(M*Real.sqrt n)*Real.sqrt n:=by rw [mul_assoc,Real.mul_self_sqrt hn]
    _≤M0*Real.sqrt n:=mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg n)
    _≤M0*(n+1):=mul_le_mul_of_nonneg_left hs hM0

/-- The profile supplies both contraction and the quadratic logarithmic
remainder budget, including the empty-boundary case. -/
theorem BoundaryMaxProfile.quadratic_log_remainder {I F:Type*} [Fintype F]
    (R P:Matrix I I ℂ) (l:F→I) (root:I) (a:ℕ) (L U M0 W0 ε D0:ℝ)
    (profile:LocalLaw.BoundaryMaxProfile P l root a L U M0 W0)
    (D:Matrix F F ℂ) (c:ℂ)
    (ha:12≤a) (hL:1≤L) (hU:0≤U) (hM0:0≤M0) (hW0:0≤W0) (hε:0≤ε) (hD0:0≤D0)
    (hcap:ε*L^(4*a)≤1) (hlarge:2*(U*(U+W0+1)*D0)≤L) (hc:‖c‖≤1)
    (hD:∀α β,‖D α β‖≤D0*L^3*ε)
    (hidentity:∀j,R root j-P root j=
      c*(∑α,∑β,P root (l α)*D α β*P (l β) j)+
      c*(∑α,∑β,(R root (l α)-P root (l α))*D α β*P (l β) j)) :
    ∀j,‖c*(∑α,∑β,(R root (l α)-P root (l α))*D α β*P (l β) j)‖≤
      boundaryQuadraticConstant U M0 W0 D0*L^(6*a+7)*ε^2 := by
  let n:ℝ:=Fintype.card F
  let δ:=D0*L^3*ε
  have hn:0≤n:=Nat.cast_nonneg _
  have hM:0≤profile.M:=profile.root_nonnegative
  have hW:0≤profile.W:=profile.square_nonnegative
  have hL0:0≤L:=by linarith
  have hδ:0≤δ:=by dsimp only [δ];positivity
  have hS:=model_column_mass_log_bound a n profile.S profile.W L U W0 hn
    profile.column_nonnegative profile.square_nonnegative hL hU hW0 profile.count profile.column_square profile.row_log
  have hsmall:n*δ*profile.S≤1/2:=by
    have hnum:=source_scaled_log_monomial_half a (3*a+4) L ε (U*(U+W0+1)*D0)
      hL hε (by positivity) hcap (by omega) hlarge
    calc
      _≤(U*L^(2*a))*δ*((U+W0+1)*L^(a+1)):=
        mul_le_mul (mul_le_mul_of_nonneg_right profile.count hδ) hS profile.column_nonnegative (by positivity)
      _=(U*(U+W0+1)*D0)*ε*L^(3*a+4):=by
        have he:L^(3*a+4)=L^(2*a)*L^3*L^(a+1):=by rw [←pow_add,←pow_add];congr 1;omega
        rw [he]
        dsimp only [δ]
        ring
      _≤1/2:=hnum
  have hraw:=BoundaryMaxProfile.entry_quadratic_remainder R P l root a L U M0 W0 profile
    D c δ hδ hc hD hidentity hsmall
  have hMn:=root_count_linear_bound profile.M n M0 profile.root_nonnegative hn hM0 profile.root_count
  have hnp:n+1≤(U+1)*L^(2*a):=by
    have hh:1≤L^(2*a):=one_le_pow₀ hL
    nlinarith [profile.count]
  intro j
  apply (hraw j).trans
  calc
    2*profile.M*n^2*δ^2*profile.S^2≤2*profile.M*n^2*δ^2*(n*profile.W):=
      mul_le_mul_of_nonneg_left profile.column_square (by positivity)
    _=2*(profile.M*n)*n^2*δ^2*profile.W:=by ring
    _≤2*(M0*((U+1)*L^(2*a)))*(U*L^(2*a))^2*δ^2*(W0*L):=by
      have hMN:=hMn.trans (mul_le_mul_of_nonneg_left hnp hM0)
      have hn2:n^2≤(U*L^(2*a))^2:=pow_le_pow_left₀ hn profile.count 2
      have hm:=mul_le_mul (mul_le_mul_of_nonneg_left hMN (by norm_num : (0:ℝ)≤2))
        hn2 (sq_nonneg n) (by positivity)
      have hmδ:=mul_le_mul_of_nonneg_right hm (sq_nonneg δ)
      exact mul_le_mul hmδ profile.row_log hW (by positivity)
    _=boundaryQuadraticConstant U M0 W0 D0*L^(6*a+7)*ε^2:=by
      have he:L^(6*a+7)=(L^(2*a))^3*(L^3)^2*L:=by
        rw [←pow_mul,←pow_mul,←pow_add,←pow_succ]
        congr 1
        omega
      rw [he]
      dsimp only [δ,boundaryQuadraticConstant]
      ring

end SpectralConsequences
