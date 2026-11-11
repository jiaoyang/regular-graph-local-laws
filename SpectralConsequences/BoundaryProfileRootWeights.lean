import SpectralConsequences.BoundaryProfileQuadratic

/-! The actual maximum profile bounds the deterministic root-weight mass. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem BoundaryMaxProfile.root_weight_sum_log {I F:Type*}[Fintype F]
    (P:Matrix I I ℂ)(l:F→I)(root:I)(a:ℕ)(L U M0 W0:ℝ)
    (profile:LocalLaw.BoundaryMaxProfile P l root a L U M0 W0)
    (hL:1≤L)(_hU:0≤U)(hM0:0≤M0):
    (∑i:F,‖P root (l i)‖)≤M0*(U+1)*L^(2*a) ∧
      (∑i:F,‖P root (l i)‖)^2≤M0^2*(U+1)^2*L^(4*a):=by
  let n:ℝ:=Fintype.card F
  have hsum:(∑i:F,‖P root (l i)‖)≤M0*(U+1)*L^(2*a):=by
    calc
      _≤∑_i:F,profile.M:=Finset.sum_le_sum (fun i _=>profile.root_bound i)
      _=profile.M*n:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,n];ring
      _≤M0*(n+1):=root_count_linear_bound profile.M n M0 profile.root_nonnegative (Nat.cast_nonneg _) hM0 profile.root_count
      _≤M0*((U+1)*L^(2*a)):=by
        have hh:1≤L^(2*a):=one_le_pow₀ hL
        exact mul_le_mul_of_nonneg_left (by nlinarith [profile.count]) hM0
      _=_:=by ring
  refine ⟨hsum,?_⟩
  apply (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) hsum 2).trans_eq
  rw [mul_pow,mul_pow,←pow_mul]
  congr 2
  omega

end SpectralConsequences
#print axioms SpectralConsequences.BoundaryMaxProfile.root_weight_sum_log
