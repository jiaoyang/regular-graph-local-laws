import SpectralConsequences.BoundaryProfileQuadratic

/-! The root cancellation in the boundary profile avoids an extra factor
of the boundary cardinality in the all-sample root cap. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem BoundaryMaxProfile.root_l1_square_count {I F:Type*}[Fintype F]
    (P:Matrix I I ℂ) (l:F→I) (root:I) (a:ℕ) (L U M0 W0:ℝ)
    (profile:BoundaryMaxProfile P l root a L U M0 W0) (_hM0:0≤M0):
    (∑α:F,‖P root (l α)‖)^2≤(Fintype.card F:ℝ)*M0^2:=by
  let n:ℝ:=Fintype.card F
  have hn:0≤n:=Nat.cast_nonneg _
  have hs:(∑α:F,‖P root (l α)‖)≤n*profile.M:=by
    apply (Finset.sum_le_sum (fun α _=>profile.root_bound α)).trans_eq
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,n]
  have hs2:=pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) hs 2
  have hc:=pow_le_pow_left₀
    (mul_nonneg profile.root_nonnegative (Real.sqrt_nonneg n)) profile.root_count 2
  have hid:(n*profile.M)^2=n*(profile.M*Real.sqrt n)^2:=by
    rw [mul_pow,mul_pow,Real.sq_sqrt hn]
    ring
  rw [hid] at hs2
  exact hs2.trans (mul_le_mul_of_nonneg_left hc hn)

theorem boundary_linear_array_norm {F:Type*}[Fintype F]
    (w:F→ℂ) (D:Matrix F F ℂ) (c:ℂ) (δ:ℝ) (hc:‖c‖≤1)
    (hD:∀i j,‖D i j‖≤δ):
    ‖c*(∑i:F,∑j:F,w i*D i j*w j)‖≤δ*(∑i:F,‖w i‖)^2:=by
  have hn:‖∑i:F,∑j:F,w i*D i j*w j‖≤δ*(∑i:F,‖w i‖)^2:=by
    apply ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _=>norm_sum_le _ _))).trans
    calc
      _≤∑i:F,∑j:F,‖w i‖*δ*‖w j‖:=by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul,norm_mul]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hD i j) (norm_nonneg _)) (norm_nonneg _)
      _=_:=by
        rw [pow_two]
        simp only [Finset.mul_sum,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans hn

theorem BoundaryMaxProfile.scalar_root_difference {I F:Type*}[Fintype F]
    (R P:Matrix I I ℂ) (l:F→I) (root:I) (a:ℕ) (L U M0 W0:ℝ)
    (profile:BoundaryMaxProfile P l root a L U M0 W0) (hM0:0≤M0)
    (D:Matrix F F ℂ) (c:ℂ) (δ Rem:ℝ) (hδ:0≤δ) (hc:‖c‖≤1)
    (hD:∀i j,‖D i j‖≤δ) (hsym:∀j,P (l j) root=P root (l j))
    (hidentity:R root root-P root root=
      c*(∑i,∑j,P root (l i)*D i j*P (l j) root)+
      c*(∑i,∑j,(R root (l i)-P root (l i))*D i j*P (l j) root))
    (hrem:‖c*(∑i,∑j,(R root (l i)-P root (l i))*D i j*P (l j) root)‖≤Rem):
    ‖R root root-P root root‖≤δ*(Fintype.card F:ℝ)*M0^2+Rem:=by
  have hfirst:‖c*(∑i,∑j,P root (l i)*D i j*P (l j) root)‖≤δ*(Fintype.card F:ℝ)*M0^2:=by
    simp_rw [hsym]
    have hh:=boundary_linear_array_norm (fun i=>P root (l i)) D c δ hc hD
    exact hh.trans ((mul_le_mul_of_nonneg_left
      (BoundaryMaxProfile.root_l1_square_count P l root a L U M0 W0 profile hM0) hδ).trans_eq (by ring))
  rw [hidentity]
  exact (norm_add_le _ _).trans (add_le_add hfirst hrem)

theorem source_quadratic_remainder_small (a:ℕ) (L ε K:ℝ)
    (ha:12≤a) (hL:1≤L) (hε:0≤ε) (hK:0≤K)
    (hcap:ε*L^(4*a)≤1) (hlarge:2*K≤L):
    K*L^(6*a+7)*ε^2≤1/2:=by
  have hh:=source_scaled_log_monomial_half a (2*a+7) L ε K hL hε hK hcap (by omega) hlarge
  calc
    _=(ε*L^(4*a))*(K*ε*L^(2*a+7)):=by
      have he:L^(6*a+7)=L^(4*a)*L^(2*a+7):=by rw [←pow_add];congr 1;omega
      rw [he]
      ring
    _≤K*ε*L^(2*a+7):=mul_le_of_le_one_left (by positivity) hcap
    _≤1/2:=hh

end SpectralConsequences
