import Mathlib

/-! # Explicit contraction from the source inverse-log error budget -/

namespace LocalLaw

theorem polynomial_leaf_contraction (a : ℕ)(ha : 1≤a)(L ε n K P D : ℝ)
    (hL : 1≤L)(hε : 0≤ε)(_hn : 0≤n)(_hK : 0≤K)(hP : 0≤P)(hD : 0≤D)
    (hcount : n≤K*L^(2*a))(hcap : ε*L^(4*a)≤1)
    (hlarge : 2*K*P*D≤L) : n*P*(D*L*ε)≤1/2 := by
  have hLp : 0<L := by linarith
  calc
    _ ≤ (K*L^(2*a))*P*(D*L*ε) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcount hP)
        (mul_nonneg (mul_nonneg hD hLp.le) hε)
    _ = K*P*D*L^(2*a+1)*ε := by rw [pow_add,pow_one];ring
    _ ≤ (L/2)*L^(2*a+1)*ε := by
      apply mul_le_mul_of_nonneg_right _ hε
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hLp.le _)
      linarith only [hlarge]
    _ = (1/2)*(L^(2*a+2)*ε) := by
      rw [show 2*a+2=(2*a+1)+1 by omega,pow_add,pow_one]
      ring
    _ ≤ (1/2)*(L^(4*a)*ε) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL (by omega : 2*a+2≤4*a)) hε) (by norm_num)
    _ ≤ 1/2 := by nlinarith only [hcap]

end LocalLaw
