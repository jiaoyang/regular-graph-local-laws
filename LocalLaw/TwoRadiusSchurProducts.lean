import LocalLaw.AsymmetricSchurProducts

/-! # Product cancellation with two independently captured radii -/

namespace LocalLaw

theorem radial_tail_mul_kernel (ρ C : ℝ) (hρ : 0≤ρ) (hρone : ρ≤1) (hC : 0≤C)
    (n d N : ℕ) (hle : N≤n+d) : ρ^n*(C*ρ^d)≤C*ρ^N := by
  calc
    _=C*ρ^(n+d) := by rw [pow_add];ring
    _≤_ := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ hρone hle) hC

theorem two_radius_product_difference_bound (a b a' b' : ℂ) (ρ u v C : ℝ)
    (hρ : 0≤ρ) (hρone : ρ≤1) (hv : 0≤v) (hC : 0≤C)
    (ei ej di dj N : ℕ) (hNi : N≤ei+dj) (hNj : N≤ej+di)
    (ha : ‖a-a'‖≤u+v*ρ^ei) (hb : ‖b-b'‖≤u+v*ρ^ej)
    (hadecay : ‖a'‖≤C*ρ^di) (hbdecay : ‖b‖≤C*ρ^dj) :
    ‖a*b-a'*b'‖≤u*(‖b‖+‖a'‖)+2*v*C*ρ^N := by
  have he : a*b-a'*b'=(a-a')*b+a'*(b-b') := by ring
  have hfirst : ρ^ei*‖b‖≤C*ρ^N :=
    (mul_le_mul_of_nonneg_left hbdecay (pow_nonneg hρ _)).trans
      (radial_tail_mul_kernel ρ C hρ hρone hC ei dj N hNi)
  have hsecond : ‖a'‖*ρ^ej≤C*ρ^N := by
    calc
      _≤(C*ρ^di)*ρ^ej := mul_le_mul_of_nonneg_right hadecay (pow_nonneg hρ _)
      _=ρ^ej*(C*ρ^di) := by ring
      _≤_ := radial_tail_mul_kernel ρ C hρ hρone hC ej di N hNj
  calc
    _≤‖a-a'‖*‖b‖+‖a'‖*‖b-b'‖ := by rw [he]; simpa only [norm_mul] using norm_add_le ((a-a')*b) (a'*(b-b'))
    _≤(u+v*ρ^ei)*‖b‖+‖a'‖*(u+v*ρ^ej) := add_le_add
      (mul_le_mul_of_nonneg_right ha (norm_nonneg _)) (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
    _=u*(‖b‖+‖a'‖)+v*(ρ^ei*‖b‖+‖a'‖*ρ^ej) := by ring
    _≤u*(‖b‖+‖a'‖)+v*(C*ρ^N+C*ρ^N) := add_le_add_left
      (mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hv) _
    _=_ := by ring

theorem omitted_two_radius_product_bound (a b : ℂ) (ρ C : ℝ)
    (hρ : 0≤ρ) (hρone : ρ≤1) (hC : 0≤C)
    (di dj N : ℕ) (hle : N≤di+dj) (ha : ‖a‖≤C*ρ^di) (hb : ‖b‖≤C*ρ^dj) :
    ‖a*b‖≤C^2*ρ^N := by
  calc
    _≤(C*ρ^di)*(C*ρ^dj) := by rw [norm_mul];exact mul_le_mul ha hb (norm_nonneg _) (mul_nonneg hC (pow_nonneg hρ _))
    _=C^2*ρ^(di+dj) := by rw [pow_add];ring
    _≤_ := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ hρone hle) (sq_nonneg _)

end LocalLaw
