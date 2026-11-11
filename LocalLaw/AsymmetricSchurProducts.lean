import LocalLaw.DiagonalSchurComparison

/-! # Cancellation of asymmetric localization tails in Schur products

The tail lost by placing one endpoint near the boundary is recovered by
decay of the opposite target factor. The ordinary error retains the true
target L1 weights; no squared leaf count enters this comparison.
-/

open scoped BigOperators
namespace LocalLaw

theorem asymmetric_tail_product (ρ:ℝ) (hρ:0≤ρ) (hρone:ρ≤1) (N m d:ℕ)
    (hm:m≤N) (hmd:m≤d) : ρ^(N-m)*ρ^d≤ρ^N := by
  rw [←pow_add]
  exact pow_le_pow_of_le_one hρ hρone (by omega)

theorem asymmetric_product_difference_bound (a b a' b':ℂ) (ρ u v C:ℝ)
    (hρ:0≤ρ) (hρone:ρ≤1) (_hu:0≤u) (hv:0≤v) (hC:0≤C)
    (N m di dj:ℕ) (hm:m≤N) (hmi:m≤di) (hmj:m≤dj)
    (hea:‖a-a'‖≤u+v*ρ^(N-m)) (heb:‖b-b'‖≤u+v*ρ^(N-m))
    (hadecay:‖a'‖≤C*ρ^di) (hbdecay:‖b‖≤C*ρ^dj) :
    ‖a*b-a'*b'‖≤u*(‖b‖+‖a'‖)+2*v*C*ρ^N := by
  have ht:0≤ρ^(N-m):=pow_nonneg hρ _
  have hleft:ρ^(N-m)*‖b‖≤C*ρ^N:=by
    calc
      _≤ρ^(N-m)*(C*ρ^dj):=mul_le_mul_of_nonneg_left hbdecay ht
      _=C*(ρ^(N-m)*ρ^dj):=by ring
      _≤C*ρ^N:=mul_le_mul_of_nonneg_left (asymmetric_tail_product ρ hρ hρone N m dj hm hmj) hC
  have hright:‖a'‖*ρ^(N-m)≤C*ρ^N:=by
    calc
      _≤(C*ρ^di)*ρ^(N-m):=mul_le_mul_of_nonneg_right hadecay ht
      _=C*(ρ^(N-m)*ρ^di):=by ring
      _≤C*ρ^N:=mul_le_mul_of_nonneg_left (asymmetric_tail_product ρ hρ hρone N m di hm hmi) hC
  have hid:a*b-a'*b'=(a-a')*b+a'*(b-b'):=by ring
  rw [hid]
  calc
    _≤‖a-a'‖*‖b‖+‖a'‖*‖b-b'‖:=by simpa only [norm_mul] using norm_add_le ((a-a')*b) (a'*(b-b'))
    _≤(u+v*ρ^(N-m))*‖b‖+‖a'‖*(u+v*ρ^(N-m)):=
      add_le_add (mul_le_mul_of_nonneg_right hea (norm_nonneg _))
        (mul_le_mul_of_nonneg_left heb (norm_nonneg _))
    _=u*(‖b‖+‖a'‖)+v*(ρ^(N-m)*‖b‖+‖a'‖*ρ^(N-m)):=by ring
    _≤u*(‖b‖+‖a'‖)+v*(C*ρ^N+C*ρ^N):=
      add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add hleft hright) hv) _
    _=_:=by ring

theorem asymmetric_schur_products_bound {I:Type*} [Fintype I]
    (a b a' b':I→ℂ) (ρ u v C B A':ℝ)
    (hρ:0≤ρ) (hρone:ρ≤1) (hu:0≤u) (hv:0≤v) (hC:0≤C)
    (N:ℕ) (m di dj:I→ℕ)
    (hm:∀i,m i≤N) (hmi:∀i,m i≤di i) (hmj:∀i,m i≤dj i)
    (hea:∀i,‖a i-a' i‖≤u+v*ρ^(N-m i)) (heb:∀i,‖b i-b' i‖≤u+v*ρ^(N-m i))
    (hadecay:∀i,‖a' i‖≤C*ρ^(di i)) (hbdecay:∀i,‖b i‖≤C*ρ^(dj i))
    (hB:(∑i,‖b i‖)≤B) (hA':(∑i,‖a' i‖)≤A') :
    (∑i,‖a i*b i-a' i*b' i‖)≤u*(B+A')+2*v*C*(Fintype.card I:ℝ)*ρ^N := by
  have hp (i:I):‖a i*b i-a' i*b' i‖≤u*(‖b i‖+‖a' i‖)+2*v*C*ρ^N:=
    asymmetric_product_difference_bound (a i) (b i) (a' i) (b' i) ρ u v C hρ hρone hu hv hC
      N (m i) (di i) (dj i) (hm i) (hmi i) (hmj i) (hea i) (heb i) (hadecay i) (hbdecay i)
  calc
    _≤∑i,(u*(‖b i‖+‖a' i‖)+2*v*C*ρ^N):=Finset.sum_le_sum (fun i _=>hp i)
    _=u*((∑i,‖b i‖)+(∑i,‖a' i‖))+(Fintype.card I:ℝ)*(2*v*C*ρ^N):=by
      rw [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_add_distrib]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _≤u*(B+A')+(Fintype.card I:ℝ)*(2*v*C*ρ^N):=
      add_le_add_right (mul_le_mul_of_nonneg_left (add_le_add hB hA') hu) _
    _=_:=by ring

theorem omitted_leaf_product_bound (a b:ℂ) (ρ C:ℝ) (hρ:0≤ρ) (hρone:ρ≤1) (hC:0≤C)
    (r di dj:ℕ) (hi:r≤di) (hj:r≤dj) (ha:‖a‖≤C*ρ^di) (hb:‖b‖≤C*ρ^dj) :
    ‖a*b‖≤C^2*ρ^(2*r) := by
  rw [norm_mul]
  calc
    _≤(C*ρ^di)*(C*ρ^dj):=mul_le_mul ha hb (norm_nonneg _) (mul_nonneg hC (pow_nonneg hρ _))
    _=C^2*ρ^(di+dj):=by rw [pow_add];ring
    _≤C^2*ρ^(2*r):=mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hρ hρone (by omega)) (sq_nonneg C)

end LocalLaw
