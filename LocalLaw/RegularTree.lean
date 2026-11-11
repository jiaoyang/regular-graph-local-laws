import LocalLaw.TreeRecursion

/-!
# The exact regular-tree model diagonal

A d-regular root is joined to d disjoint (d-1)-ary cavity trees with normalized
edge 1/sqrt(d-1). With the physical boundary root m, the concrete finite matrix
inverse at the distinguished root equals the Kesten--McKay transform. Both
branch and full-matrix nonsingularity are proved.
-/

open scoped BigOperators

namespace LocalLaw

/-- Either nonzero quadratic root gives a legitimate fixed point of the scalar
cavity map. The upper-half-plane assumptions select the physical root later. -/
theorem cavity_fixed_denominator_ne_zero {m z : ℂ}
    (hm : m ^ 2 + z * m + 1 = 0) : z + m ≠ 0 := by
  have hid : m * (z + m) = -(1 : ℂ) := by linear_combination hm
  intro hzero
  rw [hzero, mul_zero] at hid
  norm_num at hid

theorem cavityIterate_fixed_point {m z : ℂ}
    (hm : m ^ 2 + z * m + 1 = 0) (n : ℕ) : cavityIterate z m n = m := by
  have hd := cavity_fixed_denominator_ne_zero hm
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [cavityIterate, ih]
      field_simp
      linear_combination -hm

/-- Exact fixed-boundary diagonal of a genuine homogeneous finite cavity tree.
No a priori norm bound is needed when its boundary is exactly a quadratic root. -/
theorem fixed_cavityTree_inverse_root (k : ℕ) (hk : 0 < k) (z m : ℂ)
    (hm : m ^ 2 + z * m + 1 = 0) (n : ℕ) :
    IsUnit (cavityTreeMatrix k (normalizedCavityEdge k) z m n) ∧
      (cavityTreeMatrix k (normalizedCavityEdge k) z m n)⁻¹
        (cavityTreeRoot k n) (cavityTreeRoot k n) = m := by
  obtain ⟨hu, hg⟩ := cavityTree_inverse_root k (normalizedCavityEdge k) z m
    (normalizedCavityEdge_normalization k hk) n (by
      intro j _
      rw [cavityIterate_fixed_point hm]
      exact cavity_fixed_denominator_ne_zero hm)
  exact ⟨hu, by simpa only [cavityIterate_fixed_point hm] using hg⟩

theorem normalizedCavityEdge_sq (k : ℕ) (hk : 0 < k) :
    normalizedCavityEdge k ^ 2 = (k : ℂ)⁻¹ := by
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hk)
  rw [← one_div]
  apply (eq_div_iff hk0).2
  simpa only [mul_comm] using normalizedCavityEdge_normalization k hk

/-- The regular-tree reference Stieltjes transform in the paper's sign convention. -/
noncomputable def kestenMcKayTransform (d : ℕ) (m z : ℂ) : ℂ :=
  (-z - ((d : ℂ) / ((d - 1 : ℕ) : ℂ)) * m)⁻¹

/-- The root plus d copies of a depth-n forward cavity tree. Its total radius
is n+1, and its boundary weight is w. -/
noncomputable def regularTreeMatrix (d n : ℕ) (z w : ℂ) :
    Matrix (Unit ⊕ (CavityTreeIndex (d - 1) n × Fin d))
      (Unit ⊕ (CavityTreeIndex (d - 1) n × Fin d)) ℂ :=
  rootBlockMatrix (-z)
    (branchRootCoupling d (cavityTreeRoot (d - 1) n) (normalizedCavityEdge (d - 1)))
    (identicalBranches d (cavityTreeMatrix (d - 1) (normalizedCavityEdge (d - 1)) z w n))

/-- The regular-root scalar denominator has strictly negative imaginary part. -/
theorem kestenMcKay_denominator_im_neg (d : ℕ) (m z : ℂ)
    (hz : 0 < z.im) (hmim : 0 ≤ m.im) :
    (-z - ((d : ℂ) / ((d - 1 : ℕ) : ℂ)) * m).im < 0 := by
  have hcoef : (0 : ℝ) ≤ (d : ℝ) / ((d - 1 : ℕ) : ℝ) := by positivity
  have hcast : (d : ℂ) / ((d - 1 : ℕ) : ℂ) =
      Complex.ofReal ((d : ℝ) / ((d - 1 : ℕ) : ℝ)) := by
    simp only [Complex.ofReal_div, Complex.ofReal_natCast]
  rw [hcast]
  simp only [Complex.sub_im, Complex.neg_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  nlinarith [mul_nonneg hcoef hmim]

/-- The regular-root scalar reciprocal is a genuine inverse. -/
theorem kestenMcKay_denominator_ne_zero (d : ℕ) (m z : ℂ)
    (hz : 0 < z.im) (hmim : 0 ≤ m.im) :
    -z - ((d : ℂ) / ((d - 1 : ℕ) : ℂ)) * m ≠ 0 := by
  have him := kestenMcKay_denominator_im_neg d m z hz hmim
  intro hzero
  rw [hzero, Complex.zero_im] at him
  linarith

/-- The regular-tree transform lies in the upper half-plane. -/
theorem kestenMcKayTransform_im_pos (d : ℕ) (m z : ℂ)
    (hz : 0 < z.im) (hmim : 0 ≤ m.im) :
    0 < (kestenMcKayTransform d m z).im := by
  unfold kestenMcKayTransform
  rw [Complex.inv_im]
  exact div_pos (neg_pos.mpr (kestenMcKay_denominator_im_neg d m z hz hmim))
    (Complex.normSq_pos.mpr (kestenMcKay_denominator_ne_zero d m z hz hmim))

/-- Actual inverse-root identification for the concrete finite d-regular tree.
The formula is independent of the depth once the boundary is the fixed root. -/
theorem regularTree_inverse_root (d : ℕ) (hd : 3 ≤ d) (n : ℕ) (z m : ℂ)
    (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im) (hmim : 0 ≤ m.im) :
    IsUnit (regularTreeMatrix d n z m) ∧
      (regularTreeMatrix d n z m)⁻¹ (Sum.inl ()) (Sum.inl ()) =
        kestenMcKayTransform d m z := by
  have hk : 0 < d - 1 := by omega
  obtain ⟨hu, hg⟩ := fixed_cavityTree_inverse_root (d - 1) hk z m hm n
  have hschur : rootSchurValue (-z)
      (branchRootCoupling d (cavityTreeRoot (d - 1) n) (normalizedCavityEdge (d - 1)))
      (identicalBranches d (cavityTreeMatrix (d - 1) (normalizedCavityEdge (d - 1)) z m n)) =
      -z - ((d : ℂ) / ((d - 1 : ℕ) : ℂ)) * m := by
    rw [rootSchurValue, identicalBranches_self_energy d _ hu,
      normalizedCavityEdge_sq (d - 1) hk, hg]
    ring
  have hresult := rootBlock_inverse_root (-z)
    (branchRootCoupling d (cavityTreeRoot (d - 1) n) (normalizedCavityEdge (d - 1)))
    (identicalBranches d (cavityTreeMatrix (d - 1) (normalizedCavityEdge (d - 1)) z m n))
    (identicalBranches_isUnit d _ hu)
    (by rw [hschur]; exact kestenMcKay_denominator_ne_zero d m z hz hmim)
  exact ⟨hresult.1, by simpa only [hschur, kestenMcKayTransform] using hresult.2⟩

/-- The quadratic equation converts the scalar inverse denominator into the
usual algebraic Kesten--McKay denominator. -/
theorem kestenMcKay_denominator_mul_root (d : ℕ) (hd : 3 ≤ d) (m z : ℂ)
    (hm : m ^ 2 + z * m + 1 = 0) :
    (-z - ((d : ℂ) / ((d - 1 : ℕ) : ℂ)) * m) * m =
      1 - m ^ 2 / ((d - 1 : ℕ) : ℂ) := by
  have hk : 0 < d - 1 := by omega
  have hk0 : ((d - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hk)
  have hdcast : (d : ℂ) = ((d - 1 : ℕ) : ℂ) + 1 := by
    exact_mod_cast (show d = d - 1 + 1 by omega)
  have halg : ∀ K : ℂ, K ≠ 0 →
      (-z - ((K + 1) / K) * m) * m = 1 - m ^ 2 / K := by
    intro K hK
    field_simp
    linear_combination -K * hm
  simpa only [← hdcast] using halg ((d - 1 : ℕ) : ℂ) hk0

/-- Neither denominator in the equivalent transform formulas vanishes. -/
theorem kestenMcKay_algebraic_denominator_ne_zero (d : ℕ) (hd : 3 ≤ d) (m z : ℂ)
    (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im) (hmim : 0 ≤ m.im) :
    1 - m ^ 2 / ((d - 1 : ℕ) : ℂ) ≠ 0 := by
  rw [← kestenMcKay_denominator_mul_root d hd m z hm]
  exact mul_ne_zero (kestenMcKay_denominator_ne_zero d m z hz hmim) (cavity_root_ne_zero hm)

/-- The reciprocal form and the customary m/(1-m²/(d-1)) form agree, with both
inverses justified by nonvanishing rather than relying on totalized division. -/
theorem kestenMcKayTransform_eq (d : ℕ) (hd : 3 ≤ d) (m z : ℂ)
    (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im) (hmim : 0 ≤ m.im) :
    kestenMcKayTransform d m z = m / (1 - m ^ 2 / ((d - 1 : ℕ) : ℂ)) := by
  have ha := kestenMcKay_denominator_ne_zero d m z hz hmim
  have hD := kestenMcKay_algebraic_denominator_ne_zero d hd m z hm hz hmim
  apply (eq_div_iff hD).2
  unfold kestenMcKayTransform
  rw [← kestenMcKay_denominator_mul_root d hd m z hm, ← mul_assoc,
    inv_mul_cancel₀ ha, one_mul]

end LocalLaw
