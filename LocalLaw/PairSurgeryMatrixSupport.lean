import LocalLaw.PairedEndpointSurgery

/-! # Comparison-matrix support from a detached row and the literal update -/

open scoped BigOperators
namespace LocalLaw
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem pair_comparison_matrix_support (Q W : Matrix I I ℂ) (a b c j : I)
    (hQrow : ∀ k, k ≠ c → Q c k = 0)
    (hWtip : ∀ k, k ≠ b → W c k = 0)
    (hWpair : ∀ l ∈ ({b,c} : Finset I), ∀ k, k ∉ ({a,b,c} : Finset I) → W l k = 0)
    (hj : j ∉ ({b,c} : Finset I))
    (hQcross : ∀ k ∈ ({a,b,c} : Finset I), Q k j = 0) :
    (∀ k, k ∉ ({b,c} : Finset I) → (1-Q*W) c k = 0) ∧
      (∀ l ∈ ({b,c} : Finset I), (1-W*Q) l j = 0) := by
  constructor
  · intro k hk
    have hkc : c ≠ k := by intro h; exact hk (by simp [h])
    have hkb : k ≠ b := fun h => hk (by simp [h])
    have hsum : (Q*W) c k = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : l=c
      · subst l; rw [hWtip k hkb,mul_zero]
      · rw [hQrow l hl,zero_mul]
    simp only [Matrix.sub_apply,Matrix.one_apply_ne hkc,hsum,sub_self]
  · intro l hl
    have hlj : l ≠ j := fun h => hj (h ▸ hl)
    have hsum : (W*Q) l j = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hk : k ∈ ({a,b,c} : Finset I)
      · rw [hQcross k hk,mul_zero]
      · rw [hWpair l hl k hk,zero_mul]
    simp only [Matrix.sub_apply,Matrix.one_apply_ne hlj,hsum,sub_self]

end LocalLaw
