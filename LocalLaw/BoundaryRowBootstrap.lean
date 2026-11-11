import LocalLaw.CutIncidence

/-!
# Finite contraction of the actual boundary-row error

The boundary error sum is derived from an exact Schur row identity. It is
not an input inequality. Column sums of the genuine deleted-kernel error
and local model then control the nonlinear remainder without an assumed
maximum-error bootstrap conclusion.
-/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance boundaryRowBootstrapDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Sums
variable {I F : Type*} [Fintype F]

/-- A rectangular boundary sandwich is bounded by a root entry cap, an
actual deleted-error column sum and a model boundary-column sum. -/
theorem boundary_double_sum_bound (A : F → ℂ) (D : Matrix F F ℂ) (B : F → ℂ)
    (M e S : ℝ) (hM : 0 ≤ M) (he : 0 ≤ e)
    (hA : ∀ a, ‖A a‖ ≤ M) (hD : ∀ b, (∑ a, ‖D a b‖) ≤ e)
    (hB : (∑ b, ‖B b‖) ≤ S) :
    ‖∑ a, ∑ b, A a * D a b * B b‖ ≤ M * e * S := by
  calc
    _ ≤ ∑ a, ∑ b, ‖A a‖ * ‖D a b‖ * ‖B b‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a _
      simpa only [norm_mul] using norm_sum_le Finset.univ (fun b => A a * D a b * B b)
    _ = ∑ b, ∑ a, ‖A a‖ * ‖D a b‖ * ‖B b‖ := Finset.sum_comm
    _ ≤ ∑ b, (M * e) * ‖B b‖ := by
      apply Finset.sum_le_sum
      intro b _
      calc
        _ ≤ ∑ a, M * ‖D a b‖ * ‖B b‖ :=
          Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hA a) (norm_nonneg _)) (norm_nonneg _))
        _ = (M * ∑ a, ‖D a b‖) * ‖B b‖ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hD b) hM) (norm_nonneg _)
    _ = (M * e) * ∑ b, ‖B b‖ := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (mul_nonneg hM he)

end Sums

section Row
variable {I F : Type*} [Fintype F]

/-- An exact source Schur row decomposition gives a genuine contraction of
its finite boundary error sum. The nonlinear remainder bound follows. -/
theorem boundary_row_error_sum_and_remainder
    (R P : Matrix I I ℂ) (l : F → I) (D : Matrix F F ℂ) (c : ℂ) (i : I)
    (M e S : ℝ) (hM : 0 ≤ M) (he : 0 ≤ e) (hS : 0 ≤ S) (hc : ‖c‖ ≤ 1)
    (hroot : ∀ a, ‖P i (l a)‖ ≤ M)
    (hD : ∀ b, (∑ a, ‖D a b‖) ≤ e)
    (hP : ∀ j, (∑ b, ‖P (l b) j‖) ≤ S)
    (hidentity : ∀ j,
      R i j - P i j = c * (∑ a, ∑ b, P i (l a) * D a b * P (l b) j) +
        c * (∑ a, ∑ b, (R i (l a) - P i (l a)) * D a b * P (l b) j))
    (hsmall : (Fintype.card F : ℝ) * e * S ≤ 1 / 2) :
    (∑ a, ‖R i (l a) - P i (l a)‖) ≤ 2 * (Fintype.card F : ℝ) * M * e * S ∧
      ∀ j, ‖c * (∑ a, ∑ b, (R i (l a) - P i (l a)) * D a b * P (l b) j)‖ ≤
        2 * (Fintype.card F : ℝ) * M * e ^ 2 * S ^ 2 := by
  let Γ : ℝ := ∑ a, ‖R i (l a) - P i (l a)‖
  let n : ℝ := Fintype.card F
  have hΓ : 0 ≤ Γ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hpoint (a : F) : ‖R i (l a) - P i (l a)‖ ≤ Γ := by
    exact Finset.single_le_sum (f := fun a => ‖R i (l a) - P i (l a)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  have hlead (j : I) : ‖c * (∑ a, ∑ b, P i (l a) * D a b * P (l b) j)‖ ≤ M * e * S := by
    rw [norm_mul]
    have hh := boundary_double_sum_bound (fun a => P i (l a)) D (fun b => P (l b) j)
      M e S hM he hroot hD (hP j)
    exact (mul_le_mul_of_nonneg_left hh (norm_nonneg c)).trans
      (mul_le_of_le_one_left (by positivity) hc)
  have hrem (j : I) : ‖c * (∑ a, ∑ b, (R i (l a) - P i (l a)) * D a b * P (l b) j)‖ ≤ Γ * e * S := by
    rw [norm_mul]
    have hh := boundary_double_sum_bound (fun a => R i (l a) - P i (l a)) D (fun b => P (l b) j)
      Γ e S hΓ he hpoint hD (hP j)
    exact (mul_le_mul_of_nonneg_left hh (norm_nonneg c)).trans
      (mul_le_of_le_one_left (by positivity) hc)
  have hbound (j : I) : ‖R i j - P i j‖ ≤ (M + Γ) * e * S := by
    rw [hidentity j]
    exact ((norm_add_le _ _).trans (add_le_add (hlead j) (hrem j))).trans_eq (by ring)
  have hsum : Γ ≤ n * ((M + Γ) * e * S) := by
    calc
      _ ≤ ∑ a : F, (M + Γ) * e * S := Finset.sum_le_sum (fun a _ => hbound (l a))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, n]
  have hcontract : n * e * S * Γ ≤ Γ / 2 := by
    have hh := mul_le_mul_of_nonneg_right hsmall hΓ
    exact hh.trans_eq (by ring)
  have hΓbound : Γ ≤ 2 * n * M * e * S := by
    nlinarith only [hsum, hcontract]
  refine ⟨hΓbound, ?_⟩
  intro j
  apply (hrem j).trans
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΓbound he) hS
  exact hh.trans_eq (by ring)

end Row
end
end LocalLaw
