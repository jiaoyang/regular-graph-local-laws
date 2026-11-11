import LocalLaw.ResolventComparisonWard
import LocalLaw.EmbeddedCutIncidence

/-!
# Physical finite-rank updates on a genuine embedded endpoint block

The perturbation is supported on the actual image of a finite embedding.
Both convolution indices are reindexed from the ambient vertex type. The
two update equations follow from genuine physical resolvent identities;
all matrix units are supplied by Hermitian dissipativity.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance embeddedFiniteRankDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

omit [DecidableEq I] in
theorem supported_middle_submatrix (e : I ↪ V) (A W B : Matrix V V ℂ)
    (hsupport : ∀ x y, x ∉ Set.range e ∨ y ∉ Set.range e → W x y = 0) :
    (A * W * B).submatrix e e = A.submatrix e e * W.submatrix e e * B.submatrix e e := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Finset.sum_mul]
  calc
    _ = ∑ b, ∑ v, A (e i) v * W v (e b) * B (e b) (e j) := by
      apply sum_embedding_of_supported e
      intro w hw
      apply Finset.sum_eq_zero
      intro v _
      rw [hsupport v w (Or.inr hw), mul_zero, zero_mul]
    _ = ∑ b, ∑ a, A (e i) (e a) * W (e a) (e b) * B (e b) (e j) := by
      apply Finset.sum_congr rfl
      intro b _
      apply sum_embedding_of_supported e
      intro v hv
      rw [hsupport v (e b) (Or.inl hv), mul_zero, zero_mul]

omit [DecidableEq I] in
/-- Both orientations of the actual endpoint resolvent update. The
coupling is literally the old/new matrix difference on the same endpoints. -/
theorem green_embedded_finite_rank_updates (H K : Matrix V V ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) (e : I ↪ V)
    (hsupport : ∀ x y, x ∉ Set.range e ∨ y ∉ Set.range e → (K - H) x y = 0)
    (z : ℂ) (hz : 0 < z.im) :
    let R := (green H z).submatrix e e
    let T := (green K z).submatrix e e
    let W := (K - H).submatrix e e
    (T + R * W * T = R) ∧ (T + T * W * R = R) := by
  dsimp only
  have hfirst := congrArg (fun M : Matrix V V ℂ => M.submatrix e e)
    (green_matrix_difference H K hH hK z hz)
  dsimp only at hfirst
  rw [Matrix.submatrix_sub, supported_middle_submatrix e _ _ _ hsupport] at hfirst
  have hsecondFull : green H z - green K z = green K z * (K - H) * green H z := by
    have hh := green_matrix_difference K H hK hH z hz
    rw [show H - K = -(K - H) by abel, Matrix.mul_neg, Matrix.neg_mul] at hh
    have hneg := congrArg (fun M : Matrix V V ℂ => -M) hh
    simpa only [neg_sub, neg_neg] using hneg
  have hsecond := congrArg (fun M : Matrix V V ℂ => M.submatrix e e) hsecondFull
  dsimp only at hsecond
  rw [Matrix.submatrix_sub, supported_middle_submatrix e _ _ _ hsupport] at hsecond
  constructor
  · simpa only [add_comm] using (eq_sub_iff_add_eq.mp hfirst.symm)
  · simpa only [add_comm] using (eq_sub_iff_add_eq.mp hsecond.symm)

omit [DecidableEq I] in
/-- The same actual support reduction applies to finite extension matrices,
once their genuine inverse units have been derived from physical parameters. -/
theorem inverse_embedded_finite_rank_updates (A B : Matrix V V ℂ)
    (hA : IsUnit A) (hB : IsUnit B) (e : I ↪ V)
    (hsupport : ∀ x y, x ∉ Set.range e ∨ y ∉ Set.range e → (B - A) x y = 0) :
    let R := A⁻¹.submatrix e e
    let T := B⁻¹.submatrix e e
    let W := (B - A).submatrix e e
    (T + R * W * T = R) ∧ (T + T * W * R = R) := by
  have hdiff : A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
    rw [Matrix.inv_sub_inv (show IsUnit A ↔ IsUnit B from ⟨fun _ => hB, fun _ => hA⟩)]
  have hfirst := congrArg (fun M : Matrix V V ℂ => M.submatrix e e) hdiff
  dsimp only at hfirst
  rw [Matrix.submatrix_sub, supported_middle_submatrix e _ _ _ hsupport] at hfirst
  have hreverse : B⁻¹ - A⁻¹ = B⁻¹ * (A - B) * A⁻¹ := by
    rw [Matrix.inv_sub_inv (show IsUnit B ↔ IsUnit A from ⟨fun _ => hA, fun _ => hB⟩)]
  rw [show A - B = -(B - A) by abel, Matrix.mul_neg, Matrix.neg_mul] at hreverse
  have hnegative := congrArg (fun M : Matrix V V ℂ => -M) hreverse
  simp only [neg_sub, neg_neg] at hnegative
  have hsecond := congrArg (fun M : Matrix V V ℂ => M.submatrix e e) hnegative
  dsimp only at hsecond
  rw [Matrix.submatrix_sub, supported_middle_submatrix e _ _ _ hsupport] at hsecond
  constructor
  · simpa only [add_comm] using (eq_sub_iff_add_eq.mp hfirst.symm)
  · simpa only [add_comm] using (eq_sub_iff_add_eq.mp hsecond.symm)

end LocalLaw
