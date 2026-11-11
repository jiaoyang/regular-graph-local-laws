import LocalLaw.EmbeddedDeletionComparison

/-! # Removing some retained indices restricts the retained precision

All Green blocks are actual Hermitian resolvent blocks. Deleting a subset
of the retained vertices takes a principal block of the old retained
precision; it does not require a new inverse-row hypothesis.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1400000
namespace SpectralConsequences
open LocalLaw
local instance nestedRetainedPrecisionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {A V : Type} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]

theorem embedded_green_submatrix_isUnit (H : Matrix A A ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (e : V ↪ A) : IsUnit ((green H z).submatrix e e) := by
  let T : Set A := Set.range e
  letI : DecidablePred (fun a => a ∈ T) := fun _ => Classical.propDecidable _
  letI : Fintype T := Subtype.fintype _
  let φ : V ≃ T := Equiv.ofInjective e e.injective
  have hU := (green_retained_principal_inverse T H hH z hz).1
  have heq : (green H z).submatrix e e =
      ((green H z).submatrix (Subtype.val : T → A) (Subtype.val : T → A)).submatrix φ φ := by
    ext i j
    rfl
  rw [heq]
  exact (Matrix.isUnit_submatrix_equiv φ φ).mpr hU

/-- Native-decider version: the removed-set dictionaries remain those in the signature. -/
theorem embedded_green_deleted_principal_native (H : Matrix A A ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (e : V ↪ A) (Q : Set V) [DecidablePred (fun v => v ∈ Q)] :
    (green (H.submatrix (Subtype.val : ((e '' Q)ᶜ : Set A) → A)
      (Subtype.val : ((e '' Q)ᶜ : Set A) → A)) z).submatrix
        (embeddingOutsideImage e Q) (embeddingOutsideImage e Q) =
    ((green H z).submatrix e e).submatrix (Subtype.val : (Qᶜ : Set V) → V) (Subtype.val : (Qᶜ : Set V) → V) -
      ((green H z).submatrix e e).submatrix (Subtype.val : (Qᶜ : Set V) → V) (Subtype.val : Q → V) *
      (((green H z).submatrix e e).submatrix (Subtype.val : Q → V) (Subtype.val : Q → V))⁻¹ *
      ((green H z).submatrix e e).submatrix (Subtype.val : Q → V) (Subtype.val : (Qᶜ : Set V) → V) := by
  letI : DecidablePred (fun a => a ∈ e '' Q) := fun _ => Classical.propDecidable _
  letI : Fintype (e '' Q) := Subtype.fintype _
  let φ := Equiv.Set.image (e : V → A) Q e.injective
  let f := embeddingOutsideImage e Q
  let P := green H z
  let B := P.submatrix (Subtype.val : e '' Q → A) (Subtype.val : e '' Q → A)
  have hInv : (((P.submatrix e e).submatrix (Subtype.val : Q → V) (Subtype.val : Q → V)))⁻¹ =
      B⁻¹.submatrix φ φ := Matrix.inv_submatrix_equiv B φ φ
  have hprod : ((P.submatrix (Subtype.val : ((e '' Q)ᶜ : Set A) → A) (Subtype.val : e '' Q → A) *
      B⁻¹ * P.submatrix (Subtype.val : e '' Q → A) (Subtype.val : ((e '' Q)ᶜ : Set A) → A)).submatrix f f) =
      (P.submatrix e e).submatrix (Subtype.val : (Qᶜ : Set V) → V) (Subtype.val : Q → V) *
      (((P.submatrix e e).submatrix (Subtype.val : Q → V) (Subtype.val : Q → V)))⁻¹ *
      (P.submatrix e e).submatrix (Subtype.val : Q → V) (Subtype.val : (Qᶜ : Set V) → V) := by
    rw [Matrix.submatrix_mul _ _ f φ f φ.bijective,
      Matrix.submatrix_mul _ _ f φ φ φ.bijective, ← hInv]
    rfl
  have hh := congrArg (fun M : Matrix ((e '' Q)ᶜ : Set A) ((e '' Q)ᶜ : Set A) ℂ => M.submatrix f f)
    (green_deleted_principal (e '' Q) H hH z hz)
  dsimp only at hh
  simp only [Matrix.submatrix_sub, Pi.sub_apply] at hh
  rw [hprod] at hh
  exact hh

theorem embedded_deleted_retained_inverse (H : Matrix A A ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (e : V ↪ A) (Q : Set V) [DecidablePred (fun v => v ∈ Q)] :
    let P := (green H z).submatrix e e
    let R := (green (H.submatrix (Subtype.val : ((e '' Q)ᶜ : Set A) → A)
      (Subtype.val : ((e '' Q)ᶜ : Set A) → A)) z).submatrix
        (embeddingOutsideImage e Q) (embeddingOutsideImage e Q)
    IsUnit R ∧ R⁻¹ = P⁻¹.submatrix
      (Subtype.val : (Qᶜ : Set V) → V) (Subtype.val : (Qᶜ : Set V) → V) := by
  dsimp only
  let P := (green H z).submatrix e e
  let M := partitionMatrix Q P
  let R := (green (H.submatrix (Subtype.val : ((e '' Q)ᶜ : Set A) → A)
    (Subtype.val : ((e '' Q)ᶜ : Set A) → A)) z).submatrix
      (embeddingOutsideImage e Q) (embeddingOutsideImage e Q)
  have hPi : IsUnit P := embedded_green_submatrix_isUnit H hH z hz e
  have hM : IsUnit M := partitionMatrix_isUnit Q P hPi
  have hA : IsUnit M.toBlocks₁₁ := by
    let f : Q ↪ A := ⟨fun i => e i.val, fun i j hij => Subtype.ext (e.injective hij)⟩
    exact embedded_green_submatrix_isUnit H hH z hz f
  have hR : R = M.toBlocks₂₂-M.toBlocks₂₁*M.toBlocks₁₁⁻¹*M.toBlocks₁₂ :=
    embedded_green_deleted_principal_native H hH z hz e Q
  have hb := inverse_block22 M hM hA
  have hRi : IsUnit R := hR ▸ hb.1
  have hprec : R⁻¹=(M⁻¹).toBlocks₂₂ := by rw [hR]; exact hb.2.symm
  refine ⟨hRi,?_⟩
  rw [hprec,partitionMatrix_inverse,partitionMatrix22]

theorem embedded_deleted_retained_inverse_rows (H : Matrix A A ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (e : V ↪ A) (Q : Set V) [DecidablePred (fun v => v ∈ Q)]
    (C : ℝ)
    (hrows : ∀ i, ∑ j, ‖((green H z).submatrix e e)⁻¹ i j‖ ≤ C) :
    let R := (green (H.submatrix (Subtype.val : ((e '' Q)ᶜ : Set A) → A)
      (Subtype.val : ((e '' Q)ᶜ : Set A) → A)) z).submatrix
        (embeddingOutsideImage e Q) (embeddingOutsideImage e Q)
    ∀ i, ∑ j, ‖R⁻¹ i j‖ ≤ C := by
  dsimp only
  have hp := (embedded_deleted_retained_inverse H hH z hz e Q).2
  intro i
  rw [hp]
  simp only [Matrix.submatrix_apply]
  let f : (Qᶜ : Set V) ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  calc
    _ = ∑ j ∈ Finset.univ.map f, ‖((green H z).submatrix e e)⁻¹ i.val j‖ := by
      rw [Finset.sum_map]
      rfl
    _ ≤ ∑ j : V, ‖((green H z).submatrix e e)⁻¹ i.val j‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => norm_nonneg _)
    _ ≤ C := hrows i.val

end SpectralConsequences
