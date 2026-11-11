import LocalLaw.PrincipalDeletion
import LocalLaw.AttachedLeafTargetBound
import LocalLaw.NeighborhoodDeletionComparison

/-! # Quadratic comparison through a literal common deleted matrix

Small target-to-deleted-set entries and true inverse row masses give a
quadratic error. Both deleted matrices are actual principal restrictions;
their agreement is a structural matrix identity, not an error assumption.
-/

open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance commonDeletionQuadraticDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem physical_deletion_quadratic_bound {V : Type} [Fintype V] [DecidableEq V]
    (H : Matrix V V ℂ) (hH : H.IsHermitian) (S : Set V)
    (z : ℂ) (hz : 0 < z.im) (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hrows : ∀ i : S, ∑ j : S,
      ‖((green H z).submatrix (Subtype.val : S → V) (Subtype.val : S → V))⁻¹ i j‖ ≤ C)
    (x y : (Sᶜ : Set V))
    (hx : ∀ i : S, ‖green H z x.val i.val‖ ≤ δ)
    (hy : ∀ i : S, ‖green H z i.val y.val‖ ≤ δ) :
    ‖green H z x.val y.val -
      green (H.submatrix (Subtype.val : (Sᶜ : Set V) → V)
        (Subtype.val : (Sᶜ : Set V) → V)) z x y‖ ≤ (Fintype.card S : ℝ) * C * δ^2 := by
  classical
  let G := green H z
  let R := (G.submatrix (Subtype.val : S → V) (Subtype.val : S → V))⁻¹
  have hh := congrArg (fun A : Matrix (Sᶜ : Set V) (Sᶜ : Set V) ℂ => A x y)
    (green_deleted_principal S H hH z hz)
  dsimp only at hh
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.submatrix_apply, Finset.sum_mul] at hh
  rw [Finset.sum_comm] at hh
  have he : G x.val y.val -
      green (H.submatrix (Subtype.val : (Sᶜ : Set V) → V)
        (Subtype.val : (Sᶜ : Set V) → V)) z x y =
      schurBilinear (fun i : S => G x.val i.val) R (fun j : S => G j.val y.val) := by
    unfold schurBilinear
    linear_combination -hh
  change ‖G x.val y.val - _‖ ≤ _
  rw [he]
  exact (schurBilinear_bound_of_row_mass _ _ R δ δ C hδ hδ hC hx hy hrows).trans_eq (by ring)

/-- Two Hermitian matrices may use different ambient vertex types. -/
theorem physical_common_deletion_quadratic_bound
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (H : Matrix V V ℂ) (K : Matrix W W ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (S : Set V) (T : Set W) (e : (Sᶜ : Set V) ≃ (Tᶜ : Set W))
    (hcommon : H.submatrix (Subtype.val : (Sᶜ : Set V) → V) (Subtype.val : (Sᶜ : Set V) → V) =
      (K.submatrix (Subtype.val : (Tᶜ : Set W) → W) (Subtype.val : (Tᶜ : Set W) → W)).submatrix e e)
    (z : ℂ) (hz : 0 < z.im) (C D δ : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hrowsH : ∀ i : S, ∑ j : S,
      ‖((green H z).submatrix (Subtype.val : S → V) (Subtype.val : S → V))⁻¹ i j‖ ≤ C)
    (hrowsK : ∀ i : T, ∑ j : T,
      ‖((green K z).submatrix (Subtype.val : T → W) (Subtype.val : T → W))⁻¹ i j‖ ≤ D)
    (x y : (Sᶜ : Set V))
    (hxH : ∀ i : S, ‖green H z x.val i.val‖ ≤ δ)
    (hyH : ∀ i : S, ‖green H z i.val y.val‖ ≤ δ)
    (hxK : ∀ i : T, ‖green K z (e x).val i.val‖ ≤ δ)
    (hyK : ∀ i : T, ‖green K z i.val (e y).val‖ ≤ δ) :
    ‖green H z x.val y.val - green K z (e x).val (e y).val‖ ≤
      ((Fintype.card S : ℝ) * C + (Fintype.card T : ℝ) * D) * δ^2 := by
  classical
  have hh := physical_deletion_quadratic_bound H hH S z hz C δ hC hδ hrowsH x y hxH hyH
  have hk := physical_deletion_quadratic_bound K hK T z hz D δ hD hδ hrowsK (e x) (e y) hxK hyK
  have hid : green (H.submatrix (Subtype.val : (Sᶜ : Set V) → V)
      (Subtype.val : (Sᶜ : Set V) → V)) z x y =
      green (K.submatrix (Subtype.val : (Tᶜ : Set W) → W)
        (Subtype.val : (Tᶜ : Set W) → W)) z (e x) (e y) := by
    rw [hcommon, green_reindex_equiv]
    rfl
  rw [← hid] at hk
  have htri := norm_sub_le_norm_sub_add_norm_sub (green H z x.val y.val)
    (green (H.submatrix (Subtype.val : (Sᶜ : Set V) → V)
      (Subtype.val : (Sᶜ : Set V) → V)) z x y) (green K z (e x).val (e y).val)
  exact (htri.trans (add_le_add hh (by simpa only [norm_sub_rev] using hk))).trans_eq (by ring)

end SpectralConsequences
