import SpectralConsequences.CommonDeletionQuadratic

/-! # Quadratic deletion bounds using an injective indexed deleted set -/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1400000
namespace SpectralConsequences
open LocalLaw
local instance indexedDeletionQuadraticDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

theorem physical_deletion_quadratic_bound_native (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (S : Set V) [DecidablePred (fun v => v ∈ S)]
    (z : ℂ) (hz : 0 < z.im) (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hrows : ∀ i : S, ∑ j : S,
      ‖((green H z).submatrix (Subtype.val : S → V) (Subtype.val : S → V))⁻¹ i j‖ ≤ C)
    (x y : (Sᶜ : Set V))
    (hx : ∀ i : S, ‖green H z x.val i.val‖ ≤ δ)
    (hy : ∀ i : S, ‖green H z i.val y.val‖ ≤ δ) :
    ‖green H z x.val y.val -
      green (H.submatrix (Subtype.val : (Sᶜ : Set V) → V)
        (Subtype.val : (Sᶜ : Set V) → V)) z x y‖ ≤ (Fintype.card S : ℝ)*C*δ^2 := by
  let G := green H z
  let R := (G.submatrix (Subtype.val : S → V) (Subtype.val : S → V))⁻¹
  have hh := congrArg (fun A : Matrix (Sᶜ : Set V) (Sᶜ : Set V) ℂ => A x y)
    (green_deleted_principal S H hH z hz)
  dsimp only at hh
  simp only [Matrix.sub_apply,Matrix.mul_apply,Matrix.submatrix_apply,Finset.sum_mul] at hh
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

theorem physical_indexed_deletion_quadratic_bound (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (S : Set V) [DecidablePred (fun v => v ∈ S)] (φ : I ≃ S)
    (z : ℂ) (hz : 0 < z.im) (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hrows : ∀ i, ∑ j, ‖((green H z).submatrix (fun i => (φ i).val) (fun i => (φ i).val))⁻¹ i j‖ ≤ C)
    (x y : (Sᶜ : Set V))
    (hx : ∀ i, ‖green H z x.val (φ i).val‖ ≤ δ)
    (hy : ∀ i, ‖green H z (φ i).val y.val‖ ≤ δ) :
    ‖green H z x.val y.val -
      green (H.submatrix (Subtype.val : (Sᶜ : Set V) → V)
        (Subtype.val : (Sᶜ : Set V) → V)) z x y‖ ≤
      (Fintype.card I : ℝ)*C*δ^2 := by
  let P := (green H z).submatrix (Subtype.val : S → V) (Subtype.val : S → V)
  have hm : P.submatrix φ φ = (green H z).submatrix (fun i => (φ i).val) (fun i => (φ i).val) := by ext i j; rfl
  have hi : ((green H z).submatrix (fun i => (φ i).val) (fun i => (φ i).val))⁻¹ = P⁻¹.submatrix φ φ := by
    rw [←hm,Matrix.inv_submatrix_equiv]
  have hr : ∀ i : S, ∑ j : S, ‖P⁻¹ i j‖ ≤ C := by
    intro i
    have hh := hrows (φ.symm i)
    rw [hi] at hh
    simp only [Matrix.submatrix_apply,φ.apply_symm_apply] at hh
    rw [Equiv.sum_comp φ (fun j => ‖P⁻¹ i j‖)] at hh
    exact hh
  have hx' : ∀ i : S, ‖green H z x.val i.val‖ ≤ δ := by
    intro i
    simpa only [φ.apply_symm_apply] using hx (φ.symm i)
  have hy' : ∀ i : S, ‖green H z i.val y.val‖ ≤ δ := by
    intro i
    simpa only [φ.apply_symm_apply] using hy (φ.symm i)
  have hh := physical_deletion_quadratic_bound_native H hH S z hz C δ hC hδ hr x y hx' hy'
  have hc : Fintype.card S = Fintype.card I := (Fintype.card_congr φ).symm
  simpa only [hc] using hh

end SpectralConsequences
