import LocalLaw.EmbeddedFiniteRankResolvent
import LocalLaw.MatrixEntryStability

/-!
# Physical principal-minor comparison through finite endpoint surgery

Every resolvent identity and scalar Schur formula concerns the genuine
Hermitian matrices and their genuine principal minors. Small old correlations
to the other endpoints give a linear surgery cost; the new own-edge term
is quadratic in its proved off-diagonal error.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance physicalMinorSurgeryDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V]

theorem supported_middle_entry (e : I ↪ V) (A W B : Matrix V V ℂ)
    (hsupport : ∀ x y, x ∉ Set.range e ∨ y ∉ Set.range e → W x y = 0) (i j : V) :
    (A * W * B) i j = ∑ u, ∑ v, A i (e u) * (W (e u) (e v) * B (e v) j) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Finset.mul_sum]
  calc
    _ = ∑ u, ∑ y, A i (e u) * (W (e u) y * B y j) := by
      apply sum_embedding_of_supported e
      intro x hx
      apply Finset.sum_eq_zero
      intro y _
      rw [hsupport x y (Or.inl hx), zero_mul, mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u _
      apply sum_embedding_of_supported e
      intro y hy
      rw [hsupport (e u) y (Or.inr hy), zero_mul, mul_zero]

theorem green_supported_entry_bound (H K : Matrix V V ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (e : I ↪ V) (hsupport : ∀ x y, x ∉ Set.range e ∨ y ∉ Set.range e → (K - H) x y = 0)
    (z : ℂ) (hz : 0 < z.im) (a b w : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (_hw : 0 ≤ w)
    (i j : V) (hleft : ∀ u, ‖green H z i (e u)‖ ≤ a)
    (hright : ∀ v, ‖green K z (e v) j‖ ≤ b)
    (hW : ∀ u, ∑ v, ‖(K - H) (e u) (e v)‖ ≤ w) :
    ‖green H z i j - green K z i j‖ ≤ (Fintype.card I : ℝ) * a * w * b := by
  have hinner (u : I) : (∑ v, ‖(K - H) (e u) (e v)‖ * ‖green K z (e v) j‖) ≤ w * b := by
    calc
      _ ≤ ∑ v, ‖(K - H) (e u) (e v)‖ * b := Finset.sum_le_sum (fun v _ =>
        mul_le_mul_of_nonneg_left (hright v) (norm_nonneg _))
      _ = (∑ v, ‖(K - H) (e u) (e v)‖) * b := (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hW u) hb
  have hid := congrArg (fun M : Matrix V V ℂ => M i j) (green_matrix_difference H K hH hK z hz)
  dsimp only at hid
  change green H z i j - green K z i j = _ at hid
  rw [hid, supported_middle_entry e _ _ _ hsupport]
  calc
    _ ≤ ∑ u, ‖green H z i (e u)‖ * (∑ v, ‖(K - H) (e u) (e v)‖ * ‖green K z (e v) j‖) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro u _
      apply (norm_sum_le _ _).trans
      simp only [norm_mul, Finset.mul_sum]
      exact le_rfl
    _ ≤ ∑ _u : I, a * (w * b) := Finset.sum_le_sum (fun u _ =>
      mul_le_mul (hleft u) (hinner u) (Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))) ha)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

private theorem triple_product_norm_bound (x y t : ℂ) (X Y T : ℝ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (_hT : 0 ≤ T)
    (hx : ‖x‖ ≤ X) (hy : ‖y‖ ≤ Y) (ht : ‖t‖ ≤ T) : ‖x * y * t‖ ≤ X * Y * T := by
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul hx hy (norm_nonneg _) hX) ht (norm_nonneg _) (mul_nonneg hX hY)

/-- The finite physical good-diagonal comparison. The deleted perturbation
support and row bound are literal matrix facts, and every minor/Schur
identity is proved from physical inverses. -/
theorem physical_principal_minor_surgery_bound (H K : Matrix V V ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (b : V) (c : {v : V // v ≠ b}) (e : I ↪ {v : V // v ≠ b})
    (hsupport : ∀ x y, x ∉ Set.range e ∨ y ∉ Set.range e →
      (deletedMatrix K b - deletedMatrix H b) x y = 0)
    (C L φ w δ : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) (hφ : 0 ≤ φ) (hw : 0 ≤ w)
    (hδ : 0 ≤ δ) (hδC : δ ≤ C)
    (hOldNear : ‖green H z c.val b‖ ≤ C) (hOldPivot : ‖(green H z b b)⁻¹‖ ≤ L)
    (hOldC : ∀ u, ‖green H z c.val (e u).val‖ ≤ φ)
    (hOldB : ∀ u, ‖green H z b (e u).val‖ ≤ φ)
    (hNewC : ∀ u, ‖green K z (e u).val c.val‖ ≤ C)
    (hNewB : ∀ u, ‖green K z (e u).val b‖ ≤ C)
    (hNewPivot : ‖(green K z b b)⁻¹‖ ≤ L)
    (hNewCB : ‖green K z c.val b‖ ≤ δ) (hNewBC : ‖green K z b c.val‖ ≤ δ)
    (hW : ∀ u, ∑ v, ‖(deletedMatrix K b - deletedMatrix H b) (e u) (e v)‖ ≤ w) :
    ‖green K z c.val c.val - green (deletedMatrix H b) z c c‖ ≤
      (Fintype.card I : ℝ) * ((1 + C * L) * φ) * w * (C + C ^ 2 * L) + δ ^ 2 * L := by
  have hOld (u : I) : ‖green (deletedMatrix H b) z c (e u)‖ ≤ (1 + C * L) * φ := by
    rw [green_deleted_vertex H hH z hz b c (e u)]
    have hprod := triple_product_norm_bound _ _ _ C φ L hC hφ hL hOldNear (hOldB u) hOldPivot
    have hh := (norm_sub_le _ _).trans (add_le_add (hOldC u) (by
      simpa only [div_eq_mul_inv] using hprod))
    exact hh.trans_eq (by ring)
  have hNew (u : I) : ‖green (deletedMatrix K b) z (e u) c‖ ≤ C + C ^ 2 * L := by
    rw [green_deleted_vertex K hK z hz b (e u) c]
    have hprod := triple_product_norm_bound _ _ _ C C L hC hC hL (hNewB u) (hNewBC.trans hδC) hNewPivot
    have hh := (norm_sub_le _ _).trans (add_le_add (hNewC u) (by
      simpa only [div_eq_mul_inv] using hprod))
    exact hh.trans_eq (by ring)
  have hminor := green_supported_entry_bound (deletedMatrix H b) (deletedMatrix K b)
    (deletedMatrix_isHermitian H hH b) (deletedMatrix_isHermitian K hK b) e hsupport z hz
    ((1 + C * L) * φ) (C + C ^ 2 * L) w (by positivity) (by positivity) hw c c hOld hNew hW
  have hcross : ‖green K z c.val c.val - green (deletedMatrix K b) z c c‖ ≤ δ ^ 2 * L := by
    rw [green_deleted_vertex K hK z hz b c c]
    have hid : green K z c.val c.val - (green K z c.val c.val -
        green K z c.val b * green K z b c.val / green K z b b) =
        green K z c.val b * green K z b c.val * (green K z b b)⁻¹ := by rw [div_eq_mul_inv]; ring
    rw [hid]
    exact (triple_product_norm_bound _ _ _ δ δ L hδ hδ hL hNewCB hNewBC hNewPivot).trans_eq (by ring)
  have htriangle := norm_sub_le_norm_sub_add_norm_sub (green K z c.val c.val)
    (green (deletedMatrix K b) z c c) (green (deletedMatrix H b) z c c)
  exact htriangle.trans ((add_le_add hcross (by simpa only [norm_sub_rev] using hminor)).trans_eq (by ring))

end LocalLaw
