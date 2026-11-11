import LocalLaw.EmbeddedDeletionComparison
import LocalLaw.ComponentModelRows

/-!
# Actual deletion transfer for disconnected source models

The reference graph may be disconnected and may have a different size from
the ambient graph. Its componentwise reference budget supplies all cross and
inverse-block sums. The final deleted entry error follows from the full
model approximation and the genuine physical Schur identities.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance componentDeletionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section SchurTransfer
variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] {d : ℕ}

/-- The actual different-size Schur comparison, organized around intermediate
cross-sum estimates. No deleted approximation or inverse-unit premise occurs. -/
theorem embedded_model_deletion_from_rows (g : DeficientGraph V d) (hd : 3 ≤ d)
    (H : Matrix A A ℂ) (hH : H.IsHermitian) (e : V ↪ A) (T : Set V)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (C L0 δ : ℝ) (hC : 0 ≤ C) (hL0 : 0 ≤ L0) (hδ : 0 ≤ δ)
    (happrox : ∀ v w, ‖green H z (e v) (e w) - g.extensionGreen q z v w‖ ≤ δ)
    (hProw : ∀ v : (Tᶜ : Set V), (∑ y : T, ‖g.extensionGreen q z v.val y.val‖) ≤ L0)
    (hPcol : ∀ v : (Tᶜ : Set V), (∑ y : T, ‖g.extensionGreen q z y.val v.val‖) ≤ L0)
    (hInvrow : ∀ x : T, (∑ y : T, ‖((g.extensionGreen q z).submatrix
      (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ x y‖) ≤ C)
    (hInvcol : ∀ y : T, (∑ x : T, ‖((g.extensionGreen q z).submatrix
      (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ x y‖) ≤ C)
    (smallCut : (Nat.card T : ℝ) * C * δ ≤ 1 / 2) (i j : (Tᶜ : Set V)) :
    ‖green (H.submatrix (Subtype.val : ((e '' T)ᶜ : Set A) → A)
        (Subtype.val : ((e '' T)ᶜ : Set A) → A)) z
          (embeddingOutsideImage e T i) (embeddingOutsideImage e T j) -
        (g.delete T).extensionGreen q z i j‖ ≤
      (1 + 3 * C * (L0 + (Nat.card T : ℝ) * δ) +
        2 * C ^ 2 * (L0 + (Nat.card T : ℝ) * δ) ^ 2) * δ := by
  let U := (green H z).submatrix e e
  let P := g.extensionGreen q z
  let L := L0 + (Nat.card T : ℝ) * δ
  have hL : 0 ≤ L := add_nonneg hL0 (mul_nonneg (Nat.cast_nonneg _) hδ)
  have hL0L : L0 ≤ L := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hδ)
  have hUcol (v : (Tᶜ : Set V)) : (∑ y : T, ‖U y.val v.val‖) ≤ L := by
    exact row_sum_perturbation
      (U.transpose.submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V))
      (P.transpose.submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V))
      v L0 δ (fun y => happrox y.val v.val) (hPcol v)
  have hUunit := embedded_green_retained_isUnit H hH z hz e T
  have hdel := (g.delete T).extensionMatrix_isUnit hd q z hz hq
  rw [g.extensionMatrix_delete] at hdel
  have hPunit := retained_principal_inverse_isUnit T (g.extensionMatrix q z)
    (g.extensionMatrix_isUnit hd q z hz hq) hdel
  have hsmall : (Fintype.card T : ℝ) * C * δ ≤ 1 / 2 := by
    simpa only [Nat.card_eq_fintype_card] using smallCut
  have hs := schur_deletion_difference_bound (partitionMatrix T U) (partitionMatrix T P)
    (by simpa only [partitionMatrix11] using hUunit)
    (by simpa only [partitionMatrix11] using hPunit)
    C L δ hC hL hδ
    (by intro v w; exact happrox ((Equiv.Set.sumCompl T) v) ((Equiv.Set.sumCompl T) w))
    (by intro x; simpa only [partitionMatrix11] using hInvrow x)
    (by intro y; simpa only [partitionMatrix11] using hInvcol y)
    (by intro v; simpa only [partitionMatrix21] using (hProw v).trans hL0L)
    (by intro v; simpa only [partitionMatrix12] using hUcol v)
    hsmall i j
  simp only [partitionMatrix22, partitionMatrix21, partitionMatrix11, partitionMatrix12] at hs
  have hUdelete := embedded_green_deleted_principal H hH z hz e T
  have hPdelete := g.extensionGreen_delete hd T q z hz hq
  rw [← hUdelete, ← hPdelete] at hs
  exact hs

/-- Componentwise version of the finite-model Proposition-5.1 comparison.
Disconnectedness and different ambient/model vertex sizes are both allowed;
every analytic cross-sum input of the Schur argument has been discharged. -/
theorem componentwise_embedded_model_deletion_comparison (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hzero : ∀ v, g.deficit v = 0) (hbudget : g.ComponentReferenceBudget)
    (H : Matrix A A ℂ) (hH : H.IsHermitian) (e : V ↪ A)
    (o : V) (ell : ℕ) (T : Set V) (hTball : T = graphBallVertices g.graph o ell)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (B : ℝ) (hB : ‖z‖ ≤ B) (hqnear : ‖q - semicircleRoot z‖ ≤ 1)
    (R : ℕ) (hR : ∀ v w, g.graph.dist v w ≤ R)
    (smallRef : ‖q - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * ((R : ℝ) + 1) ≤ 1 / 2)
    (Rdel : ℕ) (hRdel : ∀ a b, (outsideGraph g.graph T).dist a b ≤ Rdel)
    (smallDel : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((Rdel : ℝ) + 1) ≤ 1 / 2)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (happrox : ∀ v w, ‖green H z (e v) (e w) - g.extensionGreen q z v w‖ ≤ δ)
    (smallCut : (Nat.card T : ℝ) * DeficientGraph.boundarySchurConstant d B * δ ≤ 1 / 2)
    (i j : (Tᶜ : Set V)) :
    ‖green (H.submatrix (Subtype.val : ((e '' T)ᶜ : Set A) → A)
        (Subtype.val : ((e '' T)ᶜ : Set A) → A)) z
          (embeddingOutsideImage e T i) (embeddingOutsideImage e T j) -
        (g.delete T).extensionGreen q z i j‖ ≤
      modelDeletionErrorConstant d ell (Nat.card T) B δ * δ := by
  subst T
  let T := graphBallVertices g.graph o ell
  let C := DeficientGraph.boundarySchurConstant d B
  let L0 := 2 * finiteReferenceConstant d * outsideBallKernelConstant d (finiteOmega d) * ((ell : ℝ) + 1)
  have hCref : 0 ≤ finiteReferenceConstant d := (by norm_num : (0 : ℝ) ≤ 1).trans
    (finiteReferenceConstant_ge_one d hd)
  have hCextra : 0 ≤ finiteExtraReferenceConstant d := (by norm_num : (0 : ℝ) ≤ 1).trans
    (finiteExtraReferenceConstant_ge_one d hd)
  have hC : 0 ≤ C := by
    have hB0 := (norm_nonneg z).trans hB
    have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
    have hk0 : 0 ≤ (d : ℝ) - 1 := by linarith
    dsimp [C, DeficientGraph.boundarySchurConstant]
    positivity
  have hL0 : 0 ≤ L0 := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCref)
    (outsideBallKernelConstant_nonnegative _ _)) (by positivity)
  have hrows := g.componentwise_ball_retained_inverse_bounds hd hzero hbudget o ell q z hz hq
    B hB hqnear Rdel hRdel smallDel
  apply embedded_model_deletion_from_rows g hd H hH e T q z hz hq C L0 δ hC hL0 hδ happrox
  · intro v
    exact g.componentwise_outside_ball_row_sum hd hbudget q z hz hq R hR smallRef o v.val ell v.property
  · intro v
    exact g.componentwise_outside_ball_column_sum hd hbudget q z hz hq R hR smallRef o v.val ell v.property
  · exact hrows.1
  · exact hrows.2
  · exact smallCut

end SchurTransfer
end LocalLaw
