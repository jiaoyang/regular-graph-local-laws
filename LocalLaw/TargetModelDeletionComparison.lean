import LocalLaw.ComponentDeletionComparison
import LocalLaw.TargetDeletionStability

/-!
# Target-local actual finite-model deletion comparison

The full approximation is required only on the removed block and the target
row, column and entry. These are precisely the roots whose radius-r balls
are contained in the source model B_r(T union {i,j}).
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance targetModelDeletionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] {d : ℕ}

/-- The actual different-size Schur comparison, organized around intermediate
cross-sum estimates. No deleted approximation or inverse-unit premise occurs. -/
theorem embedded_target_deletion_from_rows (g : DeficientGraph V d) (hd : 3 ≤ d)
    (H : Matrix A A ℂ) (hH : H.IsHermitian) (e : V ↪ A) (T : Set V)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (C L0 δ : ℝ) (hC : 0 ≤ C) (hL0 : 0 ≤ L0) (hδ : 0 ≤ δ)
    (i j : (Tᶜ : Set V))
    (hTT : ∀ x y : T, ‖green H z (e x.val) (e y.val) - g.extensionGreen q z x.val y.val‖ ≤ δ)
    (hrowError : ∀ x : T, ‖green H z (e i.val) (e x.val) - g.extensionGreen q z i.val x.val‖ ≤ δ)
    (hcolumnError : ∀ y : T, ‖green H z (e y.val) (e j.val) - g.extensionGreen q z y.val j.val‖ ≤ δ)
    (htarget : ‖green H z (e i.val) (e j.val) - g.extensionGreen q z i.val j.val‖ ≤ δ)
    (hProw : (∑ y : T, ‖g.extensionGreen q z i.val y.val‖) ≤ L0)
    (hPcol : (∑ y : T, ‖g.extensionGreen q z y.val j.val‖) ≤ L0)
    (hInvrow : ∀ x : T, (∑ y : T, ‖((g.extensionGreen q z).submatrix
      (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ x y‖) ≤ C)
    (hInvcol : ∀ y : T, (∑ x : T, ‖((g.extensionGreen q z).submatrix
      (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ x y‖) ≤ C)
    (smallCut : (Nat.card T : ℝ) * C * δ ≤ 1 / 2) :
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
  have hUcol : (∑ y : T, ‖U y.val j.val‖) ≤ L := by
    exact row_sum_perturbation
      (U.transpose.submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V))
      (P.transpose.submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V))
      j L0 δ hcolumnError hPcol
  have hUunit := embedded_green_retained_isUnit H hH z hz e T
  have hdel := (g.delete T).extensionMatrix_isUnit hd q z hz hq
  rw [g.extensionMatrix_delete] at hdel
  have hPunit := retained_principal_inverse_isUnit T (g.extensionMatrix q z)
    (g.extensionMatrix_isUnit hd q z hz hq) hdel
  have hsmall : (Fintype.card T : ℝ) * C * δ ≤ 1 / 2 := by
    simpa only [Nat.card_eq_fintype_card] using smallCut
  have hs := target_schur_deletion_difference_bound (partitionMatrix T U) (partitionMatrix T P)
    (by simpa only [partitionMatrix11] using hUunit)
    (by simpa only [partitionMatrix11] using hPunit)
    C L δ hC hL hδ i j
    (by intro x y; exact hTT x y)
    (by intro x; exact hrowError x)
    (by intro y; exact hcolumnError y)
    htarget
    (by intro x; simpa only [partitionMatrix11] using hInvrow x)
    (by intro y; simpa only [partitionMatrix11] using hInvcol y)
    (by simpa only [partitionMatrix21] using hProw.trans hL0L)
    (by simpa only [partitionMatrix12] using hUcol)
    hsmall
  simp only [partitionMatrix22, partitionMatrix21, partitionMatrix11, partitionMatrix12] at hs
  have hUdelete := embedded_green_deleted_principal H hH z hz e T
  have hPdelete := g.extensionGreen_delete hd T q z hz hq
  rw [← hUdelete, ← hPdelete] at hs
  exact hs

/-- Componentwise version of the finite-model Proposition-5.1 comparison.
Disconnectedness and different ambient/model vertex sizes are both allowed;
every analytic cross-sum input of the Schur argument has been discharged. -/
theorem componentwise_embedded_target_deletion_comparison (g : DeficientGraph V d) (hd : 3 ≤ d)
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
    (i j : (Tᶜ : Set V))
    (hTT : ∀ x y : T, ‖green H z (e x.val) (e y.val) - g.extensionGreen q z x.val y.val‖ ≤ δ)
    (hrowError : ∀ x : T, ‖green H z (e i.val) (e x.val) - g.extensionGreen q z i.val x.val‖ ≤ δ)
    (hcolumnError : ∀ y : T, ‖green H z (e y.val) (e j.val) - g.extensionGreen q z y.val j.val‖ ≤ δ)
    (htarget : ‖green H z (e i.val) (e j.val) - g.extensionGreen q z i.val j.val‖ ≤ δ)
    (smallCut : (Nat.card T : ℝ) * DeficientGraph.boundarySchurConstant d B * δ ≤ 1 / 2)
    :
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
  apply embedded_target_deletion_from_rows g hd H hH e T q z hz hq C L0 δ hC hL0 hδ i j
    hTT hrowError hcolumnError htarget
  · exact g.componentwise_outside_ball_row_sum hd hbudget q z hz hq R hR smallRef o i.val ell i.property
  · exact g.componentwise_outside_ball_column_sum hd hbudget q z hz hq R hR smallRef o j.val ell j.property
  · exact hrows.1
  · exact hrows.2
  · exact smallCut

end LocalLaw
