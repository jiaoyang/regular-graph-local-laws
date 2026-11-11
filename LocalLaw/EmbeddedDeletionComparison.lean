import LocalLaw.OutsideBallReferenceRows

/-!
# Principal deletion compared with a finite embedded model

The ambient Green matrix and the finite model may have different vertex
types. Their principal-deletion identities are transported through the actual
vertex embedding, so a model approximation can be used on its genuine finite
vertex set without padding it by artificial zero rows.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance embeddedDeletionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Embedding
variable {V A : Type*}

def embeddingOutsideImage (e : V ↪ A) (T : Set V) : (Tᶜ : Set V) → ((e '' T)ᶜ : Set A) :=
  fun v => ⟨e v.val, by
    rintro ⟨w, hw, hwe⟩
    exact v.property ((e.injective hwe) ▸ hw)⟩

variable [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

/-- The actual retained ambient Green block remains invertible after its
finite vertex embedding is used to index the removed set. -/
theorem embedded_green_retained_isUnit (H : Matrix A A ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (e : V ↪ A) (T : Set V) :
    IsUnit (((green H z).submatrix e e).submatrix (Subtype.val : T → V) (Subtype.val : T → V)) := by
  letI : DecidablePred (fun a => a ∈ e '' T) := fun _ => Classical.propDecidable _
  letI : Fintype (e '' T) := Subtype.fintype _
  let φ := Equiv.Set.image (e : V → A) T e.injective
  have hunit := (green_retained_principal_inverse (e '' T) H hH z hz).1
  have heq : ((green H z).submatrix e e).submatrix (Subtype.val : T → V) (Subtype.val : T → V) =
      ((green H z).submatrix (Subtype.val : e '' T → A) (Subtype.val : e '' T → A)).submatrix φ φ := by
    ext i j
    rfl
  rw [heq]
  exact (Matrix.isUnit_submatrix_equiv φ φ).mpr hunit

/-- Actual ambient deletion, indexed by the complement in the finite model.
Every sum in the Schur expression runs over the true removed set. -/
theorem embedded_green_deleted_principal (H : Matrix A A ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (e : V ↪ A) (T : Set V) :
    (green (H.submatrix (Subtype.val : ((e '' T)ᶜ : Set A) → A)
      (Subtype.val : ((e '' T)ᶜ : Set A) → A)) z).submatrix
        (embeddingOutsideImage e T) (embeddingOutsideImage e T) =
    ((green H z).submatrix e e).submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : (Tᶜ : Set V) → V) -
      ((green H z).submatrix e e).submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V) *
      (((green H z).submatrix e e).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ *
      ((green H z).submatrix e e).submatrix (Subtype.val : T → V) (Subtype.val : (Tᶜ : Set V) → V) := by
  letI : DecidablePred (fun a => a ∈ e '' T) := fun _ => Classical.propDecidable _
  letI : Fintype (e '' T) := Subtype.fintype _
  let φ := Equiv.Set.image (e : V → A) T e.injective
  let f := embeddingOutsideImage e T
  let P := green H z
  let B := P.submatrix (Subtype.val : e '' T → A) (Subtype.val : e '' T → A)
  have hInv : (((P.submatrix e e).submatrix (Subtype.val : T → V) (Subtype.val : T → V)))⁻¹ =
      B⁻¹.submatrix φ φ := by
    have hh := Matrix.inv_submatrix_equiv B φ φ
    exact hh
  have hprod : ((P.submatrix (Subtype.val : ((e '' T)ᶜ : Set A) → A) (Subtype.val : e '' T → A) *
      B⁻¹ * P.submatrix (Subtype.val : e '' T → A) (Subtype.val : ((e '' T)ᶜ : Set A) → A)).submatrix f f) =
      (P.submatrix e e).submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V) *
      (((P.submatrix e e).submatrix (Subtype.val : T → V) (Subtype.val : T → V)))⁻¹ *
      (P.submatrix e e).submatrix (Subtype.val : T → V) (Subtype.val : (Tᶜ : Set V) → V) := by
    rw [Matrix.submatrix_mul _ _ f φ f φ.bijective,
      Matrix.submatrix_mul _ _ f φ φ φ.bijective, ← hInv]
    rfl
  have hh := congrArg (fun M : Matrix ((e '' T)ᶜ : Set A) ((e '' T)ᶜ : Set A) ℂ => M.submatrix f f)
    (green_deleted_principal (e '' T) H hH z hz)
  dsimp only at hh
  simp only [Matrix.submatrix_sub, Pi.sub_apply] at hh
  rw [hprod] at hh
  exact hh

end Embedding

section RowPerturbation
variable {I J : Type*} [Fintype I]

/-- Finite cross-sum transfer from an entry approximation. -/
theorem row_sum_perturbation (U P : Matrix J I ℂ) (j : J) (L δ : ℝ)
    (hentry : ∀ i, ‖U j i - P j i‖ ≤ δ) (hrow : (∑ i, ‖P j i‖) ≤ L) :
    (∑ i, ‖U j i‖) ≤ L + (Nat.card I : ℝ) * δ := by
  have hpoint (i : I) : ‖U j i‖ ≤ ‖P j i‖ + δ := by
    have hh := norm_add_le (U j i - P j i) (P j i)
    rw [sub_add_cancel] at hh
    linarith [hentry i]
  calc
    _ ≤ ∑ i, (‖P j i‖ + δ) := Finset.sum_le_sum (fun i _ => hpoint i)
    _ = (∑ i, ‖P j i‖) + (Nat.card I : ℝ) * δ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Nat.card_eq_fintype_card]
    _ ≤ _ := add_le_add_right hrow _

end RowPerturbation

def modelDeletionCrossBudget (d ell cutCard : ℕ) (δ : ℝ) : ℝ :=
  2 * finiteReferenceConstant d * outsideBallKernelConstant d (finiteOmega d) * ((ell : ℝ) + 1) +
    (cutCard : ℝ) * δ

def modelDeletionErrorConstant (d ell cutCard : ℕ) (B δ : ℝ) : ℝ :=
  1 + 3 * DeficientGraph.boundarySchurConstant d B * modelDeletionCrossBudget d ell cutCard δ +
    2 * DeficientGraph.boundarySchurConstant d B ^ 2 * modelDeletionCrossBudget d ell cutCard δ ^ 2

def modelDeletionLogConstant (d : ℕ) (B : ℝ) : ℝ :=
  let C := DeficientGraph.boundarySchurConstant d B
  let D := 2 * finiteReferenceConstant d * outsideBallKernelConstant d (finiteOmega d) + 1
  1 + 3 * C * D + 2 * C ^ 2 * D ^ 2

/-- The explicit Schur error is cubic in a common logarithmic scale when
the model entry error is linear in that scale. This is source (5.18)'s
arithmetic, with all finite-size absorption assumptions stated literally. -/
theorem model_deletion_error_log_bound (d : ℕ) (hd : 3 ≤ d) (B : ℝ) (hB : 0 ≤ B)
    (ell cutCard : ℕ) (δ ε L : ℝ) (hδ : 0 ≤ δ) (hL : 1 ≤ L)
    (hell : (ell : ℝ) + 1 ≤ L) (hcut : (cutCard : ℝ) * δ ≤ L)
    (hentry : δ ≤ L * ε) :
    modelDeletionErrorConstant d ell cutCard B δ * δ ≤
      modelDeletionLogConstant d B * L ^ 3 * ε := by
  let C := DeficientGraph.boundarySchurConstant d B
  let D0 := 2 * finiteReferenceConstant d * outsideBallKernelConstant d (finiteOmega d)
  let D := D0 + 1
  let X := modelDeletionCrossBudget d ell cutCard δ
  let K := modelDeletionLogConstant d B
  have hCref : 0 ≤ finiteReferenceConstant d := (by norm_num : (0 : ℝ) ≤ 1).trans
    (finiteReferenceConstant_ge_one d hd)
  have hCextra : 0 ≤ finiteExtraReferenceConstant d := (by norm_num : (0 : ℝ) ≤ 1).trans
    (finiteExtraReferenceConstant_ge_one d hd)
  have hC : 0 ≤ C := by
    have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
    have hk0 : 0 ≤ (d : ℝ) - 1 := by linarith
    dsimp [C, DeficientGraph.boundarySchurConstant]
    positivity
  have hD0 : 0 ≤ D0 := mul_nonneg (mul_nonneg (by norm_num) hCref)
    (outsideBallKernelConstant_nonnegative _ _)
  have hD : 0 ≤ D := by dsimp [D]; linarith
  have hL0 : 0 ≤ L := by linarith
  have hX0 : 0 ≤ X := by
    dsimp [X, modelDeletionCrossBudget]
    positivity
  have hX : X ≤ D * L := by
    have hh := mul_le_mul_of_nonneg_left hell hD0
    dsimp [X, modelDeletionCrossBudget, D, D0] at *
    nlinarith
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have honesq : (1 : ℝ) ≤ L ^ 2 := by nlinarith
  have hlinear : 3 * C * X ≤ (3 * C * D) * L ^ 2 := by
    calc
      _ ≤ (3 * C) * (D * L) := mul_le_mul_of_nonneg_left hX (by positivity)
      _ = (3 * C * D) * L := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hLsq (by positivity)
  have hquad : 2 * C ^ 2 * X ^ 2 ≤ (2 * C ^ 2 * D ^ 2) * L ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX0 hX 2) (show 0 ≤ 2 * C ^ 2 by positivity)
    convert hh using 1
    ring
  have hK0 : 0 ≤ K := by dsimp [K, modelDeletionLogConstant]; positivity
  have hcoef : modelDeletionErrorConstant d ell cutCard B δ ≤ K * L ^ 2 := by
    change 1 + 3 * C * X + 2 * C ^ 2 * X ^ 2 ≤ K * L ^ 2
    have hsum := add_le_add (add_le_add honesq hlinear) hquad
    convert hsum using 1
    dsimp [K, modelDeletionLogConstant, C, D, D0]
    ring
  calc
    _ ≤ (K * L ^ 2) * δ := mul_le_mul_of_nonneg_right hcoef hδ
    _ ≤ (K * L ^ 2) * (L * ε) := mul_le_mul_of_nonneg_left hentry (by positivity)
    _ = _ := by ring

section ModelComparison
variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] {d : ℕ}

/-- The finite-model deletion comparison underlying Proposition 5.1. The
ambient and model graphs may have different sizes. Its only approximation
input is the full Green-to-model entry approximation; all reference cross
sums, inverse cross sums, inverse stability, and deleted errors are derived. -/
theorem embedded_model_deletion_comparison (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hzero : ∀ v, g.deficit v = 0) (hG : g.graph.Connected)
    (hbudget : graphExcess g.graph ≤ finiteOmega d)
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
  let U := (green H z).submatrix e e
  let P := g.extensionGreen q z
  let C := DeficientGraph.boundarySchurConstant d B
  let L0 := 2 * finiteReferenceConstant d * outsideBallKernelConstant d (finiteOmega d) * ((ell : ℝ) + 1)
  let L := L0 + (Nat.card T : ℝ) * δ
  have hT : (g.graph.induce T).Connected := graphBall_connected g.graph o ell
  have hcomplex : (∑ v, g.deficit v) + graphExcess g.graph ≤ finiteOmega d := by
    simpa only [hzero, Finset.sum_const_zero, zero_add] using hbudget
  have hout (v : (Tᶜ : Set V)) : ell < g.graph.dist o v.val := by
    have hh : ¬g.graph.dist o v.val ≤ ell := fun hh => v.property
      ((connected_mem_graphBall_iff_dist g.graph hG o v.val ell).mpr hh)
    omega
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
  have hL : 0 ≤ L := add_nonneg hL0 (mul_nonneg (Nat.cast_nonneg _) hδ)
  have hL0L : L0 ≤ L := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hδ)
  have hProw (v : (Tᶜ : Set V)) : (∑ y : T, ‖P v.val y.val‖) ≤ L0 := by
    have hh := g.finiteOmega_outside_ball_row_sum hd hG hcomplex q z hz hq R hR smallRef o v.val ell (hout v)
    simp only [← finsum_eq_sum_of_fintype] at hh ⊢
    exact hh
  have hPcol (v : (Tᶜ : Set V)) : (∑ y : T, ‖P y.val v.val‖) ≤ L0 := by
    have hh := g.finiteOmega_outside_ball_column_sum hd hG hcomplex q z hz hq R hR smallRef o v.val ell (hout v)
    simp only [← finsum_eq_sum_of_fintype] at hh ⊢
    exact hh
  have hUcol (v : (Tᶜ : Set V)) : (∑ y : T, ‖U y.val v.val‖) ≤ L := by
    exact row_sum_perturbation
      (U.transpose.submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V))
      (P.transpose.submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V))
      v L0 δ (fun y => happrox y.val v.val) (hPcol v)
  have hbounds := g.zero_deficit_retained_inverse_bounds hd hzero T hG hT hbudget
    q z hz hq B hB hqnear Rdel hRdel smallDel
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
    (by intro x; simpa only [partitionMatrix11] using hbounds.1 x)
    (by intro y; simpa only [partitionMatrix11] using hbounds.2 y)
    (by intro v; simpa only [partitionMatrix21] using (hProw v).trans hL0L)
    (by intro v; simpa only [partitionMatrix12] using hUcol v)
    hsmall i j
  simp only [partitionMatrix22, partitionMatrix21, partitionMatrix11, partitionMatrix12] at hs
  have hUdelete := embedded_green_deleted_principal H hH z hz e T
  have hPdelete := g.extensionGreen_delete hd T q z hz hq
  rw [← hUdelete, ← hPdelete] at hs
  exact hs

end ModelComparison
end LocalLaw
