import LocalLaw.LeafSchurModel
import LocalLaw.BlockSchurRows

/-! # Remaining-leaf rows after an actual leaf Schur deletion

The core may itself contain kept leaf slots.  Deleting only the scalar
covariance block preserves constant target-to-kept-leaf row sums, and its
core kernel inherits decay up to the controlled scalar covariance error.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance leafSchurRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Scalar
variable {L : Type} [Fintype L] [DecidableEq L]

theorem scalar_diagonal_inverse_row_col_bound (R : Matrix L L ℂ) (p : ℂ) (hp : p≠0)
    (hR : IsUnit R) (δ : ℝ) (hδ : 0≤δ)
    (herror : ∀i j,‖R i j-(if i=j then p else 0)‖≤δ)
    (hsmall : (Fintype.card L:ℝ)*‖p⁻¹‖*δ≤1/2) :
    (∀i,∑j,‖R⁻¹ i j‖≤2*‖p⁻¹‖) ∧ (∀j,∑i,‖R⁻¹ i j‖≤2*‖p⁻¹‖) := by
  have hi:=scalar_diagonal_inverse_stability R p hp hR δ hδ herror hsmall
  have he (i j : L) : ‖R⁻¹ i j‖≤(if i=j then ‖p⁻¹‖ else 0)+2*‖p⁻¹‖^2*δ := by
    calc
      _≤‖(if i=j then p⁻¹ else 0)‖+‖R⁻¹ i j-(if i=j then p⁻¹ else 0)‖ := by
        convert norm_add_le (if i=j then p⁻¹ else 0) (R⁻¹ i j-(if i=j then p⁻¹ else 0)) using 1
        congr 1
        ring
      _≤_ := by simpa only [apply_ite norm,norm_zero] using add_le_add_left (hi i j) ‖(if i=j then p⁻¹ else 0)‖
  have hs : (Fintype.card L:ℝ)*(2*‖p⁻¹‖^2*δ)≤‖p⁻¹‖ := by
    have hh:=mul_le_mul_of_nonneg_left hsmall (show 0≤2*‖p⁻¹‖ by positivity)
    nlinarith only [hh]
  constructor
  · intro i
    calc
      _≤∑j:L,((if i=j then ‖p⁻¹‖ else 0)+2*‖p⁻¹‖^2*δ) := Finset.sum_le_sum (fun j _=>he i j)
      _=‖p⁻¹‖+(Fintype.card L:ℝ)*(2*‖p⁻¹‖^2*δ) := by simp [Finset.sum_add_distrib]
      _≤_ := by linarith
  · intro j
    calc
      _≤∑i:L,((if i=j then ‖p⁻¹‖ else 0)+2*‖p⁻¹‖^2*δ) := Finset.sum_le_sum (fun i _=>he i j)
      _=‖p⁻¹‖+(Fintype.card L:ℝ)*(2*‖p⁻¹‖^2*δ) := by simp [Finset.sum_add_distrib]
      _≤_ := by linarith

end Scalar

section Core
variable {K L J : Type} [Fintype K] [Fintype L] [Fintype J] [DecidableEq K] [DecidableEq L]

/-- Remaining core columns need not be every core vertex. -/
theorem core_inverse_remaining_row_bound (M : Matrix (K⊕L) (K⊕L) ℂ)
    (hM : IsUnit M) (hc : IsUnit M.toBlocks₁₁) (e : J→K)
    (U A B D : ℝ) (hB : 0≤B) (hD : 0≤D)
    (hbase : ∀i,∑j:J,‖M⁻¹ (.inl i) (.inl (e j))‖≤U)
    (hcross : ∀i,∑l:L,‖M⁻¹ (.inl i) (.inr l)‖≤A)
    (hremaining : ∀l,∑j:J,‖M⁻¹ (.inr l) (.inl (e j))‖≤B)
    (hleaf : ∀l,∑k:L,‖(M⁻¹).toBlocks₂₂⁻¹ l k‖≤D) :
    ∀i,∑j:J,‖M.toBlocks₁₁⁻¹ i (e j)‖≤U+A*D*B := by
  let X:Matrix L J ℂ:=fun l j=>M⁻¹ (.inr l) (.inl (e j))
  have hDX : ∀l,∑j:J,‖((M⁻¹).toBlocks₂₂⁻¹*X) l j‖≤D*B :=
    rectangular_product_row_sum_bound _ X D B hB hleaf hremaining
  have hCDX : ∀i,∑j:J,‖((M⁻¹).toBlocks₁₂*((M⁻¹).toBlocks₂₂⁻¹*X)) i j‖≤A*(D*B) :=
    rectangular_product_row_sum_bound _ _ A (D*B) (mul_nonneg hD hB) hcross hDX
  intro i
  have hident:=core_inverse_leaf_schur M hM hc
  have he (j:J) : M.toBlocks₁₁⁻¹ i (e j)=M⁻¹ (.inl i) (.inl (e j))-
      ((M⁻¹).toBlocks₁₂*((M⁻¹).toBlocks₂₂⁻¹*X)) i j := by
    have hh:=congrArg (fun P:Matrix K K ℂ=>P i (e j)) hident.2
    rw [Matrix.mul_assoc] at hh
    simpa only [Matrix.sub_apply,Matrix.mul_apply,Matrix.toBlocks₁₁,Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₁,Matrix.of_apply,X] using hh
  calc
    _≤∑j:J,(‖M⁻¹ (.inl i) (.inl (e j))‖+‖((M⁻¹).toBlocks₁₂*((M⁻¹).toBlocks₂₂⁻¹*X)) i j‖) := by
      apply Finset.sum_le_sum
      intro j _
      rw [he j]
      exact norm_sub_le _ _
    _=(∑j:J,‖M⁻¹ (.inl i) (.inl (e j))‖)+∑j:J,‖((M⁻¹).toBlocks₁₂*((M⁻¹).toBlocks₂₂⁻¹*X)) i j‖ :=
      Finset.sum_add_distrib
    _≤U+A*(D*B) := add_le_add (hbase i) (hCDX i)
    _=U+A*D*B := by ring

theorem core_inverse_scalar_leaf_remaining_rows (M : Matrix (K⊕L) (K⊕L) ℂ)
    (hM : IsUnit M) (hc : IsUnit M.toBlocks₁₁) (e : J→K) (p : ℂ) (hp : p≠0)
    (δ U A B : ℝ) (hδ : 0≤δ) (hB : 0≤B)
    (herror : ∀l k:L,‖M⁻¹ (.inr l) (.inr k)-(if l=k then p else 0)‖≤δ)
    (hsmall : (Fintype.card L:ℝ)*‖p⁻¹‖*δ≤1/2)
    (hbase : ∀i,∑j:J,‖M⁻¹ (.inl i) (.inl (e j))‖≤U)
    (hcross : ∀i,∑l:L,‖M⁻¹ (.inl i) (.inr l)‖≤A)
    (hremaining : ∀l,∑j:J,‖M⁻¹ (.inr l) (.inl (e j))‖≤B) :
    ∀i,∑j:J,‖M.toBlocks₁₁⁻¹ i (e j)‖≤U+2*A*‖p⁻¹‖*B := by
  have hi:=scalar_diagonal_inverse_row_col_bound (M⁻¹).toBlocks₂₂ p hp
    (core_inverse_leaf_schur M hM hc).1 δ hδ herror hsmall
  intro i
  have hh:=core_inverse_remaining_row_bound M hM hc e U A B (2*‖p⁻¹‖) hB (by positivity)
    hbase hcross hremaining hi.1 i
  convert hh using 1
  ring

omit [Fintype L] [DecidableEq L] in
/-- Symmetry transfers any retained remaining-row estimate to columns. -/
theorem core_inverse_remaining_columns_of_rows (M : Matrix (K⊕L) (K⊕L) ℂ)
    (hs : M.IsSymm) (e : J→K) (C : ℝ)
    (hrows : ∀i,∑j:J,‖M.toBlocks₁₁⁻¹ i (e j)‖≤C) :
    ∀i,∑j:J,‖M.toBlocks₁₁⁻¹ (e j) i‖≤C := by
  have hcore : M.toBlocks₁₁.IsSymm := hs.submatrix Sum.inl
  have hi : (M.toBlocks₁₁⁻¹).IsSymm := by
    change (M.toBlocks₁₁⁻¹).transpose=M.toBlocks₁₁⁻¹
    rw [Matrix.transpose_nonsing_inv,hcore.eq]
  intro i
  simpa only [hi.apply] using hrows i

theorem core_inverse_leaf_entry_bound (M : Matrix (K⊕L) (K⊕L) ℂ)
    (hM : IsUnit M) (hc : IsUnit M.toBlocks₁₁) (i j : K) (p : ℂ)
    (σ A B X Y : ℝ) (hσ : 0≤σ) (hA : 0≤A) (hB : 0≤B)
    (ha : (∑l:L,‖M⁻¹ (.inl i) (.inr l)‖)≤A)
    (hb : (∑l:L,‖M⁻¹ (.inr l) (.inl j)‖)≤B)
    (herror : ∀l k:L,‖(M⁻¹).toBlocks₂₂⁻¹ l k-(if l=k then p⁻¹ else 0)‖≤σ)
    (hbase : ‖M⁻¹ (.inl i) (.inl j)‖≤X)
    (hproducts : (∑l:L,‖M⁻¹ (.inl i) (.inr l)*M⁻¹ (.inr l) (.inl j)‖)≤Y) :
    ‖M.toBlocks₁₁⁻¹ i j‖≤X+‖p⁻¹‖*Y+σ*A*B := by
  let a:L→ℂ:=fun l=>M⁻¹ (.inl i) (.inr l)
  let b:L→ℂ:=fun l=>M⁻¹ (.inr l) (.inl j)
  let R:Matrix L L ℂ:=(M⁻¹).toBlocks₂₂
  have hcorr:=diagonal_schur_correction_bound a b R p σ A B hσ hA hB ha hb herror
  have hsum : ‖p⁻¹*∑l:L,a l*b l‖≤‖p⁻¹‖*Y := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans hproducts) (norm_nonneg _)
  have hcorrnorm : ‖schurBilinear a R⁻¹ b‖≤‖p⁻¹‖*Y+σ*A*B := by
    calc
      _≤‖p⁻¹*∑l:L,a l*b l‖+‖schurBilinear a R⁻¹ b-p⁻¹*∑l:L,a l*b l‖ := by
        convert norm_add_le (p⁻¹*∑l:L,a l*b l) (schurBilinear a R⁻¹ b-p⁻¹*∑l:L,a l*b l) using 1
        congr 1
        ring
      _≤_ := add_le_add hsum hcorr
  rw [core_inverse_leaf_schur_bilinear M hM hc i j]
  exact (norm_sub_le _ _).trans ((add_le_add hbase hcorrnorm).trans_eq (by ring))

theorem core_inverse_scalar_leaf_decay (M : Matrix (K⊕L) (K⊕L) ℂ)
    (hM : IsUnit M) (hc : IsUnit M.toBlocks₁₁) (i j : K) (p : ℂ)
    (σ A B C T ρ : ℝ) (hσ : 0≤σ) (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hρ : 0≤ρ)
    (D : ℕ) (di dj : L→ℕ)
    (ha : (∑l:L,‖M⁻¹ (.inl i) (.inr l)‖)≤A)
    (hb : (∑l:L,‖M⁻¹ (.inr l) (.inl j)‖)≤B)
    (herror : ∀l k:L,‖(M⁻¹).toBlocks₂₂⁻¹ l k-(if l=k then p⁻¹ else 0)‖≤σ)
    (hbase : ‖M⁻¹ (.inl i) (.inl j)‖≤C*ρ^D)
    (hfirst : ∀l,‖M⁻¹ (.inl i) (.inr l)‖≤C*ρ^(di l))
    (hsecond : ∀l,‖M⁻¹ (.inr l) (.inl j)‖≤C*ρ^(dj l))
    (hconvolution : (∑l:L,ρ^(di l+dj l))≤T*ρ^D) :
    ‖M.toBlocks₁₁⁻¹ i j‖≤(C+‖p⁻¹‖*C^2*T)*ρ^D+σ*A*B := by
  have hproducts : (∑l:L,‖M⁻¹ (.inl i) (.inr l)*M⁻¹ (.inr l) (.inl j)‖)≤C^2*T*ρ^D := by
    calc
      _≤∑l:L,(C*ρ^(di l))*(C*ρ^(dj l)) := by
        apply Finset.sum_le_sum
        intro l _
        rw [norm_mul]
        exact mul_le_mul (hfirst l) (hsecond l) (norm_nonneg _) (mul_nonneg hC (pow_nonneg hρ _))
      _=C^2*∑l:L,ρ^(di l+dj l) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        rw [pow_add]
        ring
      _≤C^2*(T*ρ^D) := mul_le_mul_of_nonneg_left hconvolution (sq_nonneg _)
      _=C^2*T*ρ^D := by ring
  have hh:=core_inverse_leaf_entry_bound M hM hc i j p σ A B (C*ρ^D) (C^2*T*ρ^D)
    hσ hA hB ha hb herror hbase hproducts
  convert hh using 1
  ring

end Core
end LocalLaw
