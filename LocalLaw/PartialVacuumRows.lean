import LocalLaw.PartialVacuumBenchmark
import LocalLaw.BlockSchurRows

/-! Uniform full benchmark rows from the deficit-restored old core. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance partialVacuumRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {L : Type} [Fintype L] [DecidableEq L]

theorem partialMatching_row_sum (A B : Set L) (α : ℂ) (a:A) :
    (∑ b:B,‖partialMatchingCoupling A B α a b‖)≤‖α‖ := by
  by_cases ha:a.val∈B
  · let b0:B:=⟨a.val,ha⟩
    have hh : (∑ b:B,‖partialMatchingCoupling A B α a b‖)=‖α‖ := by
      rw [Finset.sum_eq_single b0]
      · simp [partialMatchingCoupling,b0]
      · intro b _ hbb
        have hn:a.val≠b.val:=fun h=>hbb (Subtype.ext h.symm)
        simp [partialMatchingCoupling,hn]
      · intro hn;exact False.elim (hn (Finset.mem_univ _))
    exact hh.le
  · have hn:∀ b:B,a.val≠b.val:=fun b h=>ha (h.symm ▸ b.property)
    simp only [partialMatchingCoupling,if_neg (hn _),norm_zero,Finset.sum_const_zero]
    exact norm_nonneg _

theorem partialMatching_vacuum_products (A B : Set L) (m p α : ℂ) :
    partialMatchingCoupling A B α*partialVacuumInverse A B m p=partialMatchingCoupling A B (α*m) ∧
      partialVacuumInverse A B m p*(partialMatchingCoupling A B α).transpose=partialMatchingCoupling B A (α*m) := by
  constructor
  · ext a b
    simp only [partialVacuumInverse,Matrix.mul_diagonal,partialMatchingCoupling]
    by_cases hab:a.val=b.val
    · have hb:b.val∈A:=hab ▸ a.property
      simp [hab,hb]
    · simp [hab]
  · ext b a
    simp only [partialVacuumInverse,Matrix.diagonal_mul,Matrix.transpose_apply,partialMatchingCoupling]
    by_cases hab:a.val=b.val
    · have hb:b.val∈A:=hab ▸ a.property
      simp [hab,hb]
      ring
    · have hba:b.val≠a.val:=Ne.symm hab
      simp [hab,hba]

/-- The physical partial-switch benchmark is uniformly bounded on the
whole retained A/B block. The number of retained sampled leaves does not
enter the row constant. -/
theorem partialVacuum_inverse_rows (A B : Set L) (A₀ : Matrix A A ℂ) (m p α : ℂ)
    (hm:m≠0) (hp:p≠0) (hmnorm:‖m‖≤1) (hpnorm:‖p‖≤2) (ha:‖α*m‖≤1)
    (C:ℝ) (hC:0≤C)
    (hrestored:IsUnit (A₀-Matrix.diagonal (fun _:A=>m*α^2)))
    (hrows:∀ a,∑ a',‖(A₀-Matrix.diagonal (fun _:A=>m*α^2))⁻¹ a a'‖≤C) :
    let E:=partialMatchingCoupling A B α
    let M:=Matrix.fromBlocks (A₀-partialMissingCharge A B m α) E E.transpose (partialVacuumDiagonal A B m p)
    ∀ u,∑ v,‖M⁻¹ u v‖≤2+2*C := by
  dsimp only
  let E:=partialMatchingCoupling A B α
  let D:=partialVacuumDiagonal A B m p
  let M:=Matrix.fromBlocks (A₀-partialMissingCharge A B m α) E E.transpose D
  have hv:=partialVacuum_schur A B A₀ m p α hm hp hrestored
  have hM:IsUnit M:=hv.1
  obtain ⟨hD,hDinv⟩:=partialVacuumDiagonal_inverse A B m p hm hp
  have hS : ∀ a,∑ a',‖(blockSchur M)⁻¹ a a'‖≤C := by
    rw [←inverse_block11 M hM hD,hv.2]
    exact hrows
  have hDrows : ∀ b,∑ b',‖D⁻¹ b b'‖≤(2:ℝ) := by
    intro b
    rw [hDinv]
    have hh : (∑ b',‖partialVacuumInverse A B m p b b'‖)=‖if b.val∈A then m else p‖ := by
      simp [partialVacuumInverse,Matrix.diagonal_apply,apply_ite norm]
    rw [hh]
    split_ifs
    · exact hmnorm.trans (by norm_num)
    · exact hpnorm
  have products:=partialMatching_vacuum_products A B m p α
  have hLeft : ∀ a,∑ b,‖(M.toBlocks₁₂*M.toBlocks₂₂⁻¹) a b‖≤‖α*m‖ := by
    change ∀ a,∑ b,‖(E*D⁻¹) a b‖≤‖α*m‖
    rw [hDinv,products.1]
    exact partialMatching_row_sum A B (α*m)
  have hRight : ∀ b,∑ a,‖(M.toBlocks₂₂⁻¹*M.toBlocks₂₁) b a‖≤‖α*m‖ := by
    change ∀ b,∑ a,‖(D⁻¹*E.transpose) b a‖≤‖α*m‖
    rw [hDinv,products.2]
    exact partialMatching_row_sum B A (α*m)
  exact block_inverse_row_sum_bound M hM hD C 2 ‖α*m‖ hC (by norm_num) (norm_nonneg _) ha
    hS hDrows hLeft hRight

/-- Symmetry supplies the matching column bound; no extra inverse estimate
is assumed. -/
theorem partialVacuum_inverse_columns (A B : Set L) (A₀ : Matrix A A ℂ) (m p α : ℂ)
    (hsym:A₀.IsSymm) (hm:m≠0) (hp:p≠0) (hmnorm:‖m‖≤1) (hpnorm:‖p‖≤2) (ha:‖α*m‖≤1)
    (C:ℝ) (hC:0≤C)
    (hrestored:IsUnit (A₀-Matrix.diagonal (fun _:A=>m*α^2)))
    (hrows:∀ a,∑ a',‖(A₀-Matrix.diagonal (fun _:A=>m*α^2))⁻¹ a a'‖≤C) :
    let E:=partialMatchingCoupling A B α
    let M:=Matrix.fromBlocks (A₀-partialMissingCharge A B m α) E E.transpose (partialVacuumDiagonal A B m p)
    ∀ v,∑ u,‖M⁻¹ u v‖≤2+2*C := by
  dsimp only
  let E:=partialMatchingCoupling A B α
  let M:=Matrix.fromBlocks (A₀-partialMissingCharge A B m α) E E.transpose (partialVacuumDiagonal A B m p)
  have hM:M.transpose=M := by
    change A₀.transpose=A₀ at hsym
    simp only [M,Matrix.fromBlocks_transpose,Matrix.transpose_sub,partialMissingCharge,
      partialVacuumDiagonal,Matrix.diagonal_transpose,Matrix.transpose_transpose,hsym]
  have hQ:(M⁻¹).IsSymm := by
    change (M⁻¹).transpose=M⁻¹
    rw [Matrix.transpose_nonsing_inv,hM]
  intro v
  have heq : (∑ u,‖M⁻¹ u v‖)=∑ u,‖M⁻¹ v u‖ := Finset.sum_congr rfl (fun u _=>congrArg norm (hQ.apply v u))
  rw [heq]
  exact partialVacuum_inverse_rows A B A₀ m p α hm hp hmnorm hpnorm ha C hC hrestored hrows v

end LocalLaw
