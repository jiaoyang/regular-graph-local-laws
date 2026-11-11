import LocalLaw.PartialVacuumRows
import LocalLaw.PartialSampleBenchmark

/-! # Exact partial-triple vacuum surgery

The retained masks are independent. Removing B--C, inserting A--B and
including the missing-neighbor diagonal charges isolates every retained C
vertex with cavity value m. Eliminating B restores one deficit at every A.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance partialTripleDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {L : Type} [Fintype L] [DecidableEq L]

def partialTripleOldPrecision (A B C : Set L) (A₀ : Matrix A A ℂ) (m p α : ℂ) :
    Matrix (A ⊕ (B ⊕ C)) (A ⊕ (B ⊕ C)) ℂ :=
  Matrix.fromBlocks A₀ 0 0 (partialSamplePrecision B C m p α)

def partialTripleCharge (A B C : Set L) (m α : ℂ) :
    Matrix (A ⊕ (B ⊕ C)) (A ⊕ (B ⊕ C)) ℂ :=
  Matrix.diagonal (fun u => match u with
    | .inl a => if a.val∈B then 0 else -m*α^2
    | .inr (.inl b) => -m*α^2*((if b.val∈C then 1 else 0)-(if b.val∈A then 1 else 0))
    | .inr (.inr c) => if c.val∈B then 0 else m*α^2)

def partialTripleEdgeUpdate (A B C : Set L) (α : ℂ) :
    Matrix (A ⊕ (B ⊕ C)) (A ⊕ (B ⊕ C)) ℂ :=
  fun u v => match u,v with
    | .inl a,.inr (.inl b) => partialMatchingCoupling A B α a b
    | .inr (.inl b),.inl a => partialMatchingCoupling B A α b a
    | .inr (.inl b),.inr (.inr c) => -partialMatchingCoupling B C α b c
    | .inr (.inr c),.inr (.inl b) => -partialMatchingCoupling C B α c b
    | _,_ => 0

def partialTripleNewPrecision (A B C : Set L) (A₀ : Matrix A A ℂ) (m p α : ℂ) :
    Matrix (A ⊕ (B ⊕ C)) (A ⊕ (B ⊕ C)) ℂ :=
  (Matrix.fromBlocks
    (Matrix.fromBlocks (A₀-partialMissingCharge A B m α)
      (partialMatchingCoupling A B α) (partialMatchingCoupling A B α).transpose
      (partialVacuumDiagonal A B m p)) 0 0 (Matrix.diagonal (fun _:C=>m⁻¹))).submatrix
    (Equiv.sumAssoc A B C).symm (Equiv.sumAssoc A B C).symm

omit [Fintype L] in
theorem partialTriple_precision_update (A B C : Set L) (A₀ : Matrix A A ℂ) (m p α : ℂ)
    (hrel:p⁻¹=m⁻¹-m*α^2) :
    partialTripleNewPrecision A B C A₀ m p α=
      partialTripleOldPrecision A B C A₀ m p α+
        partialTripleEdgeUpdate A B C α+partialTripleCharge A B C m α := by
  ext u v
  rcases u with a | (b | c) <;> rcases v with a' | (b' | c')
  all_goals simp only [partialTripleNewPrecision,partialTripleOldPrecision,
    partialTripleEdgeUpdate,partialTripleCharge,partialMissingCharge,partialSamplePrecision,
    partialVacuumDiagonal,Matrix.submatrix_apply,Equiv.sumAssoc_symm_apply_inl,Equiv.sumAssoc_symm_apply_inr_inl,
    Equiv.sumAssoc_symm_apply_inr_inr,
    Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂,Matrix.add_apply,Matrix.sub_apply,Matrix.diagonal_apply,
    Matrix.zero_apply,Matrix.transpose_apply,partialMatchingCoupling]
  all_goals first | rfl | simp only [Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq,if_false,add_zero,zero_add,sub_zero]
  all_goals try { split_ifs <;> simp_all [hrel] <;> ring }

theorem blockDiagonal_inverse {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Matrix I I ℂ) (D : Matrix J J ℂ) (hA:IsUnit A) (hD:IsUnit D) :
    IsUnit (Matrix.fromBlocks A 0 0 D) ∧
      (Matrix.fromBlocks A 0 0 D)⁻¹=Matrix.fromBlocks A⁻¹ 0 0 D⁻¹ := by
  have hprod : Matrix.fromBlocks A 0 0 D*Matrix.fromBlocks A⁻¹ 0 0 D⁻¹=1 := by
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA),
      Matrix.mul_nonsing_inv D ((Matrix.isUnit_iff_isUnit_det D).mp hD),Matrix.fromBlocks_one]
  exact ⟨Matrix.isUnit_of_right_inverse hprod,Matrix.inv_eq_right_inv hprod⟩

theorem partialTripleNewPrecision_inverse_rows (A B C : Set L) (A₀ : Matrix A A ℂ) (m p α : ℂ)
    (hm:m≠0) (hp:p≠0) (hmnorm:‖m‖≤1) (hpnorm:‖p‖≤2) (ha:‖α*m‖≤1)
    (K:ℝ) (hK:0≤K)
    (hrestored:IsUnit (A₀-Matrix.diagonal (fun _:A=>m*α^2)))
    (hrows:∀ a,∑ a',‖(A₀-Matrix.diagonal (fun _:A=>m*α^2))⁻¹ a a'‖≤K) :
    IsUnit (partialTripleNewPrecision A B C A₀ m p α) ∧
      ∀ u,∑ v,‖(partialTripleNewPrecision A B C A₀ m p α)⁻¹ u v‖≤2+2*K := by
  let M:=Matrix.fromBlocks (A₀-partialMissingCharge A B m α)
    (partialMatchingCoupling A B α) (partialMatchingCoupling A B α).transpose
    (partialVacuumDiagonal A B m p)
  have hM:IsUnit M:=(partialVacuum_schur A B A₀ m p α hm hp hrestored).1
  let D:Matrix C C ℂ:=Matrix.diagonal (fun _=>m⁻¹)
  have hDprod : D*Matrix.diagonal (fun _:C=>m)=1 := by
    ext c c'
    by_cases hc:c=c' <;> simp [D,Matrix.diagonal_apply,Matrix.mul_apply,Matrix.one_apply,hc,hm]
  have hD:IsUnit D:=Matrix.isUnit_of_right_inverse hDprod
  have hDinv : D⁻¹=Matrix.diagonal (fun _:C=>m):=Matrix.inv_eq_right_inv hDprod
  have hfull:=blockDiagonal_inverse M D hM hD
  let e:= (Equiv.sumAssoc A B C).symm
  have hnew : partialTripleNewPrecision A B C A₀ m p α=(Matrix.fromBlocks M 0 0 D).submatrix e e:=rfl
  constructor
  · rw [hnew]
    exact (Matrix.isUnit_submatrix_equiv e e).mpr hfull.1
  · intro u
    rw [hnew,Matrix.inv_submatrix_equiv,hfull.2]
    have heq : (∑ v,‖(Matrix.fromBlocks M⁻¹ 0 0 D⁻¹).submatrix e e u v‖)=
        ∑ v,‖Matrix.fromBlocks M⁻¹ 0 0 D⁻¹ (e u) v‖ := by
      exact e.sum_comp (fun v=>‖Matrix.fromBlocks M⁻¹ 0 0 D⁻¹ (e u) v‖)
    rw [heq]
    rcases e u with a | c
    · simpa only [Fintype.sum_sum_type,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
        Matrix.zero_apply,norm_zero,Finset.sum_const_zero,add_zero] using
        partialVacuum_inverse_rows A B A₀ m p α hm hp hmnorm hpnorm ha K hK hrestored hrows a
    · rw [Fintype.sum_sum_type,hDinv]
      simp only [Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,
        norm_zero,Finset.sum_const_zero,zero_add]
      have hh : (∑ v:C,‖Matrix.diagonal (fun _:C=>m) c v‖)=‖m‖ := by
        simp [Matrix.diagonal_apply,apply_ite norm]
      rw [hh]
      linarith

end LocalLaw
