import LocalLaw.PartialVacuumBenchmark

/-! # Exact covariance of a partially retained old sample pair

Retained B/C masks can independently omit either endpoint. A matched pair has
precision m^{-1} on both diagonal entries and coupling alpha; an unmatched
endpoint has precision p^{-1}. The proved inverse has diagonal p throughout
and matching cross entry -alpha*m*p. No inverse or comparison premise is used.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance partialSampleDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {L : Type} [Fintype L] [DecidableEq L]

omit [Fintype L] in
theorem partialMatching_transpose (B C : Set L) (α : ℂ) :
    (partialMatchingCoupling B C α).transpose=partialMatchingCoupling C B α := by
  ext c b
  simp only [Matrix.transpose_apply,partialMatchingCoupling,eq_comm]

theorem partialMatching_mul (B C : Set L) (α β : ℂ) :
    partialMatchingCoupling B C α*partialMatchingCoupling C B β=
      Matrix.diagonal (fun b:B => if b.val∈C then α*β else 0) := by
  ext b b'
  simp only [Matrix.mul_apply,partialMatchingCoupling]
  by_cases hbb : b=b'
  · subst b'
    by_cases hb : b.val∈C
    · let c0 : C := ⟨b.val,hb⟩
      rw [Finset.sum_eq_single c0]
      · simp [c0,Matrix.diagonal_apply,hb]
      · intro c _ hc
        have hbc : b.val≠c.val := fun h => hc (Subtype.ext h.symm)
        simp [hbc]
      · intro h
        exact False.elim (h (Finset.mem_univ _))
    · have hbc : ∀c:C,b.val≠c.val := fun c h => hb (h.symm ▸ c.property)
      simp [hbc,Matrix.diagonal_apply,hb]
  · have hterm (c:C) : (if b.val=c.val then α else 0)*(if c.val=b'.val then β else 0)=0 := by
      by_cases hbc : b.val=c.val
      · have hcb : c.val≠b'.val := fun h => hbb (Subtype.ext (hbc.trans h))
        simp [hcb]
      · simp [hbc]
    rw [Finset.sum_eq_zero (fun c _ => hterm c)]
    simp only [Matrix.diagonal_apply,if_neg hbb]

def partialSamplePrecision (B C : Set L) (m p α : ℂ) : Matrix (B⊕C) (B⊕C) ℂ :=
  Matrix.fromBlocks (partialVacuumDiagonal C B m p) (partialMatchingCoupling B C α)
    (partialMatchingCoupling B C α).transpose (partialVacuumDiagonal B C m p)

def partialSampleCovariance (B C : Set L) (m p α : ℂ) : Matrix (B⊕C) (B⊕C) ℂ :=
  Matrix.fromBlocks (p•1) (partialMatchingCoupling B C (-α*m*p))
    (partialMatchingCoupling B C (-α*m*p)).transpose (p•1)

theorem partialSample_diagonal_product (B C : Set L) (m p α : ℂ)
    (hp : p≠0) (hrel : p⁻¹=m⁻¹-m*α^2) :
    partialVacuumDiagonal C B m p*(p•1)+
      partialMatchingCoupling B C α*partialMatchingCoupling C B (-α*m*p)=1 := by
  rw [Matrix.smul_one_eq_diagonal,partialMatching_mul]
  simp only [partialVacuumDiagonal,Matrix.diagonal_mul_diagonal,←Matrix.diagonal_add]
  ext b b'
  by_cases hbb : b=b'
  · subst b'
    simp only [Matrix.add_apply,Matrix.diagonal_apply,if_pos rfl,Matrix.one_apply,if_true,Pi.add_apply]
    by_cases hb : b.val∈C
    · simp only [if_pos hb]
      calc
        m⁻¹*p+α*(-α*m*p)=p*(m⁻¹-m*α^2) := by ring
        _=p*p⁻¹ := by rw [←hrel]
        _=1 := mul_inv_cancel₀ hp
    · simp [hb,hp]
  · simp [Matrix.diagonal_apply,Matrix.one_apply,hbb]

theorem partialSample_offdiagonal_product (B C : Set L) (m p α : ℂ)
    (hm : m≠0) :
    partialVacuumDiagonal C B m p*partialMatchingCoupling B C (-α*m*p)+
      partialMatchingCoupling B C α*(p•(1:Matrix C C ℂ))=0 := by
  rw [Matrix.smul_one_eq_diagonal]
  ext b c
  simp only [partialVacuumDiagonal,Matrix.diagonal_mul,Matrix.mul_diagonal,
    Matrix.add_apply,Matrix.zero_apply,partialMatchingCoupling]
  by_cases hbc : b.val=c.val
  · have hb : b.val∈C := hbc.symm ▸ c.property
    simp only [if_pos hbc,if_pos hb]
    have hminv := inv_mul_cancel₀ hm
    linear_combination -α*p*hminv
  · simp [hbc]

/-- The explicit old-sample benchmark is a genuine inverse for arbitrary
independent retention masks. -/
theorem partialSamplePrecision_inverse (B C : Set L) (m p α : ℂ)
    (hm : m≠0) (hp : p≠0) (hrel : p⁻¹=m⁻¹-m*α^2) :
    IsUnit (partialSamplePrecision B C m p α) ∧
      (partialSamplePrecision B C m p α)⁻¹=partialSampleCovariance B C m p α := by
  have hBB := partialSample_diagonal_product B C m p α hp hrel
  have hBC := partialSample_offdiagonal_product B C m p α hm
  have hCB : partialMatchingCoupling C B α*(p•(1:Matrix B B ℂ))+
      partialVacuumDiagonal B C m p*partialMatchingCoupling C B (-α*m*p)=0 := by
    simpa only [add_comm] using partialSample_offdiagonal_product C B m p α hm
  have hCC : partialMatchingCoupling C B α*partialMatchingCoupling B C (-α*m*p)+
      partialVacuumDiagonal B C m p*(p•1)=1 := by
    simpa only [add_comm] using partialSample_diagonal_product C B m p α hp hrel
  have hproduct : partialSamplePrecision B C m p α*partialSampleCovariance B C m p α=1 := by
    unfold partialSamplePrecision partialSampleCovariance
    rw [partialMatching_transpose,partialMatching_transpose,Matrix.fromBlocks_multiply,
      hBB,hBC,hCB,hCC,Matrix.fromBlocks_one]
  exact ⟨Matrix.isUnit_of_right_inverse hproduct,Matrix.inv_eq_right_inv hproduct⟩

omit [Fintype L] in
theorem partialSampleCovariance_diag_left (B C : Set L) (m p α : ℂ) (b:B) :
    partialSampleCovariance B C m p α (Sum.inl b) (Sum.inl b)=p := by
  simp [partialSampleCovariance,Matrix.smul_apply,Matrix.one_apply]

omit [Fintype L] in
theorem partialSampleCovariance_diag_right (B C : Set L) (m p α : ℂ) (c:C) :
    partialSampleCovariance B C m p α (Sum.inr c) (Sum.inr c)=p := by
  simp [partialSampleCovariance,Matrix.smul_apply,Matrix.one_apply]

omit [Fintype L] in
theorem partialSampleCovariance_cross (B C : Set L) (m p α : ℂ) (b:B) (c:C) :
    partialSampleCovariance B C m p α (Sum.inl b) (Sum.inr c)=
      if b.val=c.val then -α*m*p else 0 := rfl

end LocalLaw
