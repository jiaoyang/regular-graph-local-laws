import LocalLaw.PartialVacuumNearRows

/-! # Partial ABC vacuum with an independently retained inner-endpoint mask

The L mask records which original inner endpoints remain. Eliminating B
restores exactly the genuine A deficits indexed by L, while a detached C
has diagonal q inverse or p inverse according to that same mask.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance partialLMaskVacuumDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {L : Type} [Fintype L] [DecidableEq L]

def partialLMaskShift (A Lmask : Set L) (q α : ℂ) : Matrix A A ℂ :=
  Matrix.diagonal (fun a=>if a.val∈Lmask then 0 else q*α^2)

def partialLMaskRestoration (A Lmask : Set L) (q α : ℂ) : Matrix A A ℂ :=
  Matrix.diagonal (fun a=>if a.val∈Lmask then q*α^2 else 0)

omit [Fintype L] in
theorem partialLMask_shift_sub (A Lmask : Set L) (A0 : Matrix A A ℂ) (q α : ℂ) :
    A0+partialLMaskShift A Lmask q α-Matrix.diagonal (fun _:A=>q*α^2)=
      A0-partialLMaskRestoration A Lmask q α := by
  ext a b
  by_cases hab:a=b
  · subst b
    by_cases ha:a.val∈Lmask <;>
      simp [partialLMaskShift,partialLMaskRestoration,Matrix.add_apply,Matrix.sub_apply,ha]
  · simp [partialLMaskShift,partialLMaskRestoration,Matrix.diagonal_apply,Matrix.add_apply,Matrix.sub_apply,hab]

def partialLMaskCPrecision (C Lmask : Set L) (q p : ℂ) : Matrix C C ℂ :=
  Matrix.diagonal (fun c=>if c.val∈Lmask then q⁻¹ else p⁻¹)

def partialLMaskCInverse (C Lmask : Set L) (q p : ℂ) : Matrix C C ℂ :=
  Matrix.diagonal (fun c=>if c.val∈Lmask then q else p)

theorem partialLMaskC_inverse (C Lmask : Set L) (q p : ℂ) (hq : q≠0) (hp : p≠0) :
    IsUnit (partialLMaskCPrecision C Lmask q p) ∧
      (partialLMaskCPrecision C Lmask q p)⁻¹=partialLMaskCInverse C Lmask q p := by
  have hprod : partialLMaskCPrecision C Lmask q p*partialLMaskCInverse C Lmask q p=1 := by
    unfold partialLMaskCPrecision partialLMaskCInverse
    rw [Matrix.diagonal_mul_diagonal]
    have hf : (fun c:C=>(if c.val∈Lmask then q⁻¹ else p⁻¹)*(if c.val∈Lmask then q else p))=(fun _:C=>(1:ℂ)) := by
      funext c
      by_cases hc:c.val∈Lmask <;> simp [hc,hq,hp]
    rw [hf,Matrix.diagonal_one]
  exact ⟨Matrix.isUnit_of_right_inverse hprod,Matrix.inv_eq_right_inv hprod⟩

def partialLMaskNewPrecision (A B C Lmask : Set L) (A0 : Matrix A A ℂ) (q p α : ℂ) :
    Matrix (A⊕(B⊕C)) (A⊕(B⊕C)) ℂ :=
  (Matrix.fromBlocks
    (Matrix.fromBlocks (A0+partialLMaskShift A Lmask q α-partialMissingCharge A B q α)
      (partialMatchingCoupling A B α) (partialMatchingCoupling A B α).transpose
      (partialVacuumDiagonal A B q p)) 0 0 (partialLMaskCPrecision C Lmask q p)).submatrix
    (Equiv.sumAssoc A B C).symm (Equiv.sumAssoc A B C).symm

theorem partialLMaskNewPrecision_schur (A B C Lmask : Set L) (A0 : Matrix A A ℂ) (q p α : ℂ)
    (hq : q≠0) (hp : p≠0) (hrestored : IsUnit (A0-partialLMaskRestoration A Lmask q α)) :
    IsUnit (partialLMaskNewPrecision A B C Lmask A0 q p α) ∧
      ((partialLMaskNewPrecision A B C Lmask A0 q p α)⁻¹).submatrix Sum.inl Sum.inl=
        (A0-partialLMaskRestoration A Lmask q α)⁻¹ := by
  let Ashift:=A0+partialLMaskShift A Lmask q α
  have hs : Ashift-Matrix.diagonal (fun _:A=>q*α^2)=A0-partialLMaskRestoration A Lmask q α :=
    partialLMask_shift_sub A Lmask A0 q α
  have hr : IsUnit (Ashift-Matrix.diagonal (fun _:A=>q*α^2)) := hs ▸ hrestored
  let M:=Matrix.fromBlocks (Ashift-partialMissingCharge A B q α)
    (partialMatchingCoupling A B α) (partialMatchingCoupling A B α).transpose (partialVacuumDiagonal A B q p)
  have hv:=partialVacuum_schur A B Ashift q p α hq hp hr
  have hd:=partialLMaskC_inverse C Lmask q p hq hp
  have hf:=blockDiagonal_inverse M (partialLMaskCPrecision C Lmask q p) hv.1 hd.1
  let e:=(Equiv.sumAssoc A B C).symm
  have hnew : partialLMaskNewPrecision A B C Lmask A0 q p α=
      (Matrix.fromBlocks M 0 0 (partialLMaskCPrecision C Lmask q p)).submatrix e e := rfl
  have hi : (partialLMaskNewPrecision A B C Lmask A0 q p α)⁻¹=
      (Matrix.fromBlocks M⁻¹ 0 0 (partialLMaskCPrecision C Lmask q p)⁻¹).submatrix e e := by
    rw [hnew,Matrix.inv_submatrix_equiv,hf.2]
  refine ⟨(Matrix.isUnit_submatrix_equiv e e).mpr hf.1,?_⟩
  ext a b
  rw [hi]
  have hh:=congrArg (fun N:Matrix A A ℂ=>N a b) hv.2
  rw [hs] at hh
  exact hh

theorem partialLMaskNewPrecision_inverse_rows (A B C Lmask : Set L) (A0 : Matrix A A ℂ) (q p α : ℂ)
    (hq : q≠0) (hp : p≠0) (P K : ℝ) (hP : 0≤P) (hK : 0≤K)
    (hqnorm : ‖q‖≤P) (hpnorm : ‖p‖≤P) (ha : ‖α*q‖≤1)
    (hrestored : IsUnit (A0-partialLMaskRestoration A Lmask q α))
    (hrows : ∀a,∑a',‖(A0-partialLMaskRestoration A Lmask q α)⁻¹ a a'‖≤K) :
    IsUnit (partialLMaskNewPrecision A B C Lmask A0 q p α) ∧
      ∀u,∑v,‖(partialLMaskNewPrecision A B C Lmask A0 q p α)⁻¹ u v‖≤P+2*K := by
  let Ashift:=A0+partialLMaskShift A Lmask q α
  have hs : Ashift-Matrix.diagonal (fun _:A=>q*α^2)=A0-partialLMaskRestoration A Lmask q α :=
    partialLMask_shift_sub A Lmask A0 q α
  have hr : IsUnit (Ashift-Matrix.diagonal (fun _:A=>q*α^2)) := hs ▸ hrestored
  have hrows' : ∀a,∑a',‖(Ashift-Matrix.diagonal (fun _:A=>q*α^2))⁻¹ a a'‖≤K := by rw [hs];exact hrows
  let M:=Matrix.fromBlocks (Ashift-partialMissingCharge A B q α)
    (partialMatchingCoupling A B α) (partialMatchingCoupling A B α).transpose (partialVacuumDiagonal A B q p)
  have hM : IsUnit M := (partialVacuum_schur A B Ashift q p α hq hp hr).1
  have hd:=partialLMaskC_inverse C Lmask q p hq hp
  have hf:=blockDiagonal_inverse M (partialLMaskCPrecision C Lmask q p) hM hd.1
  let e:=(Equiv.sumAssoc A B C).symm
  have hnew : partialLMaskNewPrecision A B C Lmask A0 q p α=
      (Matrix.fromBlocks M 0 0 (partialLMaskCPrecision C Lmask q p)).submatrix e e := rfl
  refine ⟨(Matrix.isUnit_submatrix_equiv e e).mpr hf.1,?_⟩
  intro u
  rw [hnew,Matrix.inv_submatrix_equiv,hf.2]
  have heq : (∑v,‖(Matrix.fromBlocks M⁻¹ 0 0 (partialLMaskCPrecision C Lmask q p)⁻¹).submatrix e e u v‖)=
      ∑v,‖Matrix.fromBlocks M⁻¹ 0 0 (partialLMaskCPrecision C Lmask q p)⁻¹ (e u) v‖ :=
    e.sum_comp (fun v=>‖Matrix.fromBlocks M⁻¹ 0 0 (partialLMaskCPrecision C Lmask q p)⁻¹ (e u) v‖)
  rw [heq]
  rcases e u with a|c
  · simpa only [Fintype.sum_sum_type,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
      Matrix.zero_apply,norm_zero,Finset.sum_const_zero,add_zero] using
      partialVacuum_inverse_rows_cap A B Ashift q p α hq hp P hP hqnorm hpnorm ha K hK hr hrows' a
  · rw [Fintype.sum_sum_type,hd.2]
    simp only [Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,
      norm_zero,Finset.sum_const_zero,zero_add]
    have hh : (∑c',‖partialLMaskCInverse C Lmask q p c c'‖)=‖if c.val∈Lmask then q else p‖ := by
      simp [partialLMaskCInverse,Matrix.diagonal_apply,apply_ite norm]
    rw [hh]
    by_cases hc:c.val∈Lmask <;> simp only [hc,if_true,if_false] <;> linarith

omit [Fintype L] in
theorem partialLMaskNewPrecision_isSymm (A B C Lmask : Set L) (A0 : Matrix A A ℂ) (q p α : ℂ)
    (hA : A0.IsSymm) : (partialLMaskNewPrecision A B C Lmask A0 q p α).IsSymm := by
  have hM : (Matrix.fromBlocks (A0+partialLMaskShift A Lmask q α-partialMissingCharge A B q α)
      (partialMatchingCoupling A B α) (partialMatchingCoupling A B α).transpose
      (partialVacuumDiagonal A B q p)).IsSymm := by
    simp only [Matrix.IsSymm,Matrix.fromBlocks_transpose,Matrix.transpose_sub,Matrix.transpose_add,
      partialLMaskShift,partialMissingCharge,partialVacuumDiagonal,Matrix.diagonal_transpose,
      Matrix.transpose_transpose,hA.eq]
  have hF : (Matrix.fromBlocks
      (Matrix.fromBlocks (A0+partialLMaskShift A Lmask q α-partialMissingCharge A B q α)
        (partialMatchingCoupling A B α) (partialMatchingCoupling A B α).transpose
        (partialVacuumDiagonal A B q p)) 0 0 (partialLMaskCPrecision C Lmask q p)).IsSymm := by
    simp only [Matrix.IsSymm,Matrix.fromBlocks_transpose,Matrix.transpose_zero,
      partialLMaskCPrecision,Matrix.diagonal_transpose,hM.eq]
  exact hF.submatrix (Equiv.sumAssoc A B C).symm

theorem partialLMaskNewPrecision_inverse_caps (A B C Lmask : Set L) (A0 : Matrix A A ℂ) (q p α : ℂ)
    (hA : A0.IsSymm) (hq : q≠0) (hp : p≠0) (P K : ℝ) (hP : 0≤P) (hK : 0≤K)
    (hqnorm : ‖q‖≤P) (hpnorm : ‖p‖≤P) (ha : ‖α*q‖≤1)
    (hrestored : IsUnit (A0-partialLMaskRestoration A Lmask q α))
    (hrows : ∀a,∑a',‖(A0-partialLMaskRestoration A Lmask q α)⁻¹ a a'‖≤K) :
    IsUnit (partialLMaskNewPrecision A B C Lmask A0 q p α) ∧
      (∀u,∑v,‖(partialLMaskNewPrecision A B C Lmask A0 q p α)⁻¹ u v‖≤P+2*K) ∧
      (∀v,∑u,‖(partialLMaskNewPrecision A B C Lmask A0 q p α)⁻¹ u v‖≤P+2*K) := by
  have hr:=partialLMaskNewPrecision_inverse_rows A B C Lmask A0 q p α hq hp P K hP hK hqnorm hpnorm ha hrestored hrows
  have hs : ((partialLMaskNewPrecision A B C Lmask A0 q p α)⁻¹).IsSymm := by
    change ((partialLMaskNewPrecision A B C Lmask A0 q p α)⁻¹).transpose=_
    rw [Matrix.transpose_nonsing_inv,(partialLMaskNewPrecision_isSymm A B C Lmask A0 q p α hA).eq]
  refine ⟨hr.1,hr.2,fun v=>?_⟩
  simpa only [hs.apply] using hr.2 v

end LocalLaw
