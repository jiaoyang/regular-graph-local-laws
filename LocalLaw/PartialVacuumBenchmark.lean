import LocalLaw.BlockSchur

/-!
# Exact Schur benchmark for partially retained switching triples

Retained A vertices may retain or omit their sampled B leaf. Retained B
vertices may omit A. The omitted branch is represented by its exact vacuum
charge. Eliminating the retained B vertices restores the same deficit at
EVERY retained A vertex, independently of this partial-retention mask.
-/
noncomputable section
namespace LocalLaw
local instance partialVacuumBenchmarkDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {L : Type} [Fintype L] [DecidableEq L]

def partialMatchingCoupling (A B : Set L) (α : ℂ) : Matrix A B ℂ :=
  fun a b=>if a.val=b.val then α else 0

def partialVacuumDiagonal (A B : Set L) (m p : ℂ) : Matrix B B ℂ :=
  Matrix.diagonal (fun b=>if b.val∈A then m⁻¹ else p⁻¹)

def partialVacuumInverse (A B : Set L) (m p : ℂ) : Matrix B B ℂ :=
  Matrix.diagonal (fun b=>if b.val∈A then m else p)

def partialMissingCharge (A B : Set L) (m α : ℂ) : Matrix A A ℂ :=
  Matrix.diagonal (fun a=>if a.val∈B then 0 else m*α^2)

theorem partialVacuumDiagonal_inverse (A B : Set L) (m p : ℂ) (hm : m≠0) (hp : p≠0) :
    IsUnit (partialVacuumDiagonal A B m p) ∧
      (partialVacuumDiagonal A B m p)⁻¹=partialVacuumInverse A B m p := by
  let D:=partialVacuumDiagonal A B m p
  let E:=partialVacuumInverse A B m p
  have hDE : D*E=1 := by
    ext i j
    by_cases hij:i=j
    · subst j
      by_cases hi:i.val∈A <;> simp [D,E,partialVacuumDiagonal,partialVacuumInverse,Matrix.diagonal_apply,Matrix.mul_apply,hi,hm,hp]
    · simp [D,E,partialVacuumDiagonal,partialVacuumInverse,Matrix.diagonal_apply,Matrix.mul_apply,Matrix.one_apply,hij]
  have hED : E*D=1 := by
    ext i j
    by_cases hij:i=j
    · subst j
      by_cases hi:i.val∈A <;> simp [D,E,partialVacuumDiagonal,partialVacuumInverse,Matrix.diagonal_apply,Matrix.mul_apply,hi,hm,hp]
    · simp [D,E,partialVacuumDiagonal,partialVacuumInverse,Matrix.diagonal_apply,Matrix.mul_apply,Matrix.one_apply,hij]
  exact ⟨⟨⟨D,E,hDE,hED⟩,rfl⟩,Matrix.inv_eq_right_inv hDE⟩

theorem partialMatching_selfEnergy (A B : Set L) (m p α : ℂ) :
    partialMatchingCoupling A B α*partialVacuumInverse A B m p*(partialMatchingCoupling A B α).transpose=
      Matrix.diagonal (fun a:A=>if a.val∈B then m*α^2 else 0) := by
  ext a a'
  have hsum : (partialMatchingCoupling A B α*partialVacuumInverse A B m p*
      (partialMatchingCoupling A B α).transpose) a a'=
      ∑ b:B, (if a.val=b.val then α else 0)*(if b.val∈A then m else p)*
        (if a'.val=b.val then α else 0) := by
    simp only [Matrix.mul_apply,partialMatchingCoupling,partialVacuumInverse,Matrix.transpose_apply,
      Matrix.diagonal_apply]
    simp
  rw [hsum]
  by_cases haa:a=a'
  · subst a'
    by_cases ha:a.val∈B
    · let b0:B:=⟨a.val,ha⟩
      have heq : (∑ b:B,(if a.val=b.val then α else 0)*(if b.val∈A then m else p)*
          (if a.val=b.val then α else 0))=α*m*α := by
        rw [Finset.sum_eq_single b0]
        · simp [b0,a.property]
        · intro b _ hbb
          have hn:a.val≠b.val := fun h=>hbb (Subtype.ext h.symm)
          simp [hn]
        · intro hn
          exact False.elim (hn (Finset.mem_univ _))
      rw [heq]
      simp only [Matrix.diagonal_apply,if_pos rfl,ha,if_true]
      ring
    · have hz : ∀ b:B,a.val≠b.val := fun b h=>ha (h.symm ▸ b.property)
      simp [hz,Matrix.diagonal_apply,ha]
  · have hzero (b:B) : (if a.val=b.val then α else 0)*(if b.val∈A then m else p)*
        (if a'.val=b.val then α else 0)=0 := by
      by_cases hab:a.val=b.val
      · have hother:a'.val≠b.val := fun h=>haa (Subtype.ext (hab.trans h.symm))
        simp [hother]
      · simp [hab]
    rw [Finset.sum_eq_zero (fun b _=>hzero b)]
    simp only [Matrix.diagonal_apply,if_neg haa]

/-- The exact partial switch benchmark has the uniformly controlled
restored A block as its Schur complement. Missing B vertices contribute
vacuum charge; retained B vertices contribute the identical self-energy. -/
theorem partialVacuum_schur (A B : Set L) (A₀ : Matrix A A ℂ) (m p α : ℂ)
    (hm : m≠0) (hp : p≠0)
    (hrestored : IsUnit (A₀-Matrix.diagonal (fun _ : A=>m*α^2))) :
    let C:=partialMatchingCoupling A B α
    let M:=Matrix.fromBlocks (A₀-partialMissingCharge A B m α) C C.transpose (partialVacuumDiagonal A B m p)
    IsUnit M ∧ (M⁻¹).toBlocks₁₁=(A₀-Matrix.diagonal (fun _ : A=>m*α^2))⁻¹ := by
  dsimp only
  let C:=partialMatchingCoupling A B α
  let D:=partialVacuumDiagonal A B m p
  let E:=partialVacuumInverse A B m p
  let Δ:=partialMissingCharge A B m α
  let M:=Matrix.fromBlocks (A₀-Δ) C C.transpose D
  obtain ⟨hD,hDinv⟩:=partialVacuumDiagonal_inverse A B m p hm hp
  have hcharge : Δ+Matrix.diagonal (fun a:A=>if a.val∈B then m*α^2 else 0)=
      Matrix.diagonal (fun _ : A=>m*α^2) := by
    unfold Δ partialMissingCharge
    rw [Matrix.diagonal_add]
    apply congrArg (fun f:A→ℂ=>Matrix.diagonal f)
    funext a
    split_ifs <;> simp
  have hS : blockSchur M=A₀-Matrix.diagonal (fun _ : A=>m*α^2) := by
    change A₀-Δ-C*D⁻¹*C.transpose=_
    rw [hDinv,partialMatching_selfEnergy]
    rw [←hcharge]
    abel
  have hM : IsUnit M := by
    letI : Invertible D:=Classical.choice hD.nonempty_invertible
    apply Matrix.isUnit_fromBlocks_iff_of_invertible₂₂.mpr
    change IsUnit (A₀-Δ-C*⅟ D*C.transpose)
    rw [Matrix.invOf_eq_nonsing_inv]
    change IsUnit (blockSchur M)
    rw [hS]
    exact hrestored
  exact ⟨hM,by rw [inverse_block11 M hM hD,hS]⟩

end LocalLaw
