import LocalLaw.AsymmetricBlockRows

/-! # Exact vacuum elimination with repeated attachment roots

Each retained sampled leaf has at most one retained core mate. Several
leaves may share that mate. An omitted core mate gives the formal full
diagonal p, while a retained mate gives the cavity diagonal q.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance vacuumLeafSchurDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {K J:Type} [Fintype K] [Fintype J] [DecidableEq K] [DecidableEq J]

def vacuumLeafIncidence (mate:J→Option K) (α:ℂ):Matrix K J ℂ:=
  fun k j=>if mate j=some k then α else 0

def vacuumLeafMultiplicity (mate:J→Option K) (k:K):ℂ:=
  ∑j,if mate j=some k then 1 else 0

def vacuumLeafDiagonal (mate:J→Option K) (q p:ℂ):Matrix J J ℂ:=
  Matrix.diagonal (fun j=>if mate j=none then p⁻¹ else q⁻¹)

def vacuumLeafInverse (mate:J→Option K) (q p:ℂ):Matrix J J ℂ:=
  Matrix.diagonal (fun j=>if mate j=none then p else q)

omit [Fintype K] in
theorem vacuumLeafDiagonal_inverse (mate:J→Option K) (q p:ℂ) (hq:q≠0) (hp:p≠0) :
    IsUnit (vacuumLeafDiagonal mate q p)∧(vacuumLeafDiagonal mate q p)⁻¹=vacuumLeafInverse mate q p := by
  have hprod:vacuumLeafDiagonal mate q p*vacuumLeafInverse mate q p=1:=by
    ext i j
    by_cases hij:i=j
    · subst j
      by_cases hi:mate i=none <;>
        simp [vacuumLeafDiagonal,vacuumLeafInverse,Matrix.diagonal_apply,Matrix.mul_apply,hi,hq,hp]
    · simp [vacuumLeafDiagonal,vacuumLeafInverse,Matrix.diagonal_apply,Matrix.mul_apply,Matrix.one_apply,hij]
  exact ⟨Matrix.isUnit_of_right_inverse hprod,Matrix.inv_eq_right_inv hprod⟩

omit [Fintype K] in
theorem vacuumLeaf_selfEnergy (mate:J→Option K) (q p α:ℂ) :
    vacuumLeafIncidence mate α*vacuumLeafInverse mate q p*(vacuumLeafIncidence mate α).transpose=
      Matrix.diagonal (fun k=>q*α^2*vacuumLeafMultiplicity mate k) := by
  ext k k'
  have heq:(vacuumLeafIncidence mate α*vacuumLeafInverse mate q p*(vacuumLeafIncidence mate α).transpose) k k'=
      ∑j,(if mate j=some k then α else 0)*(if mate j=none then p else q)*(if mate j=some k' then α else 0):=by
    simp only [Matrix.mul_apply,vacuumLeafIncidence,vacuumLeafInverse,Matrix.transpose_apply,Matrix.diagonal_apply]
    simp
  rw [heq]
  by_cases hkk:k=k'
  · subst k'
    simp only [Matrix.diagonal_apply_eq,vacuumLeafMultiplicity,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj:mate j=some k
    · simp [hj]
      ring
    · simp [hj]
  · rw [Matrix.diagonal_apply_ne _ hkk]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj:mate j=some k
    · have hn:mate j≠some k':=fun h=>hkk (Option.some.inj (hj.symm.trans h))
      simp [hn]
    · simp [hj]

omit [Fintype K] in
theorem vacuumLeaf_products (mate:J→Option K) (q p α:ℂ) :
    vacuumLeafIncidence mate α*vacuumLeafInverse mate q p=vacuumLeafIncidence mate (α*q)∧
      vacuumLeafInverse mate q p*(vacuumLeafIncidence mate α).transpose=(vacuumLeafIncidence mate (α*q)).transpose := by
  constructor
  · ext k j
    simp only [vacuumLeafInverse,Matrix.mul_diagonal,vacuumLeafIncidence]
    by_cases hj:mate j=some k
    · simp [hj]
    · simp [hj]
  · ext j k
    simp only [vacuumLeafInverse,Matrix.diagonal_mul,Matrix.transpose_apply,vacuumLeafIncidence]
    by_cases hj:mate j=some k
    · simp [hj]
      ring
    · simp [hj]

omit [Fintype K] [DecidableEq J] in
theorem vacuumLeafIncidence_row (mate:J→Option K) (β:ℂ) (k:K) :
    (∑j,‖vacuumLeafIncidence mate β k j‖)=(Nat.card {j:J//mate j=some k}:ℝ)*‖β‖ := by
  have hc:(∑j,if mate j=some k then (1:ℝ) else 0)=(Nat.card {j:J//mate j=some k}:ℝ):=by
    simp [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.sum_boole]
  rw [←hc,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj:mate j=some k <;> simp [vacuumLeafIncidence,hj]

omit [Fintype J] [DecidableEq J] in
theorem vacuumLeafIncidence_column (mate:J→Option K) (β:ℂ) (j:J) :
    (∑k,‖vacuumLeafIncidence mate β k j‖)≤‖β‖ := by
  cases hm:mate j with
  | none => simp [vacuumLeafIncidence,hm]
  | some k => simp [vacuumLeafIncidence,hm,apply_ite norm]

def vacuumLeafMatrix (mate:J→Option K) (A:Matrix K K ℂ) (degree:K→ℂ) (q p α:ℂ):
    Matrix (K⊕J) (K⊕J) ℂ:=
  Matrix.fromBlocks (A-Matrix.diagonal (fun k=>q*α^2*(degree k-vacuumLeafMultiplicity mate k)))
    (vacuumLeafIncidence mate α) (vacuumLeafIncidence mate α).transpose (vacuumLeafDiagonal mate q p)

theorem vacuumLeaf_schur (mate:J→Option K) (A:Matrix K K ℂ) (degree:K→ℂ) (q p α:ℂ)
    (hq:q≠0) (hp:p≠0)
    (hcore:IsUnit (A-Matrix.diagonal (fun k=>q*α^2*degree k))) :
    IsUnit (vacuumLeafMatrix mate A degree q p α)∧
      blockSchur (vacuumLeafMatrix mate A degree q p α)=A-Matrix.diagonal (fun k=>q*α^2*degree k)∧
      ((vacuumLeafMatrix mate A degree q p α)⁻¹).toBlocks₁₁=
        (A-Matrix.diagonal (fun k=>q*α^2*degree k))⁻¹ := by
  let M:=vacuumLeafMatrix mate A degree q p α
  obtain ⟨hD,hDinv⟩:=vacuumLeafDiagonal_inverse mate q p hq hp
  have hS:blockSchur M=A-Matrix.diagonal (fun k=>q*α^2*degree k):=by
    change A-Matrix.diagonal (fun k=>q*α^2*(degree k-vacuumLeafMultiplicity mate k))-
      vacuumLeafIncidence mate α*(vacuumLeafDiagonal mate q p)⁻¹*(vacuumLeafIncidence mate α).transpose=_
    rw [hDinv,vacuumLeaf_selfEnergy]
    ext k k'
    by_cases hkk:k=k'
    · subst k'
      simp only [Matrix.sub_apply,Matrix.diagonal_apply_eq]
      ring
    · simp [Matrix.sub_apply,Matrix.diagonal_apply,hkk]
  have hM:IsUnit M:=by
    letI:Invertible (vacuumLeafDiagonal mate q p):=Classical.choice hD.nonempty_invertible
    apply Matrix.isUnit_fromBlocks_iff_of_invertible₂₂.mpr
    change IsUnit (M.toBlocks₁₁-M.toBlocks₁₂*⅟ (vacuumLeafDiagonal mate q p)*M.toBlocks₂₁)
    rw [Matrix.invOf_eq_nonsing_inv]
    change IsUnit (blockSchur M)
    rw [hS]
    exact hcore
  exact ⟨hM,hS,by rw [inverse_block11 M hM hD,hS]⟩

end LocalLaw
