import LocalLaw.FullQuadVacuumBenchmark

/-! # Crossing charges as row sums of the full signed edge update -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
set_option maxHeartbeats 3000000
local instance fullQuadRowChargesDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {K L : Type} [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]

omit [DecidableEq L] in
theorem fullQuadRetainedEdges_row (inner outer : L → Option K) (α : ℂ) (k : K) :
    (∑ k', fullQuadRetainedEdges inner outer α k k') = α * fullQuadRetainedDegree inner outer k := by
  unfold fullQuadRetainedEdges fullQuadRetainedDegree
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases hi : inner i with
  | none => cases ho : outer i <;> simp [hi, ho]
  | some u =>
    cases ho : outer i with
    | none => simp [hi, ho]
    | some v =>
      by_cases hu : u = k
      · subst u
        by_cases hv : v = k
        · subst v
          simp [hi, ho, Finset.sum_add_distrib]
          ring
        · simp [hi, ho, hv, Ne.symm hv, Finset.sum_add_distrib]
      · by_cases hv : v = k
        · subst v
          simp [hi, ho, hu, Ne.symm hu, Finset.sum_add_distrib]
        · simp [hi, ho, hu, hv, Ne.symm hu, Ne.symm hv, Finset.sum_add_distrib]

omit [Fintype K] in
theorem vacuumLeafIncidence_complex_row {J : Type} [Fintype J]
    (mate : J → Option K) (α : ℂ) (k : K) :
    (∑ j, vacuumLeafIncidence mate α k j) = α * vacuumLeafMultiplicity mate k := by
  simp only [vacuumLeafIncidence, vacuumLeafMultiplicity, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem vacuumLeafIncidence_complex_column {J : Type}
    (mate : J → Option K) (α : ℂ) (j : J) :
    (∑ k, vacuumLeafIncidence mate α k j) = if mate j = none then 0 else α := by
  cases hm : mate j <;> simp [vacuumLeafIncidence, hm, eq_comm]

theorem partialMatching_complex_row (B C : Set L) (α : ℂ) (b : B) :
    (∑ c : C, partialMatchingCoupling B C α b c) = if b.val ∈ C then α else 0 := by
  by_cases hb : b.val ∈ C
  · let c : C := ⟨b.val, hb⟩
    rw [Finset.sum_eq_single c]
    · simp [partialMatchingCoupling, c, hb]
    · intro c' _ hc
      have he : b.val ≠ c'.val := fun h => hc (Subtype.ext h.symm)
      simp [partialMatchingCoupling, he]
    · simp
  · have hn : ∀ c : C, b.val ≠ c.val := fun c h => hb (h.symm ▸ c.property)
    simp [partialMatchingCoupling, hb, hn]

theorem fullQuadSurgery_row_charge (inner outer : L → Option K) (B C : Set L) (q α : ℂ) :
    fullQuadSurgeryCoupling inner outer B C q α =
      fullQuadSurgeryCoupling inner outer B C 0 α +
        (q * α) • Matrix.diagonal (fun u => ∑ v, fullQuadSurgeryCoupling inner outer B C 0 α u v) := by
  let mate := fullQuadLeafMate inner outer B C
  have hzero : fullQuadSampleCharge inner outer B C 0 α =
      Matrix.fromBlocks 0 (-(partialMatchingCoupling B C α))
        (-(partialMatchingCoupling B C α).transpose) 0 := by
    ext u v
    rcases u with b | c <;> rcases v with b' | c' <;>
      simp [fullQuadSampleCharge, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  have hcore (k : K) : (∑ v, fullQuadSurgeryCoupling inner outer B C 0 α (.inl k) v) =
      α * (vacuumLeafMultiplicity mate k - fullQuadRetainedDegree inner outer k) := by
    simp only [Fintype.sum_sum_type, fullQuadSurgeryCoupling, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.sub_apply, Matrix.neg_apply, zero_mul,
      Matrix.diagonal_zero, Matrix.zero_apply, sub_zero, Finset.sum_neg_distrib]
    rw [fullQuadRetainedEdges_row, ← Fintype.sum_sum_type,
      vacuumLeafIncidence_complex_row]
    dsimp only [mate]
    ring
  have hsample (j : B ⊕ C) : (∑ v, fullQuadSurgeryCoupling inner outer B C 0 α (.inr j) v) =
      α * ((if mate j = none then 0 else 1) -
        (match j with | .inl b => if b.val ∈ C then 1 else 0 | .inr c => if c.val ∈ B then 1 else 0)) := by
    rw [Fintype.sum_sum_type]
    change (∑ k, vacuumLeafIncidence mate α k j) +
      (∑ j', fullQuadSampleCharge inner outer B C 0 α j j') = _
    rw [vacuumLeafIncidence_complex_column, hzero]
    rcases j with b | c
    · rw [Fintype.sum_sum_type]
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
        Finset.sum_const_zero, Matrix.neg_apply, Finset.sum_neg_distrib,
        partialMatching_complex_row, zero_add]
      split_ifs <;> ring
    · rw [Fintype.sum_sum_type]
      simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
        Finset.sum_const_zero, Matrix.neg_apply, Finset.sum_neg_distrib,
        Matrix.transpose_apply, add_zero]
      have he : (∑ b : B, partialMatchingCoupling B C α b c) = if c.val ∈ B then α else 0 := by
        simpa only [partialMatchingCoupling, eq_comm] using partialMatching_complex_row C B α c
      rw [he]
      split_ifs <;> ring
  have hrow (u : K ⊕ (B ⊕ C)) : (∑ v, fullQuadSurgeryCoupling inner outer B C 0 α u v) =
      match u with
      | .inl k => α * (vacuumLeafMultiplicity mate k - fullQuadRetainedDegree inner outer k)
      | .inr j => α * ((if mate j = none then 0 else 1) -
          (match j with | .inl b => if b.val ∈ C then 1 else 0 | .inr c => if c.val ∈ B then 1 else 0)) := by
    rcases u with k | j
    · exact hcore k
    · exact hsample j
  ext u v
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply]
  rw [hrow u]
  rcases u with k | (b | c) <;> rcases v with k' | (b' | c')
  all_goals simp only [fullQuadSurgeryCoupling, fullQuadSampleCharge, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply,
    Matrix.sub_apply, Matrix.neg_apply, Matrix.zero_apply, zero_mul, mul_zero,
    sub_zero, zero_sub, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq]
  all_goals (try split_ifs) <;> (try simp_all [mate, fullQuadLeafMate]) <;> ring

end LocalLaw
