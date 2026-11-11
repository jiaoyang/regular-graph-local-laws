import LocalLaw.CavityAverage
import LocalLaw.GraphModel

/-!
# Coarse continuity of the actual cavity average

Universal minor-resolvent continuity is averaged over exactly d neighbors
and then N centers. The factors d and N cancel with their normalizations.
No spectral regularity event or independence assumption is used.
-/

open scoped BigOperators

noncomputable section

namespace LocalLaw

local instance cavityContinuityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Only an oriented edge contributes to the extended cavity term. -/
theorem orientedCavity_lipschitz (G : SimpleGraph V) (d : ℕ)
    (z w : ℂ) (η₀ : ℝ) (hη : 0 < η₀) (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im)
    (i j : V) :
    ‖orientedCavity G d z i j - orientedCavity G d w i j‖ ≤
      if G.Adj i j then (1 / η₀ ^ 2) * dist z w else 0 := by
  classical
  unfold orientedCavity
  by_cases hij : i ≠ j
  · by_cases hadj : G.Adj i j
    · simp only [dif_pos hij, if_pos hadj]
      exact green_entry_lipschitz_universal _
        (deletedMatrix_isHermitian _ (normalizedAdjacency_isHermitian G d) j)
        z w η₀ hη hz hw _ _
    · simp [hij, hadj]
  · have heq : i = j := not_ne_iff.mp hij
    subst j
    simp

omit [DecidableEq V] in
private theorem sum_adjacent_constant (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : V) (c : ℝ) : (∑ j, if G.Adj i j then c else 0) = (G.degree i : ℝ) * c := by
  rw [← Finset.sum_filter, ← G.neighborFinset_eq_filter]
  simp

theorem cavityAtVertex_lipschitz (G : SimpleGraph V) (d : ℕ) (hd : 0 < d)
    (hregular : G.IsRegularOfDegree d) (z w : ℂ)
    (η₀ : ℝ) (hη : 0 < η₀) (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im) (i : V) :
    ‖cavityAtVertex G d z i - cavityAtVertex G d w i‖ ≤ (1 / η₀ ^ 2) * dist z w := by
  classical
  have hdzero : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hd)
  unfold cavityAtVertex
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul]
  simp only [norm_inv, Complex.norm_natCast]
  calc
    (d : ℝ)⁻¹ * ‖∑ j, (orientedCavity G d z i j - orientedCavity G d w i j)‖
        ≤ (d : ℝ)⁻¹ * ∑ j, ‖orientedCavity G d z i j - orientedCavity G d w i j‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (d : ℝ)⁻¹ * ∑ j, (if G.Adj i j then (1 / η₀ ^ 2) * dist z w else 0) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun j _ => orientedCavity_lipschitz G d z w η₀ hη hz hw i j)
    _ = (1 / η₀ ^ 2) * dist z w := by
      rw [sum_adjacent_constant, hregular i]
      field_simp

theorem cavityAverage_lipschitz (G : SimpleGraph V) (d : ℕ) (hd : 0 < d)
    (hregular : G.IsRegularOfDegree d) (hcard : 0 < Fintype.card V)
    (z w : ℂ) (η₀ : ℝ) (hη : 0 < η₀) (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im) :
    ‖cavityAverage G d z - cavityAverage G d w‖ ≤ (1 / η₀ ^ 2) * dist z w := by
  have hNzero : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hcard)
  rw [cavityAverage_eq_mean, cavityAverage_eq_mean, ← smul_sub, ← Finset.sum_sub_distrib,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (Fintype.card V : ℝ)⁻¹)]
  calc
    (Fintype.card V : ℝ)⁻¹ * ‖∑ i, (cavityAtVertex G d z i - cavityAtVertex G d w i)‖
        ≤ (Fintype.card V : ℝ)⁻¹ * ∑ i, ‖cavityAtVertex G d z i - cavityAtVertex G d w i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (Fintype.card V : ℝ)⁻¹ * ∑ _i : V, (1 / η₀ ^ 2) * dist z w := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun i _ => cavityAtVertex_lipschitz G d hd hregular z w η₀ hη hz hw i)
    _ = (1 / η₀ ^ 2) * dist z w := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

end

namespace RegularGraph

/-- Source-specific Q continuity, ready to use in spectral transport. -/
theorem Q_lipschitz {N d : ℕ} (g : RegularGraph N d) (hN : 0 < N) (hd : 0 < d)
    (z w : ℂ) (η₀ : ℝ) (hη : 0 < η₀) (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im) :
    ‖g.Q z - g.Q w‖ ≤ (1 / η₀ ^ 2) * dist z w :=
  cavityAverage_lipschitz g.graph d hd g.regular (by simpa using hN) z w η₀ hη hz hw

end RegularGraph

end LocalLaw
