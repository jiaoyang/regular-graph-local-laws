import LocalLaw.CavityDeletionParameters

/-!
# The genuine one-edge expectation in the cavity concentration step

The normalization of the outside-edge mean is its actual cardinality, not Nd.
Exact oriented-edge counts bound this normalization change by the removed
vertex density. The resulting comparison is with the actual finite expectation
used by independent local sampling.
-/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance outsideCavityMeanDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem finiteComplexMean_norm_bound {E : Type*} [Fintype E] [Nonempty E]
    (f : E → ℂ) (M : ℝ) (hf : ∀ e, ‖f e‖ ≤ M) : ‖finiteComplexMean f‖ ≤ M := by
  have hn : (0 : ℝ) < Fintype.card E := Nat.cast_pos.mpr Fintype.card_pos
  unfold finiteComplexMean
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  calc
    _ ≤ (Fintype.card E : ℝ)⁻¹ * (∑ _e : E, M) :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun e _ => hf e))) (by positivity)
    _ = M := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

namespace RegularGraph
variable {N d : ℕ}

theorem outsideMean_normalization_difference (g : RegularGraph N d) (T : Set (Fin N))
    (hN : 0 < N) (hd : 0 < d) (hT : 4 * Nat.card T ≤ N)
    (f : OutsideOrientedEdge g.graph T → ℂ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ e, ‖f e‖ ≤ M) :
    ‖finiteComplexMean f - ((N : ℝ) * (d : ℝ))⁻¹ • ∑ e, f e‖ ≤
      (2 * (Nat.card T : ℝ) / (N : ℝ)) * M := by
  let E := OutsideOrientedEdge g.graph T
  letI : Nonempty E := g.outside_edge_nonempty T hN hd hT
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hdp : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have he : (0 : ℝ) < Fintype.card E := Nat.cast_pos.mpr Fintype.card_pos
  have hcount := g.outside_count_identity T
  have hcount' := g.boundary_interior_count T
  have heUpperNat : Fintype.card E ≤ N * d := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (OutsideOrientedEdge g.graph T) ≤ N * d
    omega
  have heLowerNat : N * d ≤ Fintype.card E + 2 * d * Nat.card T := by
    rw [← Nat.card_eq_fintype_card]
    change N * d ≤ Nat.card (OutsideOrientedEdge g.graph T) + 2 * d * Nat.card T
    nlinarith
  have heUpper : (Fintype.card E : ℝ) ≤ (N : ℝ) * (d : ℝ) := by exact_mod_cast heUpperNat
  have heLower : (N : ℝ) * (d : ℝ) ≤ (Fintype.card E : ℝ) + 2 * (d : ℝ) * (Nat.card T : ℝ) := by
    exact_mod_cast heLowerNat
  have hcpos : 0 ≤ 1 - ((N : ℝ) * (d : ℝ))⁻¹ * (Fintype.card E : ℝ) := by
    have hh := (div_le_one (mul_pos hn hdp)).mpr heUpper
    rw [div_eq_inv_mul] at hh
    linarith
  have hc : 1 - ((N : ℝ) * (d : ℝ))⁻¹ * (Fintype.card E : ℝ) ≤
      2 * (Nat.card T : ℝ) / (N : ℝ) := by
    apply (mul_le_mul_right (mul_pos hn hdp)).mp
    have heq : (1 - ((N : ℝ) * (d : ℝ))⁻¹ * (Fintype.card E : ℝ)) *
        ((N : ℝ) * (d : ℝ)) = (N : ℝ) * (d : ℝ) - (Fintype.card E : ℝ) := by field_simp
    rw [heq]
    have heq' : (2 * (Nat.card T : ℝ) / (N : ℝ)) * ((N : ℝ) * (d : ℝ)) =
        2 * (d : ℝ) * (Nat.card T : ℝ) := by field_simp; ring
    rw [heq']
    linarith
  have hsum : (∑ e, f e) = (Fintype.card E : ℝ) • finiteComplexMean f := by
    unfold finiteComplexMean
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt he), one_smul]
  rw [hsum, smul_smul]
  have hid : finiteComplexMean f - (((N : ℝ) * (d : ℝ))⁻¹ * (Fintype.card E : ℝ)) • finiteComplexMean f =
      (1 - ((N : ℝ) * (d : ℝ))⁻¹ * (Fintype.card E : ℝ)) • finiteComplexMean f := by
    rw [sub_smul, one_smul]
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcpos]
  exact (mul_le_mul_of_nonneg_left (finiteComplexMean_norm_bound f M hf) hcpos).trans
    (mul_le_mul_of_nonneg_right hc hM)

/-- The one-edge observation is a genuine deleted-vertex resolvent entry;
its cap follows from the actual outside Green and pivot caps. -/
theorem outsideOrientedCavityValue_norm_bound (g : RegularGraph N d) (T : Set (Fin N))
    (z : ℂ) (C L : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hS : ∀ i j, ‖green (normalizedAdjacency (outsideGraph g.graph T) d) z i j‖ ≤ C)
    (hSi : ∀ j, ‖(green (normalizedAdjacency (outsideGraph g.graph T) d) z j j)⁻¹‖ ≤ L)
    (e : OutsideOrientedEdge g.graph T) :
    ‖outsideOrientedCavityValue g.graph d T z e‖ ≤ C + C ^ 2 * L :=
  matrixCavityTerm_norm_bound _ C L hC hL hS hSi _ _

end RegularGraph
end
end LocalLaw
