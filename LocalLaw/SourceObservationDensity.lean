import LocalLaw.SourceBiasBadEdges
import LocalLaw.OutsideEdgeCounting

/-!
# Actual exceptional-edge sampling density

The true outside-edge denominator is at least Nd/2. The proved 3d times
the exceptional-center count therefore gives density at most 6*N^gamma/N.
A density below one supplies an actual good sample.
-/

noncomputable section
namespace LocalLaw
local instance sourceObservationDensityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem finset_card_lt_of_fraction_lt_one {E : Type*} [Fintype E] [Nonempty E]
    (bad : Finset E) (h : (Fintype.card E : ℝ)⁻¹ * (bad.card : ℝ) < 1) :
    bad.card < Fintype.card E := by
  have hE : (0 : ℝ) < Fintype.card E := Nat.cast_pos.mpr Fintype.card_pos
  have hh : (bad.card : ℝ) / Fintype.card E < 1 := by
    simpa only [div_eq_mul_inv, mul_comm] using h
  exact_mod_cast (div_lt_one hE).mp hh

namespace RegularGraph
variable {N d : ℕ}

theorem outside_bad_edge_fraction_bound (g : RegularGraph N d) (T : Set (Fin N))
    (hN : 0 < N) (hd : 0 < d) (hT : 4 * Nat.card T ≤ N)
    (bad : Finset (OutsideOrientedEdge g.graph T)) (γ : ℝ)
    (hbad : bad.card ≤ 3 * d * ⌊(N : ℝ) ^ γ⌋₊) :
    (Fintype.card (OutsideOrientedEdge g.graph T) : ℝ)⁻¹ * (bad.card : ℝ) ≤
      6 * (N : ℝ) ^ γ / (N : ℝ) := by
  let E := OutsideOrientedEdge g.graph T
  letI : Nonempty E := g.outside_edge_nonempty T hN hd hT
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hE : (0 : ℝ) < Fintype.card E := Nat.cast_pos.mpr Fintype.card_pos
  have hU : 0 ≤ (N : ℝ) ^ γ := (Real.rpow_pos_of_pos hNpos γ).le
  have hbadR : (bad.card : ℝ) ≤ 3 * (d : ℝ) * (N : ℝ) ^ γ := by
    have hh : (bad.card : ℝ) ≤ 3 * (d : ℝ) * (⌊(N : ℝ) ^ γ⌋₊ : ℝ) := by exact_mod_cast hbad
    exact hh.trans (mul_le_mul_of_nonneg_left (Nat.floor_le hU) (by positivity))
  calc
    _ = (bad.card : ℝ) / Fintype.card E := by ring
    _ ≤ 6 * (N : ℝ) ^ γ / (N : ℝ) := by
      apply (div_le_iff₀ hE).mpr
      have hh := mul_le_mul_of_nonneg_left (g.outside_edge_real_size T hT)
        (by positivity : 0 ≤ 6 * (N : ℝ) ^ γ / (N : ℝ))
      have heq : (6 * (N : ℝ) ^ γ / (N : ℝ)) * ((N : ℝ) * (d : ℝ) / 2) =
          3 * (d : ℝ) * (N : ℝ) ^ γ := by
        field_simp
        ring
      rw [heq] at hh
      exact hbadR.trans hh

end RegularGraph
end LocalLaw
