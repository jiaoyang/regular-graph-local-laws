import LocalLaw.UniversalCycleOverlap
import LocalLaw.StrongBadCenterParameters

/-!
# Strong bad-center moments without a structural-event assumption

Universal nonbacktracking cycle overlap replaces the cycle-space bound.
The extra cost is only one logarithmic power in the witness numerator at
logarithmic radii, so arbitrary polynomial tails remain available.
-/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance universalMomentDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {N : ℕ}

/-- The actual separated-cycle packing moment has a universal half-count bound. -/
theorem packedCycleMoment_lower_half_universal (G : SimpleGraph (Fin N)) (U d q : ℕ)
    (hd : 2 ≤ d) (hdeg : ∀ v, G.degree v ≤ d)
    (hsize : 2 * q * (U * ((U + 1) * (d + 1) * (d - 1) ^ U)) ≤ Nat.card (ShortCyclePattern G U)) :
    ((Nat.card (ShortCyclePattern G U) : ℝ) / 2) ^ q ≤
      (RegularGraph.packedCycleMoment q U G : ℝ) := by
  have hsep := separatedTuple_card_half (shortCycleOverlap (G := G) (U := U))
    (U * ((U + 1) * (d + 1) * (d - 1) ^ U)) q
    (shortCycleOverlap_card_universal G U d hd hdeg)
    (by simpa only [Nat.card_eq_fintype_card] using hsize)
  have hsep' : ((Nat.card (ShortCyclePattern G U) : ℝ) / 2) ^ q ≤
      (Nat.card (ShortCyclePacking G U q) : ℝ) := by
    simpa only [← Nat.card_eq_fintype_card] using hsep
  apply hsep'.trans
  exact_mod_cast shortCyclePacking_card_le_moment G U q

def universalBadCenterNumerator (d R : ℕ) : ℕ :=
  2 * (d + 1) ^ 2 * (2 * R + 2) ^ 3 * (d - 1) ^ (3 * R + 1)

/-- The universal numerator controls both greedy-packing conflicts and the
actual expected moment normalization. -/
theorem universal_cyclePacking_factor_bounds (d R : ℕ) (hd : 3 ≤ d) :
    let U := 2 * R + 1
    let A := (d + 1) * U * (d - 1) ^ R
    let D := U * ((U + 1) * (d + 1) * (d - 1) ^ U)
    let B := universalBadCenterNumerator d R
    0 < A ∧ 2 * D * A ≤ B ∧ 2 * A * (U + 1) * (d - 1) ^ U ≤ B := by
  let U := 2 * R + 1
  let k := d - 1
  let A := (d + 1) * U * k ^ R
  let D := U * ((U + 1) * (d + 1) * k ^ U)
  let B := universalBadCenterNumerator d R
  change 0 < A ∧ 2 * D * A ≤ B ∧ 2 * A * (U + 1) * k ^ U ≤ B
  have hB : B = 2 * (d + 1) ^ 2 * (U + 1) ^ 3 * k ^ (R + U) := by
    dsimp [B, universalBadCenterNumerator, U, k]
    rw [show 3 * R + 1 = R + (2 * R + 1) by omega]
  have hpoly : U ^ 2 * (U + 1) ≤ (U + 1) ^ 3 := by nlinarith
  have hfirst : 2 * D * A ≤ B := by
    calc
      _ = (2 * (d + 1) ^ 2 * k ^ (R + U)) * (U ^ 2 * (U + 1)) := by
        dsimp [D, A]
        rw [pow_add]
        ring
      _ ≤ (2 * (d + 1) ^ 2 * k ^ (R + U)) * (U + 1) ^ 3 := Nat.mul_le_mul_left _ hpoly
      _ = _ := by rw [hB]; ring
  have hOld := RegularGraph.cyclePacking_cover_factor_bounds d R hd
  have hOldLe : badCenterMomentNumerator d R ≤ B := by
    change 2 * (d + 1) * (2 * R + 2) ^ 2 * k ^ (3 * R + 1) ≤ _
    have hd1 : d + 1 ≤ (d + 1) ^ 2 := by nlinarith
    have hpow : (2 * R + 2) ^ 2 ≤ (2 * R + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hd1) hpow)
  have hkpos : 0 < k := by dsimp [k]; omega
  have hUpos : 0 < U := by dsimp [U]; omega
  refine ⟨by dsimp [A]; positivity, hfirst, ?_⟩
  exact hOld.2.2.trans hOldLe

namespace RegularGraph
variable {d : ℕ}

/-- All finite regular graphs satisfy this high-moment bad-center bound;
there is no bounded-excess event in the measured predicate. -/
theorem universal_badCenters_tail_bound (R q K : ℕ) (hd : 3 ≤ d) (hq : 1 ≤ q)
    (hK : q * (2 * R + 1) ≤ K) (hN : 0 < N)
    (hbudget : 2 * K * patternSwitchSlack d K ≤ N * d) (t : ℝ) (ht : 0 < t)
    (hthreshold : ((q * universalBadCenterNumerator d R : ℕ) : ℝ) ≤ t) :
    eventMass (weight (N := N) (d := d)) (fun g =>
      t < ((nonTreeCenters g.graph R).card : ℝ)) ≤
      2 * (((universalBadCenterNumerator d R : ℝ) / t) ^ q) := by
  let U := 2 * R + 1
  let k := d - 1
  let A := (d + 1) * U * k ^ R
  let D := U * ((U + 1) * (d + 1) * k ^ U)
  let B := universalBadCenterNumerator d R
  let E : ℝ := ((U + 1 : ℕ) : ℝ) * ((d - 1 : ℕ) : ℝ) ^ U
  let T : ℝ := (t / (2 * (A : ℝ))) ^ q
  have hb := universal_cyclePacking_factor_bounds d R hd
  change 0 < A ∧ 2 * D * A ≤ B ∧ 2 * A * (U + 1) * k ^ U ≤ B at hb
  have hAp : (0 : ℝ) < A := Nat.cast_pos.mpr hb.1
  have hTp : 0 < T := by dsimp [T]; positivity
  have hKpos : 1 ≤ K := by
    have hp : 0 < q * U := Nat.mul_pos (by omega) (by dsimp [U]; omega)
    exact hp.trans_le hK
  change ((q * B : ℕ) : ℝ) ≤ t at hthreshold
  have hsmall : 2 * q * D * A ≤ q * B := by
    calc
      _ = q * (2 * D * A) := by ring
      _ ≤ q * B := Nat.mul_le_mul_left _ hb.2.1
  have hsmallR : ((2 * q * D : ℕ) : ℝ) * (A : ℝ) ≤ t := by
    have hs : ((2 * q * D * A : ℕ) : ℝ) ≤ ((q * B : ℕ) : ℝ) := by exact_mod_cast hsmall
    simpa only [Nat.cast_mul] using hs.trans hthreshold
  have hevent : ∀ g : RegularGraph N d, t < ((nonTreeCenters g.graph R).card : ℝ) →
      T ≤ (packedCycleMoment q U g.graph : ℝ) := by
    intro g hg
    let S := Nat.card (ShortCyclePattern g.graph U)
    have hcover := g.badCenters_card_le_pattern_count R hd
    change (nonTreeCenters g.graph R).card ≤ S * A at hcover
    have hcoverR : ((nonTreeCenters g.graph R).card : ℝ) ≤ (S : ℝ) * (A : ℝ) := by exact_mod_cast hcover
    have hsizeR : ((2 * q * D : ℕ) : ℝ) ≤ (S : ℝ) := by nlinarith
    have hsize : 2 * q * D ≤ S := by exact_mod_cast hsizeR
    have hmoment := packedCycleMoment_lower_half_universal g.graph U d q (by omega)
      (fun v => (g.regular v).le) hsize
    have hSa : t ≤ (S : ℝ) * (A : ℝ) := hg.le.trans hcoverR
    have hbase : t / (2 * (A : ℝ)) ≤ (S : ℝ) / 2 := by
      calc
        _ ≤ ((S : ℝ) * (A : ℝ)) / (2 * (A : ℝ)) := div_le_div_of_nonneg_right hSa (by positivity)
        _ = (S : ℝ) / 2 := by field_simp; ring
    exact (pow_le_pow_left₀ (by positivity) hbase q).trans hmoment
  have hmass := (eventMass_mono weight weight_nonnegative hevent).trans
    (packedCycleMoment_tail q U K hK hKpos hN (by omega) hbudget T hTp)
  apply hmass.trans
  change 2 * E ^ q / T ≤ 2 * ((B : ℝ) / t) ^ q
  have hinflation : 2 * (A : ℝ) * E ≤ (B : ℝ) := by
    have hn : ((2 * A * (U + 1) * k ^ U : ℕ) : ℝ) ≤ (B : ℝ) := by exact_mod_cast hb.2.2
    simpa only [E, k, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, mul_assoc] using hn
  have hratio : E / (t / (2 * (A : ℝ))) = (2 * (A : ℝ) * E) / t := by field_simp; ring
  dsimp only [T]
  rw [mul_div_assoc, ← div_pow, hratio]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply pow_le_pow_left₀ (by positivity)
  exact div_le_div_of_nonneg_right hinflation ht.le

end RegularGraph
end
end LocalLaw
