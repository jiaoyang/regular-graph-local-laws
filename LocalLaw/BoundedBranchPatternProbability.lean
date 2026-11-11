import LocalLaw.CycleCounting

/-!
# Sparse bicyclic patterns with a bounded number of branch vertices

Vertices of degree two retain the sharp d(d-1) falling-degree factor. Only a
fixed number B of exceptional vertices contributes a degree-dependent constant.
For a connected excess-two pattern, its expected labelled copies therefore
have the sharp (d-1)^m/N rate needed by a logarithmic-radius witness count.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance branchPatternDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Descending factorials are uniformly bounded, including their vanishing
when a required degree exceeds d. -/
theorem descFactorial_le_self_power (d k : ℕ) (hd : 1 ≤ d) :
    d.descFactorial k ≤ d ^ d := by
  by_cases hk : k ≤ d
  · exact (Nat.descFactorial_le_pow d k).trans (Nat.pow_le_pow_right (by omega : 0 < d) hk)
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : d < k)]
    exact Nat.zero_le _

/-- The sharp degree-two factor is lost at only B vertices. -/
theorem boundedBranch_degreeProduct {m : ℕ} (H : SimpleGraph (Fin m)) (d B : ℕ)
    (hd : 2 ≤ d) (bad : Finset (Fin m)) (hbad : bad.card ≤ B)
    (hregular : ∀ v, v ∉ bad → H.degree v = 2) :
    patternDegreeProduct d H ≤ (d ^ d) ^ B * (d * (d - 1)) ^ m := by
  let A := d ^ d
  let D := d * (d - 1)
  have hA : 1 ≤ A := Nat.one_le_pow d d (by omega)
  have hD : 1 ≤ D := by dsimp [D]; nlinarith [show 1 ≤ d - 1 by omega]
  have hpoint : ∀ v : Fin m, d.descFactorial (H.degree v) ≤ D * (if v ∈ bad then A else 1) := by
    intro v
    by_cases hv : v ∈ bad
    · rw [if_pos hv]
      exact (descFactorial_le_self_power d _ (by omega)).trans (by
        change A ≤ D * A
        nlinarith)
    · rw [if_neg hv, mul_one, hregular v hv]
      dsimp [D]
      simp [Nat.descFactorial_succ, Nat.mul_comm]
  have hp : patternDegreeProduct d H ≤ ∏ v : Fin m, D * (if v ∈ bad then A else 1) :=
    Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun v _ => hpoint v)
  calc
    _ ≤ _ := hp
    _ = D ^ m * A ^ bad.card := by
      rw [Finset.prod_mul_distrib]
      simp [Finset.prod_ite_mem]
    _ ≤ D ^ m * A ^ B := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega : 0 < A) hbad)
    _ = _ := by dsimp [D, A]; ring

namespace RegularGraph
variable {N d m : ℕ}

/-- Actual expected count of connected bicyclic patterns with only B branch
vertices. No graph-probability estimate is an input. -/
theorem expected_boundedBranch_bicyclic_pattern (H : SimpleGraph (Fin m))
    (hconn : H.Connected) (hexcess : graphExcess H = 2) (B : ℕ)
    (bad : Finset (Fin m)) (hbad : bad.card ≤ B) (hregular : ∀ v, v ∉ bad → H.degree v = 2)
    (K : ℕ) (hK : graphEdgeCount H ≤ K) (hN : 0 < N) (hd : 2 ≤ d)
    (hbudget : 2 * K * patternSwitchSlack d K ≤ N * d) :
    (∑ g : RegularGraph N d, weight g * (labelledPatternCount H g.graph : ℝ)) ≤
      2 * (((d ^ d : ℕ) : ℝ) ^ B) * (((d - 1 : ℕ) : ℝ) ^ m) / (N : ℝ) := by
  have hEuler := connected_graph_excess_euler H hconn
  have he : graphEdgeCount H = m + 1 := by
    simp only [hexcess, Nat.card_eq_fintype_card, Fintype.card_fin] at hEuler
    omega
  have hKpos : 1 ≤ K := by omega
  have hc := pattern_switching_denominator_control N d K hN (by omega) hKpos hbudget
  let L := N * d - patternSwitchSlack d K
  let A : ℝ := ((d ^ d : ℕ) : ℝ) ^ B
  let k : ℝ := ((d - 1 : ℕ) : ℝ)
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hLp : (0 : ℝ) < L := Nat.cast_pos.mpr hc.1
  have hk : 1 ≤ k := by dsimp [k]; exact_mod_cast (show 1 ≤ d - 1 by omega)
  have hA : 0 ≤ A := by positivity
  have hLle : (L : ℝ) ≤ (N : ℝ) * (d : ℝ) := by exact_mod_cast Nat.sub_le (N * d) (patternSwitchSlack d K)
  have hr : 1 ≤ (N : ℝ) * (d : ℝ) / (L : ℝ) := (le_div_iff₀ hLp).mpr (by simpa using hLle)
  have hInflation : ((N : ℝ) * (d : ℝ) / (L : ℝ)) ^ (m + 1) ≤ 2 :=
    (pow_le_pow_right₀ hr (by omega : m + 1 ≤ K)).trans hc.2
  have hW : (patternDegreeProduct d H : ℝ) ≤ A * (((d * (d - 1) : ℕ) : ℝ) ^ m) := by
    dsimp [A]
    exact_mod_cast boundedBranch_degreeProduct H d B hd bad hbad hregular
  have hbase := expected_labelledPatternCount_power_bound H K L hK hc.1 le_rfl
  rw [he] at hbase
  calc
    _ ≤ (N : ℝ) ^ m * ((patternDegreeProduct d H : ℝ) / (L : ℝ) ^ (m + 1)) := hbase
    _ ≤ (N : ℝ) ^ m * ((A * (((d * (d - 1) : ℕ) : ℝ) ^ m)) / (L : ℝ) ^ (m + 1)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hW (by positivity)) (by positivity)
    _ = (A * ((N : ℝ) * (d : ℝ) / (L : ℝ)) ^ (m + 1) * k ^ m) / ((N : ℝ) * (d : ℝ)) := by
      dsimp [k]
      push_cast
      rw [pow_succ, pow_succ, div_pow, mul_pow]
      field_simp [ne_of_gt hn, ne_of_gt hdpos, ne_of_gt hLp]
      ring
    _ ≤ (A * 2 * k ^ m) / ((N : ℝ) * (d : ℝ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hInflation hA) (by positivity)
    _ ≤ (A * 2 * k ^ m) / (N : ℝ) := by
      apply div_le_div_of_nonneg_left (by positivity) hn
      have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
      nlinarith
    _ = _ := by dsimp [A, k]; ring

end RegularGraph
end LocalLaw
