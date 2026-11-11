import LocalLaw.BoundedBranchPatternProbability
import LocalLaw.DisjointCycleMoments

/-!
# Union bounds for actual finite bicyclic pattern families

Each family member is a connected excess-two graph with a bounded number of
vertices not of degree two. An occurring member contributes an actual labelled
copy, so first moments and a finite union bound control its occurrence.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance finitePatternFamilyDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

variable {N d : ℕ}

/-- A present pattern gives a positive actual labelled-copy count. -/
theorem pattern_occurrence_mass_le_expectation {m : ℕ} (H : SimpleGraph (Fin m)) :
    eventMass (weight (N := N) (d := d)) (fun g => ∃ f : Fin m ↪ Fin N, H.map f ≤ g.graph) ≤
      ∑ g : RegularGraph N d, weight g * (labelledPatternCount H g.graph : ℝ) := by
  have hMarkov := finite_nat_observable_markov weight weight_nonnegative
    (fun g : RegularGraph N d => labelledPatternCount H g.graph) 1 (by norm_num)
  have hsubset : ∀ g : RegularGraph N d, (∃ f : Fin m ↪ Fin N, H.map f ≤ g.graph) →
      (1 : ℝ) ≤ (labelledPatternCount H g.graph : ℝ) := by
    rintro g ⟨f, hf⟩
    have hpos : 0 < labelledPatternCount H g.graph := by
      unfold labelledPatternCount
      exact Finset.card_pos.mpr ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩⟩
    exact_mod_cast hpos
  exact (eventMass_mono weight weight_nonnegative hsubset).trans (by simpa only [div_one] using hMarkov)

/-- A finite family costs only its actual cardinality, with every pattern
probability supplied by the checked switching and falling-degree estimates. -/
theorem finite_bicyclic_pattern_family_bound {I : Type*} [Fintype I]
    (m : I → ℕ) (H : ∀ i, SimpleGraph (Fin (m i))) (B M K : ℕ)
    (bad : ∀ i, Finset (Fin (m i)))
    (hconn : ∀ i, (H i).Connected) (hexcess : ∀ i, graphExcess (H i) = 2)
    (hbad : ∀ i, (bad i).card ≤ B) (hdegree : ∀ i v, v ∉ bad i → (H i).degree v = 2)
    (hsize : ∀ i, m i ≤ M) (hK : ∀ i, graphEdgeCount (H i) ≤ K)
    (hN : 0 < N) (hd : 2 ≤ d)
    (hbudget : 2 * K * patternSwitchSlack d K ≤ N * d) :
    eventMass (weight (N := N) (d := d)) (fun g =>
      ∃ i : I, ∃ f : Fin (m i) ↪ Fin N, (H i).map f ≤ g.graph) ≤
      (Fintype.card I : ℝ) * (2 * (((d ^ d : ℕ) : ℝ) ^ B) * (((d - 1 : ℕ) : ℝ) ^ M) / (N : ℝ)) := by
  classical
  have hk : (1 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ d - 1 by omega)
  have hper : ∀ i : I,
      eventMass (weight (N := N) (d := d)) (fun g => ∃ f : Fin (m i) ↪ Fin N, (H i).map f ≤ g.graph) ≤
        2 * (((d ^ d : ℕ) : ℝ) ^ B) * (((d - 1 : ℕ) : ℝ) ^ M) / (N : ℝ) := by
    intro i
    have h := (pattern_occurrence_mass_le_expectation (H i)).trans
      (expected_boundedBranch_bicyclic_pattern (H i) (hconn i) (hexcess i) B
        (bad i) (hbad i) (hdegree i) K (hK i) hN hd hbudget)
    apply h.trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hk (hsize i)) (by positivity)) (Nat.cast_nonneg N)
  calc
    _ = eventMass weight (fun g => ∃ i ∈ (Finset.univ : Finset I),
        ∃ f : Fin (m i) ↪ Fin N, (H i).map f ≤ g.graph) := by simp
    _ ≤ ∑ i : I, eventMass weight (fun g => ∃ f : Fin (m i) ↪ Fin N, (H i).map f ≤ g.graph) :=
      eventMass_exists_finset_le _ weight weight_nonnegative _
    _ ≤ ∑ _i : I, (2 * (((d ^ d : ℕ) : ℝ) ^ B) * (((d - 1 : ℕ) : ℝ) ^ M) / (N : ℝ)) :=
      Finset.sum_le_sum (fun i _ => hper i)
    _ = _ := by simp [nsmul_eq_mul]

end RegularGraph
end LocalLaw
