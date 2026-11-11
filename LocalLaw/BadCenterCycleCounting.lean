import LocalLaw.BallCycleWitness
import LocalLaw.DisjointCycleMoments

/-!
# Count non-tree ball centers using actual short cycles

Every bad center lies within radius R of an actual labelled simple cycle of
length between 3 and 2R+1. Finite unions and the sharp ball bound give a
deterministic cycle-count bound. The checked cycle expectation then gives
the first-moment estimate with the sharp (d-1)^(3R+1) base.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000

namespace LocalLaw

local instance badCycleDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem labelledCycleCount_eq_card {N : ℕ} (ell : ℕ) (G : SimpleGraph (Fin N)) :
    labelledCycleCount ell G = Nat.card {f : Fin ell ↪ Fin N // cyclePattern f ≤ G} := by
  simp only [labelledCycleCount, labelledPatternCount, cyclePattern,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Actual labelled short cycles, with the length restricted to [3,2R+1]. -/
def ShortCycleLabels {N : ℕ} (G : SimpleGraph (Fin N)) (R : ℕ) :=
  Σ ell : (Finset.Icc 3 (2 * R + 1)), {f : Fin ell.val ↪ Fin N // cyclePattern f ≤ G}

instance shortCycleLabelsFintype {N : ℕ} (G : SimpleGraph (Fin N)) (R : ℕ) :
    Fintype (ShortCycleLabels G R) := by
  unfold ShortCycleLabels
  infer_instance

theorem shortCycleLabels_length_sum {N : ℕ} (G : SimpleGraph (Fin N)) (R : ℕ) :
    (∑ c : ShortCycleLabels G R, c.1.val) =
      ∑ ell ∈ Finset.Icc 3 (2 * R + 1), ell * labelledCycleCount ell G := by
  unfold ShortCycleLabels
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id,
    ← Nat.card_eq_fintype_card, ← labelledCycleCount_eq_card]
  rw [Finset.sum_coe_sort (Finset.Icc 3 (2 * R + 1))
    (fun ell => labelledCycleCount ell G * ell)]
  apply Finset.sum_congr rfl
  intro ell _
  exact Nat.mul_comm _ _

/-- Deterministic bad-center count by the union of actual cycle neighborhoods. -/
theorem nonTreeCenters_card_le_cycles {N : ℕ} (G : SimpleGraph (Fin N))
    (d R : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, G.degree v ≤ d) :
    (nonTreeCenters G R).card ≤ ((d + 1) * (d - 1) ^ R) *
      (∑ ell ∈ Finset.Icc 3 (2 * R + 1), ell * labelledCycleCount ell G) := by
  let neighborhood : ShortCycleLabels G R → Finset (Fin N) :=
    fun c => (graphSetBall G (Set.range c.2.val) R).toFinset
  have hcover : nonTreeCenters G R ⊆ Finset.univ.biUnion neighborhood := by
    intro o ho
    have hnotree := (nonTreeCenters_membership G R o).mp ho
    obtain ⟨ell, hell, hlen, f, hf, _, i, hi⟩ := nonTree_ball_cycle_pattern G o R hnotree
    let c : ShortCycleLabels G R := ⟨⟨ell, Finset.mem_Icc.mpr ⟨hell, hlen⟩⟩, ⟨f, hf⟩⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨c, Finset.mem_univ _, ?_⟩
    change o ∈ (graphSetBall G (Set.range f) R).toFinset
    apply Set.mem_toFinset.mpr
    refine ⟨f i, ⟨i, rfl⟩, ?_⟩
    rw [G.edist_comm]
    exact hi
  have hcard : ∀ c : ShortCycleLabels G R,
      (neighborhood c).card ≤ c.1.val * ((d + 1) * (d - 1) ^ R) := by
    intro c
    have hrange : Nat.card (Set.range c.2.val) = c.1.val := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
        (Nat.card_congr (Equiv.ofInjective c.2.val c.2.val.injective)).symm
    have h := graphSetBall_card_sharp G (Set.range c.2.val) d R hd hdegree
    rw [hrange] at h
    simpa only [neighborhood, Set.toFinset_card, ← Nat.card_eq_fintype_card] using h
  calc
    _ ≤ (Finset.univ.biUnion neighborhood).card := Finset.card_le_card hcover
    _ ≤ ∑ c : ShortCycleLabels G R, (neighborhood c).card := Finset.card_biUnion_le
    _ ≤ ∑ c : ShortCycleLabels G R, c.1.val * ((d + 1) * (d - 1) ^ R) :=
      Finset.sum_le_sum (fun c _ => hcard c)
    _ = ((d + 1) * (d - 1) ^ R) * ∑ c : ShortCycleLabels G R, c.1.val := by
      rw [← Finset.sum_mul]
      exact Nat.mul_comm _ _
    _ = _ := by rw [shortCycleLabels_length_sum]

/-- A deliberately coarse polynomial factor, retaining the correct exponential base. -/
theorem weighted_short_cycle_power_sum (k M : ℕ) (hk : 1 ≤ k) :
    (∑ ell ∈ Finset.Icc 3 M, ell * 2 * k ^ ell) ≤ 2 * (M + 1) ^ 2 * k ^ M := by
  have hterm : ∀ ell ∈ Finset.Icc 3 M,
      ell * 2 * k ^ ell ≤ (M + 1) * 2 * k ^ M := by
    intro ell hell
    have hle : ell ≤ M := (Finset.mem_Icc.mp hell).2
    exact Nat.mul_le_mul (Nat.mul_le_mul_right 2 (hle.trans (Nat.le_succ _)))
      (Nat.pow_le_pow_right hk hle)
  have hcard : (Finset.Icc 3 M).card ≤ M + 1 := by
    apply (Finset.card_le_card ?_).trans_eq (Finset.card_range (M + 1))
    intro ell hell
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hell).2)
  calc
    _ ≤ ∑ _ell ∈ Finset.Icc 3 M, (M + 1) * 2 * k ^ M :=
      Finset.sum_le_sum (fun ell hell => hterm ell hell)
    _ = (Finset.Icc 3 M).card * ((M + 1) * 2 * k ^ M) := by simp
    _ ≤ (M + 1) * ((M + 1) * 2 * k ^ M) := Nat.mul_le_mul_right _ hcard
    _ = _ := by ring

namespace RegularGraph

variable {N d : ℕ}

theorem badCenters_card_le_cycles (g : RegularGraph N d) (R : ℕ) (hd : 3 ≤ d) :
    (nonTreeCenters g.graph R).card ≤ ((d + 1) * (d - 1) ^ R) *
      (∑ ell ∈ Finset.Icc 3 (2 * R + 1), ell * labelledCycleCount ell g.graph) :=
  nonTreeCenters_card_le_cycles g.graph d R hd (fun v => (g.regular v).le)

/-- Expected number of bad radius-R centers, before estimating the length sum. -/
theorem expected_badCenters_cycle_sum_bound (R K : ℕ) (hd : 3 ≤ d)
    (hK : 2 * R + 1 ≤ K) (hN : 0 < N)
    (hbudget : 2 * K * patternSwitchSlack d K ≤ N * d) :
    (∑ g : RegularGraph N d, weight g * ((nonTreeCenters g.graph R).card : ℝ)) ≤
      (((d + 1) * (d - 1) ^ R : ℕ) : ℝ) *
        ((∑ ell ∈ Finset.Icc 3 (2 * R + 1), ell * 2 * (d - 1) ^ ell : ℕ) : ℝ) := by
  let F := (d + 1) * (d - 1) ^ R
  let I := Finset.Icc 3 (2 * R + 1)
  have hfirst : (∑ g : RegularGraph N d, weight g * ((nonTreeCenters g.graph R).card : ℝ)) ≤
      ∑ g : RegularGraph N d, weight g * ((F : ℝ) *
        ∑ ell ∈ I, (ell : ℝ) * (labelledCycleCount ell g.graph : ℝ)) := by
    apply Finset.sum_le_sum
    intro g _
    apply mul_le_mul_of_nonneg_left _ g.weight_nonnegative
    exact_mod_cast g.badCenters_card_le_cycles R hd
  have hexchange : (∑ g : RegularGraph N d, weight g * ((F : ℝ) *
        ∑ ell ∈ I, (ell : ℝ) * (labelledCycleCount ell g.graph : ℝ))) =
      (F : ℝ) * ∑ ell ∈ I, (ell : ℝ) *
        ∑ g : RegularGraph N d, weight g * (labelledCycleCount ell g.graph : ℝ) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ell _
    apply Finset.sum_congr rfl
    intro g _
    ring
  apply hfirst.trans
  rw [hexchange]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg F)
  push_cast
  apply Finset.sum_le_sum
  intro ell hell
  have hbounds := Finset.mem_Icc.mp hell
  have he := expected_labelledCycleCount_le_two hbounds.1 K
    (hbounds.2.trans hK) hN (by omega : 0 < d) hbudget
  have hmul := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg ell : (0 : ℝ) ≤ ell)
  simpa only [mul_assoc, Nat.cast_pow] using hmul

/-- First moment with the sharp (d-1)^(3R+1) exponential rate. -/
theorem expected_badCenters_bound (R K : ℕ) (hd : 3 ≤ d)
    (hK : 2 * R + 1 ≤ K) (hN : 0 < N)
    (hbudget : 2 * K * patternSwitchSlack d K ≤ N * d) :
    (∑ g : RegularGraph N d, weight g * ((nonTreeCenters g.graph R).card : ℝ)) ≤
      ((2 * (d + 1) * (2 * R + 2) ^ 2 * (d - 1) ^ (3 * R + 1) : ℕ) : ℝ) := by
  apply (expected_badCenters_cycle_sum_bound R K hd hK hN hbudget).trans
  have hsum := weighted_short_cycle_power_sum (d - 1) (2 * R + 1) (by omega)
  have hprod := Nat.mul_le_mul_left ((d + 1) * (d - 1) ^ R) hsum
  have heq : ((d + 1) * (d - 1) ^ R) *
      (2 * (2 * R + 1 + 1) ^ 2 * (d - 1) ^ (2 * R + 1)) =
        2 * (d + 1) * (2 * R + 2) ^ 2 * (d - 1) ^ (3 * R + 1) := by
    rw [show 3 * R + 1 = R + (2 * R + 1) by omega, pow_add]
    ring
  rw [heq] at hprod
  exact_mod_cast hprod

/-- The first-moment tail bound for the actual number of non-tree centers. -/
theorem badCenters_tail_bound (R K : ℕ) (hd : 3 ≤ d)
    (hK : 2 * R + 1 ≤ K) (hN : 0 < N)
    (hbudget : 2 * K * patternSwitchSlack d K ≤ N * d) (t : ℝ) (ht : 0 < t) :
    eventMass (weight (N := N) (d := d))
        (fun g => t ≤ ((nonTreeCenters g.graph R).card : ℝ)) ≤
      ((2 * (d + 1) * (2 * R + 2) ^ 2 * (d - 1) ^ (3 * R + 1) : ℕ) : ℝ) / t :=
  (finite_nat_observable_markov weight weight_nonnegative
    (fun g => (nonTreeCenters g.graph R).card) t ht).trans
      (div_le_div_of_nonneg_right
        (expected_badCenters_bound R K hd hK hN hbudget) ht.le)

/-- Strict-threshold version, suitable for the complement of a structural
bound on the number of bad centers. -/
theorem badCenters_strict_tail_bound (R K : ℕ) (hd : 3 ≤ d)
    (hK : 2 * R + 1 ≤ K) (hN : 0 < N)
    (hbudget : 2 * K * patternSwitchSlack d K ≤ N * d) (t : ℝ) (ht : 0 < t) :
    eventMass (weight (N := N) (d := d))
        (fun g => t < ((nonTreeCenters g.graph R).card : ℝ)) ≤
      ((2 * (d + 1) * (2 * R + 2) ^ 2 * (d - 1) ^ (3 * R + 1) : ℕ) : ℝ) / t :=
  (eventMass_mono weight weight_nonnegative (fun _ h => h.le)).trans
    (badCenters_tail_bound R K hd hK hN hbudget t ht)

end RegularGraph

end LocalLaw
