import LocalLaw.GraphConcentration

/-!
# Simultaneous weighted concentration about a biased target

The actual independent outside-edge sampling law gives a bound for every
finite weight family, including identically zero weights. The observation's
true one-edge bias is retained explicitly; no tail or independence estimate
is assumed. Strict failure events handle degenerate weights correctly.
-/

open scoped BigOperators NNReal
noncomputable section
namespace LocalLaw
local instance boundaryFamilyDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V]

theorem localSampling_boundary_strict_concentration (G : SimpleGraph V) (T : Set V)
    (hout : Nonempty (OutsideOrientedEdge G T))
    (Z : BoundaryOrientedEdge G T → OutsideOrientedEdge G T → ℂ)
    (b : ℝ≥0) (hb : 0 < b) (w : BoundaryOrientedEdge G T → ℂ)
    (s : Finset (BoundaryOrientedEdge G T))
    (hbound : ∀ i ∈ s, ∀ e, ‖Z i e‖ ≤ (b : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    eventMass (localSamplingWeight G T)
      (fun S => t * b * Real.sqrt (∑ i ∈ s, ‖w i‖ ^ 2) <
        ‖∑ i ∈ s, w i * (Z i (S i) - finiteComplexMean (Z i))‖) ≤
      4 * Real.exp (-t ^ 2 / 32) := by
  by_cases hpos : 0 < ∑ i ∈ s, ‖w i‖ ^ 2
  · apply (eventMass_mono _ finiteUniformWeight_nonneg (fun _ h => h.le)).trans
    exact localSampling_boundary_concentration G T hout Z b hb w s hpos hbound t ht
  · have hsumzero : (∑ i ∈ s, ‖w i‖ ^ 2) = 0 :=
      le_antisymm (le_of_not_gt hpos) (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    have hwzero : ∀ i ∈ s, w i = 0 := by
      intro i hi
      have hh := Finset.single_le_sum (fun j (_ : j ∈ s) => sq_nonneg ‖w j‖) hi
      rw [hsumzero] at hh
      have hnorm : ‖w i‖ = 0 := by nlinarith [norm_nonneg (w i)]
      exact norm_eq_zero.mp hnorm
    have hzero : ∀ S : LocalSamplingFiber G T,
        (∑ i ∈ s, w i * (Z i (S i) - finiteComplexMean (Z i))) = 0 := by
      intro S
      exact Finset.sum_eq_zero (fun i hi => by rw [hwzero i hi, zero_mul])
    have hevent : (fun S : LocalSamplingFiber G T => t * b * Real.sqrt (∑ i ∈ s, ‖w i‖ ^ 2) <
        ‖∑ i ∈ s, w i * (Z i (S i) - finiteComplexMean (Z i))‖) = fun _ => False := by
      funext S
      apply propext
      simp only [hzero, norm_zero, hsumzero, Real.sqrt_zero, mul_zero, lt_self_iff_false]
    rw [hevent]
    simp only [eventMass, if_false, Finset.sum_const_zero]
    positivity

theorem weighted_target_deviation_bound {I : Type*}
    (s : Finset I) (w observation mean target : I → ℂ) (δ : ℝ)
    (hbias : ∀ i ∈ s, ‖mean i - target i‖ ≤ δ) :
    ‖∑ i ∈ s, w i * (observation i - target i)‖ ≤
      ‖∑ i ∈ s, w i * (observation i - mean i)‖ + δ * ∑ i ∈ s, ‖w i‖ := by
  have hid : (∑ i ∈ s, w i * (observation i - target i)) =
      (∑ i ∈ s, w i * (observation i - mean i)) + ∑ i ∈ s, w i * (mean i - target i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hid]
  apply (norm_add_le _ _).trans
  apply add_le_add_left
  calc
    _ ≤ ∑ i ∈ s, ‖w i * (mean i - target i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖w i‖ * δ := Finset.sum_le_sum (fun i hi => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbias i hi) (norm_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Actual weighted independent sampling, centered at a prescribed target,
with its proved one-edge bias and including all zero-weight cases. -/
theorem localSampling_weighted_target_concentration (G : SimpleGraph V) (T : Set V)
    (hout : Nonempty (OutsideOrientedEdge G T))
    (Z : BoundaryOrientedEdge G T → OutsideOrientedEdge G T → ℂ)
    (target w : BoundaryOrientedEdge G T → ℂ)
    (s : Finset (BoundaryOrientedEdge G T)) (b : ℝ≥0) (hb : 0 < b)
    (hbound : ∀ i ∈ s, ∀ e, ‖Z i e‖ ≤ (b : ℝ)) (δ : ℝ)
    (hbias : ∀ i ∈ s, ‖finiteComplexMean (Z i) - target i‖ ≤ δ)
    (t : ℝ) (ht : 0 ≤ t) :
    eventMass (localSamplingWeight G T)
      (fun S => t * b * Real.sqrt (∑ i ∈ s, ‖w i‖ ^ 2) + δ * (∑ i ∈ s, ‖w i‖) <
        ‖∑ i ∈ s, w i * (Z i (S i) - target i)‖) ≤ 4 * Real.exp (-t ^ 2 / 32) := by
  apply (eventMass_mono _ finiteUniformWeight_nonneg ?_).trans
    (localSampling_boundary_strict_concentration G T hout Z b hb w s hbound t ht)
  intro S hS
  have hh := weighted_target_deviation_bound s w (fun i => Z i (S i))
    (fun i => finiteComplexMean (Z i)) target δ hbias
  linarith

/-- Every finite family of actual source weights is controlled in one event;
the only union cost is its actual cardinality. -/
theorem localSampling_weighted_family_concentration {J : Type*} [Fintype J]
    (G : SimpleGraph V) (T : Set V) (hout : Nonempty (OutsideOrientedEdge G T))
    (Z : BoundaryOrientedEdge G T → OutsideOrientedEdge G T → ℂ)
    (target : BoundaryOrientedEdge G T → ℂ) (w : J → BoundaryOrientedEdge G T → ℂ)
    (s : Finset (BoundaryOrientedEdge G T)) (b : ℝ≥0) (hb : 0 < b)
    (hbound : ∀ i ∈ s, ∀ e, ‖Z i e‖ ≤ (b : ℝ)) (δ : ℝ)
    (hbias : ∀ i ∈ s, ‖finiteComplexMean (Z i) - target i‖ ≤ δ)
    (t : ℝ) (ht : 0 ≤ t) :
    eventMass (localSamplingWeight G T)
      (fun S => ∃ j : J, t * b * Real.sqrt (∑ i ∈ s, ‖w j i‖ ^ 2) + δ * (∑ i ∈ s, ‖w j i‖) <
        ‖∑ i ∈ s, w j i * (Z i (S i) - target i)‖) ≤
      (Fintype.card J : ℝ) * (4 * Real.exp (-t ^ 2 / 32)) := by
  have hh := eventMass_exists_finset_le (Finset.univ : Finset J) (localSamplingWeight G T)
    finiteUniformWeight_nonneg (fun j S => t * b * Real.sqrt (∑ i ∈ s, ‖w j i‖ ^ 2) +
      δ * (∑ i ∈ s, ‖w j i‖) < ‖∑ i ∈ s, w j i * (Z i (S i) - target i)‖)
  simp only [Finset.mem_univ, true_and] at hh
  apply hh.trans
  calc
    _ ≤ ∑ _j : J, 4 * Real.exp (-t ^ 2 / 32) := Finset.sum_le_sum (fun j _ =>
      localSampling_weighted_target_concentration G T hout Z target (w j) s b hb hbound δ hbias t ht)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end LocalLaw
