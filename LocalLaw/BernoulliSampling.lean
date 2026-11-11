import LocalLaw.BoundaryConcentration
import LocalLaw.EndpointSampling

/-!
# Rare bad-sample counts under finite independent uniform sampling

The proof covers an event with at least k bad coordinates by cylinders indexed
by k-element subsets, computes their exact product probability, and takes a
finite union bound. Unlike a b=1 Hoeffding estimate, the bound retains p^k and
therefore gives polynomially small probabilities for constant k and small p.
-/

open MeasureTheory Real
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace LocalLaw

local instance bernoulliSamplingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section ProductCylinder

variable {I E : Type*} [Fintype I] [MeasurableSpace E]

/-- Exact probability of requiring every coordinate in S to land in Bad. -/
theorem product_bad_cylinder_probability (ν : Measure E) [IsProbabilityMeasure ν]
    (Bad : Set E) (S : Finset I) :
    (Measure.pi (fun _i : I => ν)).real {f : I → E | ∀ i ∈ S, f i ∈ Bad} =
      (ν.real Bad) ^ S.card := by
  classical
  have hset : {f : I → E | ∀ i ∈ S, f i ∈ Bad} =
      Set.univ.pi (fun i => if i ∈ S then Bad else Set.univ) := by
    ext f
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h i
      by_cases hi : i ∈ S
      · simpa only [if_pos hi] using h i hi
      · simp only [if_neg hi, Set.mem_univ]
    · intro h i hi
      simpa only [if_pos hi] using h i
  change ((Measure.pi (fun _i : I => ν)) {f : I → E | ∀ i ∈ S, f i ∈ Bad}).toReal = _
  rw [hset, Measure.pi_pi]
  simp [apply_ite, Finset.prod_ite_mem, ENNReal.toReal_pow]
  rfl

end ProductCylinder

section UniformBadCounts

variable {I E : Type*} [Fintype I] [Fintype E] [Nonempty E]
variable [MeasurableSpace E] [MeasurableSingletonClass E]

/-- The indices of samples that land in the specified finite bad set. -/
def badSampleIndices (Bad : Finset E) (f : I → E) : Finset I :=
  Finset.univ.filter (fun i => f i ∈ Bad)

/-- The actual one-draw bad probability under the uniform edge law. -/
def uniformBadProbability (Bad : Finset E) : ℝ :=
  (Bad.card : ℝ) / (Fintype.card E : ℝ)

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
theorem uniformBadProbability_nonnegative (Bad : Finset E) :
    0 ≤ uniformBadProbability Bad := by unfold uniformBadProbability; positivity

/-- Exact single-draw probability, in the measure API used by product sampling. -/
theorem uniform_bad_probability (Bad : Finset E) :
    (PMF.uniformOfFintype E).toMeasure.real (Bad : Set E) = uniformBadProbability Bad := by
  have h := uniform_pmf_eventMass (Ω := E) (fun e => e ∈ Bad) Bad.measurableSet
  rw [uniform_eventMass_cardinality] at h
  change (PMF.uniformOfFintype E).toMeasure.real (Bad : Set E) = _ at h
  have hcard : Nat.card {e : E // e ∈ Bad} = Bad.card := by
    change Nat.card (↑Bad) = Bad.card
    simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
  simpa only [hcard, uniformBadProbability] using h

/-- Exact probability of a prescribed finite family of bad uniform draws. -/
theorem uniform_bad_cylinder_probability (Bad : Finset E) (S : Finset I) :
    (uniformBoundarySampling (ι := I) (A := E)).real
      {f : I → E | ∀ i ∈ S, f i ∈ Bad} = (uniformBadProbability Bad) ^ S.card := by
  have h := product_bad_cylinder_probability (PMF.uniformOfFintype E).toMeasure (Bad : Set E) S
  rw [uniform_bad_probability] at h
  exact h

/-- The rare-event union bound: at least k bad coordinates require some
k-element coordinate set to be entirely bad. This also covers k>card(I). -/
theorem uniform_bad_sample_choose_tail (Bad : Finset E) (k : ℕ) :
    (uniformBoundarySampling (ι := I) (A := E)).real
      {f : I → E | k ≤ (badSampleIndices Bad f).card} ≤
        ((Fintype.card I).choose k : ℝ) * (uniformBadProbability Bad) ^ k := by
  let samples := uniformBoundarySampling (ι := I) (A := E)
  let subsets := (Finset.univ : Finset I).powersetCard k
  let cylinder : Finset I → Set (I → E) := fun S => {f | ∀ i ∈ S, f i ∈ Bad}
  have hcover : {f : I → E | k ≤ (badSampleIndices Bad f).card} ⊆
      ⋃ S ∈ subsets, cylinder S := by
    intro f hf
    obtain ⟨S, hsubset, hcard⟩ := Finset.exists_subset_card_eq hf
    apply Set.mem_iUnion.mpr
    refine ⟨S, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hcard⟩
    · intro i hi
      exact (Finset.mem_filter.mp (hsubset hi)).2
  have hcylinder : ∀ S ∈ subsets, samples.real (cylinder S) = (uniformBadProbability Bad) ^ k := by
    intro S hS
    have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    change (uniformBoundarySampling (ι := I) (A := E)).real {f : I → E | ∀ i ∈ S, f i ∈ Bad} = _
    rw [uniform_bad_cylinder_probability, hcard]
  calc
    samples.real {f : I → E | k ≤ (badSampleIndices Bad f).card} ≤
        samples.real (⋃ S ∈ subsets, cylinder S) := measureReal_mono hcover
    _ ≤ ∑ S ∈ subsets, samples.real (cylinder S) := measureReal_biUnion_finset_le _ _
    _ = ∑ _S ∈ subsets, (uniformBadProbability Bad) ^ k :=
      Finset.sum_congr rfl (fun S hS => hcylinder S hS)
    _ = ((Fintype.card I).choose k : ℝ) * (uniformBadProbability Bad) ^ k := by
      simp only [subsets, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
        nsmul_eq_mul]

/-- A coarser but useful power bound, preserving the small bad probability. -/
theorem uniform_bad_sample_power_tail (Bad : Finset E) (k : ℕ) :
    (uniformBoundarySampling (ι := I) (A := E)).real
      {f : I → E | k ≤ (badSampleIndices Bad f).card} ≤
        ((Fintype.card I : ℝ) * uniformBadProbability Bad) ^ k := by
  apply (uniform_bad_sample_choose_tail (I := I) Bad k).trans
  have hchoose : ((Fintype.card I).choose k : ℝ) ≤ (Fintype.card I : ℝ) ^ k := by
    exact_mod_cast Nat.choose_le_pow (Fintype.card I) k
  have h := mul_le_mul_of_nonneg_right hchoose
    (pow_nonneg (uniformBadProbability_nonnegative Bad) k)
  simpa only [mul_pow] using h

/-- Explicit polynomial rare-event budget for constant k. The probability
input is just the one-draw counting ratio times the number of draws. -/
theorem uniform_bad_sample_polynomial_tail (Bad : Finset E) (k N γ q : ℕ)
    (hN : 0 < N) (hexponent : q ≤ γ * k)
    (hsmall : (Fintype.card I : ℝ) * uniformBadProbability Bad ≤ 1 / (N : ℝ) ^ γ) :
    (uniformBoundarySampling (ι := I) (A := E)).real
      {f : I → E | k ≤ (badSampleIndices Bad f).card} ≤ 1 / (N : ℝ) ^ q := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt hN
  apply (uniform_bad_sample_power_tail (I := I) Bad k).trans
  calc
    ((Fintype.card I : ℝ) * uniformBadProbability Bad) ^ k ≤ (1 / (N : ℝ) ^ γ) ^ k :=
      pow_le_pow_left₀
        (mul_nonneg (Nat.cast_nonneg _) (uniformBadProbability_nonnegative Bad)) hsmall k
    _ = 1 / (N : ℝ) ^ (γ * k) := by rw [div_pow, one_pow, ← pow_mul]
    _ ≤ 1 / (N : ℝ) ^ q :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hNone hexponent)

/-- Independent uniform draws are exactly the uniform law on the full finite
function space. This connects the product-measure and local-sampling-fiber APIs. -/
theorem uniformBoundarySampling_eq_uniform_function_measure :
    uniformBoundarySampling (ι := I) (A := E) = (PMF.uniformOfFintype (I → E)).toMeasure := by
  classical
  apply Measure.ext_of_singleton
  intro f
  calc
    (uniformBoundarySampling (ι := I) (A := E)) {f} =
        ∏ i : I, (PMF.uniformOfFintype E).toMeasure {f i} := by
      unfold uniformBoundarySampling
      rw [← Set.univ_pi_singleton f, Measure.pi_pi]
    _ = ∏ _i : I, ((Fintype.card E : ℝ≥0∞)⁻¹) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
        PMF.uniformOfFintype_apply]
    _ = (PMF.uniformOfFintype (I → E)).toMeasure {f} := by
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
        PMF.uniformOfFintype_apply]
      simp [Fintype.card_fun, ENNReal.inv_pow]

/-- The choose-tail bound in the exact finite-weight API of local sampling. -/
theorem uniform_bad_sample_eventMass_tail (Bad : Finset E) (k : ℕ) :
    eventMass (finiteUniformWeight (I → E))
      (fun f => k ≤ (badSampleIndices Bad f).card) ≤
        ((Fintype.card I).choose k : ℝ) * (uniformBadProbability Bad) ^ k := by
  have hEvent : MeasurableSet {f : I → E | k ≤ (badSampleIndices Bad f).card} :=
    (Set.toFinite _).measurableSet
  rw [← uniform_pmf_eventMass (fun f : I → E => k ≤ (badSampleIndices Bad f).card) hEvent,
    ← uniformBoundarySampling_eq_uniform_function_measure]
  exact uniform_bad_sample_choose_tail Bad k

/-- The polynomial bad-count budget for the actual uniform function fiber. -/
theorem uniform_bad_sample_eventMass_polynomial (Bad : Finset E) (k N γ q : ℕ)
    (hN : 0 < N) (hexponent : q ≤ γ * k)
    (hsmall : (Fintype.card I : ℝ) * uniformBadProbability Bad ≤ 1 / (N : ℝ) ^ γ) :
    eventMass (finiteUniformWeight (I → E))
      (fun f => k ≤ (badSampleIndices Bad f).card) ≤ 1 / (N : ℝ) ^ q := by
  have hEvent : MeasurableSet {f : I → E | k ≤ (badSampleIndices Bad f).card} :=
    (Set.toFinite _).measurableSet
  rw [← uniform_pmf_eventMass (fun f : I → E => k ≤ (badSampleIndices Bad f).card) hEvent,
    ← uniformBoundarySampling_eq_uniform_function_measure]
  exact uniform_bad_sample_polynomial_tail Bad k N γ q hN hexponent hsmall

/-- Equation-(6.3)-shaped concentration in the actual finite uniform function
fiber API. Measurability is automatic for finite edge observations. -/
theorem uniform_finite_boundary_eventMass_concentration (Z : I → E → ℂ)
    (b : ℝ≥0) (hb : 0 < b) (w : I → ℂ) (s : Finset I)
    (hweights : 0 < ∑ i ∈ s, ‖w i‖ ^ 2)
    (hbound : ∀ i ∈ s, ∀ e, ‖Z i e‖ ≤ (b : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    eventMass (finiteUniformWeight (I → E))
      (fun f => t * b * Real.sqrt (∑ i ∈ s, ‖w i‖ ^ 2) ≤
        ‖∑ i ∈ s, w i * (Z i (f i) - ∫ e, Z i e ∂(PMF.uniformOfFintype E).toMeasure)‖) ≤
      4 * exp (-t ^ 2 / 32) := by
  let event : (I → E) → Prop := fun f =>
    t * b * Real.sqrt (∑ i ∈ s, ‖w i‖ ^ 2) ≤
      ‖∑ i ∈ s, w i * (Z i (f i) - ∫ e, Z i e ∂(PMF.uniformOfFintype E).toMeasure)‖
  have hEvent : MeasurableSet {f | event f} := (Set.toFinite _).measurableSet
  change eventMass (finiteUniformWeight (I → E)) event ≤ _
  rw [← uniform_pmf_eventMass event hEvent, ← uniformBoundarySampling_eq_uniform_function_measure]
  exact uniform_finite_boundary_concentration Z (fun i => measurable_of_countable (Z i))
    b hb w s hweights hbound t ht

/-- Fractional one-draw decay exponents, as needed when gamma=1-c in
Proposition 5.10. No integer lower bound on the decay exponent is imposed. -/
theorem uniform_bad_sample_real_exponent_tail (Bad : Finset E) (k N q : ℕ) (γ : ℝ)
    (hN : 0 < N) (hexponent : (q : ℝ) ≤ γ * (k : ℝ))
    (hsmall : (Fintype.card I : ℝ) * uniformBadProbability Bad ≤ (N : ℝ) ^ (-γ)) :
    (uniformBoundarySampling (ι := I) (A := E)).real
      {f : I → E | k ≤ (badSampleIndices Bad f).card} ≤ 1 / (N : ℝ) ^ q := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt hN
  apply (uniform_bad_sample_power_tail (I := I) Bad k).trans
  calc
    ((Fintype.card I : ℝ) * uniformBadProbability Bad) ^ k ≤ ((N : ℝ) ^ (-γ)) ^ k :=
      pow_le_pow_left₀
        (mul_nonneg (Nat.cast_nonneg _) (uniformBadProbability_nonnegative Bad)) hsmall k
    _ = (N : ℝ) ^ ((-γ) * (k : ℝ)) :=
      (Real.rpow_mul_natCast hNpos.le (-γ) k).symm
    _ ≤ (N : ℝ) ^ (-(q : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hNone (by linarith)
    _ = 1 / (N : ℝ) ^ q := by rw [Real.rpow_neg hNpos.le, Real.rpow_natCast, one_div]

/-- Fractional-exponent polynomial decay in the original finite uniform
function-space eventMass API. -/
theorem uniform_bad_sample_eventMass_real_exponent (Bad : Finset E) (k N q : ℕ) (γ : ℝ)
    (hN : 0 < N) (hexponent : (q : ℝ) ≤ γ * (k : ℝ))
    (hsmall : (Fintype.card I : ℝ) * uniformBadProbability Bad ≤ (N : ℝ) ^ (-γ)) :
    eventMass (finiteUniformWeight (I → E))
      (fun f => k ≤ (badSampleIndices Bad f).card) ≤ 1 / (N : ℝ) ^ q := by
  have hEvent : MeasurableSet {f : I → E | k ≤ (badSampleIndices Bad f).card} :=
    (Set.toFinite _).measurableSet
  rw [← uniform_pmf_eventMass (fun f : I → E => k ≤ (badSampleIndices Bad f).card) hEvent,
    ← uniformBoundarySampling_eq_uniform_function_measure]
  exact uniform_bad_sample_real_exponent_tail Bad k N q γ hN hexponent hsmall

end UniformBadCounts

end LocalLaw
