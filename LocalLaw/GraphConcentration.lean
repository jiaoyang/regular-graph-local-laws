import LocalLaw.BernoulliSampling
import LocalLaw.OutsideEdgeCounting
import LocalLaw.ParameterGrowth

/-!
# Concentration in the actual local-resampling fiber

Uniform draws are the actual independent outside-oriented-edge function fiber.
Only the observation boundedness remains an analytic input. No independence,
MGF or tail estimate is supplied as a hypothesis. Endpoint bias retains the
exceptional-vertex density explicitly.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
noncomputable section

namespace LocalLaw

local instance graphConcentrationDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A finite uniform complex mean, in the same scalar convention as the
empirical Stieltjes transform. -/
def finiteComplexMean {E : Type*} [Fintype E] (f : E → ℂ) : ℂ :=
  (Fintype.card E : ℝ)⁻¹ • ∑ e, f e

theorem uniform_integral_eq_finiteComplexMean {E : Type*} [Fintype E] [Nonempty E]
    [MeasurableSpace E] [MeasurableSingletonClass E] (f : E → ℂ) :
    (∫ e, f e ∂(PMF.uniformOfFintype E).toMeasure) = finiteComplexMean f := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  exact (Finset.smul_sum ..).symm

theorem finiteComplexMean_sub_const {E : Type*} [Fintype E] [Nonempty E]
    (f : E → ℂ) (c : ℂ) : finiteComplexMean (fun e => f e - c) = finiteComplexMean f - c := by
  have hn : (Fintype.card E : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  have hconst : (Fintype.card E : ℝ)⁻¹ • (∑ _e : E, c) = c := by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_smul, inv_mul_cancel₀ hn, one_smul]
  unfold finiteComplexMean
  rw [Finset.sum_sub_distrib, smul_sub, hconst]



/-- Explicit Gaussian-logarithmic tail conversion; the polynomial budget is
proved, rather than assumed by a probability wrapper. -/
theorem gaussian_log_tail_le_inverse_power (N q : ℕ) (hN : 2 ≤ N)
    (hlog : 32 * ((q : ℝ) + 2) ≤ Real.log (N : ℝ)) :
    4 * Real.exp (-(Real.log (N : ℝ)) ^ 2 / 32) ≤ 1 / (N : ℝ) ^ q := by
  have hn2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hnp : (0 : ℝ) < N := by linarith
  have hL : 0 ≤ Real.log (N : ℝ) := by
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    linarith
  have hscaled := mul_le_mul_of_nonneg_right hlog hL
  have hexponent : -(Real.log (N : ℝ)) ^ 2 / 32 ≤
      -((q + 2 : ℕ) : ℝ) * Real.log (N : ℝ) := by
    push_cast
    nlinarith
  have hexp : Real.exp (-((q + 2 : ℕ) : ℝ) * Real.log (N : ℝ)) =
      1 / (N : ℝ) ^ (q + 2) := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hnp, one_div]
  calc
    4 * Real.exp (-(Real.log (N : ℝ)) ^ 2 / 32) ≤
        4 * Real.exp (-((q + 2 : ℕ) : ℝ) * Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by norm_num)
    _ = 4 / (N : ℝ) ^ (q + 2) := by rw [hexp]; ring
    _ ≤ 1 / (N : ℝ) ^ q := by
      apply (div_le_div_iff₀ (pow_pos hnp _) (pow_pos hnp _)).2
      have hsq : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hn2 2
        norm_num at h
        exact h
      calc
        4 * (N : ℝ) ^ q ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ q :=
          mul_le_mul_of_nonneg_right hsq (pow_nonneg hnp.le _)
        _ = 1 * (N : ℝ) ^ (q + 2) := by rw [pow_add]; ring

/-- The actual t=log N concentration tail is smaller than every fixed inverse
power for sufficiently large N. -/
theorem eventually_gaussian_log_tail_le_inverse_power (q : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      4 * Real.exp (-(Real.log (N : ℝ)) ^ 2 / 32) ≤ 1 / (N : ℝ) ^ q := by
  filter_upwards [Filter.eventually_ge_atTop 2,
    eventually_log_ge_nat (32 * ((q : ℝ) + 2))] with N hN hlog
  exact gaussian_log_tail_le_inverse_power N q hN hlog

section Sampling

variable {V : Type*} [Fintype V]

/-- Lemma-6.2-shaped concentration under the actual local sampling weights,
centered by the actual finite one-edge expectation. -/
theorem localSampling_boundary_concentration (G : SimpleGraph V) (T : Set V)
    (hout : Nonempty (OutsideOrientedEdge G T))
    (Z : BoundaryOrientedEdge G T → OutsideOrientedEdge G T → ℂ)
    (b : ℝ≥0) (hb : 0 < b) (w : BoundaryOrientedEdge G T → ℂ)
    (s : Finset (BoundaryOrientedEdge G T)) (hweights : 0 < ∑ i ∈ s, ‖w i‖ ^ 2)
    (hbound : ∀ i ∈ s, ∀ e, ‖Z i e‖ ≤ (b : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    eventMass (localSamplingWeight G T)
      (fun S => t * b * Real.sqrt (∑ i ∈ s, ‖w i‖ ^ 2) ≤
        ‖∑ i ∈ s, w i * (Z i (S i) - finiteComplexMean (Z i))‖) ≤
      4 * Real.exp (-t ^ 2 / 32) := by
  letI : Nonempty (OutsideOrientedEdge G T) := hout
  letI : MeasurableSpace (OutsideOrientedEdge G T) := ⊤
  have h := uniform_finite_boundary_eventMass_concentration Z b hb w s hweights hbound t ht
  simpa only [localSamplingWeight, LocalSamplingFiber, uniform_integral_eq_finiteComplexMean] using h


/-- Polynomial version of actual finite-fiber concentration at t=log N.
Only the concrete boundedness and weight-nondegeneracy conditions remain. -/
theorem localSampling_boundary_polynomial_concentration (G : SimpleGraph V) (T : Set V)
    (hout : Nonempty (OutsideOrientedEdge G T))
    (Z : BoundaryOrientedEdge G T → OutsideOrientedEdge G T → ℂ)
    (b : ℝ≥0) (hb : 0 < b) (w : BoundaryOrientedEdge G T → ℂ)
    (s : Finset (BoundaryOrientedEdge G T)) (hweights : 0 < ∑ i ∈ s, ‖w i‖ ^ 2)
    (hbound : ∀ i ∈ s, ∀ e, ‖Z i e‖ ≤ (b : ℝ)) (N q : ℕ) (hN : 2 ≤ N)
    (hlog : 32 * ((q : ℝ) + 2) ≤ Real.log (N : ℝ)) :
    eventMass (localSamplingWeight G T)
      (fun S => Real.log (N : ℝ) * b * Real.sqrt (∑ i ∈ s, ‖w i‖ ^ 2) ≤
        ‖∑ i ∈ s, w i * (Z i (S i) - finiteComplexMean (Z i))‖) ≤ 1 / (N : ℝ) ^ q := by
  have hL : 0 ≤ Real.log (N : ℝ) := by
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    linarith
  exact (localSampling_boundary_concentration G T hout Z b hb w s hweights hbound
    (Real.log (N : ℝ)) hL).trans (gaussian_log_tail_le_inverse_power N q hN hlog)

/-- The actual diagonal observation G^(T)_{cc}, with c the sampled edge's
second endpoint and the correctly induced deleted graph. -/
def outsideCavityValue (G : SimpleGraph V) (d : ℕ) (T : Set V) (z : ℂ)
    (e : OutsideOrientedEdge G T) : ℂ :=
  green (normalizedAdjacency (outsideGraph G T) d) z
    ⟨e.val.2, e.property.2.2⟩ ⟨e.val.2, e.property.2.2⟩

/-- The source observation before centering; Y may be the finite cavity-tree
iterate at the random scalar boundary parameter. -/
def outsideCavityDeviation (G : SimpleGraph V) (d : ℕ) (T : Set V) (z Y : ℂ)
    (e : OutsideOrientedEdge G T) : ℂ := outsideCavityValue G d T z e - Y

/-- The graph Green-function specialization. The remaining bound on the
concrete observations is exactly the analytic input needed from the local
regularity estimates. -/
theorem localSampling_cavity_concentration (G : SimpleGraph V) (d : ℕ) (T : Set V)
    (z Y : ℂ) (hout : Nonempty (OutsideOrientedEdge G T))
    (b : ℝ≥0) (hb : 0 < b) (w : BoundaryOrientedEdge G T → ℂ)
    (s : Finset (BoundaryOrientedEdge G T)) (hweights : 0 < ∑ i ∈ s, ‖w i‖ ^ 2)
    (hbound : ∀ e, ‖outsideCavityDeviation G d T z Y e‖ ≤ (b : ℝ))
    (t : ℝ) (ht : 0 ≤ t) :
    eventMass (localSamplingWeight G T)
      (fun S => t * b * Real.sqrt (∑ i ∈ s, ‖w i‖ ^ 2) ≤
        ‖∑ i ∈ s, w i * (outsideCavityDeviation G d T z Y (S i) -
          finiteComplexMean (outsideCavityDeviation G d T z Y))‖) ≤
      4 * Real.exp (-t ^ 2 / 32) := by
  exact localSampling_boundary_concentration G T hout
    (fun _ e => outsideCavityDeviation G d T z Y e) b hb w s hweights
    (fun _ _ e => hbound e) t ht

end Sampling

section EndpointBias

variable {N d : ℕ}

/-- Endpoint probability 2/N turns sparse exceptional vertices into an
explicit bias budget for an outside-edge average. It is not replaced by an
assumed uniform endpoint distribution. -/
theorem outside_endpoint_mean_bias (g : RegularGraph N d) (T : Set (Fin N))
    (hN : 0 < N) (hd : 0 < d) (hT : 4 * Nat.card T ≤ N)
    (f : Fin N → ℂ) (target : ℂ) (bad : Finset (Fin N)) (δ M : ℝ) (hM : 0 ≤ M)
    (hgood : ∀ v, v ∉ bad → ‖f v - target‖ ≤ δ)
    (hbad : ∀ v, v ∈ bad → ‖f v - target‖ ≤ δ + M) :
    ‖finiteComplexMean (fun e : OutsideOrientedEdge g.graph T => f (outsideEdgeSecond g.graph T e)) - target‖ ≤
      δ + (2 * (bad.card : ℝ) / (N : ℝ)) * M := by
  let E := OutsideOrientedEdge g.graph T
  letI : Nonempty E := g.outside_edge_nonempty T hN hd hT
  let badEdges : Finset E := Finset.univ.filter (fun e => outsideEdgeSecond g.graph T e ∈ bad)
  have hcard : 0 < Fintype.card E := Fintype.card_pos
  have hmean := sparse_average_bound (fun e : E => f (outsideEdgeSecond g.graph T e) - target)
    badEdges δ M hcard
    (fun e he => hgood _ (by simpa only [badEdges, Finset.mem_filter, Finset.mem_univ, true_and] using he))
    (fun e he => hbad _ (by simpa only [badEdges, Finset.mem_filter, Finset.mem_univ, true_and] using he))
  change ‖finiteComplexMean (fun e : E => f (outsideEdgeSecond g.graph T e) - target)‖ ≤ _ at hmean
  rw [finiteComplexMean_sub_const] at hmean
  have hprob := g.outside_second_endpoint_set_probability T hN hd (g.outside_edge_real_size T hT) bad
  have hdensity : (badEdges.card : ℝ) / (Fintype.card E : ℝ) ≤ 2 * (bad.card : ℝ) / (N : ℝ) := by
    rw [uniform_eventMass_cardinality, Nat.card_eq_fintype_card, Fintype.card_subtype] at hprob
    exact hprob
  exact hmean.trans (add_le_add_left (mul_le_mul_of_nonneg_right hdensity hM) δ)

end EndpointBias

end LocalLaw
