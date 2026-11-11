import LocalLaw.WardCorrelationParameters
import LocalLaw.SharpSamplingCounts
import LocalLaw.BernoulliSampling
import LocalLaw.GraphResamplingDefect

/-!
# Few correlated samples in the actual independent resampling fiber

The one-edge inverse-log correlation estimate and the actual polylogarithmic
boundary-label count imply an arbitrary inverse-power tail for ceil(log N)
correlated samples. Independence, the tail and its numerical smallness are
proved. The generic sampling estimates take a local diagonal-imaginary-part
cap as a parameter. `DeletedDiagonalReference` proves the source model
bounds, and `SourceCorrelationProbability` supplies the specialized tail.
-/

open scoped BigOperators
noncomputable section

namespace LocalLaw

local instance correlationSamplingDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem uniformBadProbability_eq_eventMass {E : Type*} [Fintype E] (Bad : Finset E) :
    uniformBadProbability Bad = eventMass (finiteUniformWeight E) (fun e => e ∈ Bad) := by
  rw [uniform_eventMass_cardinality]
  have hcard : Nat.card {e : E // e ∈ Bad} = Bad.card := by
    change Nat.card (↑Bad) = Bad.card
    simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hcard]
  rfl

/-- Actual finite-weight version of the product counting power bound. -/
theorem uniform_bad_sample_eventMass_power_tail {I E : Type*}
    [Fintype I] [Fintype E] [Nonempty E] (Bad : Finset E) (k : ℕ) :
    eventMass (finiteUniformWeight (I → E))
      (fun f => k ≤ (badSampleIndices Bad f).card) ≤
        ((Fintype.card I : ℝ) * uniformBadProbability Bad) ^ k := by
  letI : MeasurableSpace E := ⊤
  apply (uniform_bad_sample_eventMass_tail (I := I) Bad k).trans
  have hchoose : ((Fintype.card I).choose k : ℝ) ≤ (Fintype.card I : ℝ) ^ k := by
    exact_mod_cast Nat.choose_le_pow (Fintype.card I) k
  have h := mul_le_mul_of_nonneg_right hchoose
    (pow_nonneg (uniformBadProbability_nonnegative Bad) k)
  simpa only [mul_pow] using h

/-- A ceil(log N) count turns any fixed sufficiently small mean into a
polynomial tail. No final inverse-power estimate is a premise. -/
theorem ceil_log_power_le_inverse_power (p : ℝ) (N q : ℕ)
    (hN : 0 < N) (hp : 0 ≤ p) (hsmall : p ≤ Real.exp (-(q : ℝ))) :
    p ^ Nat.ceil (Real.log (N : ℝ)) ≤ 1 / (N : ℝ) ^ q := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  calc
    p ^ Nat.ceil (Real.log (N : ℝ)) ≤
        (Real.exp (-(q : ℝ))) ^ Nat.ceil (Real.log (N : ℝ)) :=
      pow_le_pow_left₀ hp hsmall _
    _ = Real.exp ((Nat.ceil (Real.log (N : ℝ)) : ℝ) * (-(q : ℝ))) :=
      (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (-(q : ℝ) * Real.log (N : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hk := Nat.le_ceil (Real.log (N : ℝ))
      nlinarith [show (0 : ℝ) ≤ q from Nat.cast_nonneg q]
    _ = 1 / (N : ℝ) ^ q := by
      rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hNp, one_div]

/-- Every fixed inverse positive log power eventually falls below the
specific exponential constant needed by the ceil-log counting bound. -/
theorem eventually_log_mean_le_exp (a q : ℕ) (ha : 0 < a) (C : ℝ) (_hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in Filter.atTop,
      C / Real.log (N : ℝ) ^ (2 * a) ≤ Real.exp (-(q : ℝ)) := by
  filter_upwards [eventually_log_ge_nat 1,
    eventually_log_ge_nat (C * Real.exp (q : ℝ))] with N hL hsmall
  have hLp : 0 < Real.log (N : ℝ) := by linarith
  have hpower : Real.log (N : ℝ) ≤ Real.log (N : ℝ) ^ (2 * a) := by
    simpa only [pow_one] using pow_le_pow_right₀ hL (show 1 ≤ 2 * a by omega)
  apply (div_le_iff₀ (pow_pos hLp _)).mpr
  have hmul := mul_le_mul_of_nonneg_left hsmall (Real.exp_pos (-(q : ℝ))).le
  have hcancel : Real.exp (-(q : ℝ)) * (C * Real.exp (q : ℝ)) = C := by
    calc
      _ = C * (Real.exp (-(q : ℝ)) * Real.exp (q : ℝ)) := by ring
      _ = C := by rw [← Real.exp_add]; simp
  rw [hcancel] at hmul
  exact hmul.trans (mul_le_mul_of_nonneg_left hpower (Real.exp_pos _).le)

namespace RegularGraph

variable {N d : ℕ}

/-- The actual outside edges correlated to the fixed remaining vertex. -/
def correlatedOutsideEdges (g : RegularGraph N d) (T : Set (Fin N))
    (z : ℂ) (φ : ℝ) (radius : ℕ) (x : {w : Fin N // w ∉ T}) :
    Finset (OutsideOrientedEdge g.graph T) :=
  Finset.univ.filter (fun e =>
    outsideEdgeFirst g.graph T e ∈ outsideCorrelatedVertices g T z φ radius x ∨
      outsideEdgeSecond g.graph T e ∈ outsideCorrelatedVertices g T z φ radius x)

/-- Number of genuinely independent sampled outside edges correlated to x.
Boundary labels may share interior vertices and draws may repeat. -/
def correlatedSampleIndices (g : RegularGraph N d) (T : Set (Fin N))
    (z : ℂ) (φ : ℝ) (radius : ℕ) (x : {w : Fin N // w ∉ T})
    (S : LocalSamplingFiber g.graph T) : Finset (BoundaryOrientedEdge g.graph T) :=
  badSampleIndices (g.correlatedOutsideEdges T z φ radius x) S

theorem correlatedOutsideEdges_probability (g : RegularGraph N d) (T : Set (Fin N))
    (z : ℂ) (φ : ℝ) (radius : ℕ) (x : {w : Fin N // w ∉ T}) :
    uniformBadProbability (g.correlatedOutsideEdges T z φ radius x) =
      eventMass (finiteUniformWeight (OutsideOrientedEdge g.graph T))
        (fun e => outsideEdgeFirst g.graph T e ∈ outsideCorrelatedVertices g T z φ radius x ∨
          outsideEdgeSecond g.graph T e ∈ outsideCorrelatedVertices g T z φ radius x) := by
  rw [uniformBadProbability_eq_eventMass]
  congr 1
  funext e
  simp only [correlatedOutsideEdges, Finset.mem_filter, Finset.mem_univ, true_and]

end RegularGraph

/-- Uniform per-vertex ceil-log tail on the actual selected boundary fiber,
with its actual source radius and phi. The local imaginary-part cap is the
only graph-analytic premise. All count/probability/parameter budgets are derived. -/
theorem eventually_few_correlated_samples (a d q : ℕ) (c C : ℝ)
    (ha : 0 < a) (hd : 3 ≤ d) (hc : 0 ≤ c) (hc₁ : c < 1) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ), 0 < z.im →
      ∀ (v s ε : ℝ), 0 ≤ v → 0 < ε →
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      ∀ (x : {w : Fin N // w ∉ T}),
      (∀ u ∈ closedNeighborFinset (outsideGraph g.graph T) x,
        (green (normalizedAdjacency (outsideGraph g.graph T) d) z u u).im ≤
          C * (v + inflatedPrime (Real.log (N : ℝ)) ε + scalarScale s ε)) →
      eventMass (localSamplingWeight g.graph T)
        (fun S => Nat.ceil (Real.log (N : ℝ)) ≤
          (g.correlatedSampleIndices T z
            (correlationThreshold (Real.log (N : ℝ)) a N z.im v s ε)
            (logarithmicRadius (c / 4) d N / 4) x S).card) ≤ 1 / (N : ℝ) ^ q := by
  let P : ℝ := 4 * (1 + ((d + 1 : ℕ) : ℝ) ^ 2 * C)
  let M : ℝ := (d : ℝ) * ((d : ℝ) + 1)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  filter_upwards [RegularGraph.eventually_outside_correlated_endpoint_probability a d c hd hc hc₁,
    eventually_actual_boundary_card_log_bound a d hd ha,
    eventually_selected_resampling_budget a d hd ha,
    eventually_log_mean_le_exp a q ha (M * P) (mul_nonneg hM hP),
    eventually_log_ge_nat 1, Filter.eventually_ge_atTop 1]
    with N hcorr hcard hbudget hmean hlog hN
  intro g o z hz v s ε hv hε
  let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
  dsimp only
  intro x hI
  let E := OutsideOrientedEdge g.graph T
  let I := BoundaryOrientedEdge g.graph T
  let φ := correlationThreshold (Real.log (N : ℝ)) a N z.im v s ε
  let Bad := g.correlatedOutsideEdges T z φ (logarithmicRadius (c / 4) d N / 4) x
  letI : Nonempty E := g.outside_edge_nonempty T (by omega) (by omega)
    (g.ball_small o _ (hbudget z))
  have hp : uniformBadProbability Bad ≤ P / Real.log (N : ℝ) ^ (4 * a) := by
    rw [RegularGraph.correlatedOutsideEdges_probability]
    exact hcorr g T (g.ball_small o _ (hbudget z)) z hz v s ε C hv hε x hI
  have hμ : (Fintype.card I : ℝ) ≤ M * Real.log (N : ℝ) ^ (2 * a) := by
    simpa only [Nat.card_eq_fintype_card] using hcard g o z
  have hLp : 0 < Real.log (N : ℝ) := by linarith
  have hmean' : (Fintype.card I : ℝ) * uniformBadProbability Bad ≤ Real.exp (-(q : ℝ)) := by
    apply le_trans (mul_le_mul hμ hp (uniformBadProbability_nonnegative Bad)
      (mul_nonneg hM (pow_nonneg hLp.le _)))
    calc
      _ = (M * P) / Real.log (N : ℝ) ^ (2 * a) := by
        rw [show 4 * a = 2 * a + 2 * a by omega, pow_add]
        field_simp [ne_of_gt hLp]
        ring
      _ ≤ _ := hmean
  have htail := uniform_bad_sample_eventMass_power_tail (I := I) Bad (Nat.ceil (Real.log (N : ℝ)))
  have hpower := ceil_log_power_le_inverse_power
    ((Fintype.card I : ℝ) * uniformBadProbability Bad) N q (by omega)
    (mul_nonneg (Nat.cast_nonneg _) (uniformBadProbability_nonnegative Bad)) hmean'
  exact htail.trans hpower

/-- Uniformity over every remaining vertex costs one polynomial exponent,
which is supplied by the preceding per-vertex theorem at q+1. -/
theorem eventually_uniform_few_correlated_samples (a d q : ℕ) (c C : ℝ)
    (ha : 0 < a) (hd : 3 ≤ d) (hc : 0 ≤ c) (hc₁ : c < 1) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ), 0 < z.im →
      ∀ (v s ε : ℝ), 0 ≤ v → 0 < ε →
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      (∀ u : {w : Fin N // w ∉ T},
        (green (normalizedAdjacency (outsideGraph g.graph T) d) z u u).im ≤
          C * (v + inflatedPrime (Real.log (N : ℝ)) ε + scalarScale s ε)) →
      eventMass (localSamplingWeight g.graph T)
        (fun S => ∃ x : {w : Fin N // w ∉ T}, Nat.ceil (Real.log (N : ℝ)) ≤
          (g.correlatedSampleIndices T z
            (correlationThreshold (Real.log (N : ℝ)) a N z.im v s ε)
            (logarithmicRadius (c / 4) d N / 4) x S).card) ≤ 1 / (N : ℝ) ^ q := by
  filter_upwards [eventually_few_correlated_samples a d (q + 1) c C ha hd hc hc₁ hC,
    Filter.eventually_ge_atTop 1] with N htail hN
  intro g o z hz v s ε hv hε
  dsimp only
  intro hI
  let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
  let W := {w : Fin N // w ∉ T}
  let φ := correlationThreshold (Real.log (N : ℝ)) a N z.im v s ε
  let failure : W → LocalSamplingFiber g.graph T → Prop := fun x S =>
    Nat.ceil (Real.log (N : ℝ)) ≤
      (g.correlatedSampleIndices T z φ (logarithmicRadius (c / 4) d N / 4) x S).card
  have hper : ∀ x : W, eventMass (localSamplingWeight g.graph T) (failure x) ≤
      1 / (N : ℝ) ^ (q + 1) := by
    intro x
    exact htail g o z hz v s ε hv hε x (fun u _ => hI u)
  have hcard : Fintype.card W ≤ N := by
    have h := Fintype.card_le_of_injective (fun w : W => w.val) Subtype.val_injective
    simpa only [Fintype.card_fin] using h
  have hunion := eventMass_exists_finset_le (Finset.univ : Finset W)
    (localSamplingWeight g.graph T) finiteUniformWeight_nonneg failure
  have hunion' : eventMass (localSamplingWeight g.graph T) (fun S => ∃ x : W, failure x S) ≤
      ∑ x : W, eventMass (localSamplingWeight g.graph T) (failure x) := by
    simpa only [Finset.mem_univ, true_and] using hunion
  apply hunion'.trans
  calc
    _ ≤ ∑ _x : W, 1 / (N : ℝ) ^ (q + 1) := Finset.sum_le_sum (fun x _ => hper x)
    _ = (Fintype.card W : ℝ) * (1 / (N : ℝ) ^ (q + 1)) := by simp
    _ ≤ (N : ℝ) * (1 / (N : ℝ) ^ (q + 1)) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (by positivity)
    _ = 1 / (N : ℝ) ^ q := by
      rw [pow_succ]
      field_simp [Nat.cast_ne_zero.mpr (show N ≠ 0 by omega)]
      ring

end LocalLaw
