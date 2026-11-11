import LocalLaw.WardCorrelation
import LocalLaw.ErrorParameters
import LocalLaw.ParameterGrowth
import LocalLaw.SharpBallCounting

/-!
# Substitution of the actual correlation threshold into the Ward bound

The variance numerator cancels algebraically against the source threshold
phi. In particular no inverse-log correlation probability is assumed. The
diagonal-imaginary-part cap remains the local analytic input.
-/

open scoped BigOperators
noncomputable section

namespace LocalLaw

local instance wardParameterDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The strictly positive numerator in the source threshold. -/
theorem correlationVariance_pos (L v s ε : ℝ) (hL : 0 < L)
    (hv : 0 ≤ v) (hε : 0 < ε) :
    0 < v + inflatedPrime L ε + scalarScale s ε := by
  have hprime : 0 < inflatedPrime L ε := mul_pos (pow_pos hL _) hε
  have hscale := scalarScale_nonneg (s := s) hε.le
  linarith

theorem correlationThreshold_pos (L : ℝ) (a N : ℕ) (η v s ε : ℝ)
    (hL : 0 < L) (hN : 0 < N) (hη : 0 < η) (hv : 0 ≤ v) (hε : 0 < ε) :
    0 < correlationThreshold L a N η v s ε := by
  unfold correlationThreshold
  exact mul_pos (pow_pos hL _) (Real.sqrt_pos.mpr
    (div_pos (correlationVariance_pos L v s ε hL hv hε)
      (mul_pos (Nat.cast_pos.mpr hN) hη)))

theorem correlationThreshold_sq (L : ℝ) (a N : ℕ) (η v s ε : ℝ)
    (hL : 0 < L) (hN : 0 < N) (hη : 0 < η) (hv : 0 ≤ v) (hε : 0 < ε) :
    correlationThreshold L a N η v s ε ^ 2 =
      L ^ (4 * a) * (v + inflatedPrime L ε + scalarScale s ε) / ((N : ℝ) * η) := by
  unfold correlationThreshold
  rw [mul_pow, Real.sq_sqrt (div_pos (correlationVariance_pos L v s ε hL hv hε)
    (mul_pos (Nat.cast_pos.mpr hN) hη)).le, ← pow_mul]
  rw [show 2 * a * 2 = 4 * a by omega]
  ring

/-- Exact variance cancellation, retaining the separate geometric radius
term. The expression is the finite Ward/endpoint bound, not a probability
conclusion supplied as a hypothesis. -/
theorem correlationThreshold_ward_cancellation (L : ℝ) (a N : ℕ)
    (η v s ε C B D : ℝ) (hL : 0 < L) (hN : 0 < N) (hη : 0 < η)
    (hv : 0 ≤ v) (hε : 0 < ε) :
    4 / (N : ℝ) * (B + D * (C * (v + inflatedPrime L ε + scalarScale s ε)) /
      (η * correlationThreshold L a N η v s ε ^ 2)) =
      4 * B / (N : ℝ) + 4 * D * C / L ^ (4 * a) := by
  rw [correlationThreshold_sq L a N η v s ε hL hN hη hv hε]
  field_simp [ne_of_gt hL, ne_of_gt hη, Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN),
    ne_of_gt (correlationVariance_pos L v s ε hL hv hε)]
  ring

namespace RegularGraph

variable {N d : ℕ}

/-- General near-ball-cap form of the actual endpoint correlation bound with
the actual source phi. The local Im cap is C times its variance numerator. -/
theorem outside_correlated_endpoint_probability_actual_phi (g : RegularGraph N d)
    (T : Set (Fin N)) (hN : 0 < N) (hd : 0 < d) (hT : 4 * Nat.card T ≤ N)
    (L : ℝ) (a : ℕ) (z : ℂ) (hz : 0 < z.im) (v s ε C B : ℝ)
    (hL : 0 < L) (hv : 0 ≤ v) (hε : 0 < ε) (radius : ℕ)
    (x : {w : Fin N // w ∉ T})
    (hI : ∀ u ∈ closedNeighborFinset (outsideGraph g.graph T) x,
      (green (normalizedAdjacency (outsideGraph g.graph T) d) z u u).im ≤
        C * (v + inflatedPrime L ε + scalarScale s ε))
    (hnear : ((graphBallVertices (outsideGraph g.graph T) x radius).toFinset.card : ℝ) ≤ B) :
    eventMass (finiteUniformWeight (OutsideOrientedEdge g.graph T))
      (fun e => outsideEdgeFirst g.graph T e ∈ outsideCorrelatedVertices g T z
          (correlationThreshold L a N z.im v s ε) radius x ∨
        outsideEdgeSecond g.graph T e ∈ outsideCorrelatedVertices g T z
          (correlationThreshold L a N z.im v s ε) radius x) ≤
      4 * B / (N : ℝ) + 4 * ((d + 1 : ℕ) : ℝ) ^ 2 * C / L ^ (4 * a) := by
  let φ := correlationThreshold L a N z.im v s ε
  have hφ : 0 < φ := correlationThreshold_pos L a N z.im v s ε hL hN hz hv hε
  have hdegree : ∀ w, (outsideGraph g.graph T).degree w ≤ d := by
    intro w
    have hw := (induced_degree_le g.graph {w | w ∉ T} w).trans (g.regular w.val).le
    simpa only [outsideGraph, SimpleGraph.degree, SimpleGraph.neighborFinset,
      Set.toFinset_card, ← Nat.card_eq_fintype_card] using hw
  have hcard := wardCorrelatedVertices_card_bound_of_near_cap (outsideGraph g.graph T)
    (normalizedAdjacency (outsideGraph g.graph T) d)
    (normalizedAdjacency_isHermitian _ _) z hz φ hφ radius d hdegree
    (C * (v + inflatedPrime L ε + scalarScale s ε)) B x hI hnear
  have himage : (outsideCorrelatedVertices g T z φ radius x).card =
      (wardCorrelatedVertices (outsideGraph g.graph T)
        (normalizedAdjacency (outsideGraph g.graph T) d) z φ radius x).card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  have hprob := g.outside_either_endpoint_probability T hN hd
    (g.outside_edge_real_size T hT) (outsideCorrelatedVertices g T z φ radius x)
  have hbound : eventMass (finiteUniformWeight (OutsideOrientedEdge g.graph T))
      (fun e => outsideEdgeFirst g.graph T e ∈ outsideCorrelatedVertices g T z φ radius x ∨
        outsideEdgeSecond g.graph T e ∈ outsideCorrelatedVertices g T z φ radius x) ≤
      4 / (N : ℝ) * (B + ((d + 1 : ℕ) : ℝ) ^ 2 *
        (C * (v + inflatedPrime L ε + scalarScale s ε)) / (z.im * φ ^ 2)) := by
    apply hprob.trans
    rw [himage]
    calc
      _ = (4 / (N : ℝ)) * ((wardCorrelatedVertices (outsideGraph g.graph T)
          (normalizedAdjacency (outsideGraph g.graph T) d) z φ radius x).card : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcard (by positivity)
  exact hbound.trans_eq (correlationThreshold_ward_cancellation L a N z.im v s ε C B
    (((d + 1 : ℕ) : ℝ) ^ 2) hL hN hz hv hε)

/-- Sharp d-1 growth for the geometric term in the actual source threshold
bound. No acyclicity or tree approximation is needed for this counting step. -/
theorem outside_correlated_endpoint_probability_sharp (g : RegularGraph N d)
    (T : Set (Fin N)) (hN : 0 < N) (hd : 3 ≤ d) (hT : 4 * Nat.card T ≤ N)
    (L : ℝ) (a : ℕ) (z : ℂ) (hz : 0 < z.im) (v s ε C : ℝ)
    (hL : 0 < L) (hv : 0 ≤ v) (hε : 0 < ε) (radius : ℕ)
    (x : {w : Fin N // w ∉ T})
    (hI : ∀ u ∈ closedNeighborFinset (outsideGraph g.graph T) x,
      (green (normalizedAdjacency (outsideGraph g.graph T) d) z u u).im ≤
        C * (v + inflatedPrime L ε + scalarScale s ε)) :
    eventMass (finiteUniformWeight (OutsideOrientedEdge g.graph T))
      (fun e => outsideEdgeFirst g.graph T e ∈ outsideCorrelatedVertices g T z
          (correlationThreshold L a N z.im v s ε) radius x ∨
        outsideEdgeSecond g.graph T e ∈ outsideCorrelatedVertices g T z
          (correlationThreshold L a N z.im v s ε) radius x) ≤
      4 * (((d + 1 : ℕ) : ℝ) * ((d - 1 : ℕ) : ℝ) ^ radius) / (N : ℝ) +
        4 * ((d + 1 : ℕ) : ℝ) ^ 2 * C / L ^ (4 * a) := by
  apply g.outside_correlated_endpoint_probability_actual_phi T hN (by omega) hT
    L a z hz v s ε C _ hL hv hε radius x hI
  have hdegree : ∀ w, (outsideGraph g.graph T).degree w ≤ d := by
    intro w
    have hw := (induced_degree_le g.graph {w | w ∉ T} w).trans (g.regular w.val).le
    simpa only [outsideGraph, SimpleGraph.degree, SimpleGraph.neighborFinset,
      Set.toFinset_card, ← Nat.card_eq_fintype_card] using hw
  have hcard := graphBall_card_sharp (outsideGraph g.graph T) x d radius hd hdegree
  rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
  exact_mod_cast hcard

end RegularGraph

/-- The actual integer source radius R/4 has negligible geometric endpoint
mass. Its sharp ball bound is absorbed by log^(-4a), for every fixed a,d,c. -/
theorem eventually_source_correlation_near_budget (a d : ℕ) (c : ℝ)
    (hd : 3 ≤ d) (hc : 0 ≤ c) (hc₁ : c < 1) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (((d + 1 : ℕ) : ℝ) * ((d - 1 : ℕ) : ℝ) ^
        (logarithmicRadius (c / 4) d N / 4)) / (N : ℝ) ≤
          1 / Real.log (N : ℝ) ^ (4 * a) := by
  have hexp : 0 < 1 - c / 4 := by linarith
  filter_upwards [eventually_const_mul_log_rpow_le (((d + 1 : ℕ) : ℝ))
    ((4 * a : ℕ) : ℝ) (1 - c / 4) hexp,
    eventually_log_ge_nat 1, Filter.eventually_ge_atTop 1] with N hsmall hlog hN
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hLp : 0 < Real.log (N : ℝ) := by linarith
  have hsmall' : (((d + 1 : ℕ) : ℝ)) * Real.log (N : ℝ) ^ (4 * a) ≤
      (N : ℝ) ^ (1 - c / 4) := by
    simpa only [Real.rpow_natCast] using hsmall
  have hk : (1 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ d - 1 by omega)
  have hp : ((d - 1 : ℕ) : ℝ) ^ (logarithmicRadius (c / 4) d N / 4) ≤
      (N : ℝ) ^ (c / 4) := by
    apply (pow_le_pow_right₀ hk (Nat.div_le_self _ _)).trans
    exact logarithmicRadius_power_bound (c / 4) d N (by positivity) hd hN
  have hmul := mul_le_mul hsmall' hp (pow_nonneg (by linarith : (0 : ℝ) ≤ ((d - 1 : ℕ) : ℝ)) _)
    (Real.rpow_nonneg hNp.le _)
  have hid : (N : ℝ) ^ (1 - c / 4) * (N : ℝ) ^ (c / 4) = N := by
    rw [← Real.rpow_add hNp, show 1 - c / 4 + c / 4 = 1 by ring, Real.rpow_one]
  rw [hid] at hmul
  apply (div_le_div_iff₀ hNp (pow_pos hLp _)).mpr
  nlinarith

namespace RegularGraph

/-- The inverse-log probability of Lemma 5.15 / (5.38), for the actual source
phi, actual outside-edge law and actual integer structural radius. Only the
local diagonal-imaginary-part cap is analytic input. -/
theorem eventually_outside_correlated_endpoint_probability (a d : ℕ) (c : ℝ)
    (hd : 3 ≤ d) (hc : 0 ≤ c) (hc₁ : c < 1) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ (g : RegularGraph N d) (T : Set (Fin N)), 4 * Nat.card T ≤ N →
      ∀ (z : ℂ), 0 < z.im → ∀ (v s ε C : ℝ), 0 ≤ v → 0 < ε →
      ∀ (x : {w : Fin N // w ∉ T}),
      (∀ u ∈ closedNeighborFinset (outsideGraph g.graph T) x,
        (green (normalizedAdjacency (outsideGraph g.graph T) d) z u u).im ≤
          C * (v + inflatedPrime (Real.log (N : ℝ)) ε + scalarScale s ε)) →
      eventMass (finiteUniformWeight (OutsideOrientedEdge g.graph T))
        (fun e => outsideEdgeFirst g.graph T e ∈ outsideCorrelatedVertices g T z
            (correlationThreshold (Real.log (N : ℝ)) a N z.im v s ε)
              (logarithmicRadius (c / 4) d N / 4) x ∨
          outsideEdgeSecond g.graph T e ∈ outsideCorrelatedVertices g T z
            (correlationThreshold (Real.log (N : ℝ)) a N z.im v s ε)
              (logarithmicRadius (c / 4) d N / 4) x) ≤
        4 * (1 + ((d + 1 : ℕ) : ℝ) ^ 2 * C) / Real.log (N : ℝ) ^ (4 * a) := by
  filter_upwards [eventually_source_correlation_near_budget a d c hd hc hc₁,
    eventually_log_ge_nat 1, Filter.eventually_ge_atTop 1] with N hnear hlog hN
  intro g T hT z hz v s ε C hv hε x hI
  have hprob := g.outside_correlated_endpoint_probability_sharp T (by omega) hd hT
    (Real.log (N : ℝ)) a z hz v s ε C (by linarith) hv hε
    (logarithmicRadius (c / 4) d N / 4) x hI
  apply hprob.trans
  have hfour := mul_le_mul_of_nonneg_left hnear (by norm_num : (0 : ℝ) ≤ 4)
  calc
    _ ≤ 4 * (1 / Real.log (N : ℝ) ^ (4 * a)) +
        4 * ((d + 1 : ℕ) : ℝ) ^ 2 * C / Real.log (N : ℝ) ^ (4 * a) := by
      convert add_le_add_right hfour
        (4 * ((d + 1 : ℕ) : ℝ) ^ 2 * C / Real.log (N : ℝ) ^ (4 * a)) using 1
      ring
    _ = _ := by ring

end RegularGraph

end LocalLaw
