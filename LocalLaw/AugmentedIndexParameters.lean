import LocalLaw.EndpointSurgeryParameters

/-!
# Actual endpoint dimension and realized surgery smallness

An explicit finite endpoint encoding counts boundary roots and the two
endpoints of each accepted sample. The real source logarithmic count and
nominal error then realize the finite-rank contraction uniformly in z.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance augmentedIndexParametersDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

/-- The actual finite endpoint contraction holds for every labelled sample
and every selector, at every allowed source radius, eventually. -/
theorem eventually_augmented_index_surgery_smallness (a b d : ℕ) (β C w D : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hβ : 0 < β)
    (hC : 0 ≤ C) (hw : 0 ≤ w) (hD : 0 ≤ D) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (ell : ℕ),
      ell ≤ doubleLogRadius a d N → ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) (selector : ℕ) (z : ℂ),
      0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      let s := g.admissibleState (graphBallVertices g.graph o ell) boundary samples
      ∀ n : ℕ, n ≤ Nat.card (s.endpointModelRoots selector)+2 →
      (n : ℝ) * (1 + C * w) * w *
        (D * g.sourcePrime a (logarithmicRadius β d N) z) ≤ 1 / 2 := by
  let U : ℝ := 3 * (d : ℝ) * ((d : ℝ) + 1)+2
  filter_upwards [eventually_paperError_small a b d β ha hb hd hβ, eventually_log_ge_nat 1,
    eventually_log_ge_nat (2 * (U * (1 + C * w) * w * D)), Filter.eventually_ge_atTop 1]
    with N hsmall hL hlarge hN
  intro g o ell hell ι _ boundary samples selector z hz hscale
  dsimp only
  intro n hn
  let s := g.admissibleState (graphBallVertices g.graph o ell) boundary samples
  let L := Real.log (N : ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  have hε : 0 ≤ ε := graphPaperError_nonnegative a d N _ z hN hz.le
  have hcap : ε * L ^ (4 * a) ≤ 1 := by
    exact (le_div_iff₀ (pow_pos (by linarith : 0 < L) _)).mp
      (by simpa only [one_div] using hsmall z hz hscale)
  have hcount : (n : ℝ) ≤ U * L ^ (2 * a) := by
    have hnat := s.endpointModelRoots_card selector
    have hreal : (Nat.card (s.endpointModelRoots selector) : ℝ) ≤
        3 * (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ) := by exact_mod_cast hnat
    have hnreal : (n:ℝ) ≤ (Nat.card (s.endpointModelRoots selector):ℝ)+2 := by exact_mod_cast hn
    have hh := mul_le_mul_of_nonneg_left (g.boundary_card_log_bound o a ell hd hL hell) (by norm_num : (0 : ℝ) ≤ 3)
    have hpow : 1 ≤ L^(2*a) := one_le_pow₀ hL
    dsimp only [U]
    nlinarith only [hnreal,hreal,hh,hpow]
  have hh := source_endpoint_surgery_smallness a L ε (n : ℝ)
    U C w D (by omega) hL hε (by dsimp only [U]; positivity) hC hw hD hcap hcount hlarge
  convert hh using 1
  unfold sourcePrime inflatedPrime
  ring

end RegularGraph
end LocalLaw
