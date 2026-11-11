import LocalLaw.WeightedGoodDiagonal

/-!
# The actual good leading-diagonal weighted transfer

Eligibility, old correlations and guarded caps prove the physical good
diagonal comparison. Its weighted sum is transferred to the actual source
observation on the entire independent sampling fiber. Exceptional labels
are charged only their old centered observation and their maximum weight.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceGoodWeightedDiagonalDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {N d : ℕ} {T : Set (Fin N)} {ι : Type} [Fintype ι]

theorem fullResample_good_weighted_diagonal_bound (s : LabelledResamplingState (Fin N) T ι)
    (hregular : s.graph.IsRegularOfDegree d) (hd : 3 ≤ d) (selector r : ℕ) (hr : r + 2 ≤ selector)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (correlationRadius : ℕ)
    (C P φ δ b bias W : ℝ) (hC : 0 ≤ C) (hP : 0 ≤ P) (hφ : 0 ≤ φ)
    (hδ : 0 ≤ δ) (hδC : δ ≤ C) (hb : 0 ≤ b) (hbias : 0 ≤ bias) (hW : 0 ≤ W)
    (caps : RegularGraph.GuardedDeletionCaps (⟨s.graph, hregular⟩ : RegularGraph N d)
      T (boundaryFarGuard s.graph T (selector - 1)) z C P)
    (hout : Nonempty (OutsideOrientedEdge s.graph T))
    (good : Finset ι) (heligible : ∀ i ∈ good, s.Eligible selector i)
    (hcorrelation : ∀ i ∈ good, s.boundary i ∈ RegularGraph.sourceCorrelationGoodLabels
      (⟨s.graph, hregular⟩ : RegularGraph N d) T z φ correlationRadius s.samples)
    (w : ι → ℂ) (hweight : ∀ i ∉ good, ‖w i‖ ≤ W) :
    let g : RegularGraph N d := ⟨s.graph, hregular⟩
    let K := normalizedAdjacency (outsideGraph (s.fullResample selector).graph T) d
    let Y := cavityIterate z q (r + 1)
    let Z := g.sourceSingletonObservation T r selector z q
    (∀ e, ‖Z e‖ ≤ b) → ‖finiteComplexMean Z - (q - Y)‖ ≤ bias →
    (∀ i ∈ good, ∀ u : s.OtherEndpointIndex selector i,
      ‖green K z (s.otherEndpointEmbedding selector i u).val (s.sampledOutsideSecond i).val‖ ≤ C) →
    (∀ i ∈ good, ∀ u : s.OtherEndpointIndex selector i,
      ‖green K z (s.otherEndpointEmbedding selector i u).val (s.sampledOutsideFirst i)‖ ≤ C) →
    (∀ i ∈ good, ‖(green K z (s.sampledOutsideFirst i) (s.sampledOutsideFirst i))⁻¹‖ ≤ P) →
    (∀ i ∈ good, ‖green K z (s.sampledOutsideSecond i).val (s.sampledOutsideFirst i)‖ ≤ δ) →
    (∀ i ∈ good, ‖green K z (s.sampledOutsideFirst i) (s.sampledOutsideSecond i).val‖ ≤ δ) →
    ‖∑ i ∈ good, w i * (green K z (s.sampledOutsideSecond i).val (s.sampledOutsideSecond i).val - q)‖ ≤
      ‖∑ i, w i * (Z (s.samples (s.boundary i)) - (q - Y))‖ +
        ((3 * (Nat.card (BoundaryOrientedEdge s.graph T) : ℝ)) * ((1 + C * P) * φ) *
          (2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1)) * (C + C ^ 2 * P) + δ ^ 2 * P) *
            (∑ i, ‖w i‖) +
        (2 * b + bias) * ((Finset.univ \ good).card : ℝ) * W := by
  dsimp only
  intro hZ hmean hNewC hNewB hNewPivot hNewCB hNewBC
  letI : Nonempty (OutsideOrientedEdge s.graph T) := hout
  let g : RegularGraph N d := ⟨s.graph, hregular⟩
  letI : Nonempty (OutsideOrientedEdge g.graph T) := hout
  let K := normalizedAdjacency (outsideGraph (s.fullResample selector).graph T) d
  let Y := cavityIterate z q (r + 1)
  let Z := g.sourceSingletonObservation T r selector z q
  let V := fun i => green K z (s.sampledOutsideSecond i).val (s.sampledOutsideSecond i).val
  let error := (3 * (Nat.card (BoundaryOrientedEdge s.graph T) : ℝ)) * ((1 + C * P) * φ) *
    (2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1)) * (C + C ^ 2 * P) + δ ^ 2 * P
  have herror : 0 ≤ error := by dsimp only [error]; positivity
  have hgood : ∀ i ∈ good, ‖V i - Y - Z (s.samples (s.boundary i))‖ ≤ error := by
    intro i hi
    exact s.fullResample_good_diagonal_observation_bound hregular hd selector r hr z q hz hq
      ⟨i, heligible i hi⟩ correlationRadius C P φ δ hC hP hφ hδ hδC
      (hcorrelation i hi) caps (hNewC i hi) (hNewB i hi) (hNewPivot i hi) (hNewCB i hi) (hNewBC i hi)
  have hcentered : ∀ i ∉ good, ‖Z (s.samples (s.boundary i)) - (q - Y)‖ ≤ 2 * b + bias := by
    intro i _
    exact observation_centered_bound_of_mean_bias Z (q - Y) b bias hZ hmean _
  exact weighted_good_diagonal_card_transfer good w V (fun i => Z (s.samples (s.boundary i))) Y q
    error (2 * b + bias) W herror (by positivity) hW hgood hcentered hweight

end LabelledResamplingState
end LocalLaw
