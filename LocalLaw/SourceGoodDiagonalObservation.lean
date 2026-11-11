import LocalLaw.SourceGoodDiagonalComparison
import LocalLaw.SourceEligibleCavityTree
import LocalLaw.GuardedObservationBias

/-!
# The good new diagonal equals Y plus the actual old observation

The old near-edge and pivot bounds are consumed from the actual guarded
source caps. Eligibility proves the exact mask/tree identity. Physical
principal-minor surgery supplies the only comparison error.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceGoodDiagonalObservationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {N d : ℕ} {T : Set (Fin N)} {ι : Type} [Fintype ι]

theorem fullResample_good_diagonal_observation_bound (s : LabelledResamplingState (Fin N) T ι)
    (hregular : s.graph.IsRegularOfDegree d) (hd : 3 ≤ d) (selector r : ℕ) (hr : r + 2 ≤ selector)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (i : s.AdmissibleSampleIndex selector)
    (correlationRadius : ℕ) (C L φ δ : ℝ)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hφ : 0 ≤ φ) (hδ : 0 ≤ δ) (hδC : δ ≤ C)
    (hgood : s.boundary i.val ∈ RegularGraph.sourceCorrelationGoodLabels
      (⟨s.graph, hregular⟩ : RegularGraph N d) T z φ correlationRadius s.samples)
    (caps : RegularGraph.GuardedDeletionCaps (⟨s.graph, hregular⟩ : RegularGraph N d)
      T (boundaryFarGuard s.graph T (selector - 1)) z C L) :
    let g : RegularGraph N d := ⟨s.graph, hregular⟩
    let b := s.sampledOutsideFirst i.val
    let c := s.sampledOutsideSecond i.val
    let e := s.otherEndpointEmbedding selector i.val
    let K := normalizedAdjacency (outsideGraph (s.fullResample selector).graph T) d
    (∀ u, ‖green K z (e u).val c.val‖ ≤ C) →
    (∀ u, ‖green K z (e u).val b‖ ≤ C) → ‖(green K z b b)⁻¹‖ ≤ L →
    ‖green K z c.val b‖ ≤ δ → ‖green K z b c.val‖ ≤ δ →
    ‖green K z c.val c.val - cavityIterate z q (r + 1) -
      g.sourceSingletonObservation T r selector z q (s.samples (s.boundary i.val))‖ ≤
      (3 * (Nat.card (BoundaryOrientedEdge s.graph T) : ℝ)) * ((1 + C * L) * φ) *
        (2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1)) * (C + C ^ 2 * L) + δ ^ 2 * L := by
  dsimp only
  let g : RegularGraph N d := ⟨s.graph, hregular⟩
  let A := boundaryFarGuard s.graph T (selector - 1)
  let b := s.sampledOutsideFirst i.val
  let c := s.sampledOutsideSecond i.val
  let H := normalizedAdjacency (outsideGraph s.graph T) d
  let K := normalizedAdjacency (outsideGraph (s.fullResample selector).graph T) d
  intro hNewC hNewB hNewPivot hNewCB hNewBC
  have hfar := s.admissibleSampleVertex_far_boundary selector i
  have hdiv : (4 * selector) / 4 = selector := by omega
  have hsafeRaw := source_far_edge_guard s.graph T (4 * selector) (by omega)
    (s.samples (s.boundary i.val)) (by simpa only [hdiv] using hfar)
  have hsafe : b.val ∈ A ∧ c.val.val ∈ A := by simpa only [hdiv] using hsafeRaw
  have hentry (u v : (Tᶜ : Set (Fin N))) (hu : u.val ∈ A) (hv : v.val ∈ A) :
      guardedDeletedGreen g.H T A z u.val v.val = green H z u v := by
    have hh := guardedDeletedGreen_of_safe g.H T A
      (boundaryFarGuard_subset_complement s.graph T _) z ⟨u.val, hu⟩ ⟨v.val, hv⟩
    have hmatrix : g.H.submatrix (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)
        (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N) = H :=
      (normalizedAdjacency_induce s.graph d Tᶜ).symm
    rw [hmatrix] at hh
    exact hh
  have hOldNear := caps.guarded_edge c.val.val b.val (s.samples (s.boundary i.val)).property.1.symm
  rw [hentry c.val b hsafe.2 hsafe.1] at hOldNear
  have hOldPivot := caps.guarded_pivot b.val
  rw [hentry b b hsafe.1 hsafe.1] at hOldPivot
  have hcomparison := s.fullResample_good_diagonal_bound selector hregular hd z hz i.val correlationRadius
    C L φ δ hC hL hφ hδ hδC hgood hOldNear hOldPivot hNewC hNewB hNewPivot hNewCB hNewBC
  have hZ := s.eligible_sourceSingletonObservation_eq hregular hd selector r hr i q z hz hq
  have hid : green K z c.val c.val - cavityIterate z q (r + 1) -
      g.sourceSingletonObservation T r selector z q (s.samples (s.boundary i.val)) =
      green K z c.val c.val - outsideOrientedCavityValue s.graph d T z (s.samples (s.boundary i.val)) := by
    rw [hZ]
    ring
  rw [hid]
  exact hcomparison

end LabelledResamplingState
end LocalLaw
