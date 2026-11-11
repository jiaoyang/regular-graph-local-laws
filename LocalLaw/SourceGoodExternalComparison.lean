import LocalLaw.SourceGoodDiagonalComparison
import LocalLaw.PhysicalMinorExternal
import LocalLaw.EndpointModelInvariance
import LocalLaw.EndpointSurgeryParameters
import LocalLaw.CavityDeletionAverage

/-!
# Actual good-diagonal comparison after labelled resampling

The actual other-endpoint subtype has at most three times the boundary
size. Source correlation-good labels supply both old minor rows, while
the actual switching schedule supplies the principal perturbation support
and row mass. Only the specified local old/new physical caps remain inputs.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceGoodExternalDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {N d : ℕ} {T : Set (Fin N)} {ι : Type} [Fintype ι]

/-- Source good-diagonal surgery with the literal physical old/new graphs.
Old correlations, matrix support, mass and sample-count factors are derived;
new endpoint caps and its own pivot/cross-error come from model surgery. -/
theorem fullResample_good_external_bound (s : LabelledResamplingState (Fin N) T ι)
    (selector : ℕ) (hregular : s.graph.IsRegularOfDegree d) (hd : 3 ≤ d)
    (z : ℂ) (hz : 0 < z.im) (i : ι) (correlationRadius : ℕ)
    (C L φ δ : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) (hφ : 0 ≤ φ) (hδ : 0 ≤ δ) (hδC : δ ≤ C)
    (hgood : s.boundary i ∈ RegularGraph.sourceCorrelationGoodLabels (⟨s.graph, hregular⟩ : RegularGraph N d)
      T z φ correlationRadius s.samples) :
    let b := s.sampledOutsideFirst i
    let c := s.sampledOutsideSecond i
    let e := s.otherEndpointEmbedding selector i
    let H := normalizedAdjacency (outsideGraph s.graph T) d
    let K := normalizedAdjacency (outsideGraph (s.fullResample selector).graph T) d
    ∀ j : {v : (Tᶜ : Set (Fin N)) // v ≠ b},
    ‖green H z c.val b‖ ≤ C → ‖(green H z b b)⁻¹‖ ≤ L →
    ‖green H z c.val j.val‖ ≤ φ → ‖green H z b j.val‖ ≤ φ →
    (∀ u, ‖green K z (e u).val j.val‖ ≤ C) →
    (∀ u, ‖green K z (e u).val b‖ ≤ C) → ‖(green K z b b)⁻¹‖ ≤ L →
    ‖green K z c.val b‖ ≤ δ → ‖green K z b j.val‖ ≤ δ →
    ‖green K z c.val j.val‖ ≤ (1+C*L)*φ +
      (3 * (Nat.card (BoundaryOrientedEdge s.graph T) : ℝ)) * ((1 + C * L) * φ) *
        (2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1)) * (C + C ^ 2 * L) + δ ^ 2 * L := by
  dsimp only
  let g : RegularGraph N d := ⟨s.graph, hregular⟩
  let b := s.sampledOutsideFirst i
  let c := s.sampledOutsideSecond i
  let e := s.otherEndpointEmbedding selector i
  let H := normalizedAdjacency (outsideGraph s.graph T) d
  let K := normalizedAdjacency (outsideGraph (s.fullResample selector).graph T) d
  let w := 2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1)
  intro j hOldNear hOldPivot hOldTargetC hOldTargetB hNewJ hNewB hNewPivot hNewCB hNewBJ
  have hcorrelation (u : s.OtherEndpointIndex selector i) (σ : Bool) :
      ‖green H z (g.outsideEdgePoint T (s.samples (s.boundary i)) σ) (e u).val‖ ≤ φ := by
    obtain ⟨j, _, hji, hx⟩ := u.property
    exact g.source_good_other_exterior_norm_small T s.boundary s.samples z φ correlationRadius i hgood
      (e u).val ⟨j, hji, hx⟩ σ
  have hOldC : ∀ u, ‖green H z c.val (e u).val‖ ≤ φ := fun u => hcorrelation u true
  have hOldB : ∀ u, ‖green H z b (e u).val‖ ≤ φ := fun u => hcorrelation u false
  have hsupport : ∀ x y, x ∉ Set.range e ∨ y ∉ Set.range e →
      (deletedMatrix K b - deletedMatrix H b) x y = 0 := by
    intro x y hxy
    apply s.fullResample_minor_difference_supported selector d i x y
    exact hxy.imp (fun hx hmem => hx ⟨⟨x, hmem⟩, rfl⟩) (fun hy hmem => hy ⟨⟨y, hmem⟩, rfl⟩)
  have hW := (s.fullResample_minor_endpoint_mass selector d i (fun v => (hregular v).le) e).1
  have hphysical := physical_principal_minor_external_bound H K (normalizedAdjacency_isHermitian _ _)
    (normalizedAdjacency_isHermitian _ _) z hz b c j e hsupport C L φ w δ hC hL hφ (by dsimp only [w]; positivity)
      hδ hδC hOldNear hOldPivot hOldC hOldB hOldTargetC hOldTargetB hNewJ hNewB hNewPivot hNewCB hNewBJ hW
  apply hphysical.trans
  have hcard : (Fintype.card (s.OtherEndpointIndex selector i) : ℝ) ≤
      3 * (Nat.card (BoundaryOrientedEdge s.graph T) : ℝ) := by
    have hh := s.otherEndpointIndex_card selector i
    rw [Nat.card_eq_fintype_card] at hh
    exact_mod_cast hh
  have hh := mul_le_mul_of_nonneg_right hcard
    (by dsimp only [w]; positivity : 0 ≤ ((1 + C * L) * φ) * w * (C + C ^ 2 * L))
  nlinarith only [hh]

end LabelledResamplingState
end LocalLaw
