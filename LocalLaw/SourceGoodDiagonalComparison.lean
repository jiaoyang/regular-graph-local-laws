import LocalLaw.SourceMinorCorrelations
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
local instance sourceGoodDiagonalDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type*} {T : Set V} {ι : Type*} [Fintype ι]

def OtherEndpointIndex (s : LabelledResamplingState V T ι) (selector : ℕ) (i : ι) :=
  s.otherOutsideEndpoints selector i

def otherEndpointEmbedding (s : LabelledResamplingState V T ι) (selector : ℕ) (i : ι) :
    s.OtherEndpointIndex selector i ↪ {v : (Tᶜ : Set V) // v ≠ s.sampledOutsideFirst i} :=
  ⟨Subtype.val, Subtype.val_injective⟩

def sampledOutsideSecond (s : LabelledResamplingState V T ι) (i : ι) :
    {v : (Tᶜ : Set V) // v ≠ s.sampledOutsideFirst i} :=
  ⟨⟨(s.samples (s.boundary i)).val.2, (s.samples (s.boundary i)).property.2.2⟩,
    fun h => (s.samples (s.boundary i)).property.1.ne' (congrArg Subtype.val h)⟩

variable [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem otherEndpointIndex_card (s : LabelledResamplingState V T ι) (selector : ℕ) (i : ι) :
    Nat.card (s.OtherEndpointIndex selector i) ≤ 3 * Nat.card (BoundaryOrientedEdge s.graph T) := by
  let f : s.OtherEndpointIndex selector i → s.endpointModelRoots selector := fun x =>
    ⟨x.val.val, by
      obtain ⟨j, hj, _, hx⟩ := x.property
      exact s.eligible_exterior_mem_endpointModelRoots selector j hj x.val.val hx⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun v : s.endpointModelRoots selector => v.val) h))
  exact (Nat.card_le_card_of_injective f hf).trans (s.endpointModelRoots_card selector)

end LabelledResamplingState

namespace LabelledResamplingState
variable {N d : ℕ} {T : Set (Fin N)} {ι : Type} [Fintype ι]

/-- Source good-diagonal surgery with the literal physical old/new graphs.
Old correlations, matrix support, mass and sample-count factors are derived;
new endpoint caps and its own pivot/cross-error come from model surgery. -/
theorem fullResample_good_diagonal_bound (s : LabelledResamplingState (Fin N) T ι)
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
    ‖green H z c.val b‖ ≤ C → ‖(green H z b b)⁻¹‖ ≤ L →
    (∀ u, ‖green K z (e u).val c.val‖ ≤ C) →
    (∀ u, ‖green K z (e u).val b‖ ≤ C) → ‖(green K z b b)⁻¹‖ ≤ L →
    ‖green K z c.val b‖ ≤ δ → ‖green K z b c.val‖ ≤ δ →
    ‖green K z c.val c.val - outsideOrientedCavityValue s.graph d T z (s.samples (s.boundary i))‖ ≤
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
  intro hOldNear hOldPivot hNewC hNewB hNewPivot hNewCB hNewBC
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
  have hphysical := physical_principal_minor_surgery_bound H K (normalizedAdjacency_isHermitian _ _)
    (normalizedAdjacency_isHermitian _ _) z hz b c e hsupport C L φ w δ hC hL hφ (by dsimp only [w]; positivity)
      hδ hδC hOldNear hOldPivot hOldC hOldB hNewC hNewB hNewPivot hNewCB hNewBC hW
  rw [outsideOrientedCavityValue_eq_deleted s.graph d T z hz (s.samples (s.boundary i))]
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
