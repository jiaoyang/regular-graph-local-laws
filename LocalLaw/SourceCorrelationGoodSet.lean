import LocalLaw.SourceCorrelationIsolation
import LocalLaw.IsolatedCorrelationLabels
import LocalLaw.GeometricKernelProbability

/-!
# Actual isolated good labels and chosen-ball kernel probability

Good labels have small old deleted Green entries, including one-neighbor
steps, to every original boundary endpoint and every other sampled pair.
Their quadratic-log exception count and genuine enlarged-kernel failure are
proved. Further accepted/tree/unique-attachment conditions may be intersected
without losing these properties.
-/

noncomputable section
namespace LocalLaw
local instance sourceCorrelationGoodSetDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace RegularGraph
variable {N d : ℕ}

def outsideEdgePoint (g : RegularGraph N d) (T : Set (Fin N)) (e : OutsideOrientedEdge g.graph T)
    (σ : Bool) : (Tᶜ : Set (Fin N)) := if σ then g.outsideSecondPoint T e else g.outsideFirstPoint T e

def sourceCorrelationGoodLabels (g : RegularGraph N d) (T : Set (Fin N))
    (z : ℂ) (φ : ℝ) (radius : ℕ) (S : LocalSamplingFiber g.graph T) : Finset (BoundaryOrientedEdge g.graph T) :=
  correlationGoodLabels (g.deletedVertexCorrelation T z φ radius)
    (g.deletedVertexCorrelation_symmetric T z φ radius)
    (g.outsideFirstPoint T) (g.outsideSecondPoint T) (boundaryOutsideVertex g.graph T) S

theorem sourceCorrelationGoodLabels_bad_card (g : RegularGraph N d) (T : Set (Fin N))
    (z : ℂ) (φ : ℝ) (radius k : ℕ) (S : LocalSamplingFiber g.graph T)
    (hgood : ¬g.sourceGreenIsolationBad T z φ radius k S) :
    (Finset.univ \ g.sourceCorrelationGoodLabels T z φ radius S).card ≤ 4 * k ^ 2 + 3 * k := by
  exact correlationGoodLabels_bad_card _ _ _ _ _ _ k
    (fun h => hgood (Or.inl h)) (fun h => hgood (Or.inr h))

theorem deletedVertexCorrelation_norm_small (g : RegularGraph N d) (T : Set (Fin N))
    (z : ℂ) (φ : ℝ) (radius : ℕ) (x y : (Tᶜ : Set (Fin N)))
    (hxy : ¬g.deletedVertexCorrelation T z φ radius x y)
    (u v : (Tᶜ : Set (Fin N)))
    (hu : u ∈ closedNeighborFinset (outsideGraph g.graph T) x)
    (hv : v ∈ closedNeighborFinset (outsideGraph g.graph T) y) :
    ‖green (normalizedAdjacency (outsideGraph g.graph T) d) z u v‖ < φ := by
  by_contra h
  apply hxy
  exact (mem_wardCorrelatedVertices _ _ _ _ _ _ _).mpr (Or.inr ⟨u, hu, v, hv, by linarith⟩)

/-- A good sample is Green-uncorrelated with every fixed old boundary root. -/
theorem sourceCorrelationGood_old_norm_small (g : RegularGraph N d) (T : Set (Fin N))
    (z : ℂ) (φ : ℝ) (radius : ℕ) (S : LocalSamplingFiber g.graph T)
    (a : BoundaryOrientedEdge g.graph T) (ha : a ∈ g.sourceCorrelationGoodLabels T z φ radius S)
    (b : BoundaryOrientedEdge g.graph T) (σ : Bool)
    (u v : (Tᶜ : Set (Fin N)))
    (hu : u ∈ closedNeighborFinset (outsideGraph g.graph T) (boundaryOutsideVertex g.graph T b))
    (hv : v ∈ closedNeighborFinset (outsideGraph g.graph T) (g.outsideEdgePoint T (S a) σ)) :
    ‖green (normalizedAdjacency (outsideGraph g.graph T) d) z u v‖ < φ := by
  have hprop := (correlationGoodLabels_properties _ _ _ _ _ S a ha).1 b
  apply g.deletedVertexCorrelation_norm_small T z φ radius _ _ _ u v hu hv
  intro h
  apply hprop
  cases σ
  · exact Or.inl h
  · exact Or.inr h

/-- A good sample is Green-uncorrelated with both endpoints of every other
sample, including the closed-neighborhood steps used by the source relation. -/
theorem sourceCorrelationGood_other_norm_small (g : RegularGraph N d) (T : Set (Fin N))
    (z : ℂ) (φ : ℝ) (radius : ℕ) (S : LocalSamplingFiber g.graph T)
    (a : BoundaryOrientedEdge g.graph T) (ha : a ∈ g.sourceCorrelationGoodLabels T z φ radius S)
    (b : BoundaryOrientedEdge g.graph T) (hba : b ≠ a) (σ τ : Bool)
    (u v : (Tᶜ : Set (Fin N)))
    (hu : u ∈ closedNeighborFinset (outsideGraph g.graph T) (g.outsideEdgePoint T (S a) σ))
    (hv : v ∈ closedNeighborFinset (outsideGraph g.graph T) (g.outsideEdgePoint T (S b) τ)) :
    ‖green (normalizedAdjacency (outsideGraph g.graph T) d) z u v‖ < φ := by
  have hprop := (correlationGoodLabels_properties _ _ _ _ _ S a ha).2 b hba
  apply g.deletedVertexCorrelation_norm_small T z φ radius _ _ _ u v hu hv
  intro h
  apply hprop
  cases σ <;> cases τ
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end RegularGraph

def ballSourceGreenIsolationBad {N d : ℕ} (o : Fin N) (ell a rError R : ℕ) (z : ℂ) :
    BallLabelledSpace N d → Prop :=
  ballCanonicalSampleEvent o ell (fun g S =>
    let T := graphBallVertices g.graph o ell
    let φ := correlationThreshold (Real.log (N : ℝ)) a N z.im (graphKestenMcKayReference d z).im
      (spectralScale z) (graphPaperError a d N rError z)
    g.sourceGreenIsolationBad T z φ (R / 4) (Nat.ceil (Real.log (N : ℝ))) S)

/-- Actual uniform-graph enlarged-kernel probability, with every local
correlation and finite disintegration obligation discharged. -/
theorem eventually_ballSourceGreenIsolationBad_probability
    (a b d q : ℕ) (c β C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d)
    (hc : 0 < c) (hc₁ : c < 1) (hβ : 0 < β) (hβc : β ≤ c / 32) (hC1 : 0 ≤ C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (o : Fin N) (z : ℂ),
      0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ∀ Cq badCount : ℕ,
      eventMass (ballLabelledWeight N d o (actualCavityDepth a d N z - 1)) (fun ξ =>
        (ballLabelledProject ξ).SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β)
          (logarithmicRadius β d N) (logarithmicRadius (c / 4) d N)
          (actualCavityDepth a d N z - 1) (finiteOmega d) Cq badCount C1 o z ∧
        ballSourceGreenIsolationBad o (actualCavityDepth a d N z - 1) a (logarithmicRadius β d N)
          (logarithmicRadius (c / 4) d N) z ξ) ≤ 3 / (N : ℝ) ^ q := by
  filter_upwards [eventually_sourceGreenIsolation_bad_probability a b d q c β C1
    ha hb hd hc hc₁ hβ hβc hC1] with N htail
  intro o z hz hscale Cq badCount
  let ell := actualCavityDepth a d N z - 1
  let R := logarithmicRadius (c / 4) d N
  let rn := logarithmicRadius β d N
  let A : RegularGraph N d → Prop := fun g =>
    g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) rn R ell (finiteOmega d) Cq badCount C1 o z
  let P := fun (g : RegularGraph N d) (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) =>
    let T := graphBallVertices g.graph o ell
    let φ := correlationThreshold (Real.log (N : ℝ)) a N z.im (graphKestenMcKayReference d z).im
      (spectralScale z) (graphPaperError a d N rn z)
    g.sourceGreenIsolationBad T z φ (R / 4) (Nat.ceil (Real.log (N : ℝ))) S
  have hbound := ballCanonical_sample_failure_bound N d o ell A P (3 / (N : ℝ) ^ q)
    (fun g hA => htail g o z hz hscale Cq badCount hA)
  have hmass : eventMass (RegularGraph.weight (N := N) (d := d)) A ≤ 1 := finiteUniform_eventMass_le_one A
  exact hbound.trans ((mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq (mul_one _))

end LocalLaw
