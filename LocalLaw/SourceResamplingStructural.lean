import LocalLaw.ResamplingLargeBallExcess
import LocalLaw.ResamplingSmallBallExcess
import LocalLaw.SourceSpectralEvents

/-! # Actual source structural stability under local resampling

The regular switched graph is constructed from the actual labelled full
involution. On the proved full geometric sampling event, its eighth-radius
and half-radius excess budgets and doubled bad-center count satisfy all
three clauses of SourceStructuralPlus.
-/

noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
namespace RegularGraph

local instance sourceResamplingStructuralDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {N d : ℕ} {ι : Type*} [Fintype ι]

def labelledResampledGraph (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector : ℕ) : RegularGraph N d :=
  let s : LabelledResamplingState (Fin N) T ι := ⟨g.graph, boundary, S⟩
  ⟨(s.fullResample selector).graph, s.fullResample_regular selector g.regular⟩

def resamplingTripleOccupancyConstant (ω k j C : ℕ) : ℕ :=
  (ω + 1 + k) + (2 * ω + 2 * j * (ω + 1)) + (j + C)

/-- The actual switched-outside nearby-triple bound in source (5.11). -/
theorem sourceFullGood_labelledResampled_tripleNear (g : RegularGraph N d) (o : Fin N)
    (ell selector R ω k j C t : ℕ)
    (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (hgood : SourceFullGeometricGood g.graph o ell R ω k j C t S) :
    let s : LabelledResamplingState (Fin N) (graphBallVertices g.graph o ell) ι := ⟨g.graph, boundary, S⟩
    ∀ x : {v : Fin N // v ∉ graphBallVertices g.graph o ell},
      (tripleNearIndices (s.fullResample selector).graph (graphBallVertices g.graph o ell)
        (R / 2) (s.fullResample selector).samples x).card ≤
          resamplingTripleOccupancyConstant ω k j C := by
  let s : LabelledResamplingState (Fin N) (graphBallVertices g.graph o ell) ι := ⟨g.graph, boundary, S⟩
  dsimp only
  intro x
  have h := s.fullResample_tripleNear_count selector (R / 2) R (by omega) x
  have hnear := hgood.1.1 x
  have hboundary := hgood.1.2.1
  have hsampled := hgood.1.2.2.1
  unfold resamplingTripleOccupancyConstant
  change (tripleNearIndices (s.fullResample selector).graph (graphBallVertices g.graph o ell)
    (R / 2) (s.fullResample selector).samples x).card ≤ _
  nlinarith

theorem sourceFullGood_labelledResampled_structuralPlus (g : RegularGraph N d) (o : Fin N)
    (ell R ω k j C t badCount : ℕ) (hd : 3 ≤ d) (hmargin : 2 * ell + 2 ≤ R)
    (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (hbudget : ∀ v, graphBallExcess g.graph v R ≤ ω)
    (hbad : (nonTreeCenters g.graph R).card ≤ badCount)
    (hcost : 4 * Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) *
      ((d + 1) * (d - 1) ^ R) ≤ badCount)
    (hgood : SourceFullGeometricGood g.graph o ell R ω k j C t S) :
    (g.labelledResampledGraph (graphBallVertices g.graph o ell) boundary S (R / 4)).SourceStructuralPlus
      R ω (resamplingLargeExcessConstant d ω k j C t) badCount := by
  let s : LabelledResamplingState (Fin N) (graphBallVertices g.graph o ell) ι :=
    ⟨g.graph, boundary, S⟩
  have hdegree : ∀ v, g.graph.degree v ≤ d := fun v => (g.regular.degree_eq v).le
  have hsmall := s.fullResample_radius_eighth_excess R ω o ell (Set.Subset.refl _) hmargin hbudget
  have hlarge := sourceFullGood_fullResample_half_ball_excess g.graph o ell (R / 4) R d ω k j C t
    boundary S (by omega) hdegree hbudget hgood
  have hcount := s.fullResample_badCount_twice (R / 4) d R badCount hd hdegree hbad hcost
  exact ⟨hsmall, hlarge, hcount⟩

theorem structural_sourceFullGood_labelledResampled_structuralPlus
    (g : RegularGraph N d) (o : Fin N) (ell R ω k j C t badCount : ℕ)
    (hd : 3 ≤ d) (hmargin : 2 * ell + 2 ≤ R)
    (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (hstruct : g.structural R ω badCount)
    (hcost : 4 * Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) *
      ((d + 1) * (d - 1) ^ R) ≤ badCount)
    (hgood : SourceFullGeometricGood g.graph o ell R ω k j C t S) :
    (g.labelledResampledGraph (graphBallVertices g.graph o ell) boundary S (R / 4)).SourceStructuralPlus
      R ω (resamplingLargeExcessConstant d ω k j C t) badCount :=
  g.sourceFullGood_labelledResampled_structuralPlus o ell R ω k j C t badCount hd hmargin
    boundary S hstruct.1 hstruct.2 hcost hgood

end RegularGraph
end LocalLaw
