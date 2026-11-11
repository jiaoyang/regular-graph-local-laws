import LocalLaw.TripleTreeTest
import LocalLaw.BoundaryTreeCounts
import LocalLaw.SourceFullGeometricEvent

/-!
# Actual rejected-coordinate bounds from the full geometric event

The five exceptional sets account for non-tree boundary branches, non-tree
sampled pair balls, own/boundary-near samples, and the two cross-coordinate
collision sets. Outside their union, the actual guarded I and J tests hold.
Thus the number of rejected boundary labels is bounded by an explicit
constant depending only on the geometric-event parameters and omega.
-/

noncomputable section
set_option maxHeartbeats 1400000
namespace LocalLaw

local instance rejectedSwitchingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V]

theorem isolation_of_not_other_triples (G : SimpleGraph V) (T : Set V)
    (selector h R : ℕ) (hsel : selector ≤ h) (hselR : selector ≤ R)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (ha : α ∉ boundaryOtherTripleIndices G T h S)
    (hsample : α ∉ sampledOtherTripleIndices G T R S) :
    resamplingIsolation G T selector S α := by
  intro β hβα x hx y hy
  apply lt_of_not_ge
  intro hdist
  rcases (outsideTriple_mem_iff G T S α x).mp hx with rfl | rfl | rfl
  · apply ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, β, hβα, y, hy,
      hdist.trans (ENat.coe_le_coe.mpr hsel)⟩
  · apply hsample
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, β, hβα, y, hy,
      Or.inl (hdist.trans (ENat.coe_le_coe.mpr hselR))⟩
  · apply hsample
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, β, hβα, y, hy,
      Or.inr (hdist.trans (ENat.coe_le_coe.mpr hselR))⟩

theorem treeTest_of_not_geometric_exceptions (G : SimpleGraph V) (o : V)
    (ell selector h R : ℕ) (hsel : selector ≤ h) (hselR : selector ≤ R)
    (hsep : 2 * selector + 1 ≤ R)
    (S : LocalSamplingFiber G (graphBallVertices G o ell))
    (α : BoundaryOrientedEdge G (graphBallVertices G o ell))
    (ha : α ∉ boundaryNonTreeIndices G o ell h)
    (hpair : α ∉ nonTreeSampledPairIndices G (graphBallVertices G o ell) R S)
    (hown : α ∉ sampledBoundaryHitIndices G (graphBallVertices G o ell) R S) :
    ResamplingTreeTest G (graphBallVertices G o ell) selector S α := by
  let T := graphBallVertices G o ell
  have hA : (graphBall (outsideGraph G T) (boundaryOutsideVertex G T α) h).IsTree := by
    by_contra hn
    exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
  have hB : (pairBallGraph (outsideGraph G T) (sampledFirstOutsideVertex G T S α)
      (sampledSecondOutsideVertex G T S α) R).IsTree := by
    by_contra hn
    exact hpair (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
  have hfarb : (R : ℕ∞) < (outsideGraph G T).edist
      (boundaryOutsideVertex G T α) (sampledFirstOutsideVertex G T S α) := by
    apply lt_of_not_ge
    intro hnear
    apply hown
    apply (mem_endpointHitIndices G T _ S α).mpr
    exact Or.inl (Set.mem_toFinset.mpr
      (boundary_near_mem_boundary_root_ball G T R α (sampledFirstOutsideVertex G T S α) hnear))
  have hfarc : (R : ℕ∞) < (outsideGraph G T).edist
      (boundaryOutsideVertex G T α) (sampledSecondOutsideVertex G T S α) := by
    apply lt_of_not_ge
    intro hnear
    apply hown
    apply (mem_endpointHitIndices G T _ S α).mpr
    exact Or.inr (Set.mem_toFinset.mpr
      (boundary_near_mem_boundary_root_ball G T R α (sampledSecondOutsideVertex G T S α) hnear))
  exact resamplingTreeTest_of_separated_trees G T selector h R hsel hselR S α hA hB
    ((ENat.coe_le_coe.mpr hsep).trans_lt hfarb) ((ENat.coe_le_coe.mpr hsep).trans_lt hfarc)

def rejectedResamplingIndices (G : SimpleGraph V) (T : Set V) (selector : ℕ)
    (S : LocalSamplingFiber G T) : Finset (BoundaryOrientedEdge G T) :=
  Finset.univ \ acceptedResamplingIndices G T selector S

theorem rejectedResamplingIndices_subset_exceptions (G : SimpleGraph V) (o : V)
    (ell selector h R : ℕ) (hsel : selector ≤ h) (hselR : selector ≤ R)
    (hsep : 2 * selector + 1 ≤ R) (S : LocalSamplingFiber G (graphBallVertices G o ell)) :
    rejectedResamplingIndices G (graphBallVertices G o ell) selector S ⊆
      boundaryNonTreeIndices G o ell h ∪ (nonTreeSampledPairIndices G (graphBallVertices G o ell) R S ∪
        (sampledBoundaryHitIndices G (graphBallVertices G o ell) R S ∪
          (boundaryOtherTripleIndices G (graphBallVertices G o ell) h S ∪
            sampledOtherTripleIndices G (graphBallVertices G o ell) R S))) := by
  intro α hα
  by_contra hnone
  simp only [Finset.mem_union, not_or] at hnone
  have hI := treeTest_of_not_geometric_exceptions G o ell selector h R hsel hselR hsep S α
    hnone.1 hnone.2.1 hnone.2.2.1
  have hJ := isolation_of_not_other_triples G _ selector h R hsel hselR S α hnone.2.2.2.1 hnone.2.2.2.2
  exact (Finset.mem_sdiff.mp hα).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI, hJ⟩)

theorem rejectedResamplingIndices_card_five_sets (G : SimpleGraph V) (o : V)
    (ell selector h R : ℕ) (hsel : selector ≤ h) (hselR : selector ≤ R)
    (hsep : 2 * selector + 1 ≤ R) (S : LocalSamplingFiber G (graphBallVertices G o ell)) :
    (rejectedResamplingIndices G (graphBallVertices G o ell) selector S).card ≤
      (boundaryNonTreeIndices G o ell h).card +
      (nonTreeSampledPairIndices G (graphBallVertices G o ell) R S).card +
      (sampledBoundaryHitIndices G (graphBallVertices G o ell) R S).card +
      (boundaryOtherTripleIndices G (graphBallVertices G o ell) h S).card +
      (sampledOtherTripleIndices G (graphBallVertices G o ell) R S).card := by
  have hsub := rejectedResamplingIndices_subset_exceptions G o ell selector h R hsel hselR hsep S
  have h₀ := Finset.card_le_card hsub
  have h₁ := Finset.card_union_le (boundaryNonTreeIndices G o ell h)
    (nonTreeSampledPairIndices G (graphBallVertices G o ell) R S ∪
      (sampledBoundaryHitIndices G (graphBallVertices G o ell) R S ∪
        (boundaryOtherTripleIndices G (graphBallVertices G o ell) h S ∪
          sampledOtherTripleIndices G (graphBallVertices G o ell) R S)))
  have h₂ := Finset.card_union_le (nonTreeSampledPairIndices G (graphBallVertices G o ell) R S)
    (sampledBoundaryHitIndices G (graphBallVertices G o ell) R S ∪
      (boundaryOtherTripleIndices G (graphBallVertices G o ell) h S ∪
        sampledOtherTripleIndices G (graphBallVertices G o ell) R S))
  have h₃ := Finset.card_union_le (sampledBoundaryHitIndices G (graphBallVertices G o ell) R S)
    (boundaryOtherTripleIndices G (graphBallVertices G o ell) h S ∪
      sampledOtherTripleIndices G (graphBallVertices G o ell) R S)
  have h₄ := Finset.card_union_le (boundaryOtherTripleIndices G (graphBallVertices G o ell) h S)
    (sampledOtherTripleIndices G (graphBallVertices G o ell) R S)
  omega

/-- The source O_q(1) rejection count with an explicit checked constant. -/
theorem rejected_resampling_count_of_sourceFullGood (G : SimpleGraph V) (o : V)
    (ell R ω k j C t : ℕ) (hmargin : 2 * ell + 2 ≤ R)
    (hbudget : graphBallExcess G o R ≤ ω)
    (S : LocalSamplingFiber G (graphBallVertices G o ell))
    (hgood : SourceFullGeometricGood G o ell R ω k j C t S) :
    (rejectedResamplingIndices G (graphBallVertices G o ell) (R / 4) S).card ≤
      3 * ω + 2 * j * (ω + 2) + C + t := by
  have hfit : ell + 1 + R / 2 ≤ R := by omega
  have hbase := rejectedResamplingIndices_card_five_sets G o ell (R / 4) (R / 2) R
    (by omega) (by omega) (by omega) S
  have ha := boundary_nonTree_ball_count G o ell R (R / 2) ω hfit hbudget
  have hpair := hgood.1.2.2.2
  have hown := hgood.2
  have haOther := hgood.1.2.1
  have hsampleOther := hgood.1.2.2.1
  nlinarith

end LocalLaw
