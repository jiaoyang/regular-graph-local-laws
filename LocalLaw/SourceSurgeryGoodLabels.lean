import LocalLaw.SourceCorrelationGoodSet
import LocalLaw.CentralUniqueAttachment
import LocalLaw.RejectedSwitchingCounts

/-!
# Actual accepted, isolated, uniquely attached good labels

The good set intersects the proved correlation isolation event with actual
acceptance and the deterministic annulus single-attachment condition. Its
complement still has quadratic-log cardinality, plus an explicit fixed
geometric constant. No source good-label count is assumed.
-/

noncomputable section
namespace LocalLaw
local instance sourceSurgeryGoodLabelsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}

def sourceSurgeryGoodLabels (g : RegularGraph N d) (o : Fin N) (ell R : ℕ)
    (hfit : ell+1 ≤ R/8) (z : ℂ) (φ : ℝ)
    (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) :
    Finset (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) :=
  g.sourceCorrelationGoodLabels (graphBallVertices g.graph o ell) z φ (R/4) S \
    (multiattachmentBoundaryLabels g.graph o hfit ∪
      rejectedResamplingIndices g.graph (graphBallVertices g.graph o ell) (R/4) S)

theorem sourceSurgeryGoodLabels_properties (g : RegularGraph N d) (o : Fin N) (ell R : ℕ)
    (hfit : ell+1 ≤ R/8) (z : ℂ) (φ : ℝ)
    (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (a : BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (ha : a ∈ g.sourceSurgeryGoodLabels o ell R hfit z φ S) :
    a ∈ g.sourceCorrelationGoodLabels (graphBallVertices g.graph o ell) z φ (R/4) S ∧
      a ∉ multiattachmentBoundaryLabels g.graph o hfit ∧
      a ∈ acceptedResamplingIndices g.graph (graphBallVertices g.graph o ell) (R/4) S := by
  have h := Finset.mem_sdiff.mp ha
  have hn := Finset.not_mem_union.mp h.2
  refine ⟨h.1,hn.1,?_⟩
  by_contra hr
  exact hn.2 (Finset.mem_sdiff.mpr ⟨Finset.mem_univ a,hr⟩)

theorem sourceSurgeryGoodLabels_bad_card (g : RegularGraph N d) (o : Fin N)
    (ell R ω m J : ℕ) (hfit : ell+1 ≤ R/8)
    (hbudget : graphBallExcess g.graph o (R/8) ≤ ω)
    (z : ℂ) (φ : ℝ) (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (hisolation : ¬g.sourceGreenIsolationBad (graphBallVertices g.graph o ell) z φ (R/4) m S)
    (hrejected : (rejectedResamplingIndices g.graph (graphBallVertices g.graph o ell) (R/4) S).card ≤ J) :
    (Finset.univ \ g.sourceSurgeryGoodLabels o ell R hfit z φ S).card ≤ 4*m^2+3*m+2*ω+J := by
  classical
  let corr := g.sourceCorrelationGoodLabels (graphBallVertices g.graph o ell) z φ (R/4) S
  let multi := multiattachmentBoundaryLabels g.graph o hfit
  let reject := rejectedResamplingIndices g.graph (graphBallVertices g.graph o ell) (R/4) S
  have hsub : Finset.univ \ g.sourceSurgeryGoodLabels o ell R hfit z φ S ⊆
      (Finset.univ \ corr) ∪ (multi ∪ reject) := by
    intro a ha
    have hn := (Finset.mem_sdiff.mp ha).2
    by_cases hc : a ∈ corr
    · apply Finset.mem_union.mpr ∘ Or.inr
      by_contra hnone
      exact hn (Finset.mem_sdiff.mpr ⟨hc,hnone⟩)
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_univ a,hc⟩))
  have h₁ := Finset.card_le_card hsub
  have h₂ := Finset.card_union_le (Finset.univ \ corr) (multi ∪ reject)
  have h₃ := Finset.card_union_le multi reject
  have h₄ := g.sourceCorrelationGoodLabels_bad_card (graphBallVertices g.graph o ell) z φ (R/4) m S hisolation
  have h₅ := multiattachmentBoundaryLabels_card g.graph o hfit hbudget
  change (Finset.univ \ corr).card ≤ _ at h₄
  change multi.card ≤ _ at h₅
  change reject.card ≤ _ at hrejected
  omega

theorem sourceSurgeryGoodLabels_bad_card_of_sourceFullGood (g : RegularGraph N d) (o : Fin N)
    (ell R ω k j C t m : ℕ) (hfit : ell+1 ≤ R/8) (hmargin : 2*ell+2 ≤ R)
    (hbudget : graphBallExcess g.graph o (R/8) ≤ ω)
    (z : ℂ) (φ : ℝ) (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (hisolation : ¬g.sourceGreenIsolationBad (graphBallVertices g.graph o ell) z φ (R/4) m S)
    (hgood : SourceFullGeometricGood g.graph o ell R ω k j C t S)
    (hbigbudget : graphBallExcess g.graph o R ≤ ω) :
    (Finset.univ \ g.sourceSurgeryGoodLabels o ell R hfit z φ S).card ≤
      4*m^2+3*m+2*ω+(3*ω+2*j*(ω+2)+C+t) := by
  classical
  let corr := g.sourceCorrelationGoodLabels (graphBallVertices g.graph o ell) z φ (R/4) S
  let multi := multiattachmentBoundaryLabels g.graph o hfit
  let reject := rejectedResamplingIndices g.graph (graphBallVertices g.graph o ell) (R/4) S
  have hsub : Finset.univ \ g.sourceSurgeryGoodLabels o ell R hfit z φ S ⊆
      (Finset.univ \ corr) ∪ (multi ∪ reject) := by
    intro a ha
    have hn := (Finset.mem_sdiff.mp ha).2
    by_cases hc : a ∈ corr
    · apply Finset.mem_union.mpr ∘ Or.inr
      by_contra hnone
      exact hn (Finset.mem_sdiff.mpr ⟨hc,hnone⟩)
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_univ a,hc⟩))
  have h₁ := Finset.card_le_card hsub
  have h₂ := Finset.card_union_le (Finset.univ \ corr) (multi ∪ reject)
  have h₃ := Finset.card_union_le multi reject
  have h₄ := g.sourceCorrelationGoodLabels_bad_card (graphBallVertices g.graph o ell) z φ (R/4) m S hisolation
  have h₅ := multiattachmentBoundaryLabels_card g.graph o hfit hbudget
  have h₆ := rejected_resampling_count_of_sourceFullGood g.graph o ell R ω k j C t hmargin hbigbudget S hgood
  change (Finset.univ \ corr).card ≤ _ at h₄
  change multi.card ≤ _ at h₅
  change reject.card ≤ _ at h₆
  omega

end RegularGraph
end LocalLaw
