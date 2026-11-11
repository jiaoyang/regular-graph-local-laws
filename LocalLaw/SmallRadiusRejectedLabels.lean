import LocalLaw.RejectedSwitchingCounts
import LocalLaw.SourceSpectralEvents

/-! # Rejection counts using only the structural-plus half-radius budget

The boundary I-test is charged inside B_(R/2), while J uses the actual
selector R/4. No full-radius excess bound is needed for this counting
corollary. The three genuinely random exceptional counts remain explicit.
-/

noncomputable section
namespace LocalLaw
local instance smallRadiusRejectedDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V]

theorem rejected_resampling_count_of_half_ball_budget (G : SimpleGraph V) (o : V)
    (ell R Cq j C t : ℕ) (hmargin : ell + 1 + R / 4 ≤ R / 2)
    (hbudget : graphBallExcess G o (R / 2) ≤ Cq)
    (S : LocalSamplingFiber G (graphBallVertices G o ell))
    (hpair : (nonTreeSampledPairIndices G (graphBallVertices G o ell) R S).card ≤ t)
    (hown : (sampledBoundaryHitIndices G (graphBallVertices G o ell) R S).card ≤ j)
    (hother : (sampledOtherTripleIndices G (graphBallVertices G o ell) R S).card ≤ j + C) :
    (rejectedResamplingIndices G (graphBallVertices G o ell) (R / 4) S).card ≤
      3 * Cq + 2 * j * (Cq + 2) + C + t := by
  have hbase := rejectedResamplingIndices_card_five_sets G o ell (R / 4) (R / 4) R
    le_rfl (by omega) (by omega) S
  have ha := boundary_nonTree_ball_count G o ell (R / 2) (R / 4) Cq hmargin hbudget
  have hb := boundaryOtherTripleIndices_card G o ell (R / 2) (R / 4) Cq hmargin hbudget S
  have hh := (Finset.card_le_card (sampledBoundaryHitIndices_mono G _
    (show R / 4 ≤ R by omega) S)).trans hown
  nlinarith

theorem rejected_resampling_count_of_structuralPlus_sourceFullGood {N d : ℕ}
    (g : RegularGraph N d) (o : Fin N) (ell R ω Cq badCount k j C t : ℕ)
    (hmargin : ell + 1 + R / 4 ≤ R / 2)
    (hstruct : g.SourceStructuralPlus R ω Cq badCount)
    (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (hgood : SourceFullGeometricGood g.graph o ell R ω k j C t S) :
    (rejectedResamplingIndices g.graph (graphBallVertices g.graph o ell) (R / 4) S).card ≤
      3 * Cq + 2 * j * (Cq + 2) + C + t :=
  rejected_resampling_count_of_half_ball_budget g.graph o ell R Cq j C t hmargin (hstruct.2.1 o) S
    hgood.1.2.2.2 hgood.2 hgood.1.2.2.1

end LocalLaw
