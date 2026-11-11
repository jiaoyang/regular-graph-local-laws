import LocalLaw.FirstStageComparisonPacket
import LocalLaw.SourceFirstStageInterface
import LocalLaw.StructuralKernelProbability
import LocalLaw.PolynomialFailureAbsorption

/-! # First-stage probability reduces to literal deterministic comparisons

The geometric bad-event probability, structural stability, all radius/count
budgets and enlarged-event membership are proved here. The comparison-family
input lists actual physical and model boundary differences on the full good
sampling event; it does not assume event membership or a probability bound.
-/

noncomputable section
set_option maxHeartbeats 3000000
namespace LocalLaw
local instance firstStageProbabilityPackagingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def SourceFirstStageComparisonFamily (a b d : ℕ) (c β γ B : ℝ) : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∃ (Dfull Ddeleted : ℝ), 1 ≤ Dfull ∧ 0 ≤ Ddeleted ∧
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      RegularGraph.offsetStructural (logarithmicRadius (c / 4) d N) (finiteOmega d) 1 ⌊(N : ℝ) ^ γ⌋₊ g →
      (graphLocalLawFamilyWithRadii N d a (effectiveModelRadius a d N β) (logarithmicRadius β d N)).weak z g →
      ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))),
      let ell := actualCavityDepth a d N z - 1
      let T := graphBallVertices g.graph o ell
      let R := logarithmicRadius (c / 4) d N
      SourceFullGeometricGood g.graph o ell R (finiteOmega d) (q - 1) (q - 1)
        (2 * q * (2 * (q - 1) + 1)) (q - 1) samples →
      RegularGraph.FirstStageComparisonPacket g (g.labelledResampledGraph T boundary samples (R / 4))
        T a (effectiveModelRadius a d N β) (logarithmicRadius β d N) z Dfull Ddeleted

theorem sourceFirstStageAllPowers_of_comparison_family (a b d : ℕ) (c β γ B : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c) (hc₁ : c < 1)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hγ : c / 4 < γ) (hγ₁ : γ < 1) (hB : 0 ≤ B)
    (hcomparisons : SourceFirstStageComparisonFamily a b d c β γ B) :
    SourceFirstStageAllPowers a b d c β γ B := by
  intro p
  obtain ⟨q, hq, hrare⟩ := eventually_ballFullGeometricBad_probability a d (finiteOmega d) (p + 1) c γ
    (by omega) hd hc hc₁ hγ₁
  obtain ⟨Dfull, Ddeleted, hDfull, hDdeleted, hpackets⟩ := hcomparisons q hq
  let CqRaw := resamplingLargeExcessConstant d (finiteOmega d) (q - 1) (q - 1)
    (2 * q * (2 * (q - 1) + 1)) (q - 1)
  let Cq := max (finiteOmega d) CqRaw
  let C1 := max (Dfull + 1) (max (Ddeleted + 1) (max 1 (sourceDeletionConstant d β B)))
  have hCfull : Dfull + 1 ≤ C1 := le_max_left _ _
  have hCdeleted : Ddeleted + 1 ≤ C1 := (le_max_left _ _).trans (le_max_right _ _)
  have hC1 : 1 ≤ C1 := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hCdel : sourceDeletionConstant d β B ≤ C1 :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨Cq, C1, le_max_left _ _, hC1, hCdel, ?_⟩
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [hrare, hpackets,
    RegularGraph.eventually_firstStage_plus_of_comparison_packet a b d c β B Dfull Ddeleted C1
      ha hb hd hc hβ hβc hB hDfull hDdeleted hCfull hCdeleted,
    RegularGraph.eventually_resampling_badCenter_cost a d c γ hd hc.le hγ,
    eventually_resampling_radius_margin a d 2 2 (c / 4) hd (by linarith), hdepth,
    Filter.eventually_ge_atTop 4] with N hrare hpacket hmember hcost hmargin hdepth hN
  intro o z hz hzB hfloor
  let ell := actualCavityDepth a d N z - 1
  let R := logarithmicRadius (c / 4) d N
  let rn := logarithmicRadius β d N
  let r := effectiveModelRadius a d N β
  let badCount := ⌊(N : ℝ) ^ γ⌋₊
  let A : RegularGraph N d → Prop := RegularGraph.offsetStructural R (finiteOmega d) 1 badCount
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hfit : 2 * ell + 2 ≤ R := by dsimp only [R]; omega
  have hcover : ∀ ξ : BallLabelledSpace N d,
      ((A (ballLabelledProject ξ) ∧
          (graphLocalLawFamilyWithRadii N d a r rn).weak z (ballLabelledProject ξ)) ∧
        ¬(ballLabelledProject (ballLabelledResample N d (R / 4) ξ)).SourceOmegaPlusWithRadii
          a r rn R ell (finiteOmega d) Cq badCount C1 o z) →
      A (ballLabelledProject ξ) ∧ ballFullGeometricBad o ell R (finiteOmega d) q ξ := by
    intro ξ hf
    refine ⟨hf.1.1, ?_⟩
    rcases ξ with ⟨T, μ, ⟨g, hμ⟩, labels, samples⟩
    change ∀ hT : graphBallVertices g.graph o ell = T,
      ¬SourceFullGeometricGood g.graph o ell R (finiteOmega d) (q - 1) (q - 1)
        (2 * q * (2 * (q - 1) + 1)) (q - 1) (hT.symm ▸ samples)
    intro hT hgood
    cases hT
    have hsource : g.SourceOmegaWithRadii a r rn R (finiteOmega d) badCount z :=
      ⟨RegularGraph.offsetStructural_implies_structural hf.1.1, hf.1.2⟩
    have P := hpacket g o z hz hzB hfloor hf.1.1 hf.1.2 labels samples hgood
    have hstructRaw := g.structural_sourceFullGood_labelledResampled_structuralPlus o ell R (finiteOmega d)
      (q - 1) (q - 1) (2 * q * (2 * (q - 1) + 1)) (q - 1) badCount hd hfit labels samples
      hsource.1 (hcost g o ell hell) hgood
    have hstruct : (g.labelledResampledGraph (graphBallVertices g.graph o ell) labels samples (R / 4)).SourceStructuralPlus
        R (finiteOmega d) Cq badCount :=
      ⟨hstructRaw.1, fun v => (hstructRaw.2.1 v).trans (le_max_right _ _), hstructRaw.2.2⟩
    exact hf.2 (hmember g o z hz hzB hfloor Cq badCount hsource labels samples hstruct P)
  have hmass := eventMass_mono (ballLabelledWeight N d o ell) (ballLabelledWeight_nonnegative N d o ell) hcover
  exact (hmass.trans (hrare o z)).trans (const_div_pow_succ_le 4 N p (by omega) (by exact_mod_cast hN))

end LocalLaw
