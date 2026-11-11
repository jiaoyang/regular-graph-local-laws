import LocalLaw.SourceResamplingStructural
import LocalLaw.FullGeometricKernelProbability
import LocalLaw.ResamplingStructuralCost

/-! # Structural stability in the actual reversible chosen-ball kernel

The canonical labelled graph is the literal projection of the checked
resampling permutation. A structural failure therefore implies the proved
full geometric bad-sampling event, including on the auxiliary off-support
states. Finite kernel mass is bounded without an assumed transfer premise.
-/

noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw

local instance structuralKernelProbabilityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem ball_resampling_structural_failure_implies_geometric_bad {N d : ℕ}
    (o : Fin N) (ell R ω q badCount : ℕ) (hd : 3 ≤ d) (hmargin : 2 * ell + 2 ≤ R)
    (ξ : BallLabelledSpace N d)
    (hstruct : (ballLabelledProject ξ).structural R ω badCount)
    (hcost : 4 * Nat.card (BoundaryOrientedEdge (ballLabelledProject ξ).graph
      (graphBallVertices (ballLabelledProject ξ).graph o ell)) *
      ((d + 1) * (d - 1) ^ R) ≤ badCount)
    (hfailure : ¬ (ballLabelledProject (ballLabelledResample N d (R / 4) ξ)).SourceStructuralPlus
      R ω (resamplingLargeExcessConstant d ω (q - 1) (q - 1)
        (2 * q * (2 * (q - 1) + 1)) (q - 1)) badCount) :
    ballFullGeometricBad o ell R ω q ξ := by
  rcases ξ with ⟨T, μ, ⟨g, hμ⟩, boundary, S⟩
  change ∀ h : graphBallVertices g.graph o ell = T,
    ¬ SourceFullGeometricGood g.graph o ell R ω (q - 1) (q - 1)
      (2 * q * (2 * (q - 1) + 1)) (q - 1) (h.symm ▸ S)
  intro h
  cases h
  intro hgood
  apply hfailure
  exact g.structural_sourceFullGood_labelledResampled_structuralPlus o ell R ω
    (q - 1) (q - 1) (2 * q * (2 * (q - 1) + 1)) (q - 1) badCount
    hd hmargin boundary S hstruct hcost hgood

theorem ball_resampling_structural_failure_le_geometric (N d : ℕ) (o : Fin N)
    (ell R ω q badCount : ℕ) (hd : 3 ≤ d) (hmargin : 2 * ell + 2 ≤ R)
    (A : RegularGraph N d → Prop)
    (hstruct : ∀ g, A g → g.structural R ω badCount)
    (hcost : ∀ g, A g → 4 * Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) *
      ((d + 1) * (d - 1) ^ R) ≤ badCount) :
    eventMass (ballLabelledWeight N d o ell) (fun ξ => A (ballLabelledProject ξ) ∧
      ¬ (ballLabelledProject (ballLabelledResample N d (R / 4) ξ)).SourceStructuralPlus
        R ω (resamplingLargeExcessConstant d ω (q - 1) (q - 1)
          (2 * q * (2 * (q - 1) + 1)) (q - 1)) badCount) ≤
      eventMass (ballLabelledWeight N d o ell) (fun ξ => A (ballLabelledProject ξ) ∧
        ballFullGeometricBad o ell R ω q ξ) := by
  apply eventMass_mono _ (ballLabelledWeight_nonnegative N d o ell)
  intro ξ hξ
  exact ⟨hξ.1, ball_resampling_structural_failure_implies_geometric_bad o ell R ω q badCount
    hd hmargin ξ (hstruct _ hξ.1) (hcost _ hξ.1) hξ.2⟩

/-- Source Prop. 5.12 on the actual chosen-ball reversible kernel, with
arbitrary polynomial failure and all selected-radius/count budgets derived. -/
theorem eventually_ballResampling_structuralPlus_failure
    (a d ω p : ℕ) (c γ : ℝ) (ha : 0 < a) (hd : 3 ≤ d)
    (hc : 0 < c) (hc₁ : c < 1) (hγ : γ < 1) (hgap : c / 4 < γ) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ᶠ N : ℕ in Filter.atTop, ∀ (o : Fin N) (z : ℂ),
      eventMass (ballLabelledWeight N d o (actualCavityDepth a d N z - 1)) (fun ξ =>
        RegularGraph.offsetStructural (logarithmicRadius (c / 4) d N) ω 1 ⌊(N : ℝ) ^ γ⌋₊
          (ballLabelledProject ξ) ∧
        ¬ (ballLabelledProject (ballLabelledResample N d
          (logarithmicRadius (c / 4) d N / 4) ξ)).SourceStructuralPlus
            (logarithmicRadius (c / 4) d N) ω
            (resamplingLargeExcessConstant d ω (q - 1) (q - 1)
              (2 * q * (2 * (q - 1) + 1)) (q - 1)) ⌊(N : ℝ) ^ γ⌋₊) ≤
                4 / (N : ℝ) ^ p := by
  obtain ⟨q, hq, hprob⟩ := eventually_ballFullGeometricBad_probability a d ω p c γ ha hd hc hc₁ hγ
  have hr := (lowerLogLogRadius_tendsto a d ha hd).eventually (Filter.eventually_ge_atTop 4)
  refine ⟨q, hq, ?_⟩
  filter_upwards [hprob, RegularGraph.eventually_resampling_badCenter_cost a d c γ hd hc.le hgap,
    eventually_resampling_radius_margin a d 2 2 (c / 4) hd (by linarith), hr] with
      N hprob hcost hmargin hr
  intro o z
  let ell := actualCavityDepth a d N z - 1
  let R := logarithmicRadius (c / 4) d N
  let A : RegularGraph N d → Prop := RegularGraph.offsetStructural R ω 1 ⌊(N : ℝ) ^ γ⌋₊
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hr).2
  have hfit : 2 * ell + 2 ≤ R := by dsimp only [R]; omega
  apply (ball_resampling_structural_failure_le_geometric N d o ell R ω q ⌊(N : ℝ) ^ γ⌋₊
    hd hfit A (fun _ hA => RegularGraph.offsetStructural_implies_structural hA)
    (fun g _ => hcost g o ell hell)).trans
  exact hprob o z

end LocalLaw
