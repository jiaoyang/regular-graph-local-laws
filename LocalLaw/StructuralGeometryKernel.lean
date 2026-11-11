import LocalLaw.StructuralKernelProbability

/-! # The joint source structural and boundary-occupancy kernel event

Both geometric conclusions come from the same proved full sampling event.
Their joint failure therefore costs one geometric bad-event budget, not a
second union-bound factor. The occupancy predicate uses the literal actual
switched labelled state and its inherited removed set.
-/

noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw

local instance structuralGeometryKernelDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def ballResamplingTripleOccupancyGood {N d : ℕ} (R ω q : ℕ)
    (ξ : BallLabelledSpace N d) : Prop :=
  let s := (labelledBlockStateEquiv N d ξ.2.1.val ξ.1 ξ.2.2).val
  ∀ x : {v : Fin N // v ∉ ξ.1},
    (tripleNearIndices (s.fullResample (R / 4)).graph ξ.1 (R / 2)
      (s.fullResample (R / 4)).samples x).card ≤
        RegularGraph.resamplingTripleOccupancyConstant ω (q - 1) (q - 1)
          (2 * q * (2 * (q - 1) + 1))

def ballResamplingGeometryGood {N d : ℕ} (R ω q badCount : ℕ)
    (ξ : BallLabelledSpace N d) : Prop :=
  (ballLabelledProject (ballLabelledResample N d (R / 4) ξ)).SourceStructuralPlus R ω
    (resamplingLargeExcessConstant d ω (q - 1) (q - 1)
      (2 * q * (2 * (q - 1) + 1)) (q - 1)) badCount ∧
    ballResamplingTripleOccupancyGood R ω q ξ

theorem ball_resampling_occupancy_failure_implies_geometric_bad {N d : ℕ}
    (o : Fin N) (ell R ω q : ℕ) (ξ : BallLabelledSpace N d)
    (hfailure : ¬ ballResamplingTripleOccupancyGood R ω q ξ) :
    ballFullGeometricBad o ell R ω q ξ := by
  rcases ξ with ⟨T, μ, ⟨g, hμ⟩, boundary, S⟩
  change ∀ h : graphBallVertices g.graph o ell = T,
    ¬ SourceFullGeometricGood g.graph o ell R ω (q - 1) (q - 1)
      (2 * q * (2 * (q - 1) + 1)) (q - 1) (h.symm ▸ S)
  intro h
  cases h
  intro hgood
  apply hfailure
  exact g.sourceFullGood_labelledResampled_tripleNear o ell (R / 4) R ω (q - 1) (q - 1)
    (2 * q * (2 * (q - 1) + 1)) (q - 1) boundary S hgood

theorem ball_resampling_geometry_failure_le_geometric (N d : ℕ) (o : Fin N)
    (ell R ω q badCount : ℕ) (hd : 3 ≤ d) (hmargin : 2 * ell + 2 ≤ R)
    (A : RegularGraph N d → Prop)
    (hstruct : ∀ g, A g → g.structural R ω badCount)
    (hcost : ∀ g, A g → 4 * Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) *
      ((d + 1) * (d - 1) ^ R) ≤ badCount) :
    eventMass (ballLabelledWeight N d o ell) (fun ξ => A (ballLabelledProject ξ) ∧
      ¬ ballResamplingGeometryGood R ω q badCount ξ) ≤
      eventMass (ballLabelledWeight N d o ell) (fun ξ => A (ballLabelledProject ξ) ∧
        ballFullGeometricBad o ell R ω q ξ) := by
  classical
  apply eventMass_mono _ (ballLabelledWeight_nonnegative N d o ell)
  intro ξ hξ
  refine ⟨hξ.1, ?_⟩
  rcases not_and_or.mp hξ.2 with hstructural | hoccupancy
  · exact ball_resampling_structural_failure_implies_geometric_bad o ell R ω q badCount hd hmargin
      ξ (hstruct _ hξ.1) (hcost _ hξ.1) hstructural
  · exact ball_resampling_occupancy_failure_implies_geometric_bad o ell R ω q ξ hoccupancy

/-- The actual joint geometric conclusions (source (5.11) and Prop. 5.12)
hold under one arbitrary-polynomial budget on the genuine kernel. -/
theorem eventually_ballResampling_geometry_failure
    (a d ω p : ℕ) (c γ : ℝ) (ha : 0 < a) (hd : 3 ≤ d)
    (hc : 0 < c) (hc₁ : c < 1) (hγ : γ < 1) (hgap : c / 4 < γ) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ᶠ N : ℕ in Filter.atTop, ∀ (o : Fin N) (z : ℂ),
      eventMass (ballLabelledWeight N d o (actualCavityDepth a d N z - 1)) (fun ξ =>
        RegularGraph.offsetStructural (logarithmicRadius (c / 4) d N) ω 1 ⌊(N : ℝ) ^ γ⌋₊
          (ballLabelledProject ξ) ∧
        ¬ ballResamplingGeometryGood (logarithmicRadius (c / 4) d N) ω q ⌊(N : ℝ) ^ γ⌋₊ ξ) ≤
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
  apply (ball_resampling_geometry_failure_le_geometric N d o ell R ω q ⌊(N : ℝ) ^ γ⌋₊
    hd hfit A (fun _ hA => RegularGraph.offsetStructural_implies_structural hA)
    (fun g _ => hcost g o ell hell)).trans
  exact hprob o z

end LocalLaw
