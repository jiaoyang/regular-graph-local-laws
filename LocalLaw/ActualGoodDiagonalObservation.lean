import LocalLaw.SourceNewEndpointCaps
import LocalLaw.SourceGoodDiagonalParameters
import LocalLaw.SourceOmegaPlusTransferEffective
import LocalLaw.SwitchedEndpointBudget

/-!
# The actual good switched diagonal has the sixteen-log observation error

No endpoint approximation, entry cap, pivot, model budget or scalar smallness
is supplied here. They follow from the original plus event and the retained
target weak event. Only the literal eligible/correlation-good label remains.
-/

noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance actualGoodDiagonalObservationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_actual_good_diagonal_observation (a b d : ℕ) (c β B C1 : ℝ) (Cq : ℕ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hB : 0 ≤ B) (hC1 : 1 ≤ C1)
    (hCdel : sourceDeletionConstant d β B ≤ C1) (hCq : finiteOmega d ≤ Cq) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ∀ badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1) (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      let selector := logarithmicRadius (c / 4) d N / 4
      let r := effectiveModelRadius a d N β
      let s := g.admissibleState T boundary samples
      let gnew := g.labelledResampledGraph T boundary samples selector
      let φ := correlationThreshold (Real.log (N : ℝ)) a N z.im (graphKestenMcKayReference d z).im
        (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z)
      ∀ targetBadCount : ℕ,
      gnew.SourceOmegaWithRadii a r (logarithmicRadius β d N) (logarithmicRadius (c / 4) d N)
        (finiteOmega d) targetBadCount z →
      ∀ i : s.AdmissibleSampleIndex selector,
      boundary i.val ∈ g.sourceCorrelationGoodLabels T z φ selector samples →
      ‖(gnew.deficient.delete T).G z (s.admissibleSecondVertex selector i) (s.admissibleSecondVertex selector i) -
        cavityIterate z (g.Q z) (r + 1) -
        g.sourceSingletonObservation T r selector z (g.Q z) (samples (boundary i.val))‖ ≤
          graphPaperError a d N (logarithmicRadius β d N) z / Real.log (N : ℝ) ^ 16 := by
  let C := guardedGreenEntryCap d
  let P := sourceGreenPivotCap d B
  let D := sourceEndpointErrorConstant d C1
  have hCextra := finiteExtraReferenceConstant_ge_one d hd
  have hC : 0 ≤ C := by dsimp only [C, guardedGreenEntryCap, commonGreenEntryCap]; linarith
  have hCone : 1 ≤ C := by dsimp only [C, guardedGreenEntryCap, commonGreenEntryCap]; linarith
  have hP : 0 ≤ P := by dsimp only [P, sourceGreenPivotCap]; have hh := finiteReferenceConstant_ge_one d hd; positivity
  have hC10 : 0 ≤ C1 := (by norm_num : (0 : ℝ) ≤ 1).trans hC1
  have hD : 0 ≤ D := sourceEndpointErrorConstant_nonnegative d C1 hC10
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_source_new_endpoint_caps_of_post_budget a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_new_sample_pivot_caps a b d c β B C1 ha hb hd hc hβ hβc hC10 hB,
    eventually_actualGuardedDeletionCaps a b d c β C1 B ha hb hd hc hβ hβc hC10 hB,
    eventually_sourceOmegaWithRadii_subset_sourceOmegaPlusWithRadii a b d c β B C1 Cq
      ha hb hd hc hβ hβc hB hC1 hCdel hCq,
    eventually_source_good_diagonal_correction_small a b d β C P D ha hb hd hβ hC hP hD,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    hdepth, eventually_log_ge_nat 1, Filter.eventually_ge_atTop 1]
    with N hnew hnewPivot hcaps htarget hcorrection hmargin hdepth hlog hN
  intro g o z hz hzB hscale badCount hplus ι _ boundary samples
  dsimp only
  let ell := actualCavityDepth a d N z - 1
  let R := logarithmicRadius (c / 4) d N
  let selector := R / 4
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary samples
  let gnew := g.labelledResampledGraph T boundary samples selector
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let φ := correlationThreshold (Real.log (N : ℝ)) a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
  let δ := D * g.sourcePrime a (logarithmicRadius β d N) z
  intro targetBadCount target i hgood
  have targetPlus := htarget gnew o z targetBadCount hz hzB hscale target
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hcentral : ell + r + 1 ≤ R / 8 := by dsimp only [ell, r, R]; omega
  have hsep : 2 * r + 2 ≤ selector := by dsimp only [r, selector, R]; omega
  have hr : r + 2 ≤ selector := by omega
  have hpost := g.switchedEndpointModel_component_budget hd o ell selector r (R / 8)
    hcentral hsep (hplus.structural.1 o) boundary samples
  obtain ⟨hδone, hentry, hcross⟩ := hnew g o z hz hscale hzB Cq badCount hplus boundary samples hpost
  have hpivot := hnewPivot g o z hz hscale hzB boundary samples Cq targetBadCount targetPlus i
  have oldCaps := hcaps g o z hz hzB hscale Cq badCount hplus
  have hφ : 0 ≤ φ := by unfold φ correlationThreshold; positivity
  have hδ : 0 ≤ δ := by
    have hε := graphPaperError_nonnegative a d N (logarithmicRadius β d N) z hN hz.le
    unfold δ sourcePrime inflatedPrime
    positivity
  have hδC : δ ≤ C := hδone.trans hCone
  let otherRoot (u : s.OtherEndpointIndex selector i.val) : s.endpointModelRoots selector :=
    ⟨u.val.val, by
      obtain ⟨j, hj, _, hx⟩ := u.property
      exact s.eligible_exterior_mem_endpointModelRoots selector j hj u.val.val hx⟩
  have hNewC : ∀ u : s.OtherEndpointIndex selector i.val,
      ‖green (normalizedAdjacency (outsideGraph (s.fullResample selector).graph T) d) z
        (s.otherEndpointEmbedding selector i.val u).val (s.sampledOutsideSecond i.val).val‖ ≤ C := by
    intro u
    exact hentry (otherRoot u) (g.sourceEndpointTipIndex T boundary samples selector i)
  have hNewB : ∀ u : s.OtherEndpointIndex selector i.val,
      ‖green (normalizedAdjacency (outsideGraph (s.fullResample selector).graph T) d) z
        (s.otherEndpointEmbedding selector i.val u).val (s.sampledOutsideFirst i.val)‖ ≤ C := by
    intro u
    exact hentry (otherRoot u) (g.sourceEndpointBaseIndex T boundary samples selector i)
  have hfinite := s.fullResample_good_diagonal_observation_bound g.regular hd selector r hr z (g.Q z) hz
    (g.Q_im_nonnegative z hz) i selector C P φ δ hC hP hφ hδ hδC hgood oldCaps
      hNewC hNewB hpivot (hcross i).1 (hcross i).2
  exact hfinite.trans (hcorrection g o ell hell z hz hscale δ hδ le_rfl)

end RegularGraph
end LocalLaw
