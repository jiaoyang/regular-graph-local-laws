import LocalLaw.SourceEndpointVertices
import LocalLaw.SourceEndpointStability
import LocalLaw.NewSampleGuardCaps
import LocalLaw.ActualGuardedDeletionCaps

/-!
# Actual new endpoint entry and detached-cross caps

Actual source surgery supplies the approximation. Post-component root
counts give its diameter, the source budgets give feedback, and the post
finite class gives all model entry caps. The detached branch has exactly
zero model cross entry.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1400000
namespace LocalLaw
local instance sourceNewEndpointCapsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem sourceEndpointErrorConstant_nonnegative (d : ℕ) (C1 : ℝ) (hC1 : 0 ≤ C1) :
    0 ≤ sourceEndpointErrorConstant d C1 := by unfold sourceEndpointErrorConstant; positivity

namespace RegularGraph

/-- The actual target plus event supplies the new pivot at every accepted
sampled first endpoint, using its invariant vertex and its new far guard. -/
theorem eventually_source_new_sample_pivot_caps (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hC1 : 0 ≤ C1) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ‖z‖ ≤ B →
      ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      let selector := logarithmicRadius (c / 4) d N / 4
      let s := g.admissibleState T boundary samples
      let gnew := g.labelledResampledGraph T boundary samples selector
      ∀ Cq badCount : ℕ,
      gnew.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1) (finiteOmega d) Cq badCount C1 o z →
      ∀ i : s.AdmissibleSampleIndex selector,
        ‖(g.sourceEndpointT T boundary samples selector z
          (g.sourceEndpointBaseIndex T boundary samples selector i)
          (g.sourceEndpointBaseIndex T boundary samples selector i))⁻¹‖ ≤ sourceGreenPivotCap d B := by
  filter_upwards [eventually_actualGuardedDeletionCaps a b d c β C1 B ha hb hd hc hβ hβc hC1 hB,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc]
    with N hcaps hmargin
  intro g o z hz hscale hzB ι _ boundary samples
  dsimp only
  let ell := actualCavityDepth a d N z - 1
  let T := graphBallVertices g.graph o ell
  let selector := logarithmicRadius (c / 4) d N / 4
  let s := g.admissibleState T boundary samples
  let gnew := g.labelledResampledGraph T boundary samples selector
  intro Cq badCount hplus i
  have hselector : 1 ≤ selector := by dsimp only [selector]; omega
  have hTnew : graphBallVertices gnew.graph o ell = T := by
    have hT : T = graphSetBall s.graph {o} ell := by rw [graphSetBall_singleton]; rfl
    have hh := s.fullResample_ball selector {o} ell hT
    change graphBallVertices (s.fullResample selector).graph o ell = T
    simpa only [graphSetBall_singleton] using hh
  have newCaps := hcaps gnew o z hz hzB hscale Cq badCount hplus
  change gnew.GuardedDeletionCaps (graphBallVertices gnew.graph o ell)
    (boundaryFarGuard gnew.graph (graphBallVertices gnew.graph o ell) (selector - 1)) z
      (guardedGreenEntryCap d) (sourceGreenPivotCap d B) at newCaps
  rw [hTnew] at newCaps
  exact s.fullResample_first_pivot_of_guardedCaps g.regular selector hselector i.val i.property z
    (guardedGreenEntryCap d) (sourceGreenPivotCap d B) newCaps

theorem eventually_source_new_endpoint_caps_of_post_budget (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ‖z‖ ≤ B → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1) (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      let selector := logarithmicRadius (c / 4) d N / 4
      let r := effectiveModelRadius a d N β
      let s := g.admissibleState T boundary samples
      let δ := sourceEndpointErrorConstant d C1 * g.sourcePrime a (logarithmicRadius β d N) z
      (g.switchedEndpointModel T boundary samples selector r).ComponentFiniteReferenceBudget →
      δ ≤ 1 ∧
      (∀ i j : s.endpointModelRoots selector,
        ‖g.sourceEndpointT T boundary samples selector z i j‖ ≤ guardedGreenEntryCap d) ∧
      (∀ i : s.AdmissibleSampleIndex selector,
        ‖g.sourceEndpointT T boundary samples selector z
          (g.sourceEndpointTipIndex T boundary samples selector i)
          (g.sourceEndpointBaseIndex T boundary samples selector i)‖ ≤ δ ∧
        ‖g.sourceEndpointT T boundary samples selector z
          (g.sourceEndpointBaseIndex T boundary samples selector i)
          (g.sourceEndpointTipIndex T boundary samples selector i)‖ ≤ δ) := by
  let D := sourceEndpointErrorConstant d C1
  have hC10 : 0 ≤ C1 := (by norm_num : (0 : ℝ) ≤ 1).trans hC1
  have hD : 0 ≤ D := sourceEndpointErrorConstant_nonnegative d C1 hC10
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_source_endpoint_surgery_of_post_budget a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    eventually_paperError_small a b d β ha hb hd hβ, eventually_log_ge_nat 1,
    eventually_log_ge_nat D, hdepth]
    with N hsurgery hnum hmargin herror hlog hlarge hdepth
  intro g o z hz hscale hzB Cq badCount hplus ι _ boundary samples
  dsimp only
  let ell := actualCavityDepth a d N z - 1
  let R := logarithmicRadius (c / 4) d N
  let selector := R / 4
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary samples
  let M := g.switchedEndpointModel T boundary samples selector r
  let e := s.endpointModelKernelEmbedding selector r
  let L := Real.log (N : ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let δ := D * g.sourcePrime a (logarithmicRadius β d N) z
  intro hpost
  have num := hnum z hz hscale
  have hε : 0 ≤ ε := num.error_nonnegative
  have hLp : 0 < L := by dsimp only [L]; linarith
  have hεfour : ε * L ^ 4 ≤ 1 := by
    have hh : ε ≤ (L ^ (4 * a))⁻¹ := herror z hz hscale
    have hcap : ε * L ^ (4 * a) ≤ 1 :=
      (le_div_iff₀ (pow_pos hLp _)).mp (by simpa only [one_div] using hh)
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlog (show 4 ≤ 4 * a by omega)) hε).trans hcap
  have hprime : g.sourcePrime a (logarithmicRadius β d N) z ≤ 1 / L := by
    apply (le_div_iff₀ hLp).mpr
    convert hεfour using 1
    unfold sourcePrime inflatedPrime
    ring
  have hδone : δ ≤ 1 := by
    calc
      _ ≤ D * (1 / L) := mul_le_mul_of_nonneg_left hprime hD
      _ = D / L := by ring
      _ ≤ 1 := (div_le_one hLp).mpr hlarge
  have happ : ∀ i j, ‖g.sourceEndpointT T boundary samples selector z i j -
      g.sourceEndpointQ T boundary samples selector r (g.Q z) z i j‖ ≤ δ :=
    hsurgery g o z hz hscale hzB Cq badCount hplus boundary samples hpost
  have hsep : 2 * r + 2 ≤ selector := by dsimp only [r, selector, R]; omega
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hcentral : ell + r + 1 ≤ R / 8 := by dsimp only [ell, r, R]; omega
  have hcount : ∀ cc : M.graph.ConnectedComponent,
      Nat.card {i : s.endpointModelRoots selector // e i ∈ cc.supp} ≤ 2 * (finiteOmega d + 1) := by
    intro cc
    exact s.endpoint_post_root_count o ell selector r (R / 8) (finiteOmega d) rfl hsep hcentral
      (hplus.structural.1 o) cc
  have hdiam : ∀ x y, M.graph.dist x y ≤ singletonObservationDiameter d r := by
    intro x y
    exact (s.endpointModel_new_distance_bound selector r (2 * (finiteOmega d + 1))
      (by omega) hcount x y).trans (endpoint_component_diameter_le_observation d r)
  have hprior := hplus.cavity.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) hε hC1)
  have hscaled : 0 ≤ C1 ^ 2 * ε := mul_nonneg (sq_nonneg C1) hε
  have hfeedback := (DeficientGraph.weak_localization_feedback_budgets d hd z (g.Q z) hz B
    (C1 ^ 2 * ε) L (sourceObservationLogCap d β) hscaled num.log_one num.log_cap_nonnegative
      num.error_scaled hprior (singletonObservationDiameter d r) (4 * r + 1)
        num.diameter_log num.pair_log num.localization_large).1
  have hCextra : 0 ≤ 2 * finiteExtraReferenceConstant d := by linarith [finiteExtraReferenceConstant_ge_one d hd]
  have ht : physicalTransfer d z ≤ 1 := by
    have hh := physicalTransfer_sq_le_half d hd z
    have hnonneg : 0 ≤ physicalTransfer d z := norm_nonneg _
    nlinarith
  have hmodel : ∀ i j, ‖g.sourceEndpointQ T boundary samples selector r (g.Q z) z i j‖ ≤
      2 * finiteExtraReferenceConstant d := by
    intro i j
    have hh := M.componentwise_finite_kernel_decay hd hpost (g.Q z) z hz (g.Q_im_nonnegative z hz)
      (singletonObservationDiameter d r) hdiam hfeedback (e i) (e j)
    exact hh.trans (mul_le_of_le_one_right hCextra (pow_le_one₀ (norm_nonneg _) ht))
  refine ⟨hδone, ?_, ?_⟩
  · intro i j
    have hh := (norm_sub_le_norm_sub_add_norm_sub (g.sourceEndpointT T boundary samples selector z i j)
      (g.sourceEndpointQ T boundary samples selector r (g.Q z) z i j) 0).trans
        (add_le_add (happ i j) (by simpa using hmodel i j))
    simp only [sub_zero] at hh
    unfold guardedGreenEntryCap commonGreenEntryCap
    linarith
  · intro i
    have hzero := g.sourceEndpointQ_tip_base_zero hd T boundary samples selector r hsep i
      (g.Q z) z hz (g.Q_im_nonnegative z hz)
    have hfirst := happ (g.sourceEndpointTipIndex T boundary samples selector i)
      (g.sourceEndpointBaseIndex T boundary samples selector i)
    rw [hzero, sub_zero] at hfirst
    refine ⟨hfirst, ?_⟩
    have hs : (((g.labelledResampledGraph T boundary samples selector).deficient.delete T).G z).IsSymm := by
      have hh := ((g.labelledResampledGraph T boundary samples selector).deficient.delete T).extensionGreen_isSymm (0 : ℂ) z
      simpa only [DeficientGraph.G, DeficientGraph.extensionGreen, boundaryGreen, boundaryMatrix,
        zero_smul, sub_zero, green] using hh
    have heq : g.sourceEndpointT T boundary samples selector z
        (g.sourceEndpointBaseIndex T boundary samples selector i)
        (g.sourceEndpointTipIndex T boundary samples selector i) =
      g.sourceEndpointT T boundary samples selector z
        (g.sourceEndpointTipIndex T boundary samples selector i)
        (g.sourceEndpointBaseIndex T boundary samples selector i) := hs.apply _ _
    rw [heq]
    exact hfirst

end RegularGraph
end LocalLaw
