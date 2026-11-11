import LocalLaw.ActualPairedEndpointSurgery
import LocalLaw.SourceEndpointStability
import LocalLaw.SwitchedEndpointBudget

/-!
# Realize every input of actual good-label paired surgery

The source enlarged event, literal branch restoration, endpoint incidence,
model diameter and nominal-error numerics derive the old error, new model
row sums and contraction. Only membership in the actual isolated uniquely
attached good set remains to select the improved rows.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourcePairedSurgeryParametersDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_actual_paired_endpoint_offdiagonal (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25*a ≤ b) (hd : 3 ≤ d) (hc : 0<c)
    (hβ : 0<β) (hβc : β ≤ c/32) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ) ≤ z.im → ‖z‖ ≤ B → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell := actualCavityDepth a d N z-1
      let R := logarithmicRadius (c/4) d N
      let selector := R/4
      let r := effectiveModelRadius a d N β
      let T := graphBallVertices g.graph o ell
      let s := g.admissibleState T labels samples
      let C := endpointSurgeryModelRowCap d (2*(finiteOmega d+1))
      let w := endpointSurgeryCouplingCap d
      let δ := 2*C1*g.sourcePrime a (logarithmicRadius β d N) z
      ∃ hfit : ell+1 ≤ R/8, ∀ (i : s.AdmissibleSampleIndex selector) (j : ι) (φ : ℝ), 0 ≤ φ → j ≠ i.val →
      (labels i.val ∉ multiattachmentBoundaryLabels g.graph o hfit) →
      labels i.val ∈ g.sourceCorrelationGoodLabels T z φ (R/4) samples →
      ‖(g.sourceEndpointT T labels samples selector z-g.sourceEndpointQ T labels samples selector r (g.Q z) z)
        (s.endpointRootLabel selector (Sum.inr (i,1))) (s.endpointFinalBoundaryRoot selector j)‖  ≤ 
        (1+C*w)^2*φ+2*(1+C*w)^3*(2*δ+(Fintype.card (s.endpointModelRoots selector):ℝ)*φ)*w*δ := by
  let m := 2*(finiteOmega d+1)
  let C := endpointSurgeryModelRowCap d m
  let w := endpointSurgeryCouplingCap d
  have hC : 0 ≤ C := by
    dsimp only [C,endpointSurgeryModelRowCap]
    have hh := finiteExtraReferenceConstant_ge_one d hd
    positivity
  have hw : 0 ≤ w := by dsimp only [w,endpointSurgeryCouplingCap]; positivity
  have hC10 : 0 ≤ C1 := (by norm_num : (0:ℝ) ≤ 1).trans hC1
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,hdepth,
    eventually_endpoint_surgery_smallness a b d β C w (2*C1) ha hb hd hβ hC hw (by positivity)]
    with N hnum hmargin hdepth hsmall
  intro g o z hz hfloor hzB Cq badCount hplus ι _ labels samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let R := logarithmicRadius (c/4) d N
  let selector := R/4
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T labels samples
  let K := s.endpointModelVertices selector r
  let e := s.endpointModelKernelEmbedding selector r
  let old := g.deficient.delete T
  let new := (g.labelledResampledGraph T labels samples selector).deficient.delete T
  let Robs := singletonObservationDiameter d r
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let L := Real.log (N:ℝ)
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hcentral : ell+r+1 ≤ R/8 := by dsimp only [ell,r,R]; omega
  have hsep : 2*r+2 ≤ selector := by dsimp only [selector,r,R]; omega
  have hOldBudget : (old.restrict K).ComponentFiniteReferenceBudget :=
    g.endpointModel_component_budget o ell selector r (R/8) hcentral hsep (hplus.structural.1 o) labels samples
  have hNewBudget : (new.restrict K).ComponentFiniteReferenceBudget :=
    g.switchedEndpointModel_component_budget hd o ell selector r (R/8) hcentral hsep (hplus.structural.1 o) labels samples
  have hOldCount := g.endpointModel_old_component_root_count o ell selector r (R/8) (finiteOmega d)
    hcentral hsep (hplus.structural.1 o) labels samples
  have hNewCount : ∀ cc : (new.restrict K).graph.ConnectedComponent,
      Nat.card {i : s.endpointModelRoots selector // e i ∈ cc.supp} ≤ m := by
    intro cc
    exact s.endpoint_post_root_count o ell selector r (R/8) (finiteOmega d) rfl hsep hcentral (hplus.structural.1 o) cc
  have hOldDiam : ∀ x y,(old.restrict K).graph.dist x y ≤ Robs := by
    intro x y
    exact (s.endpointModel_old_distance_bound selector r m (by dsimp only [m]; omega) hOldCount x y).trans
      (endpoint_component_diameter_le_observation d r)
  have hNewDiam : ∀ x y,(new.restrict K).graph.dist x y ≤ Robs := by
    intro x y
    exact (s.endpointModel_new_distance_bound selector r m (by dsimp only [m]; omega) hNewCount x y).trans
      (endpoint_component_diameter_le_observation d r)
  have hcapture : ∀ i,graphBallVertices old.graph (e i).val r ⊆ K := fun i v hv => ⟨i.val,i.property,hv⟩
  have num := hnum z hz hfloor
  have happ : ∀ i j,‖old.G z (e i).val (e j).val-old.P r z (g.Q z) (e i).val (e j).val‖ ≤ C1*L^3*ε := by
    intro i j
    simpa only [sourcePrime,inflatedPrime,mul_assoc] using hplus.deleted (e i).val (e j).val
  have hE := old.source_endpoint_restriction_approximation hd K e r Robs z (g.Q z) hz
    (g.Q_im_nonnegative z hz) B C1 ε L (sourceObservationLogCap d β) hzB num hOldBudget hOldDiam
    num.diameter_log hcapture hplus.cavity happ
  have hscaled : 0 ≤ C1^2*ε := mul_nonneg (sq_nonneg C1) num.error_nonnegative
  have hprior := hplus.cavity.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative hC1)
  have hfeedback := (DeficientGraph.weak_localization_feedback_budgets d hd z (g.Q z) hz B (C1^2*ε) L (sourceObservationLogCap d β)
    hscaled num.log_one num.log_cap_nonnegative num.error_scaled hprior Robs (4*r+1)
      num.diameter_log num.pair_log num.localization_large).1
  have hrows := (new.restrict K).componentwise_endpoint_green_rows hd hNewBudget e m hNewCount
    (g.Q z) z hz (g.Q_im_nonnegative z hz) Robs hNewDiam hfeedback
  have hsmall' : (Fintype.card (s.endpointModelRoots selector):ℝ)*(1+C*w)*w*(2*C1*g.sourcePrime a (logarithmicRadius β d N) z) ≤ 1/2 := by
    simpa only [Nat.card_eq_fintype_card] using hsmall g o ell hell labels samples selector z hz hfloor
  refine ⟨by omega, ?_⟩
  intro i j φ hφ hji hnot hgood
  apply g.actual_paired_endpoint_offdiagonal hd o ell selector r (R/8) (R/4) hsep hcentral labels samples
    i hnot j hji (g.Q z) z hz (g.Q_im_nonnegative z hz) C
      (2*C1*g.sourcePrime a (logarithmicRadius β d N) z) φ hC (by
        have hh := num.error_nonnegative
        have hL : 0 ≤ L := (by norm_num : (0:ℝ) ≤ 1).trans num.log_one
        unfold sourcePrime inflatedPrime
        positivity) hφ hgood
      (fun u => hrows.1 (e u)) (fun v => hrows.2 (e v)) _ hsmall'
  intro u v
  exact (hE u v).trans_eq (by unfold sourcePrime inflatedPrime; ring)

end RegularGraph
end LocalLaw
