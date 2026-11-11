import LocalLaw.ActualSourceEndpointStability
import LocalLaw.SourceEndpointMatrices

/-!
# New augmented endpoint control without a post augmented reference class

Both OLD restrictions are localized through the actual old physical Green
matrix. Their actual new inverses obey the same physical perturbation law.
The endpoint-only post model supplies the comparison row sums; consequently
the augmented post model requires no finite-reference-class hypothesis.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance augmentedEndpointStabilityDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

def augmentedEndpointEmbedding (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (Saug : Set (Tᶜ : Set (Fin N)))
    (hcontain : (g.admissibleState T boundary samples).endpointModelVertices selector r ⊆ Saug) :
    (g.admissibleState T boundary samples).endpointModelRoots selector ↪ Saug where
  toFun i := ⟨i.val, hcontain ((g.admissibleState T boundary samples).endpointModelKernelEmbedding selector r i).property⟩
  inj' := by
    intro i j h
    exact Subtype.ext (congrArg (fun x : Saug => x.val) h)

end RegularGraph
namespace RegularGraph

theorem eventually_augmented_endpoint_stability_with_diameter (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ‖z‖ ≤ B → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1)
        (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      let selector := logarithmicRadius (c / 4) d N / 4
      let r := effectiveModelRadius a d N β
      let s := g.admissibleState T boundary samples
      let gnew := g.labelledResampledGraph T boundary samples selector
      ∀ (Saug : Set (Tᶜ : Set (Fin N)))
      (hcontain : s.endpointModelVertices selector r ⊆ Saug),
      ((g.deficient.delete T).restrict Saug).ComponentFiniteReferenceBudget →
      ∀ Raug : ℕ, (∀ x y, ((g.deficient.delete T).restrict Saug).graph.dist x y ≤ Raug) →
      (Raug : ℝ) + 1 ≤ sourceObservationLogCap d β * Real.log (N : ℝ) →
      let e := g.augmentedEndpointEmbedding T boundary samples selector r Saug hcontain
      ∀ i j : s.endpointModelRoots selector,
        ‖((gnew.deficient.delete T).restrict Saug).extensionGreen (g.Q z) z (e i) (e j) -
          g.sourceEndpointQ T boundary samples selector r (g.Q z) z i j‖ ≤
          2 * sourceEndpointErrorConstant d C1 * g.sourcePrime a (logarithmicRadius β d N) z := by
  let m := 2 * (finiteOmega d + 1)
  let C := endpointSurgeryModelRowCap d m
  let w := endpointSurgeryCouplingCap d
  have hC : 0 ≤ C := by dsimp only [C, endpointSurgeryModelRowCap]; have hh := finiteExtraReferenceConstant_ge_one d hd; positivity
  have hw : 0 ≤ w := by dsimp only [w, endpointSurgeryCouplingCap]; positivity
  have hC10 : 0 ≤ C1 := (by norm_num : (0 : ℝ) ≤ 1).trans hC1
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc, hdepth,
    eventually_endpoint_surgery_smallness a b d β C w (4 * C1) ha hb hd hβ hC hw (by positivity)]
    with N hnum hmargin hdepth hsmall
  intro g o z hz hscale hzB Cq badCount hplus ι _ boundary samples
  dsimp only
  let ell := actualCavityDepth a d N z - 1
  let Rgeom := logarithmicRadius (c / 4) d N
  let selector := Rgeom / 4
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary samples
  let S0 := s.endpointModelVertices selector r
  let e0 := s.endpointModelKernelEmbedding selector r
  let old := g.deficient.delete T
  let gnew := g.labelledResampledGraph T boundary samples selector
  let new := gnew.deficient.delete T
  let L := Real.log (N : ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let Rcap := singletonObservationDiameter d r
  intro Saug hcontain hbudgetAug Raug hdiamAug hRauglog
  let e := g.augmentedEndpointEmbedding T boundary samples selector r Saug hcontain
  let RR := ((old.restrict Saug).extensionGreen (g.Q z) z).submatrix e e
  let UU := ((new.restrict Saug).extensionGreen (g.Q z) z).submatrix e e
  let PP := g.sourceEndpointP T boundary samples selector r (g.Q z) z
  let QQ := g.sourceEndpointQ T boundary samples selector r (g.Q z) z
  let WW := g.sourceEndpointW T boundary samples selector
  let δ := 4 * C1 * L ^ 3 * ε
  have num := hnum z hz hscale
  have hε : 0 ≤ ε := num.error_nonnegative
  have hL : 0 ≤ L := (by norm_num : (0 : ℝ) ≤ 1).trans num.log_one
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hcentral : ell + r + 1 ≤ Rgeom / 8 := by dsimp only [ell, r, Rgeom]; omega
  have hsep : 2 * r + 2 ≤ selector := by dsimp only [r, selector, Rgeom]; omega
  have hbudget0 : (old.restrict S0).ComponentFiniteReferenceBudget :=
    g.endpointModel_component_budget o ell selector r (Rgeom / 8) hcentral hsep (hplus.structural.1 o) boundary samples
  have hbudgetNew : (new.restrict S0).ComponentFiniteReferenceBudget :=
    g.switchedEndpointModel_component_budget hd o ell selector r (Rgeom / 8) hcentral hsep
      (hplus.structural.1 o) boundary samples
  have hcountOld := g.endpointModel_old_component_root_count o ell selector r (Rgeom / 8) (finiteOmega d)
    hcentral hsep (hplus.structural.1 o) boundary samples
  have hcountNew : ∀ cc : (new.restrict S0).graph.ConnectedComponent,
      Nat.card {i : s.endpointModelRoots selector // e0 i ∈ cc.supp} ≤ m := by
    intro cc
    exact s.endpoint_post_root_count o ell selector r (Rgeom / 8) (finiteOmega d) rfl hsep hcentral
      (hplus.structural.1 o) cc
  have hdiam0 : ∀ x y, (old.restrict S0).graph.dist x y ≤ Rcap := fun x y =>
    (s.endpointModel_old_distance_bound selector r m (by dsimp only [m]; omega) hcountOld x y).trans
      (endpoint_component_diameter_le_observation d r)
  have hdiamNew : ∀ x y, (new.restrict S0).graph.dist x y ≤ Rcap := fun x y =>
    (s.endpointModel_new_distance_bound selector r m (by dsimp only [m]; omega) hcountNew x y).trans
      (endpoint_component_diameter_le_observation d r)
  have hcapture0 : ∀ i, graphBallVertices old.graph (e0 i).val r ⊆ S0 := fun i v hv => ⟨i.val, i.property, hv⟩
  have hcapture : ∀ i, graphBallVertices old.graph (e i).val r ⊆ Saug :=
    fun i v hv => hcontain (hcapture0 i hv)
  have hpair : ∀ i j, ‖old.G z (e i).val (e j).val - old.P r z (g.Q z) (e i).val (e j).val‖ ≤ C1 * L ^ 3 * ε := by
    intro i j
    simpa only [sourcePrime, inflatedPrime, mul_assoc] using hplus.deleted (e i).val (e j).val
  have happroxAug := old.source_endpoint_restriction_approximation hd Saug e r Raug z (g.Q z) hz
    (g.Q_im_nonnegative z hz) B C1 ε L (sourceObservationLogCap d β) hzB num hbudgetAug hdiamAug
      hRauglog hcapture hplus.cavity hpair
  have happrox0 := old.source_endpoint_restriction_approximation hd S0 e0 r Rcap z (g.Q z) hz
    (g.Q_im_nonnegative z hz) B C1 ε L (sourceObservationLogCap d β) hzB num hbudget0 hdiam0
      num.diameter_log hcapture0 hplus.cavity hpair
  have hE : ∀ i j, ‖(RR - PP) i j‖ ≤ δ := by
    intro i j
    have ha : ‖old.G z i.val j.val - RR i j‖ ≤ 2 * C1 * L ^ 3 * ε := happroxAug i j
    have hb : ‖old.G z i.val j.val - PP i j‖ ≤ 2 * C1 * L ^ 3 * ε := happrox0 i j
    have ha' : ‖RR i j - old.G z i.val j.val‖ ≤ 2 * C1 * L ^ 3 * ε := by
      rw [norm_sub_rev]
      exact ha
    have hh := (norm_sub_le_norm_sub_add_norm_sub (RR i j) (old.G z i.val j.val) (PP i j)).trans
      (add_le_add ha' hb)
    exact hh.trans_eq (by dsimp only [δ]; ring)
  have hgraph : ∀ x y, x ∉ Set.range (fun i => (e i).val) ∨ y ∉ Set.range (fun i => (e i).val) →
      (old.graph.Adj x y ↔ new.graph.Adj x y) := by
    intro x y hxy
    have haway : x ∉ s.fullResampleOutsideEndpoints selector ∨ y ∉ s.fullResampleOutsideEndpoints selector :=
      hxy.imp
        (fun hx hs => hx ⟨⟨x, s.fullResampleOutsideEndpoints_subset_modelRoots selector hs⟩, rfl⟩)
        (fun hy hs => hy ⟨⟨y, s.fullResampleOutsideEndpoints_subset_modelRoots selector hs⟩, rfl⟩)
    rcases haway with hx | hy
    · exact (s.fullResample_outside_adj_of_away_left selector x y hx).symm
    · rw [old.graph.adj_comm, new.graph.adj_comm]
      exact (s.fullResample_outside_adj_of_away_left selector y x hy).symm
  have haugUpdate := old.restrict_endpoint_inverse_updates new hd Saug e
    (g.deleted_degree_deficit_saturated T) (gnew.deleted_degree_deficit_saturated T) hgraph
      (g.Q z) z hz (g.Q_im_nonnegative z hz)
  have hU : UU + RR * WW * UU = RR := haugUpdate.1
  have hbase := g.source_endpoint_updates hd T boundary samples selector r (g.Q z) z hz (g.Q_im_nonnegative z hz)
  have hQ : QQ + QQ * WW * PP = PP := hbase.2.2.2
  have hprior := hplus.cavity.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) hε hC1)
  have hfeedback := (DeficientGraph.weak_localization_feedback_budgets d hd z (g.Q z) hz B
    (C1 ^ 2 * ε) L (sourceObservationLogCap d β) (mul_nonneg (sq_nonneg C1) hε) num.log_one
      num.log_cap_nonnegative num.error_scaled hprior Rcap (4 * r + 1) num.diameter_log num.pair_log num.localization_large).1
  have hrows := (new.restrict S0).componentwise_endpoint_green_rows hd hbudgetNew e0 m hcountNew
    (g.Q z) z hz (g.Q_im_nonnegative z hz) Rcap hdiamNew hfeedback
  have hQrow : ∀ i, ∑ j, ‖QQ i j‖ ≤ C := fun i => hrows.1 (e0 i)
  have hQcol : ∀ j, ∑ i, ‖QQ i j‖ ≤ C := fun j => hrows.2 (e0 j)
  have hW := g.source_endpoint_coupling_mass T boundary samples selector
  have hsmall' : (Fintype.card (s.endpointModelRoots selector) : ℝ) * (1 + C * w) * w * δ ≤ 1 / 2 := by
    have hh := hsmall g o ell hell boundary samples selector z hz hscale
    convert hh using 1
    simp only [Nat.card_eq_fintype_card, δ, sourcePrime, inflatedPrime]
    ring
  intro i j
  have hh := surgery_entry_stability RR UU PP QQ WW hU hQ C w δ hC hw hδ hQrow hQcol hW.1 hW.2 hE hsmall' i j
  exact hh.trans_eq (by dsimp only [δ, C, m, w]; unfold sourceEndpointErrorConstant sourcePrime inflatedPrime; ring)

/-- The earlier fixed diameter interface is the special case supplied by
the source observation diameter budget. -/
theorem eventually_augmented_endpoint_stability (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ‖z‖ ≤ B → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1)
        (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      let selector := logarithmicRadius (c / 4) d N / 4
      let r := effectiveModelRadius a d N β
      let s := g.admissibleState T boundary samples
      let gnew := g.labelledResampledGraph T boundary samples selector
      ∀ (Saug : Set (Tᶜ : Set (Fin N)))
      (hcontain : s.endpointModelVertices selector r ⊆ Saug),
      ((g.deficient.delete T).restrict Saug).ComponentFiniteReferenceBudget →
      (∀ x y, ((g.deficient.delete T).restrict Saug).graph.dist x y ≤ singletonObservationDiameter d r) →
      let e := g.augmentedEndpointEmbedding T boundary samples selector r Saug hcontain
      ∀ i j : s.endpointModelRoots selector,
        ‖((gnew.deficient.delete T).restrict Saug).extensionGreen (g.Q z) z (e i) (e j) -
          g.sourceEndpointQ T boundary samples selector r (g.Q z) z i j‖ ≤
          2 * sourceEndpointErrorConstant d C1 * g.sourcePrime a (logarithmicRadius β d N) z := by
  filter_upwards [eventually_augmented_endpoint_stability_with_diameter a b d c β B C1
    ha hb hd hc hβ hβc hC1,
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1]
    with N hgeneral hnum
  intro g o z hz hscale hzB Cq badCount hplus ι _ boundary samples
  dsimp only
  intro Saug hcontain hbudget hdiam
  exact hgeneral g o z hz hscale hzB Cq badCount hplus boundary samples Saug hcontain hbudget
    (singletonObservationDiameter d (effectiveModelRadius a d N β)) hdiam (hnum z hz hscale).diameter_log

end RegularGraph
end LocalLaw
