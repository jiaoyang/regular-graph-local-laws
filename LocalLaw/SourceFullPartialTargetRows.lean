import LocalLaw.SourceFullPartialInputs

/-! # Actual old target-to-full-endpoint rows on every retained subset -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceFullPartialTargetRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 2000000
namespace RegularGraph

theorem eventually_source_full_partial_target_rows (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop,∀ (g : RegularGraph N d) (o : Fin N) (z q : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → 0≤q.im →
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) →
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀{ι : Type}[Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y : Fin N),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector := logarithmicRadius (c/4) d N/4
      let r := effectiveModelRadius a d N β
      let s := g.admissibleState T labels samples
      ∀(hs : 1≤selector)(S : Set (Fin N)),S⊆s.fullTwoTargetVertices selector r x y →
      let e := s.fullPartialEmbedding selector S hs
      let G := (g.deficient.restrict S).extensionGreen q z
      ∀v:S,(∑j,‖G v (e j)‖)≤sourceFullCutRowConstant d β*Real.log (N:ℝ)^(a-1) := by
  let A := fullRestrictionLogCap d β
  let U := fullEndpointCountConstant d
  have hA := (fullRestrictionLogCap_properties d β).1
  have hAobs := (fullRestrictionLogCap_properties d β).2.1
  have hU : 0≤U := by dsimp only [U,fullEndpointCountConstant]; positivity
  filter_upwards [eventually_source_fullRestriction_geometry a b d c β B ha hb hd hc hβ hβc,
    eventually_sourceObservationBounds_of_cap a b d c β B C1 A ha hb hd hc hβ hβc hC1 hAobs,
    eventually_actual_fullPartialIndex_count a d ha hd] with N hgeo hnum hcount
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let T := graphBallVertices g.graph o ell
  let selector := logarithmicRadius (c/4) d N/4
  let r := effectiveModelRadius a d N β
  let s := g.admissibleState T labels samples
  let D := fullTwoTargetDiameter d ell r
  let R := hereditaryReferenceRadius d D
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  have num := hnum z hz hfloor
  have hscaled : 0≤C1^2*ε := mul_nonneg (sq_nonneg C1) num.error_nonnegative
  have hprior' := hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative hC1)
  intro hs S hSS
  let e := s.fullPartialEmbedding selector S hs
  let G := (g.deficient.restrict S).extensionGreen q z
  have hg := hgeo g o z hz hfloor hballs labels samples x y S hSS
  have hsmall := (DeficientGraph.weak_localization_feedback_budgets d hd z q hz B (C1^2*ε) L A
    hscaled num.log_one hA num.error_scaled hprior' R (4*r+1) hg.2.2.1 num.pair_log num.localization_large).1
  intro v
  have hsq := (g.deficient.restrict S).componentwise_extensionGreen_square_sum hd hg.1 z q hz hq R hg.2.1 hsmall v
  have hsub : (∑j,‖G v (e j)‖^2)≤∑w,‖G v w‖^2 := by
    calc
      _ = ∑w∈Finset.univ.image e,‖G v w‖^2 := (Finset.sum_image (fun _ _ _ _ h=>e.injective h)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=>sq_nonneg _)
  have hmass : (∑j,‖G v (e j)‖^2)≤(8*finiteExtraReferenceConstant d^2*A)*L := by
    calc
      _ ≤ 8*finiteExtraReferenceConstant d^2*((R:ℝ)+1) := hsub.trans hsq
      _ ≤ 8*finiteExtraReferenceConstant d^2*(A*L) := mul_le_mul_of_nonneg_left hg.2.2.1 (by positivity)
      _ = _ := by ring
  have hc : (Fintype.card (s.FullEndpointIndex selector S):ℝ)≤U*L^(2*a-4) := by
    simpa only [Nat.card_eq_fintype_card] using hcount g o z labels samples selector hs S
  exact full_mask_log_row_bound (fun j=>G v (e j)) a L U (8*finiteExtraReferenceConstant d^2*A)
    (by omega) num.log_one hU (by positivity) hc hmass

end RegularGraph
end LocalLaw
