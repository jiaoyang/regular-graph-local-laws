import LocalLaw.ActualSourceEndpointStability
import LocalLaw.SourceEndpointVertices
import LocalLaw.DetachedEndpointRows
import LocalLaw.EndpointSurgerySupport

/-! # Every detached sampled tip has small physical cross entries to all bases

The finite model row is exactly zero at every selected base. The physical
bound therefore follows from actual old-event endpoint surgery, without an
event assumption on the switched graph.
-/

open Filter
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance selectedTipCrossCapsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem selected_first_ne_second {V : Type} {T : Set V} {ι : Type} [Fintype ι]
    (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i j : s.AdmissibleSampleIndex selector) :
    s.admissibleSampleVertex selector j ≠ s.admissibleSecondVertex selector i := by
  intro h
  have hm : (s.admissibleSampleVertex selector j).val ∈ (s.quad i.val).exterior := by
    rw [h]
    exact Or.inr (Or.inr rfl)
  have hi := s.eligible_triple_index_unique selector i (s.admissibleSampleVertex selector j) hm j.val
    (Or.inr (Or.inl rfl))
  have hji : j = i := Subtype.ext hi
  subst j
  exact (s.samples (s.boundary i.val)).property.1.ne (congrArg Subtype.val h)

theorem sourceEndpointQ_tip_any_base_zero {N d : ℕ} {ι : Type} [Fintype ι]
    (g : RegularGraph N d) (hd : 3 ≤ d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hsep : 2*r+2 ≤ selector) (hr : r+2 ≤ selector)
    (i j : (g.admissibleState T labels samples).AdmissibleSampleIndex selector)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    g.sourceEndpointQ T labels samples selector r q z
      (g.sourceEndpointTipIndex T labels samples selector i)
      (g.sourceEndpointBaseIndex T labels samples selector j) = 0 := by
  let s := g.admissibleState T labels samples
  have hne : g.sourceEndpointBaseIndex T labels samples selector j ≠ s.endpointTipRoot selector i := by
    intro he
    exact selected_first_ne_second s selector i j (congrArg Subtype.val he)
  have hh := g.switchedEndpointModel_tip_endpoint_row hd T labels samples selector r hsep hr i q z hz hq
    (g.sourceEndpointBaseIndex T labels samples selector j)
  dsimp only at hh
  rw [if_neg hne] at hh
  exact hh

theorem eventually_source_selected_tip_cross_caps (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25*a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c/32) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → Real.log (N : ℝ)^b/(N : ℝ) ≤ z.im → ‖z‖ ≤ B → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector := logarithmicRadius (c/4) d N/4
      let s := g.admissibleState T labels samples
      let new := (g.labelledResampledGraph T labels samples selector).deficient.delete T
      ∀ i j : s.AdmissibleSampleIndex selector,
        ‖new.G z (s.admissibleSecondVertex selector i) (s.admissibleSampleVertex selector j)‖ ≤
          sourceEndpointErrorConstant d C1*g.sourcePrime a (logarithmicRadius β d N) z := by
  filter_upwards [RegularGraph.eventually_actual_source_endpoint_stability a b d c β B C1
      ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc]
    with N hstability hmargin
  intro g o z hz hfloor hzB Cq badCount hplus ι _ labels samples
  dsimp only
  let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector := logarithmicRadius (c/4) d N/4
  let r := effectiveModelRadius a d N β
  let s := g.admissibleState T labels samples
  intro i j
  have hsep : 2*r+2 ≤ selector := by dsimp only [selector,r]; omega
  have hr : r+2 ≤ selector := by omega
  have hh := hstability g o z hz hfloor hzB Cq badCount hplus labels samples
    (g.sourceEndpointTipIndex T labels samples selector i)
    (g.sourceEndpointBaseIndex T labels samples selector j)
  have hzmodel := sourceEndpointQ_tip_any_base_zero g hd T labels samples selector r hsep hr i j
    (g.Q z) z hz (g.Q_im_nonnegative z hz)
  change ‖_ - g.sourceEndpointQ T labels samples selector r (g.Q z) z
    (g.sourceEndpointTipIndex T labels samples selector i)
    (g.sourceEndpointBaseIndex T labels samples selector j)‖ ≤ _ at hh
  rw [hzmodel, sub_zero] at hh
  exact hh

end SpectralConsequences
