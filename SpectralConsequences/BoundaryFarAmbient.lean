import LocalLaw.ActualSourceEndpointStability
import LocalLaw.BoundaryGuardAmbientDistance
import LocalLaw.AdmissibleEndpointPatches
import LocalLaw.PairModelFarZero
import LocalLaw.IndependentRadiusEvents
import LocalLaw.EffectiveModelRadius

/-! # Actual original-event Green entries from selected samples to T

The already proved outside-boundary guard converts to the ambient metric.
The finite pair model is then disconnected, so the original local law gives
an epsilon bound, rather than a model-size or resolvent-norm bound.
-/
open Filter
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance selectedInnerCrossDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

omit [Fintype ι] in
theorem selected_pair_cross_inner_of_entry_bound (g : LocalLaw.RegularGraph N d)
    (hd : 3 ≤ d) (T : Set (Fin N)) (labels : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T) (selector r : ℕ)
    (hselector : 1 ≤ selector) (hsep : 2*r+1 ≤ selector)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (ε : ℝ)
    (happrox : ∀ x y, ‖g.G z x y-g.P r z q x y‖ ≤ ε)
    (i : (g.admissibleState T labels samples).AdmissibleSampleIndex selector)
    (v : (Tᶜ : Set (Fin N)))
    (hv : v ∈ (g.admissibleState T labels samples).admissiblePairRoots selector i)
    (t : T) : ‖g.G z v.val t.val‖ ≤ ε ∧ ‖g.G z t.val v.val‖ ≤ ε := by
  let s := g.admissibleState T labels samples
  have hguard := s.admissiblePairRoots_far_boundary selector hselector i hv
  have hfar := boundaryFarOutside_ambient_far_set g.graph T (selector-1) v hguard t.val t.property
  rw [Nat.sub_add_cancel hselector] at hfar
  have hfar' : ((2*r+1:ℕ):ℕ∞) < g.graph.edist v.val t.val :=
    (ENat.coe_le_coe.mpr hsep).trans_lt hfar
  have hzero := g.deficient.P_eq_zero_of_edist_gt hd r q z hz hq v.val t.val hfar'
  rw [g.deficient_P] at hzero
  have hzero' := g.deficient.P_eq_zero_of_edist_gt hd r q z hz hq t.val v.val
    (by change ((2*r+1:ℕ):ℕ∞)<g.graph.edist t.val v.val; rw [g.graph.edist_comm];exact hfar')
  rw [g.deficient_P] at hzero'
  constructor
  · simpa only [hzero,sub_zero] using happrox v.val t.val
  · simpa only [hzero',sub_zero] using happrox t.val v.val

theorem eventually_source_selected_inner_cross (a d : ℕ) (c β : ℝ)
    (hd : 3 ≤ d) (hc : 0 < c) (hβ : 0 < β) (hβc : β ≤ c/32) :
    ∀ᶠ N : ℕ in atTop, ∀ (g : LocalLaw.RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ∀ badCount : ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector := logarithmicRadius (c/4) d N/4
      let s := g.admissibleState T labels samples
      ∀ (i : s.AdmissibleSampleIndex selector) (v : (Tᶜ : Set (Fin N))),
      v ∈ s.admissiblePairRoots selector i → ∀ t : T,
      ‖g.G z v.val t.val‖ ≤ graphPaperError a d N (logarithmicRadius β d N) z ∧
        ‖g.G z t.val v.val‖ ≤ graphPaperError a d N (logarithmicRadius β d N) z := by
  filter_upwards [eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc]
    with N hmargin
  intro g o z hz badCount hsource ι _ labels samples
  dsimp only
  let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector := logarithmicRadius (c/4) d N/4
  let r := effectiveModelRadius a d N β
  have hsep : 2*r+1 ≤ selector := by dsimp only [r,selector];omega
  have hselector : 1 ≤ selector := by omega
  intro i v hv t
  exact selected_pair_cross_inner_of_entry_bound g hd T labels samples selector r hselector hsep
    (g.Q z) z hz (g.Q_im_nonnegative z hz) _ hsource.2.2 i v hv t

end RegularGraph
end SpectralConsequences
