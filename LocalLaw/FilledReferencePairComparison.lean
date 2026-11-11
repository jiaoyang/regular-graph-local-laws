import LocalLaw.FilledEndpointLocality
import LocalLaw.FiniteBoundaryContinuity
import LocalLaw.LocalizationFeedbackRate

/-! # Compare the fixed row reference with the actual switched pair model -/

noncomputable section
namespace LocalLaw
local instance filledReferencePairComparisonDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem filledReference_pair_comparison (g : RegularGraph N d) (hd : 3≤d)
    (T : Set (Fin N)) (labels : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T) (selector r : ℕ)
    (hsep : 2*r+2≤selector) (hr : r+2≤selector)
    (qold qnew z : ℂ) (hz : 0<z.im) (hqo : 0≤qold.im) (hqn : 0≤qnew.im)
    (B ε L A : ℝ) (hzB : ‖z‖≤B) (hε : 0≤ε) (hεOne : ε≤1)
    (hL : 1≤L) (hA : 0≤A) (hcap : ε*L^4≤1)
    (hpriorOld : ‖qold-semicircleRoot z‖≤scalarScale (spectralScale z) ε)
    (hpriorNew : ‖qnew-semicircleRoot z‖≤scalarScale (spectralScale z) ε)
    (R : ℕ)
    (hbudget : let s := g.admissibleState T labels samples
      let gnew := g.labelledResampledGraph T labels samples selector
      (gnew.filledExteriorModel T (s.endpointModelVertices selector r)).ComponentFiniteReferenceBudget)
    (hdiam : let s := g.admissibleState T labels samples
      let gnew := g.labelledResampledGraph T labels samples selector
      ∀ u v,(gnew.filledExteriorModel T (s.endpointModelVertices selector r)).graph.dist u v≤R)
    (hRlog : (R:ℝ)+1≤A*L) (hrlog : ((4*r+1:ℕ)+1:ℝ)≤A*L)
    (hlarge : DeficientGraph.localizationBudgetConstant d B A≤L) (x y : T) :
    let gnew := g.labelledResampledGraph T labels samples selector
    ‖g.sourceRetainedReference T r qold z x y-gnew.P r z qnew x.val y.val‖≤
      16*finiteExtraReferenceConstant d^2*((R:ℝ)+1)*‖qold-qnew‖+
      DeficientGraph.localizationFeedbackConstant d B A*L*
        (Real.sqrt (spectralScale z)*‖qnew-semicircleRoot z‖+‖qnew-semicircleRoot z‖^2)+
      DeficientGraph.localizationTailConstant d*physicalTransfer d z^(2*r) := by
  let s := g.admissibleState T labels samples
  let gnew := g.labelledResampledGraph T labels samples selector
  let K := s.endpointModelVertices selector r
  let M := gnew.filledExteriorModel T K
  let e := filledInnerVertex T K
  have hOld := (DeficientGraph.weak_localization_feedback_budgets d hd z qold hz B ε L A
    hε hL hA hcap hpriorOld R (4*r+1) hRlog hrlog hlarge).1
  have hNew := (DeficientGraph.weak_localization_feedback_budgets d hd z qnew hz B ε L A
    hε hL hA hcap hpriorNew R (4*r+1) hRlog hrlog hlarge).1
  have hcontinuity := M.componentwise_boundary_two_parameter hd hbudget qold qnew z hz hqo hqn R hdiam hOld hNew (e x) (e y)
  have hlocal := M.componentwise_pair_localization_feedback hd hbudget qnew z hz hqn B hzB ε L A
    hε hεOne hL hA hcap hpriorNew R r hdiam hRlog hrlog hlarge (e x) (e y)
  have hreference : M.extensionGreen qold z (e x) (e y)=g.sourceRetainedReference T r qold z x y :=
    g.switchedFilled_reference_entry hd T labels samples selector r hsep hr qold z hz hqo x y
  have hpair : M.P r z qnew (e x) (e y)=gnew.P r z qnew x.val y.val :=
    g.filledEndpoint_pair_P T labels samples selector r qnew z x y
  calc
    _ = ‖M.extensionGreen qold z (e x) (e y)-M.P r z qnew (e x) (e y)‖ := by rw [hreference,hpair]
    _ ≤ ‖M.extensionGreen qold z (e x) (e y)-M.extensionGreen qnew z (e x) (e y)‖+
        ‖M.extensionGreen qnew z (e x) (e y)-M.P r z qnew (e x) (e y)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := (add_le_add hcontinuity hlocal).trans_eq (by ring)

end RegularGraph
end LocalLaw
