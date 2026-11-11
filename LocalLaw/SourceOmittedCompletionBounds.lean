import LocalLaw.OmittedLeafDiameter
import LocalLaw.SourcePartialGeometry

/-! # Actual source bounds for the all-slot old-class completion

Every original lost-B slot and every deficit-consuming A slot is included.
The old strong-radius structural event supplies the finite class, and the
weak scalar prior supplies perturbative kernel decay. No finite-class
hypothesis for the switched target pair is used.
-/

open Filter
noncomputable section
set_option maxHeartbeats 3000000
namespace LocalLaw
local instance sourceOmittedCompletionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def omittedCompletionObservationLogCap (d : ℕ) (β : ℝ) : ℝ :=
  (2*(finiteOmega d:ℝ)+7)*sourcePartialObservationLogCap d β

namespace RegularGraph

theorem eventually_source_omitted_completion_bounds (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25*a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c/32) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in atTop,∀(g : RegularGraph N d)(o : Fin N)(z q : ℂ),
      0 < z.im → Real.log (N:ℝ)^b/(N:ℝ) ≤ z.im → 0 ≤ q.im →
      ‖q-semicircleRoot z‖ ≤ C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) →
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N) ≤ finiteOmega d) →
      ∀{ι : Type}[Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y : ((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ : Set (Fin N))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector := logarithmicRadius (c/4) d N/4
      let r := effectiveModelRadius a d N β
      let s := g.admissibleState T labels samples
      let D := hereditaryReferenceRadius d (augmentedObservationDiameter d r)
      let R := hereditaryReferenceRadius d D+2
      ∀S : Set (Tᶜ : Set (Fin N)),S ⊆ s.twoTargetEndpointVertices selector r x y →
      let H := g.omittedAllCompletion (by omega) T labels samples selector S
      H.ComponentFiniteReferenceBudget ∧
      (∀u v,H.graph.dist u v ≤ R) ∧
      ((R:ℝ)+1 ≤ omittedCompletionObservationLogCap d β*Real.log (N:ℝ)) ∧
      (‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*coreConvolutionConstant (finiteOmega d+1)*
        ((R:ℝ)+1) ≤ 1/2) ∧
      (∀u v,‖H.extensionGreen q z u v‖ ≤
        2*finiteExtraReferenceConstant d*physicalTransfer d z^(H.graph.dist u v)) ∧
      (∀u v,‖H.extensionGreen q z u v‖ ≤ 2*finiteExtraReferenceConstant d) := by
  let A := omittedCompletionObservationLogCap d β
  let F : ℝ := 2*(finiteOmega d:ℝ)+7
  have hF : 1 ≤ F := by
    dsimp only [F]
    linarith [Nat.cast_nonneg (α:=ℝ) (finiteOmega d)]
  have hApart : 0 ≤ sourcePartialObservationLogCap d β := by
    unfold sourcePartialObservationLogCap
    exact mul_nonneg (by positivity) (sourceObservationLogCap_nonnegative d hd β hβ.le)
  have hApartobs : sourceObservationLogCap d β ≤ sourcePartialObservationLogCap d β := by
    unfold sourcePartialObservationLogCap
    apply le_mul_of_one_le_left (sourceObservationLogCap_nonnegative d hd β hβ.le)
    linarith [Nat.cast_nonneg (α:=ℝ) (finiteOmega d)]
  have hAobs : sourceObservationLogCap d β ≤ A :=
    hApartobs.trans (le_mul_of_one_le_left hApart hF)
  filter_upwards [eventually_source_partial_geometry a d c β (by omega) hd hc hβ hβc,
    eventually_sourceObservationBounds_of_cap a b d c β B C1 A ha hb hd hc hβ hβc hC1 hAobs]
    with N hgeometry hnum
  intro g o z q hz hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector := logarithmicRadius (c/4) d N/4
  let r := effectiveModelRadius a d N β
  let s := g.admissibleState T labels samples
  let D := hereditaryReferenceRadius d (augmentedObservationDiameter d r)
  let R := hereditaryReferenceRadius d D+2
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  intro S hS
  let H := g.omittedAllCompletion (by omega : 1 ≤ d) T labels samples selector S
  rcases hgeometry g o z hballs labels samples x y S hS with ⟨hclass,hD,hDlog⟩
  have hbudget : H.ComponentFiniteReferenceBudget :=
    g.omittedAllCompletion_component_budget (by omega) T labels samples selector S hclass
  have hdiam : ∀u v,H.graph.dist u v ≤ R :=
    g.omittedAllCompletion_diameter (by omega) T labels samples selector S hclass D hD
  have hRgeom : (R:ℝ)+1 ≤ F*((D:ℝ)+1) := by
    dsimp only [R,hereditaryReferenceRadius,F]
    push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) (finiteOmega d),Nat.cast_nonneg (α:=ℝ) D]
  have hRlog : (R:ℝ)+1 ≤ A*L :=
    hRgeom.trans ((mul_le_mul_of_nonneg_left hDlog (by linarith : 0 ≤ F)).trans_eq (by
      dsimp only [A,omittedCompletionObservationLogCap,F,L]
      ring))
  have num := hnum z hz hfloor
  have hp := hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative hC1)
  have hsmall := (DeficientGraph.weak_localization_feedback_budgets d hd z q hz B
    (C1^2*ε) L A (mul_nonneg (sq_nonneg C1) num.error_nonnegative)
    num.log_one num.log_cap_nonnegative num.error_scaled hp R R hRlog hRlog num.localization_large).1
  have hρ : 0 ≤ physicalTransfer d z := (physicalTransfer_pos d hd z).le
  have hρ1 : physicalTransfer d z ≤ 1 := by nlinarith [physicalTransfer_sq_le_half d hd z]
  have hC : 0 ≤ 2*finiteExtraReferenceConstant d := by
    have hh := finiteExtraReferenceConstant_ge_one d hd
    positivity
  refine ⟨hbudget,hdiam,hRlog,hsmall,?_,?_⟩
  · exact H.componentwise_finite_kernel_decay hd hbudget q z hz hq R hdiam hsmall
  · intro u v
    exact (H.componentwise_finite_kernel_decay hd hbudget q z hz hq R hdiam hsmall u v).trans
      (mul_le_of_le_one_right hC (pow_le_one₀ hρ hρ1))

end RegularGraph
end LocalLaw
