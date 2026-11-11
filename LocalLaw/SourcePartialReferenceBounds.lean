import LocalLaw.HereditaryReferenceBounds
import LocalLaw.AugmentedPairCapture
import LocalLaw.OldTwoTargetParameters
import LocalLaw.SourceObservationGeneralCap
import LocalLaw.IndependentRadiusEvents
import LocalLaw.ComponentBallGeometry

/-! # Actual old q-boundary models on switched pair neighborhoods

The new pair vertex set is a literal subset of the old two-target surgery
model. Its OLD inherited graph need not capture old balls. The hereditary
intrinsic diameter theorem supplies exactly the missing perturbation input.
-/

open Filter
noncomputable section
set_option maxHeartbeats 1500000
namespace LocalLaw
local instance sourcePartialReferenceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourcePartialObservationLogCap (d : ℕ) (β : ℝ) : ℝ :=
  (2*(finiteOmega d:ℝ)+5)*sourceObservationLogCap d β

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem subset_finite_class_intrinsic_diameter (g : DeficientGraph V d) (S K : Set V)
    (hKS : K⊆S) (hbudget : (g.restrict S).ComponentFiniteReferenceBudget)
    (D : ℕ) (hD : ∀a b,(g.restrict S).graph.dist a b≤D) (a b : K) :
    (g.restrict K).graph.dist a b≤hereditaryReferenceRadius d D := by
  let U:Set S:={v | v.val∈K}
  let e : (g.restrict K).graph≃g((g.restrict S).restrict U).graph :=
    { toEquiv :=
        { toFun:=fun v=>⟨⟨v.val,hKS v.property⟩,v.property⟩
          invFun:=fun v=>⟨v.val.val,v.property⟩
          left_inv:=fun _=>rfl
          right_inv:=fun _=>rfl }
      map_rel_iff':=Iff.rfl }
  rw [←graphIso_dist e a b]
  exact (g.restrict S).finite_class_restriction_intrinsic_diameter hbudget D hD U (e a) (e b)

end DeficientGraph
namespace RegularGraph

/-- The OLD q=Q(G) reference on every actual switched pair vertex set has
uniform entries and boundary Lipschitz bounds. No ball-capture or post-model
reference-class premise is retained. -/
theorem eventually_old_switched_pair_reference_bounds (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z:ℂ)(Cq badCount:ℕ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z →
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y:((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      let K:=pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
      let M:=(g.deficient.delete T).restrict K
      M.ComponentFiniteReferenceBudget ∧
      (∀u v,M.graph.dist u v≤hereditaryReferenceRadius d (augmentedObservationDiameter d r)) ∧
      (‖g.Q z-semicircleRoot z‖*finiteExtraReferenceConstant d*coreConvolutionConstant (finiteOmega d+1)*
        ((hereditaryReferenceRadius d (augmentedObservationDiameter d r):ℝ)+1)≤1/2) ∧
      (∀u v,‖M.extensionGreen (g.Q z) z u v‖≤
        2*finiteExtraReferenceConstant d*physicalTransfer d z^(M.graph.dist u v)) ∧
      (∀u v,‖M.extensionGreen (g.Q z) z u v‖≤2*finiteExtraReferenceConstant d) ∧
      (∀u v,‖M.extensionGreen (g.Q z) z u v-M.extensionGreen (semicircleRoot z) z u v‖≤
        (16*finiteExtraReferenceConstant d^2*coreConvolutionConstant (finiteOmega d+1))*
          ‖g.Q z-semicircleRoot z‖) := by
  let A:=sourcePartialObservationLogCap d β
  let F:=2*(finiteOmega d:ℝ)+5
  have hF : 1≤F := by
    dsimp only [F]
    have hω:=Nat.cast_nonneg (α:=ℝ) (finiteOmega d)
    linarith
  have hAobs : 0≤sourceObservationLogCap d β := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hA : sourceObservationLogCap d β≤A :=
    le_mul_of_one_le_left hAobs hF
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_old_twoTarget_geometry a d c β hd hc hβ hβc,
    eventually_sourceObservationBounds_of_cap a b d c β B C1 A ha hb hd hc hβ hβc hC1 hA,
    hdepth] with N hgeometry hnum hdepthN
  intro g o z Cq badCount hz hfloor hplus hballs ι _ labels samples x y
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let S:=s.twoTargetEndpointVertices selector r x y
  let K:=pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
  let M:=(g.deficient.delete T).restrict K
  let D:=augmentedObservationDiameter d r
  let R:=hereditaryReferenceRadius d D
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  have hell : ell≤doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepthN).2
  have hgeo:=hgeometry g o ell hell hballs labels samples x y
  have hKS : K⊆S := s.switched_pairBall_subset_old_augmentation selector r x y
  have hbudget : M.ComponentFiniteReferenceBudget :=
    (g.deficient.delete T).subset_restriction_component_budget S K hKS hgeo.1
  have hdiam : ∀u v,M.graph.dist u v≤R :=
    (g.deficient.delete T).subset_finite_class_intrinsic_diameter S K hKS hgeo.1 D hgeo.2.1
  have num:=hnum z hz hfloor
  have hRgeom : (R:ℝ)+1≤F*((D:ℝ)+1) := by
    dsimp only [R,hereditaryReferenceRadius,F]
    push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) (finiteOmega d),Nat.cast_nonneg (α:=ℝ) D]
  have hRlog : (R:ℝ)+1≤A*L := by
    exact hRgeom.trans ((mul_le_mul_of_nonneg_left hgeo.2.2 (by linarith : 0≤F)).trans_eq (by
      dsimp only [A,sourcePartialObservationLogCap,F]
      ring))
  have hprior : ‖g.Q z-semicircleRoot z‖≤C1*scalarScale (spectralScale z) ε := hplus.cavity
  have hprior' := hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative hC1)
  have hscaled : 0≤C1^2*ε := mul_nonneg (sq_nonneg C1) num.error_nonnegative
  have hsmall := (DeficientGraph.weak_localization_feedback_budgets d hd z (g.Q z) hz B
    (C1^2*ε) L A hscaled num.log_one num.log_cap_nonnegative num.error_scaled hprior'
    R R hRlog hRlog num.localization_large).1
  have hρ : 0≤physicalTransfer d z := (physicalTransfer_pos d hd z).le
  have hρ1 : physicalTransfer d z≤1 := by nlinarith [physicalTransfer_sq_le_half d hd z]
  have hC : 0≤2*finiteExtraReferenceConstant d := by
    have hh:=finiteExtraReferenceConstant_ge_one d hd
    positivity
  refine ⟨hbudget,hdiam,hsmall,?_,?_,?_⟩
  · intro u v
    exact M.componentwise_finite_kernel_decay hd hbudget (g.Q z) z hz (g.Q_im_nonnegative z hz)
      R hdiam hsmall u v
  · intro u v
    have he:=M.componentwise_finite_kernel_decay hd hbudget (g.Q z) z hz (g.Q_im_nonnegative z hz)
      R hdiam hsmall u v
    exact he.trans (mul_le_of_le_one_right hC (pow_le_one₀ hρ hρ1))
  · intro u v
    exact M.componentwise_finite_uniform_lipschitz hd hbudget z (g.Q z) (semicircleRoot z) hz
      (g.Q_im_nonnegative z hz) (semicircleRoot_im_pos hz).le R hdiam hsmall (by simp) u v

end RegularGraph
end LocalLaw
