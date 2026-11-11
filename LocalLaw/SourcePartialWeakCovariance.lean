import LocalLaw.PartialEndpointWeakCovariance
import LocalLaw.SourceFormalKernelInverse
import LocalLaw.SourcePartialReferenceBounds

/-! # Actual partial qOLD covariance on both common and switched pair sets

The finite theorem is instantiated for every subset of the OLD augmented
model. Thus both the old common surgery model and the actual NEW pair vertex
set have the required qOLD covariance, at the strong logarithmic-error scale.
-/

open Filter
noncomputable section
set_option maxHeartbeats 2000000
namespace LocalLaw
local instance sourcePartialWeakCovarianceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourcePartialCovarianceConstant (d : ℕ) (β B C1 : ℝ) : ℝ :=
  (treePatchWeakConstant d B (sourcePartialObservationLogCap d β)+2*finiteExtraReferenceConstant d)*C1^2

namespace RegularGraph
variable {N d : ℕ} {ι : Type}

def oldPartialQCovarianceBound (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))(z:ℂ)(σ:ℝ) : Prop :=
  let s:=g.admissibleState T labels samples
  let G:=((g.deficient.delete T).restrict S).extensionGreen (g.Q z) z
  let P:=s.partialOldCovariance selector S G (g.Q z) (rationalTreeReference (d-1) (g.Q z)) (treeEdgeWeight d)
  ∀i j,‖(G.submatrix (s.partialEndpointEmbedding selector S)
    (s.partialEndpointEmbedding selector S)-P) i j‖≤σ

theorem eventually_source_partial_q_covariance_subsets (a b d : ℕ)(c β B C1:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hC1:1≤C1) :
    ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z:ℂ)(Cq badCount:ℕ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
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
      ∀S:Set (Tᶜ:Set (Fin N)), S⊆s.twoTargetEndpointVertices selector r x y →
      g.oldPartialQCovarianceBound T labels samples selector S z
        (sourcePartialCovarianceConstant d β B C1*Real.log (N:ℝ)*
          graphPaperError a d N (logarithmicRadius β d N) z) := by
  let Acap:=sourcePartialObservationLogCap d β
  let F:=2*(finiteOmega d:ℝ)+5
  have hF:1≤F := by dsimp only [F]; have hh:=Nat.cast_nonneg (α:=ℝ) (finiteOmega d); linarith
  have hAobs:0≤sourceObservationLogCap d β := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hAcap:sourceObservationLogCap d β≤Acap := le_mul_of_one_le_left hAobs hF
  have hAcap0:0≤Acap := hAobs.trans hAcap
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_old_twoTarget_geometry a d c β hd hc hβ hβc,
    eventually_sourceObservationBounds_of_cap a b d c β B C1 Acap ha hb hd hc hβ hβc hC1 hAcap,
    eventually_source_formal_kernel_bounds a b d c β B C1 Acap ha hb hd hc hβ hβc hC1 hAcap0,
    eventually_source_formal_kernel_inverse_bound a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,hdepth]
    with N hgeometry hnum hformal hinverse hcommon hdepthN
  intro g o z Cq badCount hz hzB hfloor hplus hballs ι _ labels samples x y
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let Saug:=s.twoTargetEndpointVertices selector r x y
  let D:=augmentedObservationDiameter d r
  let R:=hereditaryReferenceRadius d D
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let q:=g.Q z
  let p:=rationalTreeReference (d-1) q
  have hell:ell≤doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepthN).2
  have hgeo:=hgeometry g o ell hell hballs labels samples x y
  have num:=hnum z hz hfloor
  have hprior:‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z) ε := hplus.cavity
  have hf:=hformal z q hz hzB hfloor hprior
  have hi:=hinverse z q hz hzB hfloor hprior
  have hpnorm:‖p‖≤4 := hf.2.2.1
  have hp : p*(q⁻¹-q/((d:ℂ)-1))=1 := by
    have hrel:p⁻¹=q⁻¹-q/((d:ℂ)-1) := by
      rw [hf.2.2.2.1,treeEdgeWeight_sq d hd]
      simp only [mul_one_div]
    rw [←hrel]
    exact mul_inv_cancel₀ hf.2.1
  have hqpow:∀n≤4*r+1,‖q‖^n≤2 := by
    intro n hn
    have hn' : (n:ℝ)≤((4*r+1:ℕ):ℝ)+1 := by exact_mod_cast Nat.le_succ_of_le hn
    exact hf.2.2.2.2 n (hn'.trans num.pair_log)
  have hsep:2*r+2≤selector := by
    have hh:=Nat.mul_le_mul_left 2 hcommon
    dsimp only [r,selector]
    omega
  have hRgeom:(R:ℝ)+1≤F*((D:ℝ)+1) := by
    dsimp only [R,hereditaryReferenceRadius,F]
    push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) (finiteOmega d),Nat.cast_nonneg (α:=ℝ) D]
  have hRlog:(R:ℝ)+1≤Acap*L :=
    hRgeom.trans ((mul_le_mul_of_nonneg_left hgeo.2.2 (by linarith : 0≤F)).trans_eq (by
      dsimp only [Acap,sourcePartialObservationLogCap,F]
      ring))
  intro S hSS
  have hbudget:= (g.deficient.delete T).subset_restriction_component_budget Saug S hSS hgeo.1
  have hdiam:∀u v,((g.deficient.delete T).restrict S).graph.dist u v≤R :=
    (g.deficient.delete T).subset_finite_class_intrinsic_diameter Saug S hSS hgeo.1 D hgeo.2.1
  have hcov:=g.partial_endpoint_old_weak_covariance hd T labels samples selector r hsep S hbudget
    z q p hz (g.Q_im_nonnegative z hz) hf.1 hp B C1 ε L Acap hzB num hprior R hdiam hRlog hpnorm hi.2 hqpow
  dsimp only [oldPartialQCovarianceBound]
  intro i j
  exact hcov i j

end RegularGraph
end LocalLaw
