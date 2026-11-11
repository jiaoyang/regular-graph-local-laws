import LocalLaw.SourcePartialWeakCovariance
import LocalLaw.RestoredBoundaryQRows
import LocalLaw.EndpointFarTailParameters

/-! # Actual partial-boundary inputs for every nearby parameter q

The graph supplies only its original strong radius budget. All scalar,
covariance, restored-boundary and finite-size inputs follow from the weak
prior at the arbitrary q, so both pre- and post-switch Q can be used.
-/
open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance sourcePartialGenericInputsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_partial_generic_inputs (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in atTop,∀ (g : RegularGraph N d) (o : Fin N) (z q : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → 0 ≤ q.im →
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) →
      (∀ v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y : ((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      let p:=rationalTreeReference (d-1) q
      ∀ S : Set (Tᶜ:Set (Fin N)), S⊆s.twoTargetEndpointVertices selector r x y →
      let G:=((g.deficient.delete T).restrict S).extensionGreen q z
      let P:=s.partialOldCovariance selector S G q p (treeEdgeWeight d)
      let A:=G.submatrix (s.partialBoundaryEmbedding selector S) (s.partialBoundaryEmbedding selector S)
      let K:=A⁻¹-Matrix.diagonal (fun _ : s.partialBoundaryMask selector S=>q*treeEdgeWeight d^2)
      (∀ i j,‖(G.submatrix (s.partialEndpointEmbedding selector S)
        (s.partialEndpointEmbedding selector S)-P) i j‖≤
        sourcePartialCovarianceConstant d β B C1*Real.log (N:ℝ)*
          graphPaperError a d N (logarithmicRadius β d N) z) ∧
      IsUnit K ∧ (∀ i,∑ j,‖K⁻¹ i j‖≤4*finiteExtraReferenceConstant d) ∧
        (∀ j,∑ i,‖K⁻¹ i j‖≤4*finiteExtraReferenceConstant d) := by
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
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,hdepth,
    eventually_endpoint_far_tail_small a d 1 ha hd (by norm_num),
    eventually_source_radius_hierarchy a d c β hd hc hβ hβc]
    with N hgeometry hnum hformal hinverse hcommon hdepthN htail hradii
  intro g o z q hz hzB hfloor hqim hprior hballs ι _ labels samples x y
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
  let p:=rationalTreeReference (d-1) q
  have hell:ell≤doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepthN).2
  have hgeo:=hgeometry g o ell hell hballs labels samples x y
  have num:=hnum z hz hfloor
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
    z q p hz hqim hf.1 hp B C1 ε L Acap hzB num hprior R hdiam hRlog hpnorm hi.2 hqpow
  have hscaled : 0≤C1^2*ε := mul_nonneg (sq_nonneg C1) num.error_nonnegative
  have hprior' := hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative hC1)
  have hsmall := (DeficientGraph.weak_localization_feedback_budgets d hd z q hz B (C1^2*ε) L Acap
    hscaled num.log_one num.log_cap_nonnegative num.error_scaled hprior'
    R (4*r+1) hRlog num.pair_log num.localization_large).1
  have ht:=htail g o ell hell labels samples selector (logarithmicRadius β d N) selector hradii.2.2.1 z hz.le
  simp only [one_mul] at ht
  have hC1sq : 1≤C1^2 := by nlinarith
  have hεone : ε≤1 := by
    exact ((le_mul_of_one_le_left num.error_nonnegative hC1sq).trans
      (le_mul_of_one_le_right hscaled (one_le_pow₀ num.log_one))).trans num.error_scaled
  have htailOne:(Nat.card (s.endpointModelRoots selector):ℝ)*physicalTransfer d z^selector≤1 :=
    ht.trans ((div_le_self num.error_nonnegative (one_le_pow₀ num.log_one)).trans hεone)
  have hcard:=Nat.cast_le (α:=ℝ).mpr (s.partialBoundaryMask_card_le_roots selector S)
  have hmask:(Fintype.card (s.partialBoundaryMask selector S):ℝ)*physicalTransfer d z^selector≤1 := by
    have hh:=(mul_le_mul_of_nonneg_right hcard (pow_nonneg (physicalTransfer_pos d hd z).le _)).trans htailOne
    simpa only [Nat.card_eq_fintype_card] using hh
  refine ⟨?_,g.partial_restored_boundary_q_rows hd T labels samples selector S hbudget z q hz hqim R hdiam hsmall hmask⟩
  intro i j
  simpa only [sourcePartialCovarianceConstant,Acap,L,ε] using hcov i j

end RegularGraph
end LocalLaw
