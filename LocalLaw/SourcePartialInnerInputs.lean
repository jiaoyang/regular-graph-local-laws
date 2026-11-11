import LocalLaw.PartialInnerCovariance
import LocalLaw.SourceFullPartialInputs
import LocalLaw.SourceFullPartialDeletionGeometry
import LocalLaw.EffectiveLeafWeights

/-! Source-instantiated old L-mask covariance and actual partial restoration. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourcePartialInnerInputsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
set_option maxHeartbeats 4000000
namespace RegularGraph

theorem eventually_source_partial_inner_inputs (a b d:ℕ)(c β B C1:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hC1:1≤C1):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:RegularGraph N d)(o:Fin N)(z q:ℂ),
      0<z.im→‖z‖≤B→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→0≤q.im→
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z)→
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d)→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y:Fin N)(S:Set (Fin N)),
      let ell:=actualCavityDepth a d N z-1
      let T:=graphBallVertices g.graph o ell
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      S⊆s.fullTwoTargetVertices selector r x y→
      let H:=((g.deficient.restrict S).delete (s.retainedInnerSet S)).extensionGreen q z
      let e:=s.partialInnerDeletedEmbedding selector S
      let p:=rationalTreeReference (d-1) q
      let A:=s.partialBoundaryMask selector (s.fullSliceOutside S)
      let core:=H.submatrix (s.partialInnerBoundaryEmbedding selector S) (s.partialInnerBoundaryEmbedding selector S)
      let K:=core⁻¹-partialLMaskRestoration A (s.retainedInnerLabels selector S) q (treeEdgeWeight d)
      (∀i j,‖(H.submatrix e e-s.partialInnerOldCovariance selector S H q p (treeEdgeWeight d)) i j‖≤
        sourceFullCovarianceConstant d β B C1*Real.log (N:ℝ)*graphPaperError a d N (logarithmicRadius β d N) z)∧
      IsUnit K∧(∀i,∑j,‖K⁻¹ i j‖≤4*finiteExtraReferenceConstant d)∧
        (∀j,∑i,‖K⁻¹ i j‖≤4*finiteExtraReferenceConstant d):=by
  let A:=fullRestrictionLogCap d β
  let Count:ℝ:=(d:ℝ)*((d:ℝ)+1)
  have hAcaps:=fullRestrictionLogCap_properties d β
  have hCount:0≤Count:=by dsimp only [Count]; positivity
  filter_upwards [eventually_source_full_partial_deletion_geometry a b d c β B ha hb hd hc hβ hβc,
    eventually_sourceObservationBounds_of_cap a b d c β B C1 A ha hb hd hc hβ hβc hC1 hAcaps.2.1,
    eventually_source_formal_kernel_bounds a b d c β B C1 A ha hb hd hc hβ hβc hC1 hAcaps.1,
    eventually_source_formal_kernel_inverse_bound a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_selected_counts a d ha hd,
    eventually_effective_leaf_count_half_tail a d β Count hd hCount,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc]
    with N hgeometry hnum hformal hinverse hcounts hhalf hradii hcommon
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y S
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let Tm:=s.retainedInnerSet S
  let K:=s.fullSliceOutside S
  let M:=(g.deficient.restrict S).delete Tm
  let U:=(g.deficient.partialInnerAmbient T S).restrict K
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let p:=rationalTreeReference (d-1) q
  let R:=hereditaryReferenceRadius d (fullTwoTargetDiameter d ell r)
  let AM:=s.partialBoundaryMask selector K
  intro hSS
  have geo:=hgeometry g o z hz hfloor hballs labels samples x y S hSS
  have num:=hnum z hz hfloor
  have hf:=hformal z q hz hzB hfloor hprior
  have hi:=hinverse z q hz hzB hfloor hprior
  have hp:p*(q⁻¹-q/((d:ℂ)-1))=1:=by
    have hrel:p⁻¹=q⁻¹-q/((d:ℂ)-1):=by
      rw [hf.2.2.2.1,treeEdgeWeight_sq d hd]
      simp only [mul_one_div]
    rw [←hrel]
    exact mul_inv_cancel₀ hf.2.1
  have hqpow:∀n≤4*r+1,‖q‖^n≤2:=by
    intro n hn
    have hh:(n:ℝ)≤((4*r+1:ℕ):ℝ)+1:=by exact_mod_cast Nat.le_succ_of_le hn
    exact hf.2.2.2.2 n (hh.trans num.pair_log)
  have hsep:2*r+2≤selector:=by
    have hh:=Nat.mul_le_mul_left 2 hcommon
    dsimp only [selector,r]
    omega
  have hbudget:U.ComponentFiniteReferenceBudget:=
    g.deficient.partialInnerAmbient_restrict_budget T S Tm (fun _=>Iff.rfl) geo.1
  let φ:=restrictionDeletionGraphIso g.graph S T Tm (fun _=>Iff.rfl)
  have hR:∀u v,U.graph.dist u v≤R:=by
    intro u v
    have hh:=graphIso_dist φ (φ.symm u) (φ.symm v)
    rw [φ.apply_symm_apply,φ.apply_symm_apply] at hh
    exact hh.le.trans (geo.2.1 _ _)
  have hcov:=g.partial_inner_old_weak_covariance hd T labels samples selector r hsep S K hbudget
    z q p hz hq hf.1 hp B C1 ε L A hzB num hprior R hR geo.2.2.1 hf.2.2.1 hi.2 hqpow
  have hscaled:0≤C1^2*ε:=mul_nonneg (sq_nonneg C1) num.error_nonnegative
  have hprior':=hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative hC1)
  have small:=(DeficientGraph.weak_localization_feedback_budgets d hd z q hz B (C1^2*ε)
    L A hscaled num.log_one hAcaps.1 num.error_scaled hprior' R (4*r+1) geo.2.2.1
    num.pair_log num.localization_large).1
  have hcardNat:Nat.card AM≤Nat.card (BoundaryOrientedEdge g.graph T):=by
    apply Nat.card_le_card_of_injective (fun a:AM=>labels a.val.val)
    intro a b hab
    exact Subtype.ext (Subtype.ext (labels.injective hab))
  have hcard:(Fintype.card AM:ℝ)≤Count*L^(2*a):=by
    have hc:(Fintype.card AM:ℝ)≤(Nat.card (BoundaryOrientedEdge g.graph T):ℝ):=by
      simpa only [Nat.card_eq_fintype_card] using (Nat.cast_le (α:=ℝ).mpr hcardNat)
    have hp:L^(2*a-4)≤L^(2*a):=pow_le_pow_right₀ num.log_one (by omega)
    exact hc.trans (((hcounts g o z).2).trans (mul_le_mul_of_nonneg_left hp hCount))
  have hcap:ε*L^4≤1:=
    (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left num.error_nonnegative
      (show (1:ℝ)≤C1^2 by nlinarith)) (pow_nonneg (by linarith [num.log_one]:0≤L) 4)).trans num.error_scaled
  have hcount:(Fintype.card AM:ℝ)*physicalTransfer d z^selector≤1:=by
    have hh:=hhalf z hz.le hradii.1 hcap (Fintype.card AM) (Nat.cast_nonneg _) hcard
    have hρ:physicalTransfer d z≤1:=by nlinarith [physicalTransfer_sq_le_half d hd z]
    exact (mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (physicalTransfer_pos d hd z).le hρ (by omega:r≤selector)) (Nat.cast_nonneg _)).trans hh
  have restored:=g.partial_inner_boundary_restored_rows hd T labels samples selector S q z hz hq R
    geo.1 geo.2.1 small hcount
  refine ⟨?_,restored⟩
  have transport:=g.partial_inner_covariance_transport T labels samples selector S q p z
  rw [transport.1,transport.2]
  intro i j
  have hh:=hcov i j
  have hcoeff:treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d≤
      |treePatchWeakConstant d B A|+2*finiteExtraReferenceConstant d+1:=by
    linarith [le_abs_self (treePatchWeakConstant d B A)]
  have hbnd:=mul_le_mul_of_nonneg_right hcoeff
    (show 0≤C1^2*L*ε by exact mul_nonneg (mul_nonneg (sq_nonneg C1) (by linarith [num.log_one])) num.error_nonnegative)
  dsimp only [sourceFullCovarianceConstant]
  nlinarith only [hh,hbnd]

end RegularGraph
end LocalLaw
