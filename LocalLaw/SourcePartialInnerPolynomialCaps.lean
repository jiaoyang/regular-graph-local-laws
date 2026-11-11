import LocalLaw.SourcePartialInnerEndpointCaps
import LocalLaw.PartialInnerCouplingMass
import LocalLaw.TwoTargetOldEntryRows

/-! Polynomial logarithmic caps on the entire NEW partial-T deleted kernel.
The proof uses true old reference bounds and finite new endpoint rows. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourcePartialInnerPolynomialCapsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
set_option maxHeartbeats 3000000

def partialInnerOldRowCoefficient (d:ℕ)(β:ℝ):ℝ:=
  (3*(d:ℝ)*((d:ℝ)+1))*(8*finiteExtraReferenceConstant d^2*fullRestrictionLogCap d β)+1

def partialInnerGlobalCoefficient (d:ℕ)(β:ℝ):ℝ:=
  2*finiteExtraReferenceConstant d+
    partialInnerOldRowCoefficient d β*(1+4*sourcePartialEndpointRowCap d)*4*(2*finiteExtraReferenceConstant d)

namespace RegularGraph

theorem eventually_source_partial_inner_global_caps (a b d:ℕ)(c β B C1:ℝ)
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
      let H:=(((g.labelledResampledGraph T labels samples selector).deficient.restrict S).delete
        (s.retainedInnerSet S)).extensionGreen q z
      ∀u v,‖H u v‖≤partialInnerGlobalCoefficient d β*Real.log (N:ℝ)^(a-1):=by
  let A:=fullRestrictionLogCap d β
  let U:ℝ:=3*(d:ℝ)*((d:ℝ)+1)
  let M:=partialInnerOldRowCoefficient d β
  let C:=sourcePartialEndpointRowCap d
  let E:=2*finiteExtraReferenceConstant d
  have hA:0≤A:=(fullRestrictionLogCap_properties d β).1
  have hU:0≤U:=by dsimp only [U];positivity
  have hE:0≤E:=by have h:=finiteExtraReferenceConstant_ge_one d hd;dsimp only [E];positivity
  have hC:0≤C:=by have h:=finiteExtraReferenceConstant_ge_one d hd;unfold C sourcePartialEndpointRowCap;positivity
  have hM:0≤M:=by unfold M partialInnerOldRowCoefficient;positivity
  filter_upwards [eventually_source_partial_inner_endpoint_caps a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_full_partial_deletion_geometry a b d c β B ha hb hd hc hβ hβc,
    eventually_sourceObservationBounds_of_cap a b d c β B C1 A ha hb hd hc hβ hβc hC1 (fullRestrictionLogCap_properties d β).2.1,
    eventually_source_formal_edge_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_selected_counts a d ha hd] with N hcaps hgeo hnum hedge hcounts
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y S
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let Tm:=s.retainedInnerSet S
  let old:=(g.deficient.restrict S).delete Tm
  let new:=((g.labelledResampledGraph T labels samples selector).deficient.restrict S).delete Tm
  let e:=s.partialInnerDeletedEmbedding selector S
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let R:=hereditaryReferenceRadius d (fullTwoTargetDiameter d ell r)
  intro hSS
  have geo:=hgeo g o z hz hfloor hballs labels samples x y S hSS
  have num:=hnum z hz hfloor
  have hn:=hcaps g o z q hz hzB hfloor hq hprior hballs labels samples x y S hSS
  have hq2:‖q‖≤2:=(hedge z q hz hzB hfloor hprior).1
  have hscaled:0≤C1^2*ε:=mul_nonneg (sq_nonneg C1) num.error_nonnegative
  have hprior':=hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1 (spectralScale_pos hz) num.error_nonnegative hC1)
  have small:=(DeficientGraph.weak_localization_feedback_budgets d hd z q hz B (C1^2*ε) L A hscaled
    num.log_one hA num.error_scaled hprior' R (4*r+1) geo.2.2.1 num.pair_log num.localization_large).1
  have hαsq:‖treeEdgeWeight d‖^2≤1:=by
    rw [treeEdgeWeight_norm_sq d hd]
    have hh:(3:ℝ)≤d:=Nat.cast_le.mpr hd
    exact (div_le_one (by linarith)).mpr (by linarith)
  have hα:‖treeEdgeWeight d‖≤1:=by nlinarith [norm_nonneg (treeEdgeWeight d)]
  have hw:2*‖treeEdgeWeight d‖+‖q‖*‖treeEdgeWeight d‖^2≤4:=by
    nlinarith [mul_le_mul hq2 hαsq (sq_nonneg ‖treeEdgeWeight d‖) (by norm_num:(0:ℝ)≤2)]
  have hmass:∀i,∑j,‖(new.extensionMatrix q z-old.extensionMatrix q z) (e i) (e j)‖≤4:=
    fun i=>(g.partial_inner_coupling_mass hd T labels samples selector S q z i).trans hw
  have hcount:(Fintype.card (s.PartialEndpointIndex selector (s.fullSliceOutside S)):ℝ)≤U*L^(2*a-4):=by
    have hnat:Nat.card (s.PartialEndpointIndex selector (s.fullSliceOutside S))≤3*Nat.card (BoundaryOrientedEdge g.graph T):=
      (s.partialEndpoint_card_le_roots selector (s.fullSliceOutside S)).trans (s.endpointModelRoots_card selector)
    have hh:(Fintype.card (s.PartialEndpointIndex selector (s.fullSliceOutside S)):ℝ)≤3*(Nat.card (BoundaryOrientedEdge g.graph T):ℝ):=by
      simpa only [Nat.card_eq_fintype_card,Nat.cast_mul,Nat.cast_ofNat] using (Nat.cast_le (α:=ℝ).mpr hnat)
    exact hh.trans ((mul_le_mul_of_nonneg_left (hcounts g o z).2 (by norm_num:(0:ℝ)≤3)).trans_eq (by dsimp only [U];ring))
  have holdEntry:∀u v,‖old.extensionGreen q z u v‖≤E:=by
    intro u v
    exact (old.componentwise_finite_kernel_decay hd geo.1 q z hz hq R geo.2.1 small u v).trans
      (mul_le_of_le_one_right hE (pow_le_one₀ (physicalTransfer_pos d hd z).le
        (by nlinarith [physicalTransfer_sq_le_half d hd z])))
  have holdTarget (u):∑i,‖old.extensionGreen q z u (e i)‖≤M*L^(a-1):=by
    have hsq:=old.componentwise_extensionGreen_square_sum hd geo.1 z q hz hq R geo.2.1 small u
    have hsub:(∑i,‖old.extensionGreen q z u (e i)‖^2)≤∑v,‖old.extensionGreen q z u v‖^2:=by
      calc
        _=∑v∈Finset.univ.image e,‖old.extensionGreen q z u v‖^2:=(Finset.sum_image (fun _ _ _ _ h=>e.injective h)).symm
        _≤_:=Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=>sq_nonneg _)
    have hs:(∑i,‖old.extensionGreen q z u (e i)‖^2)≤(8*finiteExtraReferenceConstant d^2*A)*L:=by
      exact (hsub.trans hsq).trans ((mul_le_mul_of_nonneg_left geo.2.2.1 (by positivity)).trans_eq (by ring))
    exact full_mask_log_row_bound _ a L U (8*finiteExtraReferenceConstant d^2*A) (by omega) num.log_one hU
      (by positivity) hcount hs
  have hnewTarget (u):∑i,‖new.extensionGreen q z u (e i)‖≤(M*L^(a-1))*(1+4*C):=
    inverse_supported_endpoint_row_sum (old.extensionMatrix q z) (new.extensionMatrix q z)
      (old.extensionMatrix_isUnit hd q z hz hq) (new.extensionMatrix_isUnit hd q z hz hq) e
      (g.partial_inner_model_difference_supported hd T labels samples selector S q z) _ C 4
      (by positivity) hC (by norm_num) u (holdTarget u) hn.1 hmass
  have hp:1≤L^(a-1):=one_le_pow₀ num.log_one
  intro u v
  have hh:=inverse_supported_entry_of_new_row (old.extensionMatrix q z) (new.extensionMatrix q z)
    (old.extensionMatrix_isUnit hd q z hz hq) (new.extensionMatrix_isUnit hd q z hz hq) e
    (g.partial_inner_model_difference_supported hd T labels samples selector S q z) E
    ((M*L^(a-1))*(1+4*C)) 4 hE (by positivity) (by norm_num) u v
    (holdEntry u v) (fun i=>holdEntry (e i) v) (hnewTarget u) hmass
  refine hh.trans ?_
  change E+((M*L^(a-1))*(1+4*C))*4*E≤partialInnerGlobalCoefficient d β*L^(a-1)
  have hEp:E≤E*L^(a-1):=by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hE
  change E+(M*L^(a-1)*(1+4*C))*4*E≤(E+M*(1+4*C)*4*E)*L^(a-1)
  calc
    _≤E*L^(a-1)+(M*L^(a-1)*(1+4*C))*4*E:=add_le_add_right hEp _
    _=_:=by ring

end RegularGraph
end LocalLaw
