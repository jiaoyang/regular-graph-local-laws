import LocalLaw.SourceFullNewTargetRows
import LocalLaw.TwoTargetOldEntryRows

/-! Actual full switched model rows on endpoints together with two targets. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceFullAugmentedRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 3000000

def sourceFullAugmentedRowConstant (d : ℕ) (β : ℝ) : ℝ :=
  sourceFullEndpointRowConstant d β+3*sourceFullTargetRowConstant d β+
    2*(2*finiteExtraReferenceConstant d+sourceFullTargetRowConstant d β*fullModelCouplingCap d*(2*finiteExtraReferenceConstant d))

theorem sourceFullAugmentedRowConstant_nonnegative (d : ℕ) (β : ℝ) (hd : 3≤d) :
    0≤sourceFullAugmentedRowConstant d β := by
  have hE:=sourceFullEndpointRowConstant_nonnegative d β
  have hT:=sourceFullTargetRowConstant_nonnegative d β
  have hC:=finiteExtraReferenceConstant_ge_one d hd
  unfold sourceFullAugmentedRowConstant fullModelCouplingCap
  positivity

namespace RegularGraph

theorem eventually_source_full_augmented_rows (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop,∀(g : RegularGraph N d)(o : Fin N)(z q : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → 0≤q.im →
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) →
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀{ι : Type}[Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y : Fin N),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      ∀(hs : 1≤selector)(S : Set (Fin N)),S⊆s.fullTwoTargetVertices selector r x y →
      let e:=s.fullPartialEmbedding selector S hs
      let G:=((g.labelledResampledGraph T labels samples selector).deficient.restrict S).extensionGreen q z
      ∀u v:S,∀i:twoTargetIndexSet e u v,
        (∑j:twoTargetIndexSet e u v,‖G i.val j.val‖)≤sourceFullAugmentedRowConstant d β*Real.log (N:ℝ)^(2*a-2) := by
  let A:=fullRestrictionLogCap d β
  let K:=2*finiteExtraReferenceConstant d
  let E:=sourceFullEndpointRowConstant d β
  let V:=sourceFullTargetRowConstant d β
  let w:=fullModelCouplingCap d
  have hA:0≤A:=(fullRestrictionLogCap_properties d β).1
  have hAobs:sourceObservationLogCap d β≤A:=(fullRestrictionLogCap_properties d β).2.1
  have hK:0≤K:=by have h:=finiteExtraReferenceConstant_ge_one d hd; dsimp only [K]; positivity
  have hE:=sourceFullEndpointRowConstant_nonnegative d β
  have hV:=sourceFullTargetRowConstant_nonnegative d β
  have hw:0≤w:=by dsimp only [w,fullModelCouplingCap]; positivity
  filter_upwards [eventually_source_full_new_target_rows a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_full_partial_endpoint_caps a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_fullRestriction_geometry a b d c β B ha hb hd hc hβ hβc,
    eventually_sourceObservationBounds_of_cap a b d c β B C1 A ha hb hd hc hβ hβc hC1 hAobs,
    eventually_source_formal_edge_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1]
    with N htargets hendpoints hgeo hnum hedge
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let R:=hereditaryReferenceRadius d (fullTwoTargetDiameter d ell r)
  have num:=hnum z hz hfloor
  have hL:0≤L:=by linarith [num.log_one]
  have hpow:1≤L^(2*a-2):=one_le_pow₀ num.log_one
  have hαq:‖q*treeEdgeWeight d‖≤1:=by simpa only [mul_comm] using (hedge z q hz hzB hfloor hprior).2
  have hprior':=hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1 (spectralScale_pos hz) num.error_nonnegative hC1)
  intro hs S hSS u v
  let old:=g.deficient.restrict S
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.restrict S
  let e:=s.fullPartialEmbedding selector S hs
  have geo:=hgeo g o z hz hfloor hballs labels samples x y S hSS
  have hsmall:=(DeficientGraph.weak_localization_feedback_budgets d hd z q hz B (C1^2*ε) L A
    (mul_nonneg (sq_nonneg C1) num.error_nonnegative) num.log_one hA num.error_scaled hprior'
    R (4*r+1) geo.2.2.1 num.pair_log num.localization_large).1
  have hold:∀i j,‖old.extensionGreen q z i j‖≤K:=by
    intro i j
    exact (old.componentwise_finite_kernel_decay hd geo.1 q z hz hq R geo.2.1 hsmall i j).trans
      (mul_le_of_le_one_right hK (pow_le_one₀ (physicalTransfer_pos d hd z).le (by nlinarith [physicalTransfer_sq_le_half d hd z])))
  have he:=hendpoints g o z q hz hzB hfloor hq hprior hballs labels samples x y hs S hSS
  have ht:=htargets g o z q hz hzB hfloor hq hprior hballs labels samples x y hs S hSS
  have he':∀i,∑j,‖new.extensionGreen q z (e i) (e j)‖≤E*L^(2*a-2):=by
    intro i
    refine (he.1 i).trans (mul_le_mul_of_nonneg_left ?_ hE)
    exact pow_le_pow_right₀ num.log_one (by omega)
  have hh:=inverse_supported_two_target_rows_of_old_entries
    (old.extensionMatrix q z) (new.extensionMatrix q z)
    (old.extensionMatrix_isUnit hd q z hz hq) (new.extensionMatrix_isUnit hd q z hz hq)
    e (g.full_model_difference_supported hd T labels samples selector hs S q z) u v K
    (E*L^(2*a-2)) (V*L^(2*a-2)) w hK (by positivity) (by positivity) hw
    (new.extensionGreen_isSymm q z) hold he' (fun t _=>ht t)
    (g.full_model_endpoint_mass hd T labels samples selector hs S q z hz hq hαq).1
  intro i
  refine (hh i).trans ?_
  dsimp only [sourceFullAugmentedRowConstant,K,E,V,w]
  have hconstant:2*(2*finiteExtraReferenceConstant d)≤2*(2*finiteExtraReferenceConstant d)*L^(2*a-2):=
    by
      simpa only [mul_one] using (mul_le_mul_of_nonneg_left hpow
        (show 0≤2*(2*finiteExtraReferenceConstant d) by
          have hC:=finiteExtraReferenceConstant_ge_one d hd
          positivity))
  nlinarith only [hconstant]

end RegularGraph
end LocalLaw
