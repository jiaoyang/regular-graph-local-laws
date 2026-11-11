import LocalLaw.SourceFullNewTargetRows
import LocalLaw.SupportedBoundaryContinuity

/-! # Full new-model boundary continuity without a new reference class -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceFullBoundaryContinuityDecidable (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 2500000

def sourceFullContinuityConstant (d : ℕ) (β : ℝ) : ℝ :=
  32*finiteExtraReferenceConstant d^2*(2+2*(sourceFullTargetRowConstant d β*fullModelCouplingCap d)^2)*
    fullRestrictionLogCap d β

theorem sourceFullContinuityConstant_nonnegative (d : ℕ) (β : ℝ) : 0≤sourceFullContinuityConstant d β := by
  have hA := (fullRestrictionLogCap_properties d β).1
  unfold sourceFullContinuityConstant
  positivity

namespace RegularGraph

theorem eventually_source_full_boundary_continuity (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop,∀ (g : RegularGraph N d) (o : Fin N) (z q v : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → 0≤q.im → 0≤v.im →
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z) →
      ‖v-semicircleRoot z‖≤C1*scalarScale (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z) →
      (∀w,graphBallExcess g.graph w (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀{ι : Type}[Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y : Fin N),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector := logarithmicRadius (c/4) d N/4
      let r := effectiveModelRadius a d N β
      let s := g.admissibleState T labels samples
      ∀(_hs : 1≤selector)(S : Set (Fin N)),S⊆s.fullTwoTargetVertices selector r x y →
      let M := (g.labelledResampledGraph T labels samples selector).deficient.restrict S
      ∀u w:S,‖M.extensionGreen q z u w-M.extensionGreen v z u w‖≤
        sourceFullContinuityConstant d β*Real.log (N:ℝ)^(4*a+1)*‖q-v‖ := by
  let A := fullRestrictionLogCap d β
  have hA := (fullRestrictionLogCap_properties d β).1
  have hAobs := (fullRestrictionLogCap_properties d β).2.1
  have hK := sourceFullTargetRowConstant_nonnegative d β
  have hw : 0≤fullModelCouplingCap d := by unfold fullModelCouplingCap; positivity
  filter_upwards [eventually_source_fullRestriction_geometry a b d c β B ha hb hd hc hβ hβc,
    eventually_source_full_new_target_rows a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_formal_edge_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_sourceObservationBounds_of_cap a b d c β B C1 A ha hb hd hc hβ hβc hC1 hAobs]
    with N hgeometry htarget hedge hnum
  intro g o z q v hz hzB hfloor hq hv hpriorQ hpriorV hballs ι _ labels samples x y
  dsimp only
  let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector := logarithmicRadius (c/4) d N/4
  let r := effectiveModelRadius a d N β
  let ell := actualCavityDepth a d N z-1
  let s := g.admissibleState T labels samples
  let R := hereditaryReferenceRadius d (fullTwoTargetDiameter d ell r)
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let K := sourceFullTargetRowConstant d β
  let ww := fullModelCouplingCap d
  let aa := K*L^(2*a-2)
  have num := hnum z hz hfloor
  have hL0 : 0≤L := by linarith [num.log_one]
  have haa : 0≤aa := mul_nonneg hK (pow_nonneg hL0 _)
  intro hs S hSS u w
  let old := g.deficient.restrict S
  let new := (g.labelledResampledGraph T labels samples selector).deficient.restrict S
  let e := s.fullPartialEmbedding selector S hs
  have geo := hgeometry g o z hz hfloor hballs labels samples x y S hSS
  have hscaled : 0≤C1^2*ε := mul_nonneg (sq_nonneg C1) num.error_nonnegative
  have small (q':ℂ) (hp:‖q'-semicircleRoot z‖≤C1*scalarScale (spectralScale z) ε) :
      ‖q'-semicircleRoot z‖*finiteExtraReferenceConstant d*coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2 := by
    have hp' := hp.trans (scalarScale_constant_absorption (spectralScale z) ε C1 (spectralScale_pos hz) num.error_nonnegative hC1)
    exact (DeficientGraph.weak_localization_feedback_budgets d hd z q' hz B (C1^2*ε) L A
      hscaled num.log_one hA num.error_scaled hp' R (4*r+1) geo.2.2.1 num.pair_log num.localization_large).1
  have mass (q':ℂ) (hq':0≤q'.im) (hp:‖q'-semicircleRoot z‖≤C1*scalarScale (spectralScale z) ε) :=
    g.full_model_endpoint_mass hd T labels samples selector hs S q' z hz hq'
      (by simpa only [mul_comm] using (hedge z q' hz hzB hfloor hp).2)
  have rowsQ := htarget g o z q hz hzB hfloor hq hpriorQ hballs labels samples x y hs S hSS u
  have rowsV := htarget g o z v hz hzB hfloor hv hpriorV hballs labels samples x y hs S hSS w
  have hh := old.supported_two_parameter_continuity new hd geo.1 e q v z hz hq hv R geo.2.1
    (small q hpriorQ) (small v hpriorV)
    (g.full_model_difference_supported hd T labels samples selector hs S q z)
    (g.full_model_difference_supported hd T labels samples selector hs S v z)
    aa aa ww ww haa haa hw hw (mass q hq hpriorQ).1 (mass v hv hpriorV).1 u w rowsQ rowsV
  have hp : L^(2*a-2)≤L^(2*a) := pow_le_pow_right₀ num.log_one (by omega)
  have hpw : (aa*ww)^2≤(K*ww)^2*L^(4*a) := by
    have hm : aa*ww≤(K*ww)*L^(2*a) := by
      dsimp only [aa]
      nlinarith only [mul_le_mul_of_nonneg_left hp (mul_nonneg hK hw)]
    have hs := pow_le_pow_left₀ (mul_nonneg haa hw) hm 2
    calc
      _ ≤ ((K*ww)*L^(2*a))^2 := hs
      _ = _ := by rw [mul_pow,←pow_mul,show (2*a)*2=4*a by omega]
  have hcoef : 2+(aa*ww)^2+(aa*ww)^2≤(2+2*(K*ww)^2)*L^(4*a) := by
    have hpone := one_le_pow₀ (n:=4*a) num.log_one
    nlinarith only [hpw,hpone]
  apply hh.trans
  have hbnd : 32*finiteExtraReferenceConstant d^2*(2+(aa*ww)^2+(aa*ww)^2)*((R:ℝ)+1) ≤
      sourceFullContinuityConstant d β*L^(4*a+1) := by
    calc
      _ ≤ 32*finiteExtraReferenceConstant d^2*((2+2*(K*ww)^2)*L^(4*a))*(A*L) := by gcongr; exact geo.2.2.1
      _ = _ := by dsimp only [sourceFullContinuityConstant,K,ww,A]; rw [pow_succ]; ring
  exact mul_le_mul_of_nonneg_right hbnd (norm_nonneg (q-v))

end RegularGraph
end LocalLaw
