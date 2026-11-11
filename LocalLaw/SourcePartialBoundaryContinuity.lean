import LocalLaw.ActualPartialBoundaryContinuity
import LocalLaw.ActualSourcePartialEndpointCaps
import LocalLaw.SourcePartialGenericTargetRows
import LocalLaw.SourcePartialGeometry

/-! # Actual first-stage model continuity at every nearby boundary value

Both boundary values obey only a weak physical-root prior. All finite
reference, endpoint, target-weight, support and numerical inputs are derived
from the old graph and the literal nearby-triple counts.
-/

open Filter
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourcePartialBoundaryContinuityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourcePartialContinuityConstant (d : ℕ) (β : ℝ) (Bnear : ℕ) : ℝ :=
  let a:=2*finiteExtraReferenceConstant d*(3*(Bnear:ℝ)+1)
  let C:=sourcePartialEndpointRowCap d
  32*finiteExtraReferenceConstant d^2*(2+2*(a*(1+4*C)*4)^2)*sourcePartialObservationLogCap d β

namespace RegularGraph

theorem eventually_source_partial_boundary_continuity (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in atTop,∀ (g : RegularGraph N d) (o : Fin N) (z q v : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → 0 ≤ q.im → 0 ≤ v.im →
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) →
      ‖v-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) →
      (∀ w,graphBallExcess g.graph w (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y : ((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      ∀ S : Set (Tᶜ:Set (Fin N)), S⊆s.twoTargetEndpointVertices selector r x y →
      let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S
      ∀ (Bnear : ℕ) (u w : S),
      (tripleNearIndices g.graph T (logarithmicRadius (c/4) d N/2) samples u.val).card≤Bnear →
      (tripleNearIndices g.graph T (logarithmicRadius (c/4) d N/2) samples w.val).card≤Bnear →
      ‖M.extensionGreen q z u w-M.extensionGreen v z u w‖≤
        sourcePartialContinuityConstant d β Bnear*Real.log (N:ℝ)*‖q-v‖ := by
  let A:=sourcePartialObservationLogCap d β
  have hAobs : 0≤sourceObservationLogCap d β := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hA : sourceObservationLogCap d β≤A := by
    apply le_mul_of_one_le_left hAobs
    dsimp only [sourcePartialObservationLogCap]
    have hh:=Nat.cast_nonneg (α:=ℝ) (finiteOmega d)
    linarith
  filter_upwards [eventually_source_partial_geometry a d c β (by omega) hd hc hβ hβc,
    eventually_source_partial_generic_target_rows a b d c β B C1 A ha hb hd hc hβ hβc hC1 hA,
    eventually_source_partial_endpoint_caps a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_formal_edge_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_sourceObservationBounds_of_cap a b d c β B C1 A ha hb hd hc hβ hβc hC1 hA]
    with N hgeometry htarget hcaps hedge hnum
  intro g o z q v hz hzB hfloor hq hv hpriorQ hpriorV hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let R:=hereditaryReferenceRadius d (augmentedObservationDiameter d r)
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  intro S hS Bnear u w hnearU hnearW
  have geo:=hgeometry g o z hballs labels samples x y S hS
  have num:=hnum z hz hfloor
  have hscaled : 0≤C1^2*ε := mul_nonneg (sq_nonneg C1) num.error_nonnegative
  have small (q' : ℂ) (hp : ‖q'-semicircleRoot z‖≤C1*scalarScale (spectralScale z) ε) :
      ‖q'-semicircleRoot z‖*finiteExtraReferenceConstant d*
        coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2 := by
    have hp' := hp.trans (scalarScale_constant_absorption (spectralScale z) ε C1
      (spectralScale_pos hz) num.error_nonnegative hC1)
    exact (DeficientGraph.weak_localization_feedback_budgets d hd z q' hz B (C1^2*ε) L A
      hscaled num.log_one num.log_cap_nonnegative num.error_scaled hp'
      R (4*r+1) geo.2.2 num.pair_log num.localization_large).1
  let aa:=2*finiteExtraReferenceConstant d*(3*(Bnear:ℝ)+1)
  let C:=sourcePartialEndpointRowCap d
  have haa : 0≤aa := by
    have hh:=finiteExtraReferenceConstant_ge_one d hd
    dsimp only [aa]
    positivity
  have hC : 0≤C := by
    have hh:=finiteExtraReferenceConstant_ge_one d hd
    dsimp only [C,sourcePartialEndpointRowCap]
    positivity
  have oldQ:=htarget g o z q hz hfloor hq hpriorQ labels samples S geo.1 R geo.2.1 geo.2.2 Bnear u hnearU
  have oldV:=htarget g o z v hz hfloor hv hpriorV labels samples S geo.1 R geo.2.1 geo.2.2 Bnear w hnearW
  have capQ:=hcaps g o z q hz hzB hfloor hq hpriorQ hballs labels samples x y S hS
  have capV:=hcaps g o z v hz hzB hfloor hv hpriorV hballs labels samples x y S hS
  have hh:=g.partial_model_boundary_continuity hd T labels samples selector S geo.1 q v z hz hq hv
    (hedge z q hz hzB hfloor hpriorQ).1 (hedge z v hz hzB hfloor hpriorV).1
    R geo.2.1 (small q hpriorQ) (small v hpriorV) aa aa C C haa haa hC hC u w oldQ oldV capQ.1 capV.1
  apply hh.trans
  have hlen:=mul_le_mul_of_nonneg_left geo.2.2
    (show 0≤32*finiteExtraReferenceConstant d^2*(2+(aa*(1+4*C)*4)^2+(aa*(1+4*C)*4)^2) by positivity)
  have hlen':=mul_le_mul_of_nonneg_right hlen (norm_nonneg (q-v))
  exact hlen'.trans_eq (by dsimp only [sourcePartialContinuityConstant,aa,C,A,L]; ring)

end RegularGraph
end LocalLaw
