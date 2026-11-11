import LocalLaw.SmallSampleKernelDecay
import LocalLaw.SourceLocalSelectedColumns
import LocalLaw.SelectedFirstFullPairOccupancy
import LocalLaw.FullOutsideAugmentation

/-! # Entire upper deleted-T reference on the full switched pair

All inputs come from the original graph and its weak boundary value.
The restored upper model is not assumed to satisfy a new pair budget.
The exterior slice identity and the at-most-two sampled-vertex theorem
make the proved omitted-core estimate sufficient for full kernel decay.
-/
open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
namespace LocalLaw
local instance sourceFullUpperKernelDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceFullUpperKernelCap (d:ℕ)(β B C1:ℝ):ℝ:=
  smallSampleKernelCoefficient d (sourceLocalSelectedCoreCap d β B C1)
    (sourcePartialEndpointRowCap d) (sourcePartialFirstOffDiagonalConstant d β B C1)

namespace RegularGraph

theorem eventually_source_full_upper_kernel_decay (a b d:ℕ)(c β Bcap C1:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hC1:1≤C1):
    ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z q:ℂ),
      0<z.im→‖z‖≤Bcap→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→0≤q.im→
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z)→
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d)→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y:((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      let S:=s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x.val y.val r)
      let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S
      ∀(u v:S)(h:ℕ),((2*h+2:ℕ):ℕ∞)≤(s.fullResample selector).graph.edist u.val.val v.val.val→
      ‖M.extensionGreen q z u v‖≤sourceFullUpperKernelCap d β Bcap C1*Real.log (N:ℝ)^2*physicalTransfer d z^h+
        sourceFullUpperKernelCap d β Bcap C1*Real.log (N:ℝ)^3*
          graphPaperError a d N (logarithmicRadius β d N) z:=by
  let K:=sourceLocalSelectedCoreCap d β Bcap C1
  let C:=sourcePartialEndpointRowCap d
  let D:=sourcePartialFirstOffDiagonalConstant d β Bcap C1
  have hK:0≤K:=by dsimp only[K,sourceLocalSelectedCoreCap];positivity
  have hC:0≤C:=by
    have he:=finiteExtraReferenceConstant_ge_one d hd
    dsimp only[C,sourcePartialEndpointRowCap]
    positivity
  have hD:0≤D:=by
    have he:=finiteExtraReferenceConstant_ge_one d hd
    dsimp only[D,sourcePartialFirstOffDiagonalConstant]
    positivity
  filter_upwards [eventually_source_omitted_restored_decay a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_partial_endpoint_caps a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_partial_first_offdiagonal a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_sourceObservationBounds a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc]
    with N hcore hcaps hoff hnum hmargin
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let S:=s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x.val y.val r)
  let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S
  let Bi:=s.partialFirstRemovedSet selector S
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  have num:=hnum z hz hfloor
  have hL:0≤L:=by linarith[num.log_one]
  have hε:0≤ε:=num.error_nonnegative
  have hεone:ε≤1:=by
    calc
      _≤C1^2*ε:=le_mul_of_one_le_left hε (one_le_pow₀ hC1)
      _≤(C1^2*ε)*L^4:=le_mul_of_one_le_right (by positivity) (one_le_pow₀ num.log_one)
      _≤1:=num.error_scaled
  have hsep:2*r≤selector:=by dsimp only[r,selector];omega
  have hcard:Nat.card Bi≤2:=s.partialFirstRemovedSet_new_full_pair_card selector r hsep x.val y.val
  have hS:S⊆s.twoTargetEndpointVertices selector r x y:=s.switched_full_pair_outside_subset selector r x y
  have hi:=hcore g o z q hz hzB hfloor hq hprior hballs labels samples x y S hS
  have hn:=g.native_omitted_core_decay T labels samples selector S q z Bcap C1
    (omittedCompletionObservationLogCap d β) L ε hL hε hi
  have hee:=hcaps g o z q hz hzB hfloor hq hprior hballs labels samples x y S hS
  have hBB:∀u:Bi,∑v:Bi,‖M.extensionGreen q z u.val v.val‖≤C:=
    s.partialFirst_removed_rows_of_endpoint_rows selector S (M.extensionGreen q z) C hee.1
  have hOff:∀u v:Bi,u≠v→‖M.extensionGreen q z u.val v.val‖≤D*L*ε:=
    s.partialFirst_removed_offdiagonal_of_indexed selector S (M.extensionGreen q z) (D*L*ε)
      (hoff g o z q hz hzB hfloor hq hprior hballs labels samples x y S hS)
  intro u v h hfar
  have hmetric:(s.fullResample selector).graph.edist u.val.val v.val.val≤M.graph.edist u v:=
    (ambient_edist_le_induced_edist (s.fullResample selector).graph Tᶜ u.val v.val).trans
      (ambient_edist_le_induced_edist (outsideGraph (s.fullResample selector).graph T) S u v)
  exact M.small_sample_entire_kernel_decay hd Bi q z hz hq K L ε C D hK num.log_one hε hεone hC hD
    hcard hn hBB hOff u v h (hfar.trans hmetric)

end RegularGraph
end LocalLaw
