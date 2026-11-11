import SpectralConsequences.BoundaryProfileQuadratic
import SpectralConsequences.SwitchedTreeBoundaryBlock
import LocalLaw.SourceCavityMinorProfile
import LocalLaw.CavityMinorRowIdentity

/-! The actual neighbor-deleted Schur remainder stays quadratic before averaging. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceCavityQuadraticRemainderDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def cavityRootQuadraticConstant (d:ℕ) (β C1:ℝ):ℝ:=
  boundaryQuadraticConstant ((d:ℝ)*((d:ℝ)+1))
    (2*finiteExtraReferenceConstant d*((d:ℝ)+1))
    (8*(d:ℝ)*finiteExtraReferenceConstant d^2*sourceObservationLogCap d β)
    (sourceEndpointErrorConstant d C1+1)

namespace RegularGraph

theorem eventually_source_cavity_quadratic_remainder (a b d:ℕ) (c β B C1:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c)
    (hβ:0<β) (hβc:β≤c/32) (hC1:1≤C1):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀Cq badCount:ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z→
      (graphBall g.graph o (logarithmicRadius (c/4) d N)).IsTree→
      let ell:=actualCavityDepth a d N z-1
      let T:=graphBallVertices g.graph o ell
      ∃hell:2≤ell,∀(j:T)(hjo:g.graph.Adj j.val o),
      ∀{ι:Type}[Fintype ι](labels:ι≃BoundaryOrientedEdge g.graph T)
      (samples:LocalSamplingFiber g.graph T),
      let selector:=logarithmicRadius (c/4) d N/4
      let R:=(g.labelledResampledGraph T labels samples selector).retainedPhysicalMinor T j z
      let P:=((g.deficient.restrict T).deleteVertex j).extensionGreen (g.Q z) z
      let root:=g.truncatedCavityRoot o ell j hjo
      let l:=fun i=>g.truncatedCavityBoundaryInner o ell hell j hjo (labels i)
      let D:=g.sourceTruncatedBoundaryDefect T labels samples selector (g.Q z) z
      ∀v,‖(treeEdgeWeight d)^2*(∑i,∑k,(R root (l i)-P root (l i))*D i k*P (l k) v)‖≤
        cavityRootQuadraticConstant d β C1*Real.log (N:ℝ)^(6*a+7)*
          (graphPaperError a d N (logarithmicRadius β d N) z)^2:=by
  let U:ℝ:=(d:ℝ)*((d:ℝ)+1)
  let M0:ℝ:=2*finiteExtraReferenceConstant d*((d:ℝ)+1)
  let W0:ℝ:=8*(d:ℝ)*finiteExtraReferenceConstant d^2*sourceObservationLogCap d β
  let D0:ℝ:=sourceEndpointErrorConstant d C1+1
  have hC:0≤finiteExtraReferenceConstant d:=(by norm_num:(0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have hA:=sourceObservationLogCap_nonnegative d hd β hβ.le
  have hU:0≤U:=by dsimp only [U];positivity
  have hM:0≤M0:=by dsimp only [M0];positivity
  have hW:0≤W0:=by dsimp only [W0];positivity
  have hD0:0≤D0:=by
    dsimp only [D0,sourceEndpointErrorConstant]
    have hC1':0≤C1:=by linarith
    positivity
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [LocalLaw.RegularGraph.eventually_source_cavity_minor_profile a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_switched_tree_boundary_cap a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_paperError_small a b d β ha hb hd hβ,eventually_log_ge_nat 1,
    eventually_log_ge_nat (2*(U*(U+W0+1)*D0)),Filter.eventually_ge_atTop 1,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,hdepth]
    with N hprofile hcap hsmall hlog hlarge hN hmargin hdepthN
  intro g o z hz hfloor hzB Cq badCount hplus htree
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  obtain ⟨hell,profiles⟩:=hprofile g o z hz hfloor Cq badCount hplus
  refine ⟨hell,?_⟩
  intro j hjo ι _ labels samples
  let selector:=logarithmicRadius (c/4) d N/4
  let R:=(g.labelledResampledGraph T labels samples selector).retainedPhysicalMinor T j z
  let P:=((g.deficient.restrict T).deleteVertex j).extensionGreen (g.Q z) z
  let root:=g.truncatedCavityRoot o ell j hjo
  let l0:=g.truncatedCavityBoundaryInner o ell hell j hjo
  let l:=fun i=>l0 (labels i)
  let D:=g.sourceTruncatedBoundaryDefect T labels samples selector (g.Q z) z
  have hellBound:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepthN).2
  have htreeEll:=(graphBall_tree_mono g.graph o (show ell≤logarithmicRadius (c/4) d N by omega) htree)
  obtain ⟨profile0⟩:=(profiles j hjo htreeEll).1
  let profile:BoundaryMaxProfile P l root a L U M0 W0:=
    profile0.pullback P l0 root a L U M0 W0 id labels l root rfl (fun _=>rfl)
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hbudget:ε*L^(4*a)≤1:=(le_div_iff₀ (pow_pos (by linarith:(0:ℝ)<L) _)).mp
    (by simpa only [one_div] using hsmall z hz hfloor)
  have hD:∀i k,‖D i k‖≤D0*L^3*ε:=by
    intro i k
    have hh:=hcap g o z hz hfloor hzB Cq badCount hplus htree labels samples i k
    have he:‖D i k‖≤D0*(L^3*ε):=by
      simpa only [D,LocalLaw.RegularGraph.sourceTruncatedBoundaryDefect,Matrix.sub_apply,
        Matrix.submatrix_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,
        mul_ite,mul_one,mul_zero,D0,L,ε,LocalLaw.RegularGraph.sourcePrime,inflatedPrime] using hh
    exact he.trans_eq (by ring)
  have hc':‖(treeEdgeWeight d)^2‖≤1:=by convert cut_coefficient_norm_le_one d hd using 1
  exact BoundaryMaxProfile.quadratic_log_remainder R P l root a L U M0 W0 ε D0 profile D
    ((treeEdgeWeight d)^2) ha hlog hU hM hW hε hD0 hbudget hlarge hc' hD
    (g.cavity_minor_row_identity hd o ell hell j hjo labels samples selector (g.Q z) z hz
      (g.Q_im_nonnegative z hz))

end RegularGraph
end SpectralConsequences
