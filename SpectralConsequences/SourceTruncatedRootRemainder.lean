import SpectralConsequences.SourceTruncatedRootProfile
import SpectralConsequences.BoundaryProfileQuadratic
import SpectralConsequences.SwitchedTreeBoundaryBlock

/-! The actual full-root Schur remainder is quadratic for every sample. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceTruncatedRootRemainderDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def traceRootQuadraticConstant (d:ℕ) (β C1:ℝ):ℝ:=
  boundaryQuadraticConstant ((d:ℝ)*((d:ℝ)+1))
    (2*finiteExtraReferenceConstant d*((d:ℝ)+1))
    (8*(d:ℝ)*finiteExtraReferenceConstant d^2*sourceObservationLogCap d β)
    (sourceEndpointErrorConstant d C1+1)

namespace RegularGraph

theorem eventually_source_truncated_root_remainder (a b d:ℕ) (c β B C1:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c)
    (hβ:0<β) (hβc:β≤c/32) (hC1:1≤C1):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀Cq badCount:ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z→
      (graphBall g.graph o (logarithmicRadius (c/4) d N)).IsTree→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let new:=g.labelledResampledGraph T labels samples selector
      let R:=(new.G z).submatrix (Subtype.val:T→Fin N) (Subtype.val:T→Fin N)
      let P:=(g.deficient.restrict T).extensionGreen (g.Q z) z
      let root:=cavityBallRoot g.graph o (actualCavityDepth a d N z-1)
      let l:=truncatedBoundaryInner g T labels
      let D:=g.sourceTruncatedBoundaryDefect T labels samples selector (g.Q z) z
      ∀v,‖(treeEdgeWeight d)^2*(∑i,∑j,(R root (l i)-P root (l i))*D i j*P (l j) v)‖≤
        traceRootQuadraticConstant d β C1*Real.log (N:ℝ)^(6*a+7)*
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
  filter_upwards [eventually_source_truncated_root_profile a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_switched_tree_boundary_cap a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_paperError_small a b d β ha hb hd hβ,eventually_log_ge_nat 1,
    eventually_log_ge_nat (2*(U*(U+W0+1)*D0)),Filter.eventually_ge_atTop 1]
    with N hprofile hcap hsmall hlog hlarge hN
  intro g o z hz hfloor hzB Cq badCount hplus htree ι _ labels samples
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let new:=g.labelledResampledGraph T labels samples selector
  let R:=(new.G z).submatrix (Subtype.val:T→Fin N) (Subtype.val:T→Fin N)
  let P:=(g.deficient.restrict T).extensionGreen (g.Q z) z
  let root:=cavityBallRoot g.graph o ell
  let l:=truncatedBoundaryInner g T labels
  let D:=g.sourceTruncatedBoundaryDefect T labels samples selector (g.Q z) z
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  obtain ⟨profile0⟩:=hprofile g o z hz hfloor Cq badCount hplus
  let profile:BoundaryMaxProfile P l root a L U M0 W0:=
    profile0.pullback P (truncatedBoundaryInner g T (Equiv.refl _)) root a L U M0 W0 id labels l root rfl (fun _=>rfl)
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hbudget:ε*L^(4*a)≤1:=(le_div_iff₀ (pow_pos (by linarith:(0:ℝ)<L) _)).mp
    (by simpa only [one_div] using hsmall z hz hfloor)
  have hD:∀i j,‖D i j‖≤D0*L^3*ε:=by
    intro i j
    have hh:=hcap g o z hz hfloor hzB Cq badCount hplus htree labels samples i j
    have he:‖D i j‖≤D0*(L^3*ε):=by
      simpa only [D,LocalLaw.RegularGraph.sourceTruncatedBoundaryDefect,Matrix.sub_apply,
        Matrix.submatrix_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,
        mul_ite,mul_one,mul_zero,D0,L,ε,LocalLaw.RegularGraph.sourcePrime,inflatedPrime] using hh
    exact he.trans_eq (by ring)
  have hc':‖(treeEdgeWeight d)^2‖≤1:=by
    convert cut_coefficient_norm_le_one d hd using 1
  exact BoundaryMaxProfile.quadratic_log_remainder R P l root a L U M0 W0 ε D0 profile D
    ((treeEdgeWeight d)^2) ha hlog hU hM hW hε hD0 hbudget hlarge hc' hD
    (truncated_root_row_identity g hd T labels samples selector (g.Q z) z hz (g.Q_im_nonnegative z hz) root)

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.eventually_source_truncated_root_remainder
