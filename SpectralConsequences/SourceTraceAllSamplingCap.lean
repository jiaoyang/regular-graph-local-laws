import SpectralConsequences.SourceTruncatedRootRemainder
import SpectralConsequences.BoundaryProfileSmallRoot
import SpectralConsequences.RegularBallRecursion
import SpectralConsequences.SourceTruncatedParameterBounds
import SpectralConsequences.SourceSelectedMinorFromWeak

/-! Actual pointwise trace-root control for every sampling assignment,
using only the original source event and its original tree neighborhood. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceTraceAllSamplingCapDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def tracePointErrorConstant (d:ℕ)(β C1:ℝ):ℝ:=
  |(sourceEndpointErrorConstant d C1+1)*((d:ℝ)*((d:ℝ)+1))*
    (2*finiteExtraReferenceConstant d*((d:ℝ)+1))^2|+|traceRootQuadraticConstant d β C1|+1

namespace RegularGraph

theorem eventually_source_trace_all_sampling_cap (a b d:ℕ)(c β B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hB:0≤B):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      (graphBall g.graph o (logarithmicRadius (c/4) d N)).IsTree→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell:=actualCavityDepth a d N z-1
      let T:=graphBallVertices g.graph o ell
      let new:=g.labelledResampledGraph T labels samples (logarithmicRadius (c/4) d N/4)
      ‖new.G z o o-regularRootValue d ell (g.Q z) z‖≤
        tracePointErrorConstant d β (sourceMinorEnlargementConstant d β B)*Real.log (N:ℝ)^(2*a+7)*
          graphPaperError a d N (logarithmicRadius β d N) z ∧
      ‖new.G z o o‖≤2*finiteExtraReferenceConstant d+1:=by
  let C1:=sourceMinorEnlargementConstant d β B
  let U:ℝ:=(d:ℝ)*((d:ℝ)+1)
  let M0:ℝ:=2*finiteExtraReferenceConstant d*((d:ℝ)+1)
  let D0:ℝ:=sourceEndpointErrorConstant d C1+1
  let Kq:ℝ:=traceRootQuadraticConstant d β C1
  let K:ℝ:=tracePointErrorConstant d β C1
  have hC1:1≤C1:=by dsimp only [C1,sourceMinorEnlargementConstant];linarith [abs_nonneg (sourceDeletionConstant d β B)]
  have hCdel:sourceDeletionConstant d β B≤C1:=by
    dsimp only [C1,sourceMinorEnlargementConstant];linarith [le_abs_self (sourceDeletionConstant d β B)]
  have hC:0≤finiteExtraReferenceConstant d:=(by norm_num:(0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have hU:0≤U:=by dsimp only [U];positivity
  have hM:0≤M0:=by dsimp only [M0];positivity
  have hK:0≤K:=by dsimp only [K,tracePointErrorConstant];positivity
  have hD0:0≤D0:=by
    dsimp only [D0,sourceEndpointErrorConstant]
    have hC1':0≤C1:=by linarith
    positivity
  have hKq:0≤Kq:=by
    have hA:=sourceObservationLogCap_nonnegative d hd β hβ.le
    dsimp only [Kq,traceRootQuadraticConstant,boundaryQuadraticConstant]
    positivity
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_source_truncated_root_remainder a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_truncated_root_profile a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_switched_tree_boundary_cap a b d c β B C1 ha hb hd hc hβ hβc hC1,
    LocalLaw.RegularGraph.eventually_sourceOmegaWithRadii_subset_sourceOmegaPlusWithRadii a b d c β B C1
      (finiteOmega d) ha hb hd hc hβ hβc hB hC1 hCdel le_rfl,
    eventually_source_truncated_parameter_bounds a b d c β B ha hb hd hc hβ hβc,
    eventually_paperError_small a b d β ha hb hd hβ,eventually_log_ge_nat 1,eventually_log_ge_nat (2*K),
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,hdepth,
    Filter.eventually_ge_atTop 1] with N hrem hprofile hDcap hplus hparam hsmall hlog hlarge hmargin hdepth hN
  intro g o z hz hfloor hzB badCount hold htree ι _ labels samples
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let root:=cavityBallRoot g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let new:=g.labelledResampledGraph T labels samples selector
  let R:=(new.G z).submatrix (Subtype.val:T→Fin N) (Subtype.val:T→Fin N)
  let P:=(g.deficient.restrict T).extensionGreen (g.Q z) z
  let l:=truncatedBoundaryInner g T labels
  let w:ι→ℂ:=fun i=>P root (l i)
  let D:=g.sourceTruncatedBoundaryDefect T labels samples selector (g.Q z) z
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  have hplus':=hplus g o z badCount hz hzB hfloor hold
  have hε:0≤ε:=graphPaperError_nonnegative _ _ _ _ _ hN hz.le
  have hcap:ε*L^(4*a)≤1:=(le_div_iff₀ (pow_pos (by linarith:(0:ℝ)<L) _)).mp
    (by simpa only [one_div] using hsmall z hz hfloor)
  obtain ⟨profile0⟩:=hprofile g o z hz hfloor (finiteOmega d) badCount hplus'
  let profile:BoundaryMaxProfile P l root a L U M0
      (8*(d:ℝ)*finiteExtraReferenceConstant d^2*sourceObservationLogCap d β):=
    profile0.pullback P (truncatedBoundaryInner g T (Equiv.refl _)) root a L U M0 _ id labels l root rfl (fun _=>rfl)
  have hw:(∑i:ι,‖w i‖)^2≤U*L^(2*a)*M0^2:=
    (BoundaryMaxProfile.root_l1_square_count P l root a L U M0 _ profile hM).trans
      (mul_le_mul_of_nonneg_right profile.count (sq_nonneg M0))
  have hD:∀i j,‖D i j‖≤D0*L^3*ε:=by
    intro i j
    have hh:=hDcap g o z hz hfloor hzB (finiteOmega d) badCount hplus' htree labels samples i j
    have he:‖D i j‖≤D0*(L^3*ε):=by
      simpa only [D,LocalLaw.RegularGraph.sourceTruncatedBoundaryDefect,Matrix.sub_apply,
        Matrix.submatrix_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,mul_ite,mul_one,mul_zero,
        D0,L,ε,LocalLaw.RegularGraph.sourcePrime,inflatedPrime] using hh
    exact he.trans_eq (by ring)
  have hc':‖(treeEdgeWeight d)^2‖≤1:=by convert cut_coefficient_norm_le_one d hd using 1
  have hlead:‖(treeEdgeWeight d)^2*(∑i,∑j,P root (l i)*D i j*P (l j) root)‖≤
      (D0*U*M0^2)*L^(2*a+7)*ε:=by
    have hsym:∀j,P (l j) root=w j:=fun j=>((g.deficient.restrict T).extensionGreen_isSymm (g.Q z) z).apply _ _
    simp_rw [hsym]
    have hh:=boundary_linear_array_norm w D ((treeEdgeWeight d)^2) (D0*L^3*ε) hc' hD
    apply hh.trans
    apply (mul_le_mul_of_nonneg_left hw (by positivity:0≤D0*L^3*ε)).trans
    calc
      _=(D0*U*M0^2)*L^(2*a+3)*ε:=by rw [pow_add];ring
      _≤_:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hlog (by omega:2*a+3≤2*a+7)) (by positivity)) hε
  have hquadratic:Kq*L^(6*a+7)*ε^2≤Kq*L^(2*a+7)*ε:=by
    calc
      _=(Kq*L^(2*a+7)*ε)*(ε*L^(4*a)):=by
        have he:L^(6*a+7)=L^(2*a+7)*L^(4*a):=by rw [←pow_add];congr 1;omega
        rw [he]
        ring
      _≤(Kq*L^(2*a+7)*ε)*1:=mul_le_mul_of_nonneg_left hcap (by positivity)
      _=_:=mul_one _
  have hid:=truncated_root_row_identity g hd T labels samples selector (g.Q z) z hz (g.Q_im_nonnegative z hz) root root
  have herror:‖new.G z o o-P root root‖≤K*L^(2*a+7)*ε:=by
    change ‖R root root-P root root‖≤_
    rw [hid]
    apply ((norm_add_le _ _).trans (add_le_add hlead
      ((hrem g o z hz hfloor hzB (finiteOmega d) badCount hplus' htree labels samples root).trans hquadratic))).trans
    have hcoeff:D0*U*M0^2+Kq≤K:=by
      dsimp only [K,tracePointErrorConstant,D0,U,M0,Kq]
      linarith [le_abs_self ((sourceEndpointErrorConstant d C1+1)*((d:ℝ)*((d:ℝ)+1))*
        (2*finiteExtraReferenceConstant d*((d:ℝ)+1))^2),le_abs_self (traceRootQuadraticConstant d β C1)]
    calc
      _=(D0*U*M0^2+Kq)*L^(2*a+7)*ε:=by ring
      _≤_:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff
        (pow_nonneg (show 0≤L by dsimp only [L];linarith) _)) hε
  have hell:1≤ell:=by
    have hh:(1:ℝ)≤(ell:ℝ):=by
      have hp:=(actualCavityDepth_radius_bounds a d N z hdepth).1
      dsimp only [ell];linarith
    exact_mod_cast hh
  have hellBound:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepth).2
  have htreeEll:(graphBall g.graph o ell).IsTree:=graphBall_tree_mono g.graph o (by dsimp only [ell];omega) htree
  have hdiag:P root root=regularRootValue d ell (g.Q z) z:=
    full_ball_extension_diagonal g hd o ell hell htreeEll (g.Q z) z hz (g.Q_im_nonnegative z hz)
  refine ⟨by simpa only [hdiag] using herror,?_⟩
  have hhalf:K*L^(2*a+7)*ε≤1/2:=by
    have hh:=source_scaled_log_monomial_half a (2*a+7) L ε K hlog hε hK hcap (by omega) hlarge
    convert hh using 1;ring
  have hPcap:‖P root root‖≤2*finiteExtraReferenceConstant d:=
    ((hparam g o z (g.Q z) hz hfloor (g.Q_im_nonnegative z hz) hold.2.1 htreeEll).1 _ _).1
  have hn:‖new.G z o o‖≤‖new.G z o o-P root root‖+‖P root root‖:=by
    calc
      _=‖(new.G z o o-P root root)+P root root‖:=by rw [sub_add_cancel]
      _≤_:=norm_add_le _ _
  exact hn.trans ((add_le_add (herror.trans hhalf) hPcap).trans (by linarith))

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.eventually_source_trace_all_sampling_cap
