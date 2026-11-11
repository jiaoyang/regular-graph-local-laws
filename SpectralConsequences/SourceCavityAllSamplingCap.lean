import SpectralConsequences.CavityVertexMean
import SpectralConsequences.BoundaryProfileSmallRoot

/-! # Uniform switched cavity caps for every sampling assignment

The new graph is not assumed to satisfy the weak event. The exact root
Schur identity, its root cancellation, and its proved quadratic remainder
supply the cap even on sampling exits.
-/
open scoped BigOperators
open Filter
noncomputable section
set_option maxHeartbeats 2400000
namespace SpectralConsequences
open LocalLaw
local instance sourceCavityAllSamplingCapDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_cavity_all_sampling_cap (a b d:ℕ) (c β B:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hβ:0<β) (hβc:β≤c/32) (hB:0≤B):
    ∀ᶠ N:ℕ in atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      (graphBall g.graph o (logarithmicRadius (c/4) d N)).IsTree→
      let ell:=actualCavityDepth a d N z-1
      let T:=graphBallVertices g.graph o ell
      let selector:=logarithmicRadius (c/4) d N/4
      ∀{ι:Type}[Fintype ι](labels:ι≃BoundaryOrientedEdge g.graph T)(S:LocalSamplingFiber g.graph T),
      ‖cavityAtVertex (g.labelledResampledGraph T labels S selector).graph d z o‖≤
        2*finiteExtraReferenceConstant d+1:=by
  let C1:=sourceMinorEnlargementConstant d β B
  let U:ℝ:=(d:ℝ)*((d:ℝ)+1)
  let M0:ℝ:=2*finiteExtraReferenceConstant d*((d:ℝ)+1)
  let W0:ℝ:=8*(d:ℝ)*finiteExtraReferenceConstant d^2*sourceObservationLogCap d β
  let D0:ℝ:=sourceEndpointErrorConstant d C1+1
  let Klinear:=D0*U*M0^2
  let Kquad:=cavityRootQuadraticConstant d β C1
  have hC1:1≤C1:=by dsimp only [C1,sourceMinorEnlargementConstant];linarith [abs_nonneg (sourceDeletionConstant d β B)]
  have hCdel:sourceDeletionConstant d β B≤C1:=by
    dsimp only [C1,sourceMinorEnlargementConstant];linarith [le_abs_self (sourceDeletionConstant d β B)]
  have hC:0≤finiteExtraReferenceConstant d:=(by norm_num:(0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have hA:=sourceObservationLogCap_nonnegative d hd β hβ.le
  have hU:0≤U:=by dsimp only [U];positivity
  have hM0:0≤M0:=by dsimp only [M0];positivity
  have hD0:0≤D0:=by dsimp only [D0,sourceEndpointErrorConstant];positivity
  have hKl:0≤Klinear:=by dsimp only [Klinear];positivity
  have hKq:0≤Kquad:=by dsimp only [Kquad,cavityRootQuadraticConstant,boundaryQuadraticConstant];positivity
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [LocalLaw.RegularGraph.eventually_sourceOmegaWithRadii_subset_sourceOmegaPlusWithRadii a b d c β B C1
      (finiteOmega d) ha hb hd hc hβ hβc hB hC1 hCdel le_rfl,
    LocalLaw.RegularGraph.eventually_source_cavity_minor_profile a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_cavity_quadratic_remainder a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_switched_tree_boundary_cap a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_truncated_parameter_bounds a b d c β B ha hb hd hc hβ hβc,
    eventually_paperError_small a b d β ha hb hd hβ,eventually_log_ge_nat 1,
    eventually_log_ge_nat (2*Klinear),eventually_log_ge_nat (2*Kquad),
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,hdepth,
    Filter.eventually_ge_atTop 1]
    with N hplus hprofile hrem hcap hparam hsmall hlog hlarge₁ hlarge₂ hmargin hdepthN hN
  intro g o z hz hfloor hzB badCount hold htree
  dsimp only
  intro ι _ labels S
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let δ:=D0*L^3*ε
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hδ:0≤δ:=by dsimp only [δ];positivity
  have hbudget:ε*L^(4*a)≤1:=(le_div_iff₀ (pow_pos (by linarith:(0:ℝ)<L) _)).mp
    (by simpa only [one_div] using hsmall z hz hfloor)
  have hplus':=hplus g o z badCount hz hzB hfloor hold
  obtain ⟨hell,profiles⟩:=hprofile g o z hz hfloor (finiteOmega d) badCount hplus'
  obtain ⟨hell',remainders⟩:=hrem g o z hz hfloor hzB (finiteOmega d) badCount hplus' htree
  have hell1:1≤ell:=by omega
  have hellB:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepthN).2
  have htreeEll:=(graphBall_tree_mono g.graph o (show ell≤logarithmicRadius (c/4) d N by omega) htree)
  have hpar:=hparam g o z (g.Q z) hz hfloor (g.Q_im_nonnegative z hz) hold.2.1 htreeEll
  have hD:∀i k,‖g.sourceTruncatedBoundaryDefect T labels S selector (g.Q z) z i k‖≤δ:=by
    intro i k
    have hh:=hcap g o z hz hfloor hzB (finiteOmega d) badCount hplus' htree labels S i k
    have he:‖g.sourceTruncatedBoundaryDefect T labels S selector (g.Q z) z i k‖≤D0*(L^3*ε):=by
      simpa only [LocalLaw.RegularGraph.sourceTruncatedBoundaryDefect,Matrix.sub_apply,
        Matrix.submatrix_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,
        mul_ite,mul_one,mul_zero,D0,L,ε,LocalLaw.RegularGraph.sourcePrime,inflatedPrime] using hh
    exact he.trans_eq (by dsimp only [δ];ring)
  have hminor (j:T) (hjo:g.graph.Adj j.val o):
      ‖(g.labelledResampledGraph T labels S selector).retainedPhysicalMinor T j z
        (g.truncatedCavityRoot o ell j hjo) (g.truncatedCavityRoot o ell j hjo)‖≤2*finiteExtraReferenceConstant d+1:=by
    let P:=((g.deficient.restrict T).deleteVertex j).extensionGreen (g.Q z) z
    let R:=(g.labelledResampledGraph T labels S selector).retainedPhysicalMinor T j z
    let root:=g.truncatedCavityRoot o ell j hjo
    let l0:=g.truncatedCavityBoundaryInner o ell hell j hjo
    let l:=fun i=>l0 (labels i)
    let D:=g.sourceTruncatedBoundaryDefect T labels S selector (g.Q z) z
    obtain ⟨profile0⟩:=(profiles j hjo htreeEll).1
    let profile:BoundaryMaxProfile P l root a L U M0 W0:=
      profile0.pullback P l0 root a L U M0 W0 id labels l root rfl (fun _=>rfl)
    have hidentity:=g.cavity_minor_row_identity hd o ell hell j hjo labels S selector (g.Q z) z hz
      (g.Q_im_nonnegative z hz) root
    have hs:∀i,P (l i) root=P root (l i):=fun i=>
      (((g.deficient.restrict T).deleteVertex j).extensionGreen_isSymm (g.Q z) z).apply _ _
    have hh:=BoundaryMaxProfile.scalar_root_difference R P l root a L U M0 W0 profile hM0 D
      ((treeEdgeWeight d)^2) δ (Kquad*L^(6*a+7)*ε^2) hδ
      (by convert cut_coefficient_norm_le_one d hd using 1) hD hs hidentity
      (remainders j hjo labels S root)
    have hfirst:δ*(Fintype.card ι:ℝ)*M0^2≤1/2:=by
      apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left profile.count hδ) (sq_nonneg M0)).trans
      have he:δ*(U*L^(2*a))*M0^2=Klinear*ε*L^(2*a+3):=by
        dsimp only [δ,Klinear]
        rw [pow_add]
        ring
      rw [he]
      exact source_scaled_log_monomial_half a (2*a+3) L ε Klinear hlog hε hKl hbudget (by omega) hlarge₁
    have hsecond:=source_quadratic_remainder_small a L ε Kquad ha hlog hε hKq hbudget hlarge₂
    have hdiff:‖R root root-P root root‖≤1:=hh.trans (by linarith)
    have hp:‖P root root‖≤2*finiteExtraReferenceConstant d:=(hpar.2 j root root).1
    have ht:=norm_add_le (R root root-P root root) (P root root)
    rw [sub_add_cancel] at ht
    exact ht.trans (by linarith)
  have hcard:0<Fintype.card (g.graph.neighborSet o):=by
    rw [SimpleGraph.card_neighborSet_eq_degree,g.regular o]
    omega
  letI:Nonempty (g.graph.neighborSet o):=Fintype.card_pos_iff.mp hcard
  rw [resampled_cavityAtVertex_eq_neighbor_mean g o ell hell1 labels S selector z]
  exact finiteComplexMean_norm_bound _ _ (fun j=>hminor
    (rootNeighborInBall g.graph o ell hell1 j) j.property.symm)

end RegularGraph
end SpectralConsequences
