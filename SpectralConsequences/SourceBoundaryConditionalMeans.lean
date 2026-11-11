import SpectralConsequences.BoundaryConditionalMeans
import SpectralConsequences.SourceSelectedMinorFromWeak
import LocalLaw.SourceFormalEdgeBounds
import LocalLaw.IndependentRadiusSourceCaps
import LocalLaw.ResamplingRadiusGrowth

/-! # Actual conditional means of switched boundary entries

All analytic comparisons are obtained from the original weak event.
The only displayed sampling contribution is the actual probability that
one of the prescribed labels is rejected. It will be bounded by the proved
protected-patch sampling theorem, rather than being a mean hypothesis.
-/
open Filter
noncomputable section
set_option maxHeartbeats 2200000
namespace SpectralConsequences
open LocalLaw
local instance sourceBoundaryConditionalMeansDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceCellEntryCap (d:ℕ) (β B:ℝ):ℝ:=
  |sourceEndpointErrorConstant d (sourceMinorEnlargementConstant d β B)|+1

def sourceCellBadCap (d:ℕ) (β B:ℝ):ℝ:=
  sourceCellEntryCap d β B+4*sourceGreenEntryCap d+
    (sourceGreenEntryCap d)^2*sourceGreenPivotCap d B+2

namespace RegularGraph
variable {N d:ℕ} {T:Set (Fin N)} {ι:Type} [Fintype ι]

def sourceConditionalCellError (g:LocalLaw.RegularGraph N d) (a:ℕ) (β B:ℝ)
    (labels:ι≃BoundaryOrientedEdge g.graph T) (selector r:ℕ) (z:ℂ):ℝ:=
  (2*sourceSelectedMinorConstant d B (sourceMinorEnlargementConstant d β B))*
      (Nat.card (BoundaryOrientedEdge g.graph T):ℝ)*(g.sourcePrime a r z)^2+
    |twoSampleQuadraticConstant d β B| *Real.log (N:ℝ)^2*(graphPaperError a d N r z)^2+
    sourceCellBadCap d β B*eventMass (localSamplingWeight g.graph T)
      (fun S=>¬allSamplesEligible g labels selector S)+
    32*(sourceGreenEntryCap d+(sourceGreenEntryCap d)^2*sourceGreenPivotCap d B+1)*
      (Nat.card T:ℝ)/(N:ℝ)

theorem eventually_source_boundary_conditional_means (a b d:ℕ) (c β B:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hβ:0<β) (hβc:β≤c/32) (hB:0≤B) :
    ∀ᶠ N:ℕ in atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      (graphBall g.graph o (logarithmicRadius (c/4) d N)).IsTree→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let err:=sourceConditionalCellError g a β B labels selector (logarithmicRadius β d N) z
      (∀j:ι,‖finiteComplexMean (fun S:LocalSamplingFiber g.graph T=>
        switchedBoundaryEntry g labels S selector z j j-g.Q z)‖≤err) ∧
      (∀j k:ι,j≠k→‖finiteComplexMean (fun S:LocalSamplingFiber g.graph T=>
        switchedBoundaryEntry g labels S selector z j k)-
          (1+treeEdgeWeight d*g.Q z)^2*((N:ℂ)⁻¹*(treeEdgeWeight d*(d:ℂ)-z)⁻¹)‖≤err) := by
  let C1:=sourceMinorEnlargementConstant d β B
  have hC1:1≤C1:=by
    dsimp only [C1,sourceMinorEnlargementConstant]
    linarith [abs_nonneg (sourceDeletionConstant d β B)]
  have hCdel:sourceDeletionConstant d β B≤C1:=by
    dsimp only [C1,sourceMinorEnlargementConstant]
    linarith [le_abs_self (sourceDeletionConstant d β B)]
  have hdepth:∀ᶠ N:ℕ in atTop,4≤lowerLogLogRadius a d N:=
    (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_source_boundary_offdiag_pointwise a b d c β B C1 ha hb hd hc hβ hβc hB hC1,
    eventually_source_tree_sampled_minor_comparison a b d c β B C1 ha hb hd hc hβ hβc hB hC1,
    eventually_switched_tree_boundary_cap a b d c β B C1 ha hb hd hc hβ hβc hC1,
    LocalLaw.RegularGraph.eventually_sourceOmegaWithRadii_subset_sourceOmegaPlusWithRadii a b d c β B C1
      (finiteOmega d) ha hb hd hc hβ hβc hB hC1 hCdel le_rfl,
    LocalLaw.RegularGraph.eventually_sourceOmegaWithRadii_green_caps a b d c β B ha hb hd hc hβ hβc hB,
    eventually_source_formal_edge_bounds a b d c β B 1 ha hb hd hc hβ hβc (by norm_num),
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_resampling_ball_budget a d hd,hdepth,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    Filter.eventually_ge_atTop 1]
    with N hpoint hminor hcap hplus hGcap hq hnum hbudget hdepthN hmargin hN
  intro g o z hz hfloor hzB badCount hold hTree ι _ labels
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let ε':=g.sourcePrime a (logarithmicRadius β d N) z
  let C:=sourceGreenEntryCap d
  let P:=sourceGreenPivotCap d B
  let V:=sourceCellEntryCap d β B
  let μ:ℝ:=Nat.card (BoundaryOrientedEdge g.graph T)
  let eg:=(2*sourceSelectedMinorConstant d B C1)*μ*ε'^2+
    |twoSampleQuadraticConstant d β B| *L^2*ε^2
  let prob:=eventMass (localSamplingWeight g.graph T) (fun S=>¬allSamplesEligible g labels selector S)
  have hC:0≤C:=by
    dsimp only [C,sourceGreenEntryCap]
    have hh:=finiteReferenceConstant_ge_one d hd
    linarith
  have hP:0≤P:=by
    dsimp only [P,sourceGreenPivotCap]
    have hh:=finiteReferenceConstant_ge_one d hd
    positivity
  have hV:0≤V:=by dsimp only [V,sourceCellEntryCap];positivity
  have hμ:0≤μ:=Nat.cast_nonneg _
  have hK:0≤sourceSelectedMinorConstant d B C1:=by dsimp only [sourceSelectedMinorConstant];positivity
  have heg:0≤eg:=by dsimp only [eg];positivity
  have hp:0≤prob:=by
    dsimp only [prob,eventMass,localSamplingWeight,finiteUniformWeight]
    positivity
  have num:=hnum z hz hfloor
  have hε:0≤ε:=num.error_nonnegative
  have hL:1≤L:=num.log_one
  have hε4:ε*L^4≤1:=by
    have hC1sq:1≤C1^2:=one_le_pow₀ hC1
    have hh:=mul_le_mul_of_nonneg_right hC1sq (mul_nonneg hε (pow_nonneg (by linarith) 4))
    have hscaled:=num.error_scaled
    dsimp only [L,ε] at *
    nlinarith only [hh,hscaled]
  have hprime:0≤ε' ∧ ε'≤1:=by
    change 0≤L^3*ε ∧ L^3*ε≤1
    constructor
    · positivity
    · exact ((mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL (by omega:3≤4)) hε).trans_eq
        (mul_comm _ _)).trans hε4
  have hplus':=hplus g o z badCount hz hzB hfloor hold
  have hc':=hGcap g z badCount hz hzB hfloor hold
  have hprior:‖g.Q z-semicircleRoot z‖≤1*scalarScale (spectralScale z) ε:=by
    simpa only [one_mul] using hold.2.1
  have hq':=hq z (g.Q z) hz hzB hfloor hprior
  have hell:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepthN).2
  have hT:4*Nat.card T≤N:=g.ball_small o ell
    ((Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by omega:0<d+1) hell)).trans hbudget)
  have htreeT:(g.graph.induce T).IsTree:=graphBall_tree_mono g.graph o (show ell≤logarithmicRadius (c/4) d N by omega) hTree
  have hv (S:LocalSamplingFiber g.graph T) (j k:ι):
      ‖switchedBoundaryEntry g labels S selector z j k-(if j=k then g.Q z else 0)‖≤V:=by
    have hh:=hcap g o z hz hfloor hzB (finiteOmega d) badCount hplus' hTree labels S j k
    have hcoef:sourceEndpointErrorConstant d C1+1≤V:=by
      dsimp only [V,sourceCellEntryCap,C1]
      linarith [le_abs_self (sourceEndpointErrorConstant d (sourceMinorEnlargementConstant d β B))]
    have hcoefp:0≤sourceEndpointErrorConstant d C1+1:=by
      dsimp only [sourceEndpointErrorConstant]
      positivity
    apply hh.trans
    exact (mul_le_of_le_one_right hcoefp hprime.2).trans hcoef
  have hdiag (S:LocalSamplingFiber g.graph T) (j:ι)
      (hs:allSamplesEligible g labels selector S):
      ‖switchedBoundaryEntry g labels S selector z j j-
        fullEdgeCavity g z ⟨(S (labels j)).val,(S (labels j)).property.1⟩‖≤eg:=by
    let s:=g.admissibleState T labels S
    let i:s.AdmissibleSampleIndex selector:=⟨j,hs j⟩
    have hh:=hminor g o z hz hfloor hzB (finiteOmega d) badCount hold hplus' labels S htreeT i i
    rw [switchedBoundaryEntry_accepted g labels S selector z j j (hs j) (hs j)]
    rw [←sampledDoubleMinor_self g labels S selector z hz i]
    exact hh.trans (le_add_of_nonneg_right (by positivity))
  have hoff (S:LocalSamplingFiber g.graph T) (j k:ι) (hjk:j≠k)
      (hs:allSamplesEligible g labels selector S):
      ‖switchedBoundaryEntry g labels S selector z j k-sampledBoundaryLeading g labels S z j k‖≤eg:=by
    have hh:=hpoint g o z hz hfloor hzB (finiteOmega d) badCount hold hplus' htreeT labels S j k hjk (hs j) (hs k)
    apply hh.trans
    exact add_le_add_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg L)) (sq_nonneg ε)) _
  constructor
  · intro j
    have hh:=switched_boundary_diagonal_mean g labels selector (by omega) (by omega) hT z hz j
      C P V 2 eg hC hP heg hc'.1 hc'.2 hq'.1 (fun S=>by simpa only [if_true] using hv S j j)
      (fun S hs=>hdiag S j hs)
    apply hh.trans
    change eg+(V+C+C^2*P+2)*prob+4*(C+C^2*P)*(Nat.card T:ℝ)/(N:ℝ)≤
      eg+sourceCellBadCap d β B*prob+32*(C+C^2*P+1)*(Nat.card T:ℝ)/(N:ℝ)
    have hbad:V+C+C^2*P+2≤sourceCellBadCap d β B:=by
      dsimp only [sourceCellBadCap,V,C,P]
      linarith
    have hdens:4*(C+C^2*P)*(Nat.card T:ℝ)/(N:ℝ)≤32*(C+C^2*P+1)*(Nat.card T:ℝ)/(N:ℝ):=by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      nlinarith [mul_nonneg (sq_nonneg C) hP]
    exact add_le_add (add_le_add_left (mul_le_mul_of_nonneg_right hbad hp) eg) hdens
  · intro j k hjk
    have hh:=switched_boundary_offdiag_mean g labels selector (by omega) (by omega) hT z hz j k hjk
      C V eg hC heg hc'.1 hq'.2
      (fun S=>by simpa only [hjk,if_false,sub_zero] using hv S j k)
      (fun S hs=>hoff S j k hjk hs)
    apply hh.trans
    change eg+(V+4*C)*prob+32*C*(Nat.card T:ℝ)/(N:ℝ)≤
      eg+sourceCellBadCap d β B*prob+32*(C+C^2*P+1)*(Nat.card T:ℝ)/(N:ℝ)
    have hbad:V+4*C≤sourceCellBadCap d β B:=by
      change V+4*C≤V+4*C+C^2*P+2
      nlinarith [mul_nonneg (sq_nonneg C) hP]
    have hdens:32*C*(Nat.card T:ℝ)/(N:ℝ)≤32*(C+C^2*P+1)*(Nat.card T:ℝ)/(N:ℝ):=by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      nlinarith [mul_nonneg (sq_nonneg C) hP]
    exact add_le_add (add_le_add_left (mul_le_mul_of_nonneg_right hbad hp) eg) hdens

end RegularGraph
end SpectralConsequences
