import SpectralConsequences.SourceTracePhysicalDrift
import SpectralConsequences.SourceCellQuadraticBudget
import SpectralConsequences.PoleScaleAbsorption

/-! The actual labelled trace drift has a fixed logarithmic epsilon² budget. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceTraceDriftBudgetDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceTraceDriftConstant (d:ℕ)(β B:ℝ):ℝ:=
  |cellUpperQuadraticConstant d β B*(2*finiteExtraReferenceConstant d)^2*((d:ℝ)*((d:ℝ)+1))^2|+
    |traceRootQuadraticConstant d β (sourceMinorEnlargementConstant d β B)|+
    |boundaryCorrectionSensitivityConstant d β*poleScaleConstant (regularSpectralRadius d) B|+1

namespace RegularGraph

theorem eventually_source_trace_drift_quadratic (a b d:ℕ)(c β B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hc1:c≤1/16)(hβ:0<β)(hβc:β≤c/32)(hB:0≤B):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      (graphBall g.graph o (logarithmicRadius (c/4) d N)).IsTree→LargeTreeCountAux (4*c) (7*c) g→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell:=actualCavityDepth a d N z-1
      let T:=graphBallVertices g.graph o ell
      let selector:=logarithmicRadius (c/4) d N/4
      ‖finiteComplexMean (fun S:LocalSamplingFiber g.graph T=>
          (g.labelledResampledGraph T labels S selector).G z o o)-
        regularRootValue d ell (g.Q z) z-trivialTraceCorrection N d ell z‖≤
        sourceTraceDriftConstant d β B*Real.log (N:ℝ)^(6*a+7)*
          (graphPaperError a d N (logarithmicRadius β d N) z)^2:=by
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_source_trace_physical_drift a b d c β B ha hb hd hc hβ hβc hB,
    eventually_source_conditional_cell_error_bound a d c β B (by omega) hd hc hc1 hB,
    eventually_source_conditional_cell_upper_quadratic a d c β B (by omega) hd hc hc1 hβ.le hβc,
    eventually_source_pole_scale_quadratic a b d B hd hB,
    eventually_source_truncated_parameter_bounds a b d c β B ha hb hd hc hβ hβc,
    eventually_actual_boundary_card_log_bound a d hd (by omega),
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    eventually_log_ge_nat 1,hdepth] with N hdrift hCellUpper hCellQuad hPole hparam hcount hmargin hlog hdepth
  intro g o z hz hfloor hzB badCount hold hTree haux ι _ labels
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let μ:ℝ:=Nat.card (BoundaryOrientedEdge g.graph T)
  let U:ℝ:=(d:ℝ)*((d:ℝ)+1)
  let C:=2*finiteExtraReferenceConstant d
  let Kcell:=cellUpperQuadraticConstant d β B
  let Kquad:=traceRootQuadraticConstant d β (sourceMinorEnlargementConstant d β B)
  let Ks:=boundaryCorrectionSensitivityConstant d β
  let Kp:=poleScaleConstant (regularSpectralRadius d) B
  let e:=sourceConditionalCellError g a β B labels selector (logarithmicRadius β d N) z
  let w:ι→ℂ:=fun i=>fullBoundaryWeight g o ell (g.Q z) z (labels i)
  have hC:0≤C:=by
    have hh:=finiteExtraReferenceConstant_ge_one d hd
    dsimp only [C];positivity
  have hKcell:0≤Kcell:=by
    dsimp only [Kcell,cellUpperQuadraticConstant,sourceSelectedMinorConstant]
    positivity
  have hKs:0≤Ks:=by
    have hh:=sourceObservationLogCap_nonnegative d hd β hβ.le
    dsimp only [Ks,boundaryCorrectionSensitivityConstant,truncatedParameterContinuityConstant]
    positivity
  have hKp:0≤Kp:=by
    have hh:=regularSpectralRadius_gt_two d hd
    have hg:0≤(regularSpectralRadius d-2)/2:=by linarith
    dsimp only [Kp,poleScaleConstant]
    positivity
  have he:0≤e:=by
    have hh:=finiteReferenceConstant_ge_one d hd
    dsimp only [e,sourceConditionalCellError,sourceCellBadCap,sourceCellEntryCap,
      sourceSelectedMinorConstant,sourceMinorEnlargementConstant,sourceGreenEntryCap,sourceGreenPivotCap,
      eventMass,localSamplingWeight,finiteUniformWeight]
    positivity
  have hell:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepth).2
  have htreeT:(g.graph.induce T).IsTree:=graphBall_tree_mono g.graph o (by dsimp only [ell];omega) hTree
  have hcell:e≤Kcell*L^(2*a+6)*ε^2:=
    (hCellUpper g o z (logarithmicRadius β d N) haux hTree labels).trans
      (hCellQuad g o z hz.le htreeT labels)
  have hp:=hparam g o z (g.Q z) hz hfloor (g.Q_im_nonnegative z hz) hold.2.1 htreeT
  have hμ:μ≤U*L^(2*a):=hcount g o z
  have hsum:(∑i:ι,‖w i‖)≤C*U*L^(2*a):=by
    have hcard:(Fintype.card ι:ℝ)=μ:=by
      dsimp only [μ]
      rw [Nat.card_eq_fintype_card]
      exact_mod_cast Fintype.card_congr labels
    calc
      _≤∑_i:ι,C:=Finset.sum_le_sum (fun i _=>(hp.1 _ _).1)
      _=C*μ:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hcard];ring
      _≤C*(U*L^(2*a)):=mul_le_mul_of_nonneg_left hμ hC
      _=_:=by ring
  have hweight:‖(treeEdgeWeight d)^2‖*e*(∑i:ι,‖w i‖)^2≤
      (Kcell*C^2*U^2)*L^(6*a+7)*ε^2:=by
    have hc':‖(treeEdgeWeight d)^2‖≤1:=by convert cut_coefficient_norm_le_one d hd using 1
    have hh:=mul_le_mul hcell (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) hsum 2)
      (sq_nonneg _) (by positivity)
    calc
      _≤e*(∑i:ι,‖w i‖)^2:=mul_le_mul_of_nonneg_right (mul_le_of_le_one_left he hc') (sq_nonneg _)
      _≤(Kcell*L^(2*a+6)*ε^2)*(C*U*L^(2*a))^2:=hh
      _=(Kcell*C^2*U^2)*L^(6*a+6)*ε^2:=by
        have heq:L^(6*a+6)=L^(2*a+6)*(L^(2*a))^2:=by rw [←pow_mul,←pow_add];congr 1;omega
        rw [heq,mul_pow,mul_pow]
        ring
      _≤_:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hlog (by omega:6*a+6≤6*a+7)) (by positivity)) (sq_nonneg ε)
  have hsensitivity:Ks*L^(4*a+1)*scalarScale (spectralScale z) ε*‖trivialPole N d z‖≤
      (Ks*Kp)*L^(6*a+7)*ε^2:=by
    have hh:=mul_le_mul_of_nonneg_left (hPole z hz hfloor hzB (logarithmicRadius β d N))
      (show 0≤Ks*L^(4*a+1) by positivity)
    have hfirst:Ks*L^(4*a+1)*scalarScale (spectralScale z) ε*‖trivialPole N d z‖≤
        (Ks*Kp)*L^(4*a+1)*ε^2:=by convert hh using 1 <;>ring
    exact hfirst.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hlog (by omega:4*a+1≤6*a+7)) (mul_nonneg hKs hKp)) (sq_nonneg ε))
  have hh:=hdrift g o z hz hfloor hzB badCount hold hTree labels
  apply hh.trans
  have hcombined:=add_le_add_right (add_le_add_right hweight (Kquad*L^(6*a+7)*ε^2))
    (Ks*L^(4*a+1)*scalarScale (spectralScale z) ε*‖trivialPole N d z‖)
  apply hcombined.trans
  have hcombined':=add_le_add_left hsensitivity ((Kcell*C^2*U^2)*L^(6*a+7)*ε^2+Kquad*L^(6*a+7)*ε^2)
  apply hcombined'.trans
  have hcoeff:Kcell*C^2*U^2+Kquad+Ks*Kp≤sourceTraceDriftConstant d β B:=by
    dsimp only [sourceTraceDriftConstant,Kcell,C,U,Kquad,Ks,Kp]
    linarith [le_abs_self (cellUpperQuadraticConstant d β B*(2*finiteExtraReferenceConstant d)^2*((d:ℝ)*((d:ℝ)+1))^2),
      le_abs_self (traceRootQuadraticConstant d β (sourceMinorEnlargementConstant d β B)),
      le_abs_self (boundaryCorrectionSensitivityConstant d β*poleScaleConstant (regularSpectralRadius d) B)]
  calc
    _=(Kcell*C^2*U^2+Kquad+Ks*Kp)*L^(6*a+7)*ε^2:=by ring
    _≤_:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff
      (pow_nonneg (show 0≤L by dsimp only [L];linarith) _)) (sq_nonneg ε)

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.eventually_source_trace_drift_quadratic
