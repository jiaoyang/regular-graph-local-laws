import SpectralConsequences.SourceCavityConditionalKernel
import SpectralConsequences.SourceTraceDriftBudget

/-! The actual reversible cavity drift is quadratic at a fixed logarithmic cost. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceCavityKernelBudgetDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_cavity_kernel_quadratic (a b d:ℕ) (c β B:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hc1:c≤1/16)
    (hβ:0<β) (hβc:β≤c/32) (hB:0≤B):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      (graphBall g.graph o (logarithmicRadius (c/4) d N)).IsTree→
      LargeTreeCountAux (4*c) (7*c) g→
      let ell:=actualCavityDepth a d N z-1
      ‖ballLabelledConditionalMean N d o ell
        (cavitySwitchDrift N d o ell (logarithmicRadius (c/4) d N/4) z) g‖≤
        sourceTraceDriftConstant d β B*Real.log (N:ℝ)^(6*a+7)*
          (graphPaperError a d N (logarithmicRadius β d N) z)^2:=by
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_source_cavity_conditional_kernel a b d c β B ha hb hd hc hc1 hβ hβc hB,
    eventually_source_conditional_cell_upper_quadratic a d c β B (by omega) hd hc hc1 hβ.le hβc,
    eventually_source_pole_scale_quadratic a b d B hd hB,
    eventually_actual_boundary_card_log_bound a d hd (by omega),
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    eventually_log_ge_nat 1,hdepth]
    with N hkernel hcell hpole hcount hmargin hlog hdepthN
  intro g o z hz hfloor hzB badCount hold htree haux
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let labels:=Equiv.refl (BoundaryOrientedEdge g.graph T)
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let μ:ℝ:=Nat.card (BoundaryOrientedEdge g.graph T)
  let U:ℝ:=(d:ℝ)*((d:ℝ)+1)
  let C:=2*finiteExtraReferenceConstant d
  let Kcell:=cellUpperQuadraticConstant d β B
  let Kquad:=cavityRootQuadraticConstant d β (sourceMinorEnlargementConstant d β B)
  let Ks:=boundaryCorrectionSensitivityConstant d β
  let Kp:=poleScaleConstant (regularSpectralRadius d) B
  have hC:0≤C:=by
    have hh:=finiteExtraReferenceConstant_ge_one d hd
    dsimp only [C];positivity
  have hKcell:0≤Kcell:=by dsimp only [Kcell,cellUpperQuadraticConstant,sourceSelectedMinorConstant];positivity
  have hKs:0≤Ks:=by
    have hh:=sourceObservationLogCap_nonnegative d hd β hβ.le
    dsimp only [Ks,boundaryCorrectionSensitivityConstant,truncatedParameterContinuityConstant];positivity
  have hKp:0≤Kp:=by
    have hh:=regularSpectralRadius_gt_two d hd
    have hg:0≤(regularSpectralRadius d-2)/2:=by linarith
    dsimp only [Kp,poleScaleConstant];positivity
  have hell:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepthN).2
  have htreeT:(g.graph.induce T).IsTree:=graphBall_tree_mono g.graph o (show ell≤logarithmicRadius (c/4) d N by omega) htree
  have hcell':sourceConditionalCellUpper g a β B labels (logarithmicRadius β d N) z≤Kcell*L^(2*a+6)*ε^2:=
    hcell g o z hz.le htreeT labels
  have hμ:μ≤U*L^(2*a):=hcount g o z
  have hweight:sourceConditionalCellUpper g a β B labels (logarithmicRadius β d N) z*(C*μ)^2≤
      (Kcell*C^2*U^2)*L^(6*a+7)*ε^2:=by
    have hμ':C*μ≤C*U*L^(2*a):=
      (mul_le_mul_of_nonneg_left hμ hC).trans_eq (by ring)
    have hh:=mul_le_mul hcell' (pow_le_pow_left₀ (mul_nonneg hC (Nat.cast_nonneg _)) hμ' 2)
      (sq_nonneg _) (by positivity)
    calc
      _≤(Kcell*L^(2*a+6)*ε^2)*(C*U*L^(2*a))^2:=hh
      _=(Kcell*C^2*U^2)*L^(6*a+6)*ε^2:=by
        have he:L^(6*a+6)=L^(2*a+6)*(L^(2*a))^2:=by rw [←pow_mul,←pow_add];congr 1;omega
        rw [he,mul_pow,mul_pow];ring
      _≤_:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hlog (by omega:6*a+6≤6*a+7)) (by positivity)) (sq_nonneg ε)
  have hsens:Ks*L^(4*a+1)*scalarScale (spectralScale z) ε*‖trivialPole N d z‖≤
      (Ks*Kp)*L^(6*a+7)*ε^2:=by
    have hh:=mul_le_mul_of_nonneg_left (hpole z hz hfloor hzB (logarithmicRadius β d N))
      (show 0≤Ks*L^(4*a+1) by positivity)
    have hf:Ks*L^(4*a+1)*scalarScale (spectralScale z) ε*‖trivialPole N d z‖≤
        (Ks*Kp)*L^(4*a+1)*ε^2:=by convert hh using 1 <;>ring
    exact hf.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hlog (by omega:4*a+1≤6*a+7)) (mul_nonneg hKs hKp)) (sq_nonneg ε))
  apply (hkernel g o z hz hfloor hzB badCount hold htree haux).trans
  change sourceConditionalCellUpper g a β B labels (logarithmicRadius β d N) z*(C*μ)^2+
    Kquad*L^(6*a+7)*ε^2+Ks*L^(4*a+1)*scalarScale (spectralScale z) ε*‖trivialPole N d z‖≤_
  apply (add_le_add (add_le_add_right hweight _) hsens).trans
  have hcoeff:Kcell*C^2*U^2+Kquad+Ks*Kp≤sourceTraceDriftConstant d β B:=by
    dsimp only [sourceTraceDriftConstant,Kcell,C,U,Kquad,Ks,Kp]
    change _+traceRootQuadraticConstant d β (sourceMinorEnlargementConstant d β B)+_≤_
    linarith [le_abs_self (cellUpperQuadraticConstant d β B*(2*finiteExtraReferenceConstant d)^2*((d:ℝ)*((d:ℝ)+1))^2),
      le_abs_self (traceRootQuadraticConstant d β (sourceMinorEnlargementConstant d β B)),
      le_abs_self (boundaryCorrectionSensitivityConstant d β*poleScaleConstant (regularSpectralRadius d) B)]
  calc
    _=(Kcell*C^2*U^2+Kquad+Ks*Kp)*L^(6*a+7)*ε^2:=by ring
    _≤_:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff
      (pow_nonneg (show 0≤L by dsimp only [L];linarith) _)) (sq_nonneg ε)

end RegularGraph
end SpectralConsequences
