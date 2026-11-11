import SpectralConsequences.SourceEligibilityProbability
import SpectralConsequences.QuadraticDensityAbsorption
import SpectralConsequences.TreeBoundaryCount

/-! Actual conditional-cell upper errors have a fixed quadratic log budget. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceCellQuadraticBudgetDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def cellUpperQuadraticConstant (d:ℕ)(β B:ℝ):ℝ:=
  2*sourceSelectedMinorConstant d B (sourceMinorEnlargementConstant d β B)*((d:ℝ)*((d:ℝ)+1))+
    |twoSampleQuadraticConstant d β B|+2

namespace RegularGraph

theorem eventually_source_conditional_cell_upper_quadratic (a d:ℕ)(c β B:ℝ)
    (ha:0<a)(hd:3≤d)(hc:0<c)(hc1:c≤1/16)(hβ:0≤β)(hβc:β≤c/32):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),0≤z.im→
      let ell:=actualCavityDepth a d N z-1
      let T:=graphBallVertices g.graph o ell
      (g.graph.induce T).IsTree→∀{ι:Type}[Fintype ι](labels:ι≃BoundaryOrientedEdge g.graph T),
      sourceConditionalCellUpper g a β B labels (logarithmicRadius β d N) z≤
        cellUpperQuadraticConstant d β B*Real.log (N:ℝ)^(2*a+6)*
          (graphPaperError a d N (logarithmicRadius β d N) z)^2:=by
  let U:ℝ:=(d:ℝ)*((d:ℝ)+1)
  let Kb:=sourceCellBadCap d β B
  let Kd:=32*(sourceGreenEntryCap d+(sourceGreenEntryCap d)^2*sourceGreenPivotCap d B+1)
  have hgap:2*β<(9/32:ℝ):=by linarith
  filter_upwards [eventually_quadratic_density_absorbed a d 0 0 β (9/32) Kb hd hβ hgap,
    eventually_quadratic_density_absorbed a d (2*a) 0 β 1 (Kd*U) hd hβ (by linarith),
    eventually_actual_boundary_card_log_bound a d hd ha,eventually_log_ge_nat 1,
    Filter.eventually_ge_atTop 1] with N hbad hdensity hcount hlog hN
  intro g o z hz
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let μ:ℝ:=Nat.card (BoundaryOrientedEdge g.graph T)
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let Km:=sourceSelectedMinorConstant d B (sourceMinorEnlargementConstant d β B)
  have hKm:0≤Km:=by dsimp only [Km,sourceSelectedMinorConstant];positivity
  have hε:0≤ε:=graphPaperError_nonnegative _ _ _ _ _ hN hz
  have hμ:μ≤U*L^(2*a):=hcount g o z
  intro htree ι _ labels
  have hT:(Nat.card T:ℝ)≤μ:=by
    change (Nat.card T:ℝ)≤(Nat.card (BoundaryOrientedEdge g.graph T):ℝ)
    exact_mod_cast (tree_boundary_dominates_vertices g hd T htree)
  have hdens:Kd*(Nat.card T:ℝ)/(N:ℝ)≤ε^2:=by
    -- Kd need not be positive for a vacuous bounded-disk parameter B.
    by_cases hKd:0≤Kd
    · have hh:Kd*(Nat.card T:ℝ)/(N:ℝ)≤(Kd*U)*L^(2*a)/(N:ℝ):=by
        have hh:=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hT.trans hμ) hKd) (Nat.cast_nonneg N)
        convert hh using 1;ring
      exact hh.trans (by simpa only [Real.rpow_one,pow_zero,div_one] using hdensity z hz)
    · have hh:Kd*(Nat.card T:ℝ)/(N:ℝ)≤0:=div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hKd) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
      exact hh.trans (sq_nonneg ε)
  have hbad':Kb/(N:ℝ)^(9/32:ℝ)≤ε^2:=by
    simpa only [pow_zero,mul_one,div_one] using hbad z hz
  have hp:ε^2≤L^(2*a+6)*ε^2:=le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hlog)
  have hmain:(2*Km)*μ*(g.sourcePrime a (logarithmicRadius β d N) z)^2≤
      (2*Km*U)*L^(2*a+6)*ε^2:=by
    change (2*Km)*μ*(L^3*ε)^2≤_
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hμ (by positivity)) (sq_nonneg _)).trans_eq
    have he:L^(2*a+6)=L^(2*a)*(L^3)^2:=by
      rw [←pow_mul,←pow_add]
    simp only [he,mul_pow]
    ring
  have htwo:|twoSampleQuadraticConstant d β B| *L^2*ε^2≤
      |twoSampleQuadraticConstant d β B| *L^(2*a+6)*ε^2:=by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hlog (show 2≤2*a+6 by omega)) (abs_nonneg _)) (sq_nonneg ε)
  change (2*Km)*μ*(g.sourcePrime a (logarithmicRadius β d N) z)^2+
    |twoSampleQuadraticConstant d β B| *L^2*ε^2+Kb/(N:ℝ)^(9/32:ℝ)+Kd*(Nat.card T:ℝ)/(N:ℝ)≤_
  have hh:=add_le_add (add_le_add (add_le_add hmain htwo) (hbad'.trans hp)) (hdens.trans hp)
  exact hh.trans_eq (by dsimp only [cellUpperQuadraticConstant,Km,U,L,ε];ring)

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.eventually_source_conditional_cell_upper_quadratic
