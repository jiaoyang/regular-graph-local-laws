import SpectralConsequences.SourceBoundaryConditionalMeans
import SpectralConsequences.SourceLargePatchProbability

/-! # The actual rejection probability in the conditional means

The protected-patch event implies acceptance of every label. Its proved
sampling probability therefore controls the exceptional term in Section7.5.
-/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceEligibilityProbabilityDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_all_eligible_probability (a d:ℕ) (c:ℝ)
    (ha:0<a) (hd:3≤d) (hc:0<c) (hc1:c≤1/16):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      let ell:=actualCavityDepth a d N z-1
      let T:=graphBallVertices g.graph o ell
      let R:=logarithmicRadius (c/4) d N
      LargeTreeCountAux (4*c) (7*c) g→(graphBall g.graph o R).IsTree→
      ∀{ι:Type}[Fintype ι](labels:ι≃BoundaryOrientedEdge g.graph T),
      eventMass (localSamplingWeight g.graph T) (fun S=>¬allSamplesEligible g labels (R/4) S)≤
        1/(N:ℝ)^(9/32:ℝ):=by
  filter_upwards [eventually_source_protectedPatches_probability a d (4*c) (7*c)
    ha hd (by linarith) (by linarith) (by linarith),Filter.eventually_ge_atTop 1]
    with N hprob hN
  intro g o z
  dsimp only
  intro haux htree ι _ labels
  have hp:=hprob g o z haux
  rw [show (4*c)/16=c/4 by ring] at hp
  have hh:=hp htree labels
  apply (eventMass_mono (localSamplingWeight g.graph _) finiteUniformWeight_nonneg ?_).trans
    (hh.trans ?_)
  · intro S hbad hprotected
    exact hbad hprotected.accepted
  · apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega)) _)
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)

variable {N d:ℕ} {T:Set (Fin N)} {ι:Type}[Fintype ι]

def sourceConditionalCellUpper (g:LocalLaw.RegularGraph N d) (a:ℕ) (β B:ℝ)
    (_labels:ι≃BoundaryOrientedEdge g.graph T) (r:ℕ) (z:ℂ):ℝ:=
  (2*sourceSelectedMinorConstant d B (sourceMinorEnlargementConstant d β B))*
      (Nat.card (BoundaryOrientedEdge g.graph T):ℝ)*(g.sourcePrime a r z)^2+
    |twoSampleQuadraticConstant d β B| *Real.log (N:ℝ)^2*(graphPaperError a d N r z)^2+
    sourceCellBadCap d β B/(N:ℝ)^(9/32:ℝ)+
    32*(sourceGreenEntryCap d+(sourceGreenEntryCap d)^2*sourceGreenPivotCap d B+1)*
      (Nat.card T:ℝ)/(N:ℝ)

theorem eventually_source_conditional_cell_error_bound (a d:ℕ) (c β B:ℝ)
    (ha:0<a) (hd:3≤d) (hc:0<c) (hc1:c≤1/16) (hB:0≤B):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ)(r:ℕ),
      let ell:=actualCavityDepth a d N z-1
      let T:=graphBallVertices g.graph o ell
      let R:=logarithmicRadius (c/4) d N
      LargeTreeCountAux (4*c) (7*c) g→(graphBall g.graph o R).IsTree→
      ∀{ι:Type}[Fintype ι](labels:ι≃BoundaryOrientedEdge g.graph T),
      sourceConditionalCellError g a β B labels (R/4) r z≤
        sourceConditionalCellUpper g a β B labels r z:=by
  filter_upwards [eventually_source_all_eligible_probability a d c ha hd hc hc1]
    with N hprob
  intro g o z r
  dsimp only
  intro haux htree ι _ labels
  have hp:=hprob g o z haux htree labels
  have hbad:0≤sourceCellBadCap d β B:=by
    have hC:=finiteReferenceConstant_ge_one d hd
    dsimp only [sourceCellBadCap,sourceCellEntryCap,sourceGreenEntryCap,sourceGreenPivotCap]
    positivity
  dsimp only [sourceConditionalCellError,sourceConditionalCellUpper]
  gcongr
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hp hbad

end RegularGraph
end SpectralConsequences
