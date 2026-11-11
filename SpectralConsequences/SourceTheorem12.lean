import SpectralConsequences.SourceActualHighMoments
import SpectralConsequences.SourceMomentTailBridge
import SpectralConsequences.SourceRigidityReduction

/-! The full source graph eigenvalue rigidity theorem. Actual Section7
moments, physical residual tails, exterior confinement, original conditioning
and quantile inversion are all discharged. No analytic certificate remains. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem source_theorem_1_2 (d:ℕ)(c:ℝ)(hd:3≤d)(hc:0<c)(hc1:c<1):
    ∀D:ℕ,∀ᶠ N:ℕ in Filter.atTop,Nonempty (RegularGraph N d)→
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g ∧
          ¬SourceRigid hd (canonicalRigidityExponent c) g)/
        eventMass (RegularGraph.weight (N:=N) (d:=d))
          (RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊)≤1/(N:ℝ)^D:=by
  obtain ⟨hβ,hβwork,hβsmall,_,_⟩:=canonicalRigidity_parameters c hc
  have haux:0<exteriorAuxParameter c:=lt_min (by linarith) (by norm_num)
  have hauxcap:exteriorAuxParameter c≤1/4:=min_le_right _ _
  have hwork:0<exteriorWorkParameter c:=by unfold exteriorWorkParameter;positivity
  have hworkcap:exteriorWorkParameter c≤1/16:=by unfold exteriorWorkParameter;linarith
  have hB:2*(d:ℝ)≤sourceExteriorProbabilityBound d:=by
    have hh:2≤sourceSpectralBox d:=le_max_left _ _
    unfold sourceExteriorProbabilityBound
    linarith
  have hmom:SourceHighMomentBounds 12 300 d (exteriorWorkParameter c)
      (canonicalRigidityBeta c) (sourceExteriorProbabilityBound d):=
    source_actual_high_moment_bounds 12 300 d (exteriorWorkParameter c)
      (canonicalRigidityBeta c) (sourceExteriorProbabilityBound d)
      (by norm_num) (by norm_num) hd hwork hworkcap hβ hβwork hB
  have htails:ExteriorPhysicalResidualTails 12 d c (canonicalRigidityBeta c)
      (9/32) (canonicalRigidityBeta c/256) 1 0:=
    source_high_moments_imply_exterior_tails 12 300 d c (canonicalRigidityBeta c)
      (9/32) (canonicalRigidityBeta c/256) hd hβ hβsmall (by positivity) hmom
  exact canonical_source_rigidity_of_residual_tails d c hd hc hc1 htails

theorem source_theorem_1_2_positive_rate (d:ℕ)(c:ℝ)(hd:3≤d)(hc:0<c)(hc1:c<1):
    ∃α:ℝ,0<α ∧∀D:ℕ,∀ᶠ N:ℕ in Filter.atTop,Nonempty (RegularGraph N d)→
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g ∧
          ¬SourceRigid hd α g)/
        eventMass (RegularGraph.weight (N:=N) (d:=d))
          (RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊)≤1/(N:ℝ)^D:=
  ⟨canonicalRigidityExponent c,canonicalRigidityExponent_pos c hc,source_theorem_1_2 d c hd hc hc1⟩

end SpectralConsequences
#print axioms SpectralConsequences.source_theorem_1_2
#print axioms SpectralConsequences.source_theorem_1_2_positive_rate
