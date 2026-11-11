import SpectralConsequences.OriginalExteriorProbability
import SpectralConsequences.ConditionalRigidityAssembly

/-! # Intermediate source rigidity reduction to the physical Section 7 tails

This intermediate reduction combines counting, original conditioning,
exterior stability, the finite spectral mesh and quantile inversion, taking
tails of the two genuine physical fluctuations as explicit hypotheses.
`SourceActualHighMoments` and `SourceMomentTailBridge` prove those tails;
`SourceTheorem12` applies this reduction to obtain the source rigidity theorem.
-/
open Filter
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceRigidityReductionDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem source_rigidity_original_of_residual_tails (a b d:ℕ)
    (cOriginal β γ e K:ℝ) (p:ℕ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<cOriginal) (hc1:cOriginal<1)
    (hβ:0<β) (hβwork:β≤exteriorWorkParameter cOriginal/32) (hβsmall:β≤1/128)
    (hγ:9/32≤γ) (he:0≤e) (heβ:e<β/16) (hK:1≤K)
    (htails:ExteriorPhysicalResidualTails a d cOriginal β γ e K p):
    ∀D:ℕ,∀ᶠ N:ℕ in atTop,Nonempty (RegularGraph N d)→
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        RegularGraph.structural (logarithmicRadius (cOriginal/4) d N) (finiteOmega d)
          ⌊(N:ℝ)^cOriginal⌋₊ g ∧ ¬SourceRigid hd (β/32) g)/
        eventMass (RegularGraph.weight (N:=N) (d:=d))
          (RegularGraph.structural (logarithmicRadius (cOriginal/4) d N) (finiteOmega d)
            ⌊(N:ℝ)^cOriginal⌋₊)≤1/(N:ℝ)^D := by
  have hβc:β≤cOriginal/32:=by
    have ha:exteriorAuxParameter cOriginal≤cOriginal/2:=min_le_left _ _
    have hw:exteriorWorkParameter cOriginal=exteriorAuxParameter cOriginal/4:=rfl
    rw [hw] at hβwork
    linarith
  apply conditional_rigidity_assembly d (a:ℝ) (b:ℝ) cOriginal β hd
    (by exact_mod_cast ha) (by exact_mod_cast hb) hc hc1 hβ hβc
  exact source_confinement_original_of_residual_tails a b d cOriginal β γ e K p
    ha hb hd hc hc1 hβ hβwork hβsmall hγ he heβ hK htails

/-- One fixed source mesoscopic exponent, chosen strictly inside every work
and exterior margin. -/
def canonicalRigidityBeta (cOriginal:ℝ):ℝ:=exteriorAuxParameter cOriginal/256

/-- The positive ordered-eigenvalue exponent delivered by the completed
counting and confinement reductions. -/
def canonicalRigidityExponent (cOriginal:ℝ):ℝ:=canonicalRigidityBeta cOriginal/32

theorem canonicalRigidityBeta_pos (cOriginal:ℝ) (hc:0<cOriginal):
    0<canonicalRigidityBeta cOriginal:=by
  have hh:0<exteriorAuxParameter cOriginal:=lt_min (by linarith) (by norm_num)
  exact div_pos hh (by norm_num)

theorem canonicalRigidityExponent_pos (cOriginal:ℝ) (hc:0<cOriginal):
    0<canonicalRigidityExponent cOriginal:=
  div_pos (canonicalRigidityBeta_pos cOriginal hc) (by norm_num)

/-- All finite numerical parameter inequalities for the canonical choice;
none are deferred to a source certificate. -/
theorem canonicalRigidity_parameters (cOriginal:ℝ) (hc:0<cOriginal):
    0<canonicalRigidityBeta cOriginal ∧
    canonicalRigidityBeta cOriginal≤exteriorWorkParameter cOriginal/32 ∧
    canonicalRigidityBeta cOriginal≤1/128 ∧
    0≤canonicalRigidityBeta cOriginal/256 ∧
    canonicalRigidityBeta cOriginal/256<canonicalRigidityBeta cOriginal/16 := by
  have hpos:=canonicalRigidityBeta_pos cOriginal hc
  have haux:0<exteriorAuxParameter cOriginal:=lt_min (by linarith) (by norm_num)
  have hauxcap:exteriorAuxParameter cOriginal≤1/4:=min_le_right _ _
  refine ⟨hpos,?_,?_,by positivity,by linarith⟩
  · dsimp only [canonicalRigidityBeta,exteriorWorkParameter]
    linarith
  · dsimp only [canonicalRigidityBeta]
    linarith

/-- Canonical intermediate reduction. Its sole probabilistic hypothesis is
exactly the two physical residual tails, at a=12, b=300 and the displayed
fixed parameters. The original structural denominator is retained. -/
theorem canonical_source_rigidity_of_residual_tails (d:ℕ) (cOriginal:ℝ)
    (hd:3≤d) (hc:0<cOriginal) (hc1:cOriginal<1)
    (htails:ExteriorPhysicalResidualTails 12 d cOriginal (canonicalRigidityBeta cOriginal)
      (9/32) (canonicalRigidityBeta cOriginal/256) 1 0):
    ∀D:ℕ,∀ᶠ N:ℕ in atTop,Nonempty (RegularGraph N d)→
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        RegularGraph.structural (logarithmicRadius (cOriginal/4) d N) (finiteOmega d)
          ⌊(N:ℝ)^cOriginal⌋₊ g ∧ ¬SourceRigid hd (canonicalRigidityExponent cOriginal) g)/
        eventMass (RegularGraph.weight (N:=N) (d:=d))
          (RegularGraph.structural (logarithmicRadius (cOriginal/4) d N) (finiteOmega d)
            ⌊(N:ℝ)^cOriginal⌋₊)≤1/(N:ℝ)^D := by
  obtain ⟨hβ,hβwork,hβsmall,he,heβ⟩:=canonicalRigidity_parameters cOriginal hc
  exact source_rigidity_original_of_residual_tails 12 300 d cOriginal
    (canonicalRigidityBeta cOriginal) (9/32) (canonicalRigidityBeta cOriginal/256) 1 0
    (by norm_num) (by norm_num) hd hc hc1 hβ hβwork hβsmall (by norm_num)
    he heβ (by norm_num) htails

end SpectralConsequences
