import LocalLaw.SourceStrongDefectReduction

/-! # The first-stage estimate as an actual finite-kernel interface

This module defines the first-stage hypotheses used by the bootstrap
reductions. `SourceFirstStageProof` proves the all-polynomial estimate.
-/

noncomputable section
namespace LocalLaw
local instance sourceFirstStageInterfaceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceFirstStageFailureMass (a d N Cq : ℕ) (c β γ C1 : ℝ) (o : Fin N) (z : ℂ) : ℝ :=
  let R := logarithmicRadius (c / 4) d N
  let rn := logarithmicRadius β d N
  let r := effectiveModelRadius a d N β
  let ell := actualCavityDepth a d N z - 1
  eventMass (ballLabelledWeight N d o ell) (fun ξ =>
    (RegularGraph.offsetStructural R (finiteOmega d) 1 ⌊(N : ℝ) ^ γ⌋₊ (ballLabelledProject ξ) ∧
      (graphLocalLawFamilyWithRadii N d a r rn).weak z (ballLabelledProject ξ)) ∧
    ¬(ballLabelledProject (ballLabelledResample N d (R / 4) ξ)).SourceOmegaPlusWithRadii
      a r rn R ell (finiteOmega d) Cq ⌊(N : ℝ) ^ γ⌋₊ C1 o z)

def SourceFirstStageEstimate (a b d p Cq : ℕ) (c β γ B C1 : ℝ) : Prop :=
  ∀ᶠ N : ℕ in Filter.atTop, ∀ (o : Fin N) (z : ℂ),
    0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      sourceFirstStageFailureMass a d N Cq c β γ C1 o z ≤ 1 / (N : ℝ) ^ p

def SourceFirstStageAllPowers (a b d : ℕ) (c β γ B : ℝ) : Prop :=
  ∀ p : ℕ, ∃ (Cq : ℕ) (C1 : ℝ), finiteOmega d ≤ Cq ∧ 1 ≤ C1 ∧
    sourceDeletionConstant d β B ≤ C1 ∧ SourceFirstStageEstimate a b d p Cq c β γ B C1

end LocalLaw
