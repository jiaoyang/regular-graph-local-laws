import LocalLaw.SourceSpectralEvents

/-!
# Independent finite-model and nominal error radii

The internal neighborhood radius can be shortened while every paper error,
inflation branch, scalar stability scale and source tolerance remains at its
nominal radius. This interface supports endpoint geometry without comparing
different discontinuously inflated paper errors. Equal radii recover all
previous source events exactly.
-/

noncomputable section
namespace LocalLaw
local instance independentRadiusEventsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def graphLocalLawFamilyWithRadii (N d a rModel rError : ℕ) :
    LocalLawFamily (RegularGraph N d) (Fin N) :=
  { graphLocalLawFamily N d a rModel with ε := graphPaperError a d N rError }

@[simp] theorem graphLocalLawFamilyWithRadii_diagonal (N d a r : ℕ) :
    graphLocalLawFamilyWithRadii N d a r r = graphLocalLawFamily N d a r := rfl

namespace RegularGraph
variable {N d : ℕ}

def SourceOmegaWithRadii (g : RegularGraph N d) (a rModel rError R ω badCount : ℕ) (z : ℂ) : Prop :=
  structural R ω badCount g ∧ (graphLocalLawFamilyWithRadii N d a rModel rError).weak z g

def SourceOmegaMinusWithRadii (g : RegularGraph N d) (a rModel rError R ω badCount : ℕ) (z : ℂ) : Prop :=
  structural R ω badCount g ∧ (graphLocalLawFamilyWithRadii N d a rModel rError).strict z g

structure SourceOmegaPlusWithRadii (g : RegularGraph N d)
    (a rModel rError R ell ω Cq badCount : ℕ) (C1 : ℝ) (o : Fin N) (z : ℂ) : Prop where
  structural : g.SourceStructuralPlus R ω Cq badCount
  cavity : ‖g.Q z - semicircleRoot z‖ ≤ C1 * g.sourceScale a rError z
  full : ∀ i j, ‖g.G z i j - g.P rModel z (g.Q z) i j‖ ≤ C1 / Real.log (N : ℝ)
  deleted : let T := graphBallVertices g.graph o ell
    ∀ i j : (Tᶜ : Set (Fin N)),
      ‖(g.deficient.delete T).G z i j - g.deletedP T rModel z (g.Q z) i j‖ ≤
        C1 * g.sourcePrime a rError z

structure SourceOmegaMinusLocalWithRadii (g : RegularGraph N d)
    (a rModel rError R ell : ℕ) (C2 : ℝ) (o : Fin N) (z : ℂ) : Prop where
  cavity : ‖g.Q z - semicircleRoot z‖ ≤ C2 * g.sourceScale a rError z
  rowInside : ∀ i ∈ graphBallVertices g.graph o ell,
    ‖g.G z o i - g.P rModel z (g.Q z) o i‖ ≤ g.sourceInsideRowBudget a rError ell C2 o i z
  rowOutside : ∀ i ∉ graphBallVertices g.graph o ell,
    ‖g.G z o i - g.P rModel z (g.Q z) o i‖ ≤ g.sourceOutsideRowBudget a rError ell C2 z
  localCavity : (graphBall g.graph o R).IsTree →
    g.sourceCavityAbsoluteResidual ell o z ≤
      C2 * (Real.log (N : ℝ) * g.sourcePrime a rError z / resamplingDecayDenominator d ell)

@[simp] theorem SourceOmegaWithRadii_diagonal (g : RegularGraph N d) (a r R ω badCount : ℕ) (z : ℂ) :
    g.SourceOmegaWithRadii a r r R ω badCount z ↔ g.SourceOmega a r R ω badCount z := Iff.rfl

@[simp] theorem SourceOmegaMinusWithRadii_diagonal (g : RegularGraph N d) (a r R ω badCount : ℕ) (z : ℂ) :
    g.SourceOmegaMinusWithRadii a r r R ω badCount z ↔ g.SourceOmegaMinus a r R ω badCount z := Iff.rfl

@[simp] theorem SourceOmegaPlusWithRadii_diagonal (g : RegularGraph N d)
    (a r R ell ω Cq badCount : ℕ) (C1 : ℝ) (o : Fin N) (z : ℂ) :
    g.SourceOmegaPlusWithRadii a r r R ell ω Cq badCount C1 o z ↔
      g.SourceOmegaPlus a r R ell ω Cq badCount C1 o z := by
  constructor <;> intro h
  · exact ⟨h.structural, h.cavity, h.full, h.deleted⟩
  · exact ⟨h.structural, h.cavity, h.full, h.deleted⟩

@[simp] theorem SourceOmegaMinusLocalWithRadii_diagonal (g : RegularGraph N d)
    (a r R ell : ℕ) (C2 : ℝ) (o : Fin N) (z : ℂ) :
    g.SourceOmegaMinusLocalWithRadii a r r R ell C2 o z ↔ g.SourceOmegaMinusLocal a r R ell C2 o z := by
  constructor <;> intro h
  · exact ⟨h.cavity, h.rowInside, h.rowOutside, h.localCavity⟩
  · exact ⟨h.cavity, h.rowInside, h.rowOutside, h.localCavity⟩

end RegularGraph
end LocalLaw
