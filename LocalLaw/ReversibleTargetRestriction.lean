import LocalLaw.GraphResamplingDefect
import LocalLaw.IndependentRadiusEvents

/-!
# Retain the original target event in the reversible second stage

The strict-event defect is already restricted to the original structural and
weak event A. Reversibility keeps that same condition on the second-stage
target at no probability cost. Thus the local improvement needs to be proved
only where the target weak prior and original structural geometry hold.
-/

open scoped BigOperators
namespace LocalLaw

/-- The second stage may retain exactly the original target condition. -/
theorem reversible_two_stage_restricted {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (φ : Equiv.Perm Ω)
    (hwφ : ∀ x, w (φ x) = w x) (hφ : Function.Involutive φ)
    (A B C : Ω → Prop) (δ₁ δ₂ : ℝ)
    (h₁ : eventMass w (fun x => A x ∧ ¬B (φ x)) ≤ δ₁)
    (h₂ : eventMass w (fun x => B x ∧ A (φ x) ∧ ¬C (φ x)) ≤ δ₂) :
    eventMass w (fun x => A x ∧ ¬C x) ≤ δ₁ + δ₂ := by
  classical
  have hh := reversible_two_stage w hw φ hwφ hφ A B (fun x => A x → C x) δ₁ δ₂ h₁
    (by simpa only [_root_.not_imp] using h₂)
  simpa only [_root_.not_imp, and_self_left] using hh

/-- Actual enlarged-space projection with the retained target event. -/
theorem projected_reversible_two_stage_restricted {X Ω : Type*} [Fintype X] [Fintype Ω]
    (w : X → ℝ) (ν : Ω → ℝ) (hν : ∀ ω, 0 ≤ ν ω) (π : Ω → X)
    (marginal : ∀ P : X → Prop, eventMass ν (fun ω => P (π ω)) = eventMass w P)
    (τ : Equiv.Perm Ω) (preserve : ∀ ω, ν (τ ω) = ν ω) (involution : Function.Involutive τ)
    (A B C : X → Prop) (α γ : ℝ)
    (first : eventMass ν (fun ω => A (π ω) ∧ ¬B (π (τ ω))) ≤ α)
    (second : eventMass ν (fun ω => B (π ω) ∧ A (π (τ ω)) ∧ ¬C (π (τ ω))) ≤ γ) :
    eventMass w (fun x => A x ∧ ¬C x) ≤ α + γ := by
  rw [← marginal (fun x => A x ∧ ¬C x)]
  exact reversible_two_stage_restricted ν hν τ preserve involution
    (fun ω => A (π ω)) (fun ω => B (π ω)) (fun ω => C (π ω)) α γ first second

/-- Actual graph-kernel defect at independent model/error radii. The source
local estimates retain the original weak/structural target condition. -/
theorem actual_graph_resampling_defect_with_radii_restricted (N d a rModel rError R ell switchRadius : ℕ) (z : ℂ)
    (hN : 0 < N) (hd : 0 < d) (hbudget : 4 * (d + 1) ^ ell ≤ N)
    (structural : RegularGraph N d → Prop)
    (D : ClosureBudget z (semicircleRoot z) (spectralScale z) (graphPaperError a d N rError z))
    (intermediate : Fin N → RegularGraph N d → Prop) (α γ : Fin N → ℝ)
    (exceptional : ∀ g, structural g → (graphLocalLawFamilyWithRadii N d a rModel rError).weak z g →
      ∀ i ∈ nonTreeCenters g.graph R,
        ‖cavityAtVertex g.graph d z i - cavityIterate z (g.Q z) D.depth‖ ≤ D.exceptionalCavity)
    (absorption : ∀ g, structural g → (graphLocalLawFamilyWithRadii N d a rModel rError).weak z g →
      D.cavityError + (((nonTreeCenters g.graph R).card : ℝ) / (N : ℝ)) *
        D.exceptionalCavity ≤ graphPaperError a d N rError z / D.L ^ 2)
    (first : ∀ o : Fin N,
      let E := ballLabelledReversibleExtension N d o ell switchRadius hN hd hbudget
      eventMass E.weight (fun ω =>
        (structural (E.project ω) ∧ (graphLocalLawFamilyWithRadii N d a rModel rError).weak z (E.project ω)) ∧
          ¬ intermediate o (E.project (E.switching ω))) ≤ α o)
    (second : ∀ o : Fin N,
      let E := ballLabelledReversibleExtension N d o ell switchRadius hN hd hbudget
      eventMass E.weight (fun ω => intermediate o (E.project ω) ∧
        (structural (E.project (E.switching ω)) ∧
          (graphLocalLawFamilyWithRadii N d a rModel rError).weak z (E.project (E.switching ω))) ∧
        ¬ CavityRowCertificate ((E.project (E.switching ω)).Q z) (semicircleRoot z) z
          (spectralScale z) (graphPaperError a d N rError z) D
          ((E.project (E.switching ω)).G z) (fun w => (E.project (E.switching ω)).P rModel z w)
          (cavityAtVertex (E.project (E.switching ω)).graph d z)
          (nonTreeCenters (E.project (E.switching ω)).graph R) o) ≤ γ o) :
    eventMass (RegularGraph.weight (N := N) (d := d)) (fun g => structural g ∧
      (graphLocalLawFamilyWithRadii N d a rModel rError).weak z g ∧ ¬ (graphLocalLawFamilyWithRadii N d a rModel rError).strict z g) ≤
      ∑ o : Fin N, (α o + γ o) := by
  classical
  let A : RegularGraph N d → Prop := fun g => structural g ∧ (graphLocalLawFamilyWithRadii N d a rModel rError).weak z g
  let H : RegularGraph N d → Prop := fun g => (graphLocalLawFamilyWithRadii N d a rModel rError).strict z g
  let C : Fin N → RegularGraph N d → Prop := fun o g =>
    CavityRowCertificate (g.Q z) (semicircleRoot z) z (spectralScale z)
      (graphPaperError a d N rError z) D (g.G z) (fun w => g.P rModel z w)
      (cavityAtVertex g.graph d z) (nonTreeCenters g.graph R) o
  have hclose : ∀ g, A g → (∀ o ∈ (Finset.univ : Finset (Fin N)), C o g) → H g := by
    intro g hg hcert
    apply actual_local_certificate_closure (g.Q z) (semicircleRoot z) z (spectralScale z)
      (graphPaperError a d N rError z) D (g.G z) (fun w => g.P rModel z w)
      (cavityAtVertex g.graph d z) (nonTreeCenters g.graph R)
      (by simpa only [Fintype.card_fin] using hN)
    · simpa only [RegularGraph.Q, Fintype.card_fin] using cavityAverage_eq_mean g.graph d z
    · exact exceptional g hg.1 hg.2
    · simpa only [Fintype.card_fin] using absorption g hg.1 hg.2
    · exact hg.2
    · exact fun o => hcert o (Finset.mem_univ _)
  have hsite : ∀ o, eventMass RegularGraph.weight (fun g => A g ∧ ¬ C o g) ≤ α o + γ o := by
    intro o
    let E := ballLabelledReversibleExtension N d o ell switchRadius hN hd hbudget
    exact projected_reversible_two_stage_restricted RegularGraph.weight E.weight E.nonnegative E.project
      E.marginal E.switching E.preserve E.involution A (intermediate o) (C o) (α o) (γ o)
      (first o) (second o)
  have hh := certificate_defect_mass RegularGraph.weight RegularGraph.weight_nonnegative
    (Finset.univ : Finset (Fin N)) A H C (fun o => α o + γ o) hclose (fun o _ => hsite o)
  simpa only [A, H, and_assoc] using hh

end LocalLaw
