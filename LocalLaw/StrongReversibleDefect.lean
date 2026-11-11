import LocalLaw.ReversibleTargetRestriction
import LocalLaw.StrongCertificateClosure

/-! # Actual target-restricted resampling defect with strong scalar closure -/

open scoped BigOperators
namespace LocalLaw

theorem actual_strong_graph_resampling_defect_restricted (N d a rModel rError R ell switchRadius : ℕ) (z : ℂ)
    (hN : 0 < N) (hd : 0 < d) (hbudget : 4 * (d + 1) ^ ell ≤ N)
    (structural : RegularGraph N d → Prop)
    (D : StrongClosureBudget z (semicircleRoot z) (spectralScale z) (graphPaperError a d N rError z))
    (intermediate : Fin N → RegularGraph N d → Prop) (α γ : Fin N → ℝ)
    (exceptional : ∀ g, structural g → (graphLocalLawFamilyWithRadii N d a rModel rError).weak z g →
      ∀ i ∈ nonTreeCenters g.graph R,
        ‖cavityAtVertex g.graph d z i - cavityIterate z (g.Q z) D.depth‖ ≤ D.exceptionalCavity)
    (absorption : ∀ g, structural g → (graphLocalLawFamilyWithRadii N d a rModel rError).weak z g →
      D.cavityError + (((nonTreeCenters g.graph R).card : ℝ) / (N : ℝ)) *
        D.exceptionalCavity ≤ D.residualConstant * graphPaperError a d N rError z / D.L ^ 4)
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
        ¬ StrongCavityRowCertificate ((E.project (E.switching ω)).Q z) (semicircleRoot z) z
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
    StrongCavityRowCertificate (g.Q z) (semicircleRoot z) z (spectralScale z)
      (graphPaperError a d N rError z) D (g.G z) (fun w => g.P rModel z w)
      (cavityAtVertex g.graph d z) (nonTreeCenters g.graph R) o
  have hclose : ∀ g, A g → (∀ o ∈ (Finset.univ : Finset (Fin N)), C o g) → H g := by
    intro g hg hcert
    apply actual_strong_local_certificate_closure (g.Q z) (semicircleRoot z) z (spectralScale z)
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
