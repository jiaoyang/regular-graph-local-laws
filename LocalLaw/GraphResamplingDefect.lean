import LocalLaw.BallResamplingMeasure
import LocalLaw.ClosureParameters
import LocalLaw.LocalSamplingAsymptotics

/-!
# Local defect transfer using the actual graph resampling kernel

The enlarged space, switching involution and marginal law are the constructed
ball-labelled kernel. Local two-stage estimates imply the actual graph
weak-to-strict defect via cavity averaging and the proved deterministic
closure. No stationarity, invertibility, event tightening, or final local-law
probability is requested as an additional axiom.
-/

open scoped BigOperators

namespace LocalLaw

/-- The actual selected log-log radius satisfies the kernel's numerical
sampling budget, uniformly in the spectral parameter, eventually. -/
theorem eventually_selected_resampling_budget (a d : ℕ) (hd : 3 ≤ d) (ha : 0 < a) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ z : ℂ,
      4 * (d + 1) ^ (actualCavityDepth a d N z - 1) ≤ N := by
  have hr := (lowerLogLogRadius_tendsto a d ha hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [hr, eventually_resampling_ball_budget a d hd] with N hr hbudget
  intro z
  have he := (actualCavityDepth_radius_bounds a d N z hr).2
  exact (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by omega : 0 < d + 1) he)).trans hbudget

/-- The actual source kernel at one center; `switchRadius` is the isolation
radius in its admissibility selector. All finite-data properties are proved
in BallResamplingMeasure and LocalResamplingInvolution. -/
noncomputable def selectedGraphResampling (N d a : ℕ) (z : ℂ) (o : Fin N)
    (switchRadius : ℕ) (hN : 0 < N) (hd : 0 < d)
    (hbudget : 4 * (d + 1) ^ (actualCavityDepth a d N z - 1) ≤ N) :
    ReversibleExtension (RegularGraph N d) (RegularGraph.weight (N := N) (d := d)) :=
  ballLabelledReversibleExtension N d o (actualCavityDepth a d N z - 1) switchRadius hN hd hbudget

/-- Graph-specific two-stage local defect theorem. First and second are the
source resampling estimates (Propositions 4.6 and 4.8). All reversible
probability transfer and certificate closure are conclusions here. -/
theorem actual_graph_resampling_defect (N d a r R ell switchRadius : ℕ) (z : ℂ)
    (hN : 0 < N) (hd : 0 < d) (hbudget : 4 * (d + 1) ^ ell ≤ N)
    (structural : RegularGraph N d → Prop)
    (D : ClosureBudget z (semicircleRoot z) (spectralScale z) (graphPaperError a d N r z))
    (intermediate : Fin N → RegularGraph N d → Prop) (α γ : Fin N → ℝ)
    (exceptional : ∀ g, structural g → (graphLocalLawFamily N d a r).weak z g →
      ∀ i ∈ nonTreeCenters g.graph R,
        ‖cavityAtVertex g.graph d z i - cavityIterate z (g.Q z) D.depth‖ ≤ D.exceptionalCavity)
    (absorption : ∀ g, structural g → (graphLocalLawFamily N d a r).weak z g →
      D.cavityError + (((nonTreeCenters g.graph R).card : ℝ) / (N : ℝ)) *
        D.exceptionalCavity ≤ graphPaperError a d N r z / D.L ^ 2)
    (first : ∀ o : Fin N,
      let E := ballLabelledReversibleExtension N d o ell switchRadius hN hd hbudget
      eventMass E.weight (fun ω =>
        (structural (E.project ω) ∧ (graphLocalLawFamily N d a r).weak z (E.project ω)) ∧
          ¬ intermediate o (E.project (E.switching ω))) ≤ α o)
    (second : ∀ o : Fin N,
      let E := ballLabelledReversibleExtension N d o ell switchRadius hN hd hbudget
      eventMass E.weight (fun ω => intermediate o (E.project ω) ∧
        ¬ CavityRowCertificate ((E.project (E.switching ω)).Q z) (semicircleRoot z) z
          (spectralScale z) (graphPaperError a d N r z) D
          ((E.project (E.switching ω)).G z) (fun w => (E.project (E.switching ω)).P r z w)
          (cavityAtVertex (E.project (E.switching ω)).graph d z)
          (nonTreeCenters (E.project (E.switching ω)).graph R) o) ≤ γ o) :
    eventMass (RegularGraph.weight (N := N) (d := d)) (fun g => structural g ∧
      (graphLocalLawFamily N d a r).weak z g ∧ ¬ (graphLocalLawFamily N d a r).strict z g) ≤
      ∑ o : Fin N, (α o + γ o) := by
  classical
  let A : RegularGraph N d → Prop := fun g => structural g ∧ (graphLocalLawFamily N d a r).weak z g
  let H : RegularGraph N d → Prop := fun g => (graphLocalLawFamily N d a r).strict z g
  let C : Fin N → RegularGraph N d → Prop := fun o g =>
    CavityRowCertificate (g.Q z) (semicircleRoot z) z (spectralScale z)
      (graphPaperError a d N r z) D (g.G z) (fun w => g.P r z w)
      (cavityAtVertex g.graph d z) (nonTreeCenters g.graph R) o
  have hclose : ∀ g, A g → (∀ o ∈ (Finset.univ : Finset (Fin N)), C o g) → H g := by
    intro g hg hcert
    apply actual_local_certificate_closure (g.Q z) (semicircleRoot z) z (spectralScale z)
      (graphPaperError a d N r z) D (g.G z) (fun w => g.P r z w)
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
    exact projected_reversible_two_stage RegularGraph.weight E.weight E.nonnegative E.project
      E.marginal E.switching E.preserve E.involution A (intermediate o) (C o) (α o) (γ o)
      (first o) (second o)
  have hh := certificate_defect_mass RegularGraph.weight RegularGraph.weight_nonnegative
    (Finset.univ : Finset (Fin N)) A H C (fun o => α o + γ o) hclose (fun o _ => hsite o)
  simpa only [A, H, and_assoc] using hh

/-- The union over actual graph centers costs one exponent, with the exact
finite cardinality N derived by Lean. -/
theorem actual_graph_resampling_defect_polynomial (N d a r R ell switchRadius q : ℕ)
    (z : ℂ) (hN : 0 < N) (hd : 0 < d) (hbudget : 4 * (d + 1) ^ ell ≤ N)
    (structural : RegularGraph N d → Prop)
    (D : ClosureBudget z (semicircleRoot z) (spectralScale z) (graphPaperError a d N r z))
    (intermediate : Fin N → RegularGraph N d → Prop) (α γ : Fin N → ℝ)
    (exceptional : ∀ g, structural g → (graphLocalLawFamily N d a r).weak z g →
      ∀ i ∈ nonTreeCenters g.graph R,
        ‖cavityAtVertex g.graph d z i - cavityIterate z (g.Q z) D.depth‖ ≤ D.exceptionalCavity)
    (absorption : ∀ g, structural g → (graphLocalLawFamily N d a r).weak z g →
      D.cavityError + (((nonTreeCenters g.graph R).card : ℝ) / (N : ℝ)) *
        D.exceptionalCavity ≤ graphPaperError a d N r z / D.L ^ 2)
    (first : ∀ o : Fin N,
      let E := ballLabelledReversibleExtension N d o ell switchRadius hN hd hbudget
      eventMass E.weight (fun ω =>
        (structural (E.project ω) ∧ (graphLocalLawFamily N d a r).weak z (E.project ω)) ∧
          ¬ intermediate o (E.project (E.switching ω))) ≤ α o)
    (second : ∀ o : Fin N,
      let E := ballLabelledReversibleExtension N d o ell switchRadius hN hd hbudget
      eventMass E.weight (fun ω => intermediate o (E.project ω) ∧
        ¬ CavityRowCertificate ((E.project (E.switching ω)).Q z) (semicircleRoot z) z
          (spectralScale z) (graphPaperError a d N r z) D
          ((E.project (E.switching ω)).G z) (fun w => (E.project (E.switching ω)).P r z w)
          (cavityAtVertex (E.project (E.switching ω)).graph d z)
          (nonTreeCenters (E.project (E.switching ω)).graph R) o) ≤ γ o)
    (C₀ : ℝ) (hq : 1 ≤ q) (hα : ∀ o, α o ≤ C₀ / (N : ℝ) ^ q)
    (hγ : ∀ o, γ o ≤ C₀ / (N : ℝ) ^ q) :
    eventMass (RegularGraph.weight (N := N) (d := d)) (fun g => structural g ∧
      (graphLocalLawFamily N d a r).weak z g ∧ ¬ (graphLocalLawFamily N d a r).strict z g) ≤
      2 * C₀ / (N : ℝ) ^ (q - 1) := by
  have hbase := actual_graph_resampling_defect N d a r R ell switchRadius z hN hd hbudget
    structural D intermediate α γ exceptional absorption first second
  have hn : (N : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hN)
  have hp : (N : ℝ) ^ q = (N : ℝ) ^ (q - 1) * (N : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  apply hbase.trans
  calc
    (∑ o : Fin N, (α o + γ o)) ≤ ∑ _o : Fin N, (2 * C₀ / (N : ℝ) ^ q) :=
      Finset.sum_le_sum (fun o _ => by
        calc
          α o + γ o ≤ C₀ / (N : ℝ) ^ q + C₀ / (N : ℝ) ^ q := add_le_add (hα o) (hγ o)
          _ = _ := by ring)
    _ = (N : ℝ) * (2 * C₀ / (N : ℝ) ^ q) := by simp [nsmul_eq_mul]
    _ = 2 * C₀ / (N : ℝ) ^ (q - 1) := by rw [hp]; field_simp [hn]; ring

end LocalLaw
