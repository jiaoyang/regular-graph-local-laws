import LocalLaw.IndependentRadiusForest
import LocalLaw.GraphBootstrap

/-!
# Actual continuum bootstrap with separate model and nominal error radii

The ordered forest and nominal numerical mesh are constructed. Only the
physical exterior anchor and one-point local defect estimate remain as
analytic inputs; all continuum transport and polynomial union costs are
proved for the internal-radius model and unchanged nominal paper budget.
-/

open scoped BigOperators
namespace LocalLaw
theorem actual_graph_bounded_bootstrapWithRadii (N d a b rModel rError : ℕ) (B δ : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (structural : RegularGraph N d → Prop)
    (mesh : UniformGraphMesh N d a rError (boundedLocalLawDomain N b (2 * B))
      (2 / (N : ℝ) ^ 12))
    (anchor : ∀ E : ℝ, |E| ≤ B → ∀ g, structural g →
      (graphLocalLawFamilyWithRadii N d a rModel rError).weak (⟨E, B⟩ : ℂ) g)
    (localDefect : ∀ z ∈ boundedLocalLawDomain N b (2 * B),
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        structural g ∧ (graphLocalLawFamilyWithRadii N d a rModel rError).weak z g ∧
          ¬ (graphLocalLawFamilyWithRadii N d a rModel rError).strict z g) ≤ δ) :
    eventMass (RegularGraph.weight (N := N) (d := d)) (fun g => structural g ∧
      ¬ ∀ z ∈ boundedLocalLawDomain N b B, (graphLocalLawFamilyWithRadii N d a rModel rError).weak z g) ≤
      bootstrapGridConstant B * (N : ℝ) ^ 36 * δ := by
  classical
  obtain ⟨T, node, hT, hnode, htransport, hcover⟩ :=
    bounded_graph_ordered_forestWithRadii N d a b rModel rError B hB structural mesh anchor
  let A : Fin T → RegularGraph N d → Prop := fun t g =>
    structural g ∧ (graphLocalLawFamilyWithRadii N d a rModel rError).weak (node t) g
  let H : Fin T → RegularGraph N d → Prop := fun t g =>
    (graphLocalLawFamilyWithRadii N d a rModel rError).strict (node t) g
  have hfinite := ordered_bootstrap_mass RegularGraph.weight RegularGraph.weight_nonnegative
    structural A H (by
      intro t g hg previous
      exact ⟨hg, htransport t g hg previous⟩) (fun _ => δ) (by
      intro t
      simpa only [A, H, and_assoc] using localDefect (node t) (hnode t))
  calc
    _ ≤ eventMass RegularGraph.weight (fun g => structural g ∧ ¬ ∀ t, H t g) :=
      eventMass_mono _ RegularGraph.weight_nonnegative (by
        intro g hg
        exact ⟨hg.1, fun hall => hg.2 (hcover g hg.1 hall)⟩)
    _ ≤ ∑ _t : Fin T, δ := hfinite
    _ = (T : ℝ) * δ := by simp [nsmul_eq_mul]
    _ ≤ bootstrapGridConstant B * (N : ℝ) ^ 36 * δ :=
      mul_le_mul_of_nonneg_right hT hδ

/-- A local defect of size D/N^q loses exactly the proved 36 net exponents.
A separate union over N resampling centers is accounted for in the local q. -/
theorem actual_graph_bounded_bootstrap_polynomialWithRadii (N d a b rModel rError q : ℕ) (B D : ℝ)
    (hq : 36 ≤ q) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (structural : RegularGraph N d → Prop)
    (mesh : UniformGraphMesh N d a rError (boundedLocalLawDomain N b (2 * B))
      (2 / (N : ℝ) ^ 12))
    (anchor : ∀ E : ℝ, |E| ≤ B → ∀ g, structural g →
      (graphLocalLawFamilyWithRadii N d a rModel rError).weak (⟨E, B⟩ : ℂ) g)
    (localDefect : ∀ z ∈ boundedLocalLawDomain N b (2 * B),
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        structural g ∧ (graphLocalLawFamilyWithRadii N d a rModel rError).weak z g ∧
          ¬ (graphLocalLawFamilyWithRadii N d a rModel rError).strict z g) ≤ D / (N : ℝ) ^ q) :
    eventMass (RegularGraph.weight (N := N) (d := d)) (fun g => structural g ∧
      ¬ ∀ z ∈ boundedLocalLawDomain N b B, (graphLocalLawFamilyWithRadii N d a rModel rError).weak z g) ≤
      bootstrapGridConstant B * D / (N : ℝ) ^ (q - 36) := by
  have hN : (N : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr mesh.vertexPositive)
  have hp : (N : ℝ) ^ q = (N : ℝ) ^ (q - 36) * (N : ℝ) ^ 36 := by
    rw [← pow_add]
    congr 1
    omega
  have h := actual_graph_bounded_bootstrapWithRadii N d a b rModel rError B (D / (N : ℝ) ^ q)
    hB (by positivity) structural mesh anchor localDefect
  apply h.trans_eq
  rw [hp]
  field_simp [hN]
  ring

/-- The conditional uniform-structural law retains its actual denominator;
the familiar factor two follows only from the separate mass lower bound. -/
theorem actual_graph_bounded_bootstrap_conditionalWithRadii (N d a b rModel rError q : ℕ) (B D : ℝ)
    (hq : 36 ≤ q) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (structural : RegularGraph N d → Prop)
    (mesh : UniformGraphMesh N d a rError (boundedLocalLawDomain N b (2 * B))
      (2 / (N : ℝ) ^ 12))
    (anchor : ∀ E : ℝ, |E| ≤ B → ∀ g, structural g →
      (graphLocalLawFamilyWithRadii N d a rModel rError).weak (⟨E, B⟩ : ℂ) g)
    (localDefect : ∀ z ∈ boundedLocalLawDomain N b (2 * B),
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        structural g ∧ (graphLocalLawFamilyWithRadii N d a rModel rError).weak z g ∧
          ¬ (graphLocalLawFamilyWithRadii N d a rModel rError).strict z g) ≤ D / (N : ℝ) ^ q)
    (mass : 1 / 2 ≤ eventMass (RegularGraph.weight (N := N) (d := d)) structural) :
    eventMass (RegularGraph.weight (N := N) (d := d)) (fun g => structural g ∧
      ¬ ∀ z ∈ boundedLocalLawDomain N b B, (graphLocalLawFamilyWithRadii N d a rModel rError).weak z g) /
        eventMass (RegularGraph.weight (N := N) (d := d)) structural ≤
      2 * bootstrapGridConstant B * D / (N : ℝ) ^ (q - 36) := by
  have h := actual_graph_bounded_bootstrap_polynomialWithRadii N d a b rModel rError q B D hq hB hD
    structural mesh anchor localDefect
  have hC : 0 ≤ bootstrapGridConstant B := by unfold bootstrapGridConstant; positivity
  have hbudget : 0 ≤ bootstrapGridConstant B * D / (N : ℝ) ^ (q - 36) := by positivity
  have hh := conditional_budget_factor_two _ _ _ hbudget mass h
  convert hh using 1
  ring

/-- The original logarithmic parameters eventually discharge every mesh and
net hypothesis in the continuum bootstrap. -/
theorem eventually_actual_graph_bounded_bootstrapWithRadii (a b d q : ℕ) (β B D : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hq : 36 ≤ q)
    (hβ : 0 < β) (hβ₁ : β ≤ 1) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ rModel : ℕ, ∀ structural : RegularGraph N d → Prop,
      (∀ E : ℝ, |E| ≤ B → ∀ g, structural g →
        (graphLocalLawFamilyWithRadii N d a rModel (logarithmicRadius β d N)).weak (⟨E, B⟩ : ℂ) g) →
      (∀ z ∈ boundedLocalLawDomain N b (2 * B),
        eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
          structural g ∧ (graphLocalLawFamilyWithRadii N d a rModel (logarithmicRadius β d N)).weak z g ∧
            ¬ (graphLocalLawFamilyWithRadii N d a rModel (logarithmicRadius β d N)).strict z g) ≤
          D / (N : ℝ) ^ q) →
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g => structural g ∧
        ¬ ∀ z ∈ boundedLocalLawDomain N b B,
          (graphLocalLawFamilyWithRadii N d a rModel (logarithmicRadius β d N)).weak z g) ≤
        bootstrapGridConstant B * D / (N : ℝ) ^ (q - 36) := by
  filter_upwards [eventually_polynomial_graph_mesh a b d β (2 * B) ha hb hd hβ hβ₁
    (by positivity)] with N hmesh
  intro rModel structural anchor localDefect
  exact actual_graph_bounded_bootstrap_polynomialWithRadii N d a b rModel _ q B D hq hB hD structural
    (Classical.choice hmesh) anchor localDefect

end LocalLaw
