import LocalLaw.BoundedVerticalForest

/-!
# The actual bounded-domain spectral bootstrap

The paper's error and integer radius are used directly. The finite ordered
forest is constructed, rather than requested as input. A pointwise local
weak-to-strict probability estimate and the exterior weak anchor yield the
simultaneous continuum weak event, with an explicit polynomial union cost.
The remaining local defect estimate is the substance of Proposition 4.12.
-/

open scoped BigOperators

namespace LocalLaw

noncomputable def bootstrapGridConstant (B : ℝ) : ℝ :=
  2 * (2 * B + 2) * (B + 2) ^ 2

/-- Actual finite-N continuum bootstrap. The input is only the local defect
probability at a single spectral point, not the simultaneous conclusion. -/
theorem actual_graph_bounded_bootstrap (N d a b r : ℕ) (B δ : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (structural : RegularGraph N d → Prop)
    (mesh : UniformGraphMesh N d a r (boundedLocalLawDomain N b (2 * B))
      (2 / (N : ℝ) ^ 12))
    (anchor : ∀ E : ℝ, |E| ≤ B → ∀ g, structural g →
      (graphLocalLawFamily N d a r).weak (⟨E, B⟩ : ℂ) g)
    (localDefect : ∀ z ∈ boundedLocalLawDomain N b (2 * B),
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        structural g ∧ (graphLocalLawFamily N d a r).weak z g ∧
          ¬ (graphLocalLawFamily N d a r).strict z g) ≤ δ) :
    eventMass (RegularGraph.weight (N := N) (d := d)) (fun g => structural g ∧
      ¬ ∀ z ∈ boundedLocalLawDomain N b B, (graphLocalLawFamily N d a r).weak z g) ≤
      bootstrapGridConstant B * (N : ℝ) ^ 36 * δ := by
  classical
  obtain ⟨T, node, hT, hnode, htransport, hcover⟩ :=
    bounded_graph_ordered_forest N d a b r B hB structural mesh anchor
  let A : Fin T → RegularGraph N d → Prop := fun t g =>
    structural g ∧ (graphLocalLawFamily N d a r).weak (node t) g
  let H : Fin T → RegularGraph N d → Prop := fun t g =>
    (graphLocalLawFamily N d a r).strict (node t) g
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
theorem actual_graph_bounded_bootstrap_polynomial (N d a b r q : ℕ) (B D : ℝ)
    (hq : 36 ≤ q) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (structural : RegularGraph N d → Prop)
    (mesh : UniformGraphMesh N d a r (boundedLocalLawDomain N b (2 * B))
      (2 / (N : ℝ) ^ 12))
    (anchor : ∀ E : ℝ, |E| ≤ B → ∀ g, structural g →
      (graphLocalLawFamily N d a r).weak (⟨E, B⟩ : ℂ) g)
    (localDefect : ∀ z ∈ boundedLocalLawDomain N b (2 * B),
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        structural g ∧ (graphLocalLawFamily N d a r).weak z g ∧
          ¬ (graphLocalLawFamily N d a r).strict z g) ≤ D / (N : ℝ) ^ q) :
    eventMass (RegularGraph.weight (N := N) (d := d)) (fun g => structural g ∧
      ¬ ∀ z ∈ boundedLocalLawDomain N b B, (graphLocalLawFamily N d a r).weak z g) ≤
      bootstrapGridConstant B * D / (N : ℝ) ^ (q - 36) := by
  have hN : (N : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr mesh.vertexPositive)
  have hp : (N : ℝ) ^ q = (N : ℝ) ^ (q - 36) * (N : ℝ) ^ 36 := by
    rw [← pow_add]
    congr 1
    omega
  have h := actual_graph_bounded_bootstrap N d a b r B (D / (N : ℝ) ^ q)
    hB (by positivity) structural mesh anchor localDefect
  apply h.trans_eq
  rw [hp]
  field_simp [hN]
  ring

/-- The conditional uniform-structural law retains its actual denominator;
the familiar factor two follows only from the separate mass lower bound. -/
theorem actual_graph_bounded_bootstrap_conditional (N d a b r q : ℕ) (B D : ℝ)
    (hq : 36 ≤ q) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (structural : RegularGraph N d → Prop)
    (mesh : UniformGraphMesh N d a r (boundedLocalLawDomain N b (2 * B))
      (2 / (N : ℝ) ^ 12))
    (anchor : ∀ E : ℝ, |E| ≤ B → ∀ g, structural g →
      (graphLocalLawFamily N d a r).weak (⟨E, B⟩ : ℂ) g)
    (localDefect : ∀ z ∈ boundedLocalLawDomain N b (2 * B),
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        structural g ∧ (graphLocalLawFamily N d a r).weak z g ∧
          ¬ (graphLocalLawFamily N d a r).strict z g) ≤ D / (N : ℝ) ^ q)
    (mass : 1 / 2 ≤ eventMass (RegularGraph.weight (N := N) (d := d)) structural) :
    eventMass (RegularGraph.weight (N := N) (d := d)) (fun g => structural g ∧
      ¬ ∀ z ∈ boundedLocalLawDomain N b B, (graphLocalLawFamily N d a r).weak z g) /
        eventMass (RegularGraph.weight (N := N) (d := d)) structural ≤
      2 * bootstrapGridConstant B * D / (N : ℝ) ^ (q - 36) := by
  have h := actual_graph_bounded_bootstrap_polynomial N d a b r q B D hq hB hD
    structural mesh anchor localDefect
  have hC : 0 ≤ bootstrapGridConstant B := by unfold bootstrapGridConstant; positivity
  have hbudget : 0 ≤ bootstrapGridConstant B * D / (N : ℝ) ^ (q - 36) := by positivity
  have hh := conditional_budget_factor_two _ _ _ hbudget mass h
  convert hh using 1
  ring

/-- The original logarithmic parameters eventually discharge every mesh and
net hypothesis in the continuum bootstrap. -/
theorem eventually_actual_graph_bounded_bootstrap (a b d q : ℕ) (β B D : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hq : 36 ≤ q)
    (hβ : 0 < β) (hβ₁ : β ≤ 1) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ structural : RegularGraph N d → Prop,
      (∀ E : ℝ, |E| ≤ B → ∀ g, structural g →
        (graphLocalLawFamily N d a (logarithmicRadius β d N)).weak (⟨E, B⟩ : ℂ) g) →
      (∀ z ∈ boundedLocalLawDomain N b (2 * B),
        eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
          structural g ∧ (graphLocalLawFamily N d a (logarithmicRadius β d N)).weak z g ∧
            ¬ (graphLocalLawFamily N d a (logarithmicRadius β d N)).strict z g) ≤
          D / (N : ℝ) ^ q) →
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g => structural g ∧
        ¬ ∀ z ∈ boundedLocalLawDomain N b B,
          (graphLocalLawFamily N d a (logarithmicRadius β d N)).weak z g) ≤
        bootstrapGridConstant B * D / (N : ℝ) ^ (q - 36) := by
  filter_upwards [eventually_polynomial_graph_mesh a b d β (2 * B) ha hb hd hβ hβ₁
    (by positivity)] with N hmesh
  intro structural anchor localDefect
  exact actual_graph_bounded_bootstrap_polynomial N d a b _ q B D hq hB hD structural
    (Classical.choice hmesh) anchor localDefect

end LocalLaw
