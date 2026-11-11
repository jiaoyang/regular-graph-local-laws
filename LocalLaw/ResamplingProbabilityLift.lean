import LocalLaw.BallResamplingMeasure

/-!
# Lift genuine local sample estimates to the actual labelled kernel

Boundary permutations are auxiliary uniform labels. Marginalizing them leaves
the canonical outside-edge sample law exactly; summing the actual boundary
blocks then returns the graph law. This connects pointwise sampling bounds to
the enlarged reversible space without adding a probability-transfer premise.
-/

set_option maxHeartbeats 1800000

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance probabilityLiftDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Canonical finite sigma summation avoids dependence on enumerations of
nested graph subtypes in later disintegration proofs. -/
theorem finite_finsum_sigma {A : Type*} {B : A → Type*} [Finite A] [∀ a, Finite (B a)]
    (f : (Σ a, B a) → ℝ) : (∑ᶠ a, ∑ᶠ b, f ⟨a, b⟩) = ∑ᶠ s, f s := by
  classical
  letI := Fintype.ofFinite A
  letI (a : A) := Fintype.ofFinite (B a)
  simp only [finsum_eq_sum_of_fintype]
  exact (Fintype.sum_sigma f).symm

/-- Discarding an independent nonempty uniform label leaves the exact uniform
law on the actual sample space, including when that sample space is empty. -/
theorem finiteUniform_product_snd_mass {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (P : B → Prop) :
    eventMass (finiteUniformWeight (A × B)) (fun p => P p.2) = eventMass (finiteUniformWeight B) P := by
  have hw : ∀ a : A, ∀ b : B, finiteUniformWeight (A × B) (a, b) =
      finiteUniformWeight A a * finiteUniformWeight B b := by
    intro a b
    simp only [finiteUniformWeight, Fintype.card_prod, Nat.cast_mul, one_div, mul_inv]
  calc
    _ = ∑ a : A, ∑ b : B, if P b then finiteUniformWeight A a * finiteUniformWeight B b else 0 := by
      unfold eventMass
      rw [Fintype.sum_prod_type]
      simp only [hw]
    _ = ∑ a : A, finiteUniformWeight A a * eventMass (finiteUniformWeight B) P := by
      unfold eventMass
      simp_rw [Finset.mul_sum, mul_ite, mul_zero]
    _ = (∑ a : A, finiteUniformWeight A a) * eventMass (finiteUniformWeight B) P := (Finset.sum_mul ..).symm
    _ = _ := by rw [finiteUniformWeight_total, one_mul]

/-- The finite dependent conditional probability is exactly the uniform mass
on its fiber. This does not require that fiber to be nonempty. -/
theorem finiteFiberProbability_eq_uniform {Γ : Type*} (S : Γ → Type*)
    [∀ g, Fintype (S g)] (R : (Σ g, S g) → Prop) (g : Γ) :
    finiteFiberProbability S R g = eventMass (finiteUniformWeight (S g)) (fun s => R ⟨g, s⟩) := by
  unfold finiteFiberProbability eventMass finiteUniformWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> simp [one_div]

/-- Uniform boundary labels have no effect on any canonical sample event. -/
theorem labelledBoundaryFiber_sample_probability {N d μ : ℕ} {T : Set (Fin N)}
    (g : RegularBoundaryBlock N d μ T) (P : LocalSamplingFiber g.val.graph T → Prop) :
    eventMass (finiteUniformWeight (LabelledBoundaryFiber g)) (fun x => P x.2) =
      eventMass (localSamplingWeight g.val.graph T) P := by
  letI : Nonempty (Fin μ ≃ BoundaryOrientedEdge g.val.graph T) := ⟨boundaryBlockLabel g⟩
  exact finiteUniform_product_snd_mass P

/-- Any canonical sample predicate on the actual fixed-T global space. -/
def globalLabelledSampleEvent {N d : ℕ} {T : Set (Fin N)}
    (P : ∀ g : RegularGraph N d, LocalSamplingFiber g.graph T → Prop)
    (ω : GlobalLabelledSpace N d T) : Prop := P ω.2.1.val ω.2.2.2

/-- Exact fixed-T disintegration into the physical graph law and the actual
local outside-edge sampling law, including all boundary-size blocks. -/
theorem globalLabelled_sample_mass (N d : ℕ) (T : Set (Fin N))
    (P : ∀ g : RegularGraph N d, LocalSamplingFiber g.graph T → Prop) :
    eventMass (globalLabelledWeight N d T) (globalLabelledSampleEvent P) =
      ∑ g : RegularGraph N d, RegularGraph.weight g * eventMass (localSamplingWeight g.graph T) (P g) := by
  calc
    _ = ∑ μ : Fin (N * d + 1), eventMass
        (finiteFiberWeight (fun g : RegularBoundaryBlock N d μ.val T => LabelledBoundaryFiber g)
          (fun _ => (1 : ℝ) / Fintype.card (RegularGraph N d)))
        (fun ω => P ω.1.val ω.2.2) := by
      unfold eventMass
      exact Fintype.sum_sigma _
    _ = ∑ μ : Fin (N * d + 1), ∑ g : RegularBoundaryBlock N d μ.val T,
        ((1 : ℝ) / Fintype.card (RegularGraph N d)) * eventMass (localSamplingWeight g.val.graph T) (P g.val) := by
      apply Finset.sum_congr rfl
      intro μ _
      rw [finiteFiberWeight_disintegration]
      apply Finset.sum_congr rfl
      intro g _
      rw [finiteFiberProbability_eq_uniform]
      congr 1
      exact labelledBoundaryFiber_sample_probability g (P g.val)
    _ = _ := by
      simp only [← finsum_eq_sum_of_fintype]
      let F : (Σ μ : Fin (N * d + 1), RegularBoundaryBlock N d μ.val T) → ℝ :=
        fun ω => ((1 : ℝ) / Fintype.card (RegularGraph N d)) *
          eventMass (localSamplingWeight ω.2.val.graph T) (P ω.2.val)
      change (∑ᶠ μ, ∑ᶠ g, F ⟨μ, g⟩) = _
      rw [finite_finsum_sigma F]
      apply finsum_eq_of_bijective (regularBoundaryDecomposition N d T)
        (regularBoundaryDecomposition N d T).bijective
      intro g
      rfl

/-- Pointwise local sample bounds integrate over the exact fixed-T labelled
space. No label-independence hypothesis is left to a caller. -/
theorem globalLabelled_sample_failure_bound (N d : ℕ) (T : Set (Fin N))
    (A : RegularGraph N d → Prop)
    (P : ∀ g : RegularGraph N d, LocalSamplingFiber g.graph T → Prop) (δ : ℝ)
    (hP : ∀ g, A g → eventMass (localSamplingWeight g.graph T) (P g) ≤ δ) :
    eventMass (globalLabelledWeight N d T)
      (globalLabelledSampleEvent (fun g S => A g ∧ P g S)) ≤
        δ * eventMass RegularGraph.weight A := by
  rw [globalLabelled_sample_mass]
  unfold eventMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro g _
  by_cases hA : A g
  · simp only [hA, true_and, if_true]
    have hh := mul_le_mul_of_nonneg_left (hP g hA) (RegularGraph.weight_nonnegative g)
    change RegularGraph.weight g * eventMass (localSamplingWeight g.graph T) (P g) ≤ δ * RegularGraph.weight g
    simpa only [mul_comm] using hh
  · simp [hA]

/-- The actual sample assignment in a fixed-T labelled state. -/
def globalLabelledSamples {N d : ℕ} {T : Set (Fin N)} (ω : GlobalLabelledSpace N d T) :
    LocalSamplingFiber (globalLabelledProject ω).graph T := ω.2.2.2

/-- An arbitrary canonical sample predicate on the graph-dependent chosen-ball space. -/
def ballLabelledSampleEvent {N d : ℕ}
    (P : ∀ (T : Set (Fin N)) (g : RegularGraph N d), LocalSamplingFiber g.graph T → Prop)
    (ω : BallLabelledSpace N d) : Prop := P ω.1 (ballLabelledProject ω) (globalLabelledSamples ω.2)

/-- Exact chosen-ball disintegration. This holds even before imposing the
sampling nonemptiness budget; on empty sample spaces both sides vanish. -/
theorem ballLabelled_sample_mass (N d : ℕ) (o : Fin N) (ell : ℕ)
    (P : ∀ (T : Set (Fin N)) (g : RegularGraph N d), LocalSamplingFiber g.graph T → Prop) :
    eventMass (ballLabelledWeight N d o ell) (ballLabelledSampleEvent P) =
      ∑ g : RegularGraph N d, RegularGraph.weight g *
        eventMass (localSamplingWeight g.graph (graphBallVertices g.graph o ell))
          (P (graphBallVertices g.graph o ell) g) := by
  have hrestrict : ∀ T : Set (Fin N),
      eventMass (ballRestrictedWeight N d T o ell) (globalLabelledSampleEvent (P T)) =
        eventMass (globalLabelledWeight N d T)
          (globalLabelledSampleEvent (fun g S => ChosenResamplingBall o ell T g ∧ P T g S)) := by
    intro T
    unfold eventMass ballRestrictedWeight globalLabelledSampleEvent
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hB : ChosenResamplingBall o ell T ω.2.1.val <;>
      by_cases hP : P T ω.2.1.val ω.2.2.2 <;> simp [globalLabelledProject, hB, hP]
  have hlocal : ∀ (T : Set (Fin N)) (g : RegularGraph N d),
      eventMass (localSamplingWeight g.graph T) (fun S => ChosenResamplingBall o ell T g ∧ P T g S) =
        if ChosenResamplingBall o ell T g then eventMass (localSamplingWeight g.graph T) (P T g) else 0 := by
    intro T g
    by_cases hB : ChosenResamplingBall o ell T g <;> simp [eventMass, hB]
  calc
    _ = ∑ T : Set (Fin N), eventMass (ballRestrictedWeight N d T o ell)
        (globalLabelledSampleEvent (P T)) := by
      unfold eventMass
      exact Fintype.sum_sigma _
    _ = ∑ T : Set (Fin N), ∑ g : RegularGraph N d, RegularGraph.weight g *
        (if ChosenResamplingBall o ell T g then eventMass (localSamplingWeight g.graph T) (P T g) else 0) := by
      apply Finset.sum_congr rfl
      intro T _
      rw [hrestrict T, globalLabelled_sample_mass]
      simp_rw [hlocal]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      rw [← Finset.mul_sum]
      congr 1
      simp [ChosenResamplingBall]

/-- Pointwise bounds on canonical local samples lift to the genuine
ball-labelled kernel with its original graph base law. -/
theorem ballLabelled_sample_failure_bound (N d : ℕ) (o : Fin N) (ell : ℕ)
    (A : RegularGraph N d → Prop)
    (P : ∀ (T : Set (Fin N)) (g : RegularGraph N d), LocalSamplingFiber g.graph T → Prop) (δ : ℝ)
    (hP : ∀ g, A g → eventMass (localSamplingWeight g.graph (graphBallVertices g.graph o ell))
      (P (graphBallVertices g.graph o ell) g) ≤ δ) :
    eventMass (ballLabelledWeight N d o ell)
      (fun ω => A (ballLabelledProject ω) ∧ ballLabelledSampleEvent P ω) ≤
        δ * eventMass RegularGraph.weight A := by
  change eventMass _ (ballLabelledSampleEvent (fun T g S => A g ∧ P T g S)) ≤ _
  rw [ballLabelled_sample_mass]
  unfold eventMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro g _
  by_cases hA : A g
  · simp only [hA, true_and, if_true]
    have hh := mul_le_mul_of_nonneg_left (hP g hA) (RegularGraph.weight_nonnegative g)
    change RegularGraph.weight g * eventMass
      (localSamplingWeight g.graph (graphBallVertices g.graph o ell))
      (P (graphBallVertices g.graph o ell) g) ≤ δ * RegularGraph.weight g
    simpa only [mul_comm] using hh
  · simp [hA]

end
end LocalLaw
