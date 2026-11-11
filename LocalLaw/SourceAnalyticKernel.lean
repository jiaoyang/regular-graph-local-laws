import LocalLaw.SourceSurgeryProbability
import LocalLaw.SourceRetainedWeightKernel
import LocalLaw.SourceCavityWeightConcentration

/-! # One actual rare event for retained-row and cavity improvements

The three proved mechanisms share a single rejection threshold. The cavity
weight failure is charged only when its actual source retained ball is a
tree. This preserves the correct target-to-source tree direction.
-/

noncomputable section
namespace LocalLaw
local instance sourceAnalyticKernelDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def ballSourceAnalyticBad {N d : ℕ} (a qReject Cq : ℕ) (c β C1 : ℝ) (o : Fin N) (z : ℂ)
    (ξ : BallLabelledSpace N d) : Prop :=
  ballSourceSurgeryBad o (actualCavityDepth a d N z-1) a (logarithmicRadius β d N)
      (logarithmicRadius (c/4) d N) Cq qReject z ξ ∨
  ballSourceRetainedWeightBad a c β C1 o z ξ ∨
    ((graphBall (ballLabelledProject ξ).graph o (actualCavityDepth a d N z-1)).IsTree ∧
      ballSourceCavityWeightBad a c β C1 o z ξ)

theorem ballSourceAnalyticBad_complement {N d : ℕ} (a qReject Cq : ℕ) (c β C1 : ℝ)
    (o : Fin N) (z : ℂ) (ξ : BallLabelledSpace N d)
    (h : ¬ballSourceAnalyticBad a qReject Cq c β C1 o z ξ) :
    ¬ballSourceSurgeryBad o (actualCavityDepth a d N z-1) a (logarithmicRadius β d N)
      (logarithmicRadius (c/4) d N) Cq qReject z ξ ∧
    ¬ballSourceRetainedWeightBad a c β C1 o z ξ ∧
    ((graphBall (ballLabelledProject ξ).graph o (actualCavityDepth a d N z-1)).IsTree →
      ¬ballSourceCavityWeightBad a c β C1 o z ξ) := by
  exact ⟨fun hi => h (Or.inl hi),fun hi => h (Or.inr (Or.inl hi)),
    fun ht hi => h (Or.inr (Or.inr ⟨ht,hi⟩))⟩

theorem eventually_ballSourceAnalyticBad_probability (a b d p : ℕ) (c β γ B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c) (hc₁ : c<1)
    (hβ : 0<β) (hβc : β≤c/32) (hγ : c/4<γ) (hgap : γ+β<1)
    (hB : 0≤B) (hC1 : 1≤C1) :
    ∃ qReject : ℕ,1≤qReject ∧ ∀ᶠ N : ℕ in Filter.atTop,∀ (o : Fin N) (z : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ Cq : ℕ,
      eventMass (ballLabelledWeight N d o (actualCavityDepth a d N z-1)) (fun ξ =>
        (ballLabelledProject ξ).SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β)
          (logarithmicRadius β d N) (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
          (finiteOmega d) Cq ⌊(N:ℝ)^γ⌋₊ C1 o z ∧
        ballSourceAnalyticBad a qReject Cq c β C1 o z ξ)≤6/(N:ℝ)^p := by
  have hγ1 : γ<1 := by linarith
  have hC10 : 0≤C1 := by linarith
  obtain ⟨q,hq,hsurgery⟩ := eventually_ballSourceSurgeryBad_probability a b d p c β γ C1
    ha hb hd hc hc₁ hβ hβc hγ1 hC10
  refine ⟨q,hq,?_⟩
  filter_upwards [hsurgery,eventually_ballSourceRetainedWeightBad_probability a b d p c β γ B C1
    ha hb hd hc hβ hβc hγ hgap hB hC1,
    eventually_ballSourceCavityWeightBad_probability a b d p c β γ B C1
    ha hb hd hc hβ hβc hγ hgap hB hC1] with N hsurgery hretained hcavity
  intro o z hz hzB hscale Cq
  let ell := actualCavityDepth a d N z-1
  let A : BallLabelledSpace N d → Prop := fun ξ =>
    (ballLabelledProject ξ).SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β)
      (logarithmicRadius β d N) (logarithmicRadius (c/4) d N) ell (finiteOmega d) Cq ⌊(N:ℝ)^γ⌋₊ C1 o z
  let P : BallLabelledSpace N d → Prop := fun ξ => A ξ ∧
    ballSourceSurgeryBad o ell a (logarithmicRadius β d N) (logarithmicRadius (c/4) d N) Cq q z ξ
  let Q : BallLabelledSpace N d → Prop := fun ξ => A ξ ∧ ballSourceRetainedWeightBad a c β C1 o z ξ
  let W : BallLabelledSpace N d → Prop := fun ξ => A ξ ∧
    (graphBall (ballLabelledProject ξ).graph o ell).IsTree ∧ ballSourceCavityWeightBad a c β C1 o z ξ
  have hcover : ∀ ξ,A ξ ∧ ballSourceAnalyticBad a q Cq c β C1 o z ξ → P ξ ∨ Q ξ ∨ W ξ := by
    rintro ξ ⟨hA,hi | hi | hi⟩
    · exact Or.inl ⟨hA,hi⟩
    · exact Or.inr (Or.inl ⟨hA,hi⟩)
    · exact Or.inr (Or.inr ⟨hA,hi⟩)
  have hmass := (eventMass_mono (ballLabelledWeight N d o ell) (ballLabelledWeight_nonnegative N d o ell) hcover).trans
    ((eventMass_union_le (ballLabelledWeight N d o ell) (ballLabelledWeight_nonnegative N d o ell) P (fun ξ => Q ξ∨W ξ)).trans
      (add_le_add_left (eventMass_union_le (ballLabelledWeight N d o ell) (ballLabelledWeight_nonnegative N d o ell) Q W) _))
  exact hmass.trans ((add_le_add (hsurgery o z hz hscale Cq)
    (add_le_add (hretained o z hz hzB hscale Cq) (hcavity o z hz hzB hscale Cq))).trans_eq (by ring))

end LocalLaw
