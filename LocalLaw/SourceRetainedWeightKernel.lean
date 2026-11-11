import LocalLaw.SourceRetainedWeightGood
import LocalLaw.GeometricKernelProbability

/-! # Actual enlarged-kernel probability for retained weight concentration -/

noncomputable section
namespace LocalLaw
local instance sourceRetainedWeightKernelDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def ballSourceRetainedWeightBad {N d : ℕ} (a : ℕ) (c β C1 : ℝ) (o : Fin N) (z : ℂ) :
    BallLabelledSpace N d → Prop :=
  ballCanonicalSampleEvent o (actualCavityDepth a d N z-1)
    (fun g samples => ¬g.SourceRetainedWeightGood a c β C1 o z samples)

theorem eventually_ballSourceRetainedWeightBad_probability (a b d p : ℕ) (c β γ B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hγ : c/4<γ) (hgap : γ+β<1)
    (hB : 0≤B) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (o : Fin N) (z : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ Cq : ℕ,
      eventMass (ballLabelledWeight N d o (actualCavityDepth a d N z-1)) (fun ξ =>
        (ballLabelledProject ξ).SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
          (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq ⌊(N:ℝ)^γ⌋₊ C1 o z ∧
        ballSourceRetainedWeightBad a c β C1 o z ξ)≤1/(N:ℝ)^p := by
  filter_upwards [RegularGraph.eventually_sourceRetainedWeightGood_failure a b d p c β γ B C1
    ha hb hd hc hβ hβc hγ hgap hB hC1] with N htail
  intro o z hz hzB hfloor Cq
  let ell := actualCavityDepth a d N z-1
  let A : RegularGraph N d → Prop := fun g =>
    g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
      (logarithmicRadius (c/4) d N) ell (finiteOmega d) Cq ⌊(N:ℝ)^γ⌋₊ C1 o z
  have h := ballCanonical_sample_failure_bound N d o ell A
    (fun g samples => ¬g.SourceRetainedWeightGood a c β C1 o z samples) (1/(N:ℝ)^p)
      (fun g hA => htail g o z hz hzB hfloor Cq _ le_rfl hA)
  have hmass : eventMass (RegularGraph.weight (N:=N) (d:=d)) A≤1 := finiteUniform_eventMass_le_one A
  have hbound := h.trans ((mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq (mul_one _))
  exact hbound

end LocalLaw
