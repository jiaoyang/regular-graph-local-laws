import LocalLaw.SourceCorrelationGoodSet
import LocalLaw.OmegaPlusRejectedKernel

/-!
# Actual joint failure for the sparse surgery good-label construction

The correlation-isolation failure and the accepted-label rejection failure
are united on the genuine graph-dependent reversible kernel. The resulting
arbitrary polynomial bound has no conditional-probability input.
-/

noncomputable section
namespace LocalLaw
local instance sourceSurgeryProbabilityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def ballSourceSurgeryBad {N d : ℕ} (o : Fin N) (ell a rError R Cq qReject : ℕ) (z : ℂ) :
    BallLabelledSpace N d → Prop := fun ξ =>
  ballSourceGreenIsolationBad o ell a rError R z ξ ∨ ballSourceRejectedBad o ell R Cq qReject ξ

theorem eventually_ballSourceSurgeryBad_probability (a b d p : ℕ) (c β γ C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c) (hc₁ : c<1)
    (hβ : 0<β) (hβc : β≤c/32) (hγ : γ<1) (hC1 : 0≤C1) :
    ∃ qReject : ℕ, 1≤qReject ∧ ∀ᶠ N : ℕ in Filter.atTop, ∀ (o : Fin N) (z : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ Cq : ℕ,
      eventMass (ballLabelledWeight N d o (actualCavityDepth a d N z-1)) (fun ξ =>
        (ballLabelledProject ξ).SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β)
          (logarithmicRadius β d N) (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
          (finiteOmega d) Cq ⌊(N:ℝ)^γ⌋₊ C1 o z ∧
        ballSourceSurgeryBad o (actualCavityDepth a d N z-1) a (logarithmicRadius β d N)
          (logarithmicRadius (c/4) d N) Cq qReject z ξ) ≤ 4/(N:ℝ)^p := by
  obtain ⟨q,hq,hr⟩ := eventually_ballSourceRejectedBad_probability a d p c γ (by omega) hd hc hc₁ hγ
  refine ⟨q,hq,?_⟩
  filter_upwards [hr,eventually_ballSourceGreenIsolationBad_probability a b d p c β C1
    ha hb hd hc hc₁ hβ hβc hC1] with N hr hi
  intro o z hz hfloor Cq
  let ell := actualCavityDepth a d N z-1
  let R := logarithmicRadius (c/4) d N
  let rn := logarithmicRadius β d N
  let A : BallLabelledSpace N d → Prop := fun ξ =>
    (ballLabelledProject ξ).SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) rn R ell
      (finiteOmega d) Cq ⌊(N:ℝ)^γ⌋₊ C1 o z
  let I : BallLabelledSpace N d → Prop := ballSourceGreenIsolationBad o ell a rn R z
  let J : BallLabelledSpace N d → Prop := ballSourceRejectedBad o ell R Cq q
  have hcover : ∀ ξ, A ξ ∧ ballSourceSurgeryBad o ell a rn R Cq q z ξ →
      (A ξ ∧ I ξ) ∨ (A ξ ∧ J ξ) := by
    rintro ξ ⟨hA,hI|hJ⟩
    · exact Or.inl ⟨hA,hI⟩
    · exact Or.inr ⟨hA,hJ⟩
  have hmass := (eventMass_mono (ballLabelledWeight N d o ell) (ballLabelledWeight_nonnegative N d o ell) hcover).trans
    (eventMass_union_le (ballLabelledWeight N d o ell) (ballLabelledWeight_nonnegative N d o ell)
      (fun ξ => A ξ ∧ I ξ) (fun ξ => A ξ ∧ J ξ))
  have hi' := hi o z hz hfloor Cq ⌊(N:ℝ)^γ⌋₊
  have hr' := hr o z (effectiveModelRadius a d N β) rn (finiteOmega d) Cq C1
  exact hmass.trans ((add_le_add hi' hr').trans_eq (by ring))

end LocalLaw
