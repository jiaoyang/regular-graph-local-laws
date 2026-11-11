import LocalLaw.SourceAnalyticGood
import LocalLaw.OmegaPlusHalfGeometry

/-! # Common analytic and half-radius geometric good event, cost seven -/

noncomputable section
namespace LocalLaw
local instance sourceExtendedAnalyticDecidable (p:Prop) : Decidable p:=Classical.propDecidable p

def ballSourceExtendedAnalyticBad {N d:ℕ} (a qReject qGeo Cq:ℕ) (c β C1:ℝ)
    (o:Fin N)(z:ℂ)(ξ:BallLabelledSpace N d):Prop:=
  ballSourceAnalyticBad a qReject Cq c β C1 o z ξ ∨ ballOmegaPlusHalfGeometricBad a Cq qGeo c o z ξ

theorem sourceExtendedAnalyticGood_of_not_bad {N d:ℕ} (a qReject qGeo Cq:ℕ)(c β C1:ℝ)
    (o:Fin N)(z:ℂ)(ξ:BallLabelledSpace N d)
    (h:¬ballSourceExtendedAnalyticBad a qReject qGeo Cq c β C1 o z ξ):
    ∃hT:graphBallVertices (ballLabelledProject ξ).graph o (actualCavityDepth a d N z-1)=ξ.1,
      (ballLabelledProject ξ).SourceAnalyticGood a qReject Cq c β C1 o z (hT.symm ▸ globalLabelledSamples ξ.2) ∧
      SourceFullGeometricGood (ballLabelledProject ξ).graph o (actualCavityDepth a d N z-1)
        (logarithmicRadius (c/4) d N/2) Cq (qGeo-1) (qGeo-1) (2*qGeo*(2*(qGeo-1)+1)) (qGeo-1)
        (hT.symm ▸ globalLabelledSamples ξ.2):=by
  obtain ⟨hT,hgood⟩:=sourceAnalyticGood_of_not_bad a qReject Cq c β C1 o z ξ (fun hA=>h (Or.inl hA))
  refine ⟨hT,hgood,?_⟩
  by_contra hg
  apply h
  apply Or.inr
  exact (ballCanonicalSampleEvent_iff_of_chosen o (actualCavityDepth a d N z-1) _ ξ hT).mpr hg

theorem eventually_ballSourceExtendedAnalyticBad_probability (a b d p:ℕ)(c β γ B C1:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hc₁:c<1)(hβ:0<β)(hβc:β≤c/32)
    (hγ:c/4<γ)(hgap:γ+β<1)(hB:0≤B)(hC1:1≤C1):
    ∃qReject qGeo:ℕ,1≤qReject ∧ 1≤qGeo ∧ ∀ᶠ N:ℕ in Filter.atTop,∀(o:Fin N)(z:ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀Cq:ℕ,
      eventMass (ballLabelledWeight N d o (actualCavityDepth a d N z-1)) (fun ξ=>
        (ballLabelledProject ξ).SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
          (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq ⌊(N:ℝ)^γ⌋₊ C1 o z ∧
        ballSourceExtendedAnalyticBad a qReject qGeo Cq c β C1 o z ξ)≤7/(N:ℝ)^p:=by
  have hγ1:γ<1:=by linarith
  obtain ⟨qA,hqA,hA⟩:=eventually_ballSourceAnalyticBad_probability a b d p c β γ B C1
    ha hb hd hc hc₁ hβ hβc hγ hgap hB hC1
  obtain ⟨qG,hqG,hG⟩:=eventually_ballOmegaPlusHalfGeometricBad_probability a d p c γ (by omega) hd hc hc₁ hγ1
  refine ⟨qA,qG,hqA,hqG,?_⟩
  filter_upwards [hA,hG] with N hA hG
  intro o z hz hzB hscale Cq
  let ell:=actualCavityDepth a d N z-1
  let E:BallLabelledSpace N d→Prop:=fun ξ=>
    (ballLabelledProject ξ).SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
      (logarithmicRadius (c/4) d N) ell (finiteOmega d) Cq ⌊(N:ℝ)^γ⌋₊ C1 o z
  let A:BallLabelledSpace N d→Prop:=fun ξ=>E ξ∧ballSourceAnalyticBad a qA Cq c β C1 o z ξ
  let G:BallLabelledSpace N d→Prop:=fun ξ=>E ξ∧ballOmegaPlusHalfGeometricBad a Cq qG c o z ξ
  have hcover:∀ξ,E ξ∧ballSourceExtendedAnalyticBad a qA qG Cq c β C1 o z ξ→A ξ∨G ξ:=by
    rintro ξ ⟨he,ha|hg⟩
    · exact Or.inl ⟨he,ha⟩
    · exact Or.inr ⟨he,hg⟩
  exact ((eventMass_mono (ballLabelledWeight N d o ell) (ballLabelledWeight_nonnegative N d o ell) hcover).trans
    (eventMass_union_le (ballLabelledWeight N d o ell) (ballLabelledWeight_nonnegative N d o ell) A G)).trans
      ((add_le_add (hA o z hz hzB hscale Cq)
        (hG o z (effectiveModelRadius a d N β) (logarithmicRadius β d N) Cq C1)).trans_eq (by ring))

end LocalLaw
