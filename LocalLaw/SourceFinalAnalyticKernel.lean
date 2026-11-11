import LocalLaw.SourceExtendedAnalyticKernel
import LocalLaw.SourceCorrelationKernel

/-! # Full common second-stage rare event, including uniform external F2

The old boundary/pair isolation event does not imply the separate uniform
external-target correlation count. This proved extra tail is charged explicitly.
-/

noncomputable section
namespace LocalLaw
local instance sourceFinalAnalyticDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def ballSourceFinalAnalyticBad {N d:ℕ}(a qReject qGeo Cq:ℕ)(c β C1:ℝ)
    (o:Fin N)(z:ℂ)(ξ:BallLabelledSpace N d):Prop:=
  ballSourceExtendedAnalyticBad a qReject qGeo Cq c β C1 o z ξ ∨
    ballSourceCorrelationBad o (actualCavityDepth a d N z-1) a (logarithmicRadius β d N)
      (logarithmicRadius (c/4) d N) z ξ

theorem sourceFinalAnalyticGood_of_not_bad {N d:ℕ}(a qReject qGeo Cq:ℕ)(c β C1:ℝ)
    (o:Fin N)(z:ℂ)(ξ:BallLabelledSpace N d)
    (h:¬ballSourceFinalAnalyticBad a qReject qGeo Cq c β C1 o z ξ):
    ∃hT:graphBallVertices (ballLabelledProject ξ).graph o (actualCavityDepth a d N z-1)=ξ.1,
      (ballLabelledProject ξ).SourceAnalyticGood a qReject Cq c β C1 o z (hT.symm ▸ globalLabelledSamples ξ.2) ∧
      SourceFullGeometricGood (ballLabelledProject ξ).graph o (actualCavityDepth a d N z-1)
        (logarithmicRadius (c/4) d N/2) Cq (qGeo-1) (qGeo-1) (2*qGeo*(2*(qGeo-1)+1)) (qGeo-1)
        (hT.symm ▸ globalLabelledSamples ξ.2) ∧
      ∀x:((graphBallVertices (ballLabelledProject ξ).graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N)),
        ((ballLabelledProject ξ).correlatedSampleIndices _ z
          (correlationThreshold (Real.log (N:ℝ)) a N z.im (graphKestenMcKayReference d z).im (spectralScale z)
            (graphPaperError a d N (logarithmicRadius β d N) z))
          (logarithmicRadius (c/4) d N/4) x (hT.symm ▸ globalLabelledSamples ξ.2)).card≤Nat.ceil (Real.log (N:ℝ)):=by
  obtain ⟨hT,hA,hG⟩:=sourceExtendedAnalyticGood_of_not_bad a qReject qGeo Cq c β C1 o z ξ
    (fun he=>h (Or.inl he))
  refine ⟨hT,hA,hG,?_⟩
  intro x
  by_contra hcount
  apply h
  apply Or.inr
  let P : ∀g:RegularGraph N d,LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))→Prop :=
    fun g S=>∃x:((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N)),
      Nat.ceil (Real.log (N:ℝ))≤(g.correlatedSampleIndices _ z
        (correlationThreshold (Real.log (N:ℝ)) a N z.im (graphKestenMcKayReference d z).im (spectralScale z)
          (graphPaperError a d N (logarithmicRadius β d N) z))
        (logarithmicRadius (c/4) d N/4) x S).card
  exact (ballCanonicalSampleEvent_iff_of_chosen o (actualCavityDepth a d N z-1) P ξ hT).mpr ⟨x,by omega⟩

theorem eventually_ballSourceFinalAnalyticBad_probability (a b d p:ℕ)(c β γ B C1:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hc₁:c<1)(hβ:0<β)(hβc:β≤c/32)
    (hγ:c/4<γ)(hgap:γ+β<1)(hB:0≤B)(hC1:1≤C1):
    ∃qReject qGeo:ℕ,1≤qReject ∧ 1≤qGeo ∧ ∀ᶠ N:ℕ in Filter.atTop,∀(o:Fin N)(z:ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀Cq:ℕ,
      eventMass (ballLabelledWeight N d o (actualCavityDepth a d N z-1)) (fun ξ=>
        (ballLabelledProject ξ).SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
          (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq ⌊(N:ℝ)^γ⌋₊ C1 o z ∧
        ballSourceFinalAnalyticBad a qReject qGeo Cq c β C1 o z ξ)≤8/(N:ℝ)^p:=by
  obtain ⟨qA,qG,hqA,hqG,hAG⟩:=eventually_ballSourceExtendedAnalyticBad_probability a b d p c β γ B C1
    ha hb hd hc hc₁ hβ hβc hγ hgap hB hC1
  refine ⟨qA,qG,hqA,hqG,?_⟩
  filter_upwards [hAG,eventually_ballSourceCorrelationBad_probability a b d p c β C1
    ha hb hd hc hc₁ hβ hβc (by linarith)] with N hAG hC
  intro o z hz hzB hscale Cq
  let ell:=actualCavityDepth a d N z-1
  let E:BallLabelledSpace N d→Prop:=fun ξ=>
    (ballLabelledProject ξ).SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
      (logarithmicRadius (c/4) d N) ell (finiteOmega d) Cq ⌊(N:ℝ)^γ⌋₊ C1 o z
  let A:BallLabelledSpace N d→Prop:=fun ξ=>E ξ∧ballSourceExtendedAnalyticBad a qA qG Cq c β C1 o z ξ
  let C:BallLabelledSpace N d→Prop:=fun ξ=>E ξ∧ballSourceCorrelationBad o ell a (logarithmicRadius β d N)
    (logarithmicRadius (c/4) d N) z ξ
  have hcover:∀ξ,E ξ∧ballSourceFinalAnalyticBad a qA qG Cq c β C1 o z ξ→A ξ∨C ξ:=by
    rintro ξ ⟨he,ha|hc⟩
    · exact Or.inl ⟨he,ha⟩
    · exact Or.inr ⟨he,hc⟩
  exact ((eventMass_mono (ballLabelledWeight N d o ell) (ballLabelledWeight_nonnegative N d o ell) hcover).trans
    (eventMass_union_le (ballLabelledWeight N d o ell) (ballLabelledWeight_nonnegative N d o ell) A C)).trans
      ((add_le_add (hAG o z hz hzB hscale Cq)
        (hC o z hz hscale Cq ⌊(N:ℝ)^γ⌋₊)).trans_eq (by ring))

end LocalLaw
