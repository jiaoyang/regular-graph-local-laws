import LocalLaw.CompleteStrongCertificate

/-! # The actual second resampling stage has an arbitrary-polynomial bound

All local row and cavity estimates have been instantiated. The target is
restricted to the original weak/structural event, as allowed by the proved
reversible transfer. The sole probability input used here is the separately
proved common sampling bad event with cost eight.
-/

noncomputable section
set_option maxHeartbeats 3000000
namespace LocalLaw
local instance sourceSecondStageProbabilityDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem eventually_actual_second_stage_strong_certificate_probability (a b d p Cq:ℕ)(c β γ B C1:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hc₁:c<1)(hβ:0<β)(hβc:β≤c/32)
    (hγ:c/4<γ)(hgap:γ+β<1)(hB:0≤B)(hC1:1≤C1)
    (hCdel:sourceDeletionConstant d β B≤C1)(hCq:finiteOmega d≤Cq):
    ∃qReject qGeo:ℕ,1≤qReject ∧ 1≤qGeo ∧ ∀ᶠ N:ℕ in Filter.atTop,∀(o:Fin N)(z:ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      let R:=logarithmicRadius (c/4) d N
      let rn:=logarithmicRadius β d N
      let r:=effectiveModelRadius a d N β
      let ell:=actualCavityDepth a d N z-1
      let ε:=graphPaperError a d N rn z
      ∀D:StrongClosureBudget z (semicircleRoot z) (spectralScale z) ε,
      D.depth=actualCavityDepth a d N z → D.L=Real.log (N:ℝ) → D.U=sourceSecondU d Cq qReject qGeo β B C1 →
      D.V=sourceSecondV d β B → D.residualConstant=sourceSecondM d Cq qReject β C1 →
      D.rowBase=D.U*ε/D.L → D.rowFeedback=D.V*D.L^2 → D.cavityError=D.residualConstant*ε/(2*D.L^4) →
      eventMass (ballLabelledWeight N d o ell) (fun ξ=>
        (ballLabelledProject ξ).SourceOmegaPlusWithRadii a r rn R ell (finiteOmega d) Cq ⌊(N:ℝ)^γ⌋₊ C1 o z ∧
        (ballLabelledProject (ballLabelledResample N d (R/4) ξ)).SourceOmegaWithRadii a r rn R (finiteOmega d) ⌊(N:ℝ)^γ⌋₊ z ∧
        ¬StrongCavityRowCertificate
          ((ballLabelledProject (ballLabelledResample N d (R/4) ξ)).Q z) (semicircleRoot z) z (spectralScale z) ε D
          ((ballLabelledProject (ballLabelledResample N d (R/4) ξ)).G z)
          (fun w=>(ballLabelledProject (ballLabelledResample N d (R/4) ξ)).P r z w)
          (cavityAtVertex (ballLabelledProject (ballLabelledResample N d (R/4) ξ)).graph d z)
          (nonTreeCenters (ballLabelledProject (ballLabelledResample N d (R/4) ξ)).graph R) o)≤8/(N:ℝ)^p:=by
  obtain ⟨qA,qG,hqA,hqG,hrare⟩:=eventually_ballSourceFinalAnalyticBad_probability a b d p c β γ B C1
    ha hb hd hc hc₁ hβ hβc hγ hgap hB hC1
  refine ⟨qA,qG,hqA,hqG,?_⟩
  filter_upwards [hrare,RegularGraph.eventually_source_complete_strong_certificate a b d qA qG Cq c β γ B C1
    ha hb hd hc hβ hβc hγ hgap hB hC1 hCdel hCq] with N hrare hcertificate
  intro o z hz hzB hfloor
  dsimp only
  let R:=logarithmicRadius (c/4) d N
  let rn:=logarithmicRadius β d N
  let r:=effectiveModelRadius a d N β
  let ell:=actualCavityDepth a d N z-1
  let ε:=graphPaperError a d N rn z
  let badCount:=⌊(N:ℝ)^γ⌋₊
  intro D hdepth hlog hU hV hM hbase hfeedback hcavity
  let A:BallLabelledSpace N d→Prop:=fun ξ=>
    (ballLabelledProject ξ).SourceOmegaPlusWithRadii a r rn R ell (finiteOmega d) Cq badCount C1 o z
  have hcover:∀ξ:BallLabelledSpace N d,
      (A ξ ∧ (ballLabelledProject (ballLabelledResample N d (R/4) ξ)).SourceOmegaWithRadii a r rn R (finiteOmega d) badCount z ∧
      ¬StrongCavityRowCertificate ((ballLabelledProject (ballLabelledResample N d (R/4) ξ)).Q z)
        (semicircleRoot z) z (spectralScale z) ε D ((ballLabelledProject (ballLabelledResample N d (R/4) ξ)).G z)
        (fun w=>(ballLabelledProject (ballLabelledResample N d (R/4) ξ)).P r z w)
        (cavityAtVertex (ballLabelledProject (ballLabelledResample N d (R/4) ξ)).graph d z)
        (nonTreeCenters (ballLabelledProject (ballLabelledResample N d (R/4) ξ)).graph R) o) →
      A ξ ∧ ballSourceFinalAnalyticBad a qA qG Cq c β C1 o z ξ:=by
    intro ξ hf
    refine ⟨hf.1,?_⟩
    by_contra hbad
    obtain ⟨hT,hgood,hgeo,hcorr⟩:=sourceFinalAnalyticGood_of_not_bad a qA qG Cq c β C1 o z ξ hbad
    rcases ξ with ⟨T,μ,⟨g,hμ⟩,labels,samples⟩
    change graphBallVertices g.graph o ell=T at hT
    cases hT
    exact hf.2.2 (hcertificate g o z hz hzB hfloor badCount le_rfl hf.1 labels samples hf.2.1
      hgood hgeo hcorr D hdepth hlog hU hV hM hbase hfeedback hcavity)
  exact (eventMass_mono (ballLabelledWeight N d o ell) (ballLabelledWeight_nonnegative N d o ell) hcover).trans
    (hrare o z hz hzB hfloor Cq)

end LocalLaw
