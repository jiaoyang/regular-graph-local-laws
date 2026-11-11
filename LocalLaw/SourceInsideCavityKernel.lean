import LocalLaw.SourceAnalyticGood
import LocalLaw.SourceInsideRow
import LocalLaw.SourceCavityAverageCertificate

/-! # Actual common inside-row and cavity improvement in the reversible kernel

The desired two estimates are derived on the common analytic good event.
The target weak/structural event is retained, and no probability bound for
the desired certificate is supplied as a hypothesis.
-/

noncomputable section
set_option maxHeartbeats 3000000
namespace LocalLaw
local instance sourceInsideCavityKernelDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def ballSourceInsideCavityGood {N d : ℕ} (a q Cq : ℕ) (c β B C1 : ℝ)
    (o : Fin N) (z : ℂ) (ξ : BallLabelledSpace N d) : Prop :=
  let R := logarithmicRadius (c/4) d N
  let r := effectiveModelRadius a d N β
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let L := Real.log (N:ℝ)
  let J := sourceRejectionConstant Cq q
  let gnew := ballLabelledProject (ballLabelledResample N d (R/4) ξ)
  (∀ y : ξ.1, ‖gnew.G z o y.val-gnew.P r z (gnew.Q z) o y.val‖≤
    sourceInsideBaseConstant d J β C1*(ε/L^2)+sourceInsideFeedbackConstant d β B*L^2*gnew.sourceFeedback z) ∧
  ((graphBall gnew.graph o R).IsTree →
    gnew.sourceCavityAbsoluteResidual (actualCavityDepth a d N z-1) o z≤sourceCavityAverageConstant d J β C1*(ε/L^4))

theorem eventually_ballSourceInsideCavityGood_failure (a b d p Cq : ℕ) (c β γ B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c) (hc₁ : c<1)
    (hβ : 0<β) (hβc : β≤c/32) (hγ : c/4<γ) (hgap : γ+β<1)
    (hB : 0≤B) (hC1 : 1≤C1) (hCdel : sourceDeletionConstant d β B≤C1) (hCq : finiteOmega d≤Cq) :
    ∃ q : ℕ,1≤q ∧ ∀ᶠ N : ℕ in Filter.atTop,∀ (o : Fin N) (z : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      let ell := actualCavityDepth a d N z-1
      let R := logarithmicRadius (c/4) d N
      let rn := logarithmicRadius β d N
      let r := effectiveModelRadius a d N β
      eventMass (ballLabelledWeight N d o ell) (fun ξ =>
        (ballLabelledProject ξ).SourceOmegaPlusWithRadii a r rn R ell (finiteOmega d) Cq ⌊(N:ℝ)^γ⌋₊ C1 o z ∧
        (ballLabelledProject (ballLabelledResample N d (R/4) ξ)).SourceOmegaWithRadii a r rn R
          (finiteOmega d) ⌊(N:ℝ)^γ⌋₊ z ∧
        ¬ballSourceInsideCavityGood a q Cq c β B C1 o z ξ)≤6/(N:ℝ)^p := by
  obtain ⟨q,hq,hrare⟩ := eventually_ballSourceAnalyticBad_probability a b d p c β γ B C1
    ha hb hd hc hc₁ hβ hβc hγ hgap hB hC1
  refine ⟨q,hq,?_⟩
  let J := sourceRejectionConstant Cq q
  filter_upwards [hrare,RegularGraph.eventually_source_inside_row a b d J c β γ B C1 Cq
    ha hb hd hc hβ hβc hγ hgap hB hC1 hCdel hCq,
    RegularGraph.eventually_source_cavity_average_certificate a b d J c β γ B C1 Cq
    ha hb hd hc hβ hβc hγ hgap hB hC1 hCdel hCq,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc]
    with N hrare hinside hcavity hmargin
  intro o z hz hzB hfloor
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let R := logarithmicRadius (c/4) d N
  let rn := logarithmicRadius β d N
  let r := effectiveModelRadius a d N β
  let badCount := ⌊(N:ℝ)^γ⌋₊
  have hcover : ∀ ξ : BallLabelledSpace N d,
      ((ballLabelledProject ξ).SourceOmegaPlusWithRadii a r rn R ell (finiteOmega d) Cq badCount C1 o z ∧
      (ballLabelledProject (ballLabelledResample N d (R/4) ξ)).SourceOmegaWithRadii a r rn R (finiteOmega d) badCount z ∧
      ¬ballSourceInsideCavityGood a q Cq c β B C1 o z ξ) →
      (ballLabelledProject ξ).SourceOmegaPlusWithRadii a r rn R ell (finiteOmega d) Cq badCount C1 o z ∧
        ballSourceAnalyticBad a q Cq c β C1 o z ξ := by
    intro ξ hf
    refine ⟨hf.1,?_⟩
    by_contra hbad
    obtain ⟨hT,hgood⟩ := sourceAnalyticGood_of_not_bad a q Cq c β C1 o z ξ hbad
    rcases ξ with ⟨T,μ,⟨g,hμ⟩,labels,samples⟩
    change graphBallVertices g.graph o ell=T at hT
    cases hT
    apply hf.2.2
    change (∀ y : graphBallVertices g.graph o ell,_ ) ∧ _
    have hplus := hf.1
    have htarget := hf.2.1
    refine ⟨hinside g o z hz hzB hfloor badCount le_rfl hplus labels samples htarget
      hgood.1 hgood.2.1 hgood.2.2.1,?_⟩
    intro htree
    let s := g.admissibleState (graphBallVertices g.graph o ell) labels samples
    have hfit : ell+r+1≤R/8 := by
      have hh := hmargin.2.2.2 z
      change r+ell+1≤R/8 at hh
      omega
    have hsmallTree : (graphBall g.graph o (R/8)).IsTree :=
      s.fullResample_tree_implies_source_eighth_tree R o ell rfl (by omega) htree
    have hellTree := graphBall_tree_mono g.graph o (show ell≤R/8 by omega) hsmallTree
    exact hcavity g o z hz hzB hfloor badCount le_rfl hplus labels samples htarget
      hgood.1 hgood.2.1 (hgood.2.2.2 hellTree) htree
  exact (eventMass_mono (ballLabelledWeight N d o ell) (ballLabelledWeight_nonnegative N d o ell) hcover).trans
    (hrare o z hz hzB hfloor Cq)

end LocalLaw
