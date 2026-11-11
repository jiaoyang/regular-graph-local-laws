import LocalLaw.SourceCavityAverageCertificate
import LocalLaw.SourceCorrelationGoodSet
import LocalLaw.OmegaPlusRejectedKernel

/-! # Actual restricted-target cavity certificate failure in the reversible kernel

The three genuinely proved bad events are isolation failure, too many rejected
labels, and concentration failure for the deterministic cavity weights.
The target tree is transported backwards before the source-weight tail is
used. No probability of a desired local certificate is assumed.
-/

noncomputable section
set_option maxHeartbeats 3000000
namespace LocalLaw
local instance sourceCavityKernelProbabilityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def ballSourceCavityCertificateBad {N d : ℕ} (a : ℕ) (c β K : ℝ) (o : Fin N) (z : ℂ)
    (ξ : BallLabelledSpace N d) : Prop :=
  let ell := actualCavityDepth a d N z-1
  let R := logarithmicRadius (c/4) d N
  let gnew := ballLabelledProject (ballLabelledResample N d (R/4) ξ)
  (graphBall gnew.graph o R).IsTree ∧
    ¬gnew.sourceCavityAbsoluteResidual ell o z≤K*
      (graphPaperError a d N (logarithmicRadius β d N) z/Real.log (N:ℝ)^4)

theorem eventually_ballSourceCavityCertificateBad_probability
    (a b d p Cq : ℕ) (c β γ B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c) (hc₁ : c<1)
    (hβ : 0<β) (hβc : β≤c/32) (hγ : c/4<γ) (hgap : γ+β<1)
    (hB : 0≤B) (hC1 : 1≤C1)
    (hCdel : sourceDeletionConstant d β B≤C1) (hCq : finiteOmega d≤Cq) :
    ∃ q : ℕ,1≤q ∧ ∀ᶠ N : ℕ in Filter.atTop,∀ (o : Fin N) (z : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      let ell := actualCavityDepth a d N z-1
      let R := logarithmicRadius (c/4) d N
      let rn := logarithmicRadius β d N
      let r := effectiveModelRadius a d N β
      let K := sourceCavityAverageConstant d (sourceRejectionConstant Cq q) β C1
      eventMass (ballLabelledWeight N d o ell) (fun ξ =>
        (ballLabelledProject ξ).SourceOmegaPlusWithRadii a r rn R ell (finiteOmega d) Cq ⌊(N:ℝ)^γ⌋₊ C1 o z ∧
        (ballLabelledProject (ballLabelledResample N d (R/4) ξ)).SourceOmegaWithRadii a r rn R
          (finiteOmega d) ⌊(N:ℝ)^γ⌋₊ z ∧
        ballSourceCavityCertificateBad a c β K o z ξ)≤5/(N:ℝ)^p := by
  have hC10 : 0≤C1 := by linarith
  have hγ1 : γ<1 := by linarith
  obtain ⟨q,hq,hrejection⟩ := eventually_ballSourceRejectedBad_probability a d p c γ (by omega) hd hc hc₁ hγ1
  refine ⟨q,hq,?_⟩
  let J := sourceRejectionConstant Cq q
  filter_upwards [hrejection,
    RegularGraph.eventually_source_cavity_average_certificate a b d J c β γ B C1 Cq
      ha hb hd hc hβ hβc hγ hgap hB hC1 hCdel hCq,
    eventually_ballSourceGreenIsolationBad_probability a b d p c β C1 ha hb hd hc hc₁ hβ hβc hC10,
    eventually_ballSourceCavityWeightBad_probability a b d p c β γ B C1 ha hb hd hc hβ hβc hγ hgap hB hC1,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc]
    with N hrejection hcertificate hisolation hweights hrad
  intro o z hz hzB hfloor
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let R := logarithmicRadius (c/4) d N
  let rn := logarithmicRadius β d N
  let r := effectiveModelRadius a d N β
  let badCount := ⌊(N:ℝ)^γ⌋₊
  let K := sourceCavityAverageConstant d J β C1
  let A : RegularGraph N d → Prop := fun g =>
    g.SourceOmegaPlusWithRadii a r rn R ell (finiteOmega d) Cq badCount C1 o z
  let P₁ := fun ξ : BallLabelledSpace N d => A (ballLabelledProject ξ) ∧
    ballSourceGreenIsolationBad o ell a rn R z ξ
  let P₂ := fun ξ : BallLabelledSpace N d => A (ballLabelledProject ξ) ∧
    ballSourceRejectedBad o ell R Cq q ξ
  let P₃ := fun ξ : BallLabelledSpace N d => A (ballLabelledProject ξ) ∧
    (graphBall (ballLabelledProject ξ).graph o ell).IsTree ∧ ballSourceCavityWeightBad a c β C1 o z ξ
  have hcover : ∀ ξ : BallLabelledSpace N d,
      (A (ballLabelledProject ξ) ∧
      (ballLabelledProject (ballLabelledResample N d (R/4) ξ)).SourceOmegaWithRadii a r rn R (finiteOmega d) badCount z ∧
      ballSourceCavityCertificateBad a c β K o z ξ) → P₁ ξ ∨ P₂ ξ ∨ P₃ ξ := by
    intro ξ hf
    by_cases hi : ballSourceGreenIsolationBad o ell a rn R z ξ
    · exact Or.inl ⟨hf.1,hi⟩
    by_cases hj : ballSourceRejectedBad o ell R Cq q ξ
    · exact Or.inr (Or.inl ⟨hf.1,hj⟩)
    rcases ξ with ⟨T,μ,⟨g,hμ⟩,labels,samples⟩
    change ¬∀ h : graphBallVertices g.graph o ell=T,
      g.sourceGreenIsolationBad (graphBallVertices g.graph o ell) z
        (correlationThreshold (Real.log (N:ℝ)) a N z.im (graphKestenMcKayReference d z).im
          (spectralScale z) (graphPaperError a d N rn z)) (R/4) (Nat.ceil (Real.log (N:ℝ))) (h.symm ▸ samples) at hi
    push_neg at hi
    obtain ⟨hT,hi⟩ := hi
    cases hT
    have hplus : A g := hf.1
    have htarget : (g.labelledResampledGraph (graphBallVertices g.graph o ell) labels samples (R/4)).SourceOmegaWithRadii
        a r rn R (finiteOmega d) badCount z := hf.2.1
    have hTree : (graphBall (g.labelledResampledGraph (graphBallVertices g.graph o ell) labels samples (R/4)).graph o R).IsTree := hf.2.2.1
    have hfit : ell+effectiveModelRadius a d N β+1≤R/8 := by
      have hh := hrad.2.2.2 z
      change effectiveModelRadius a d N β+ell+1≤R/8 at hh
      omega
    let s := g.admissibleState (graphBallVertices g.graph o ell) labels samples
    have hTreeSmall : (graphBall g.graph o (R/8)).IsTree :=
      s.fullResample_tree_implies_source_eighth_tree R o ell rfl (by omega) hTree
    have hTreeEll := graphBall_tree_mono g.graph o (show ell≤R/8 by omega) hTreeSmall
    have hreject : (rejectedResamplingIndices g.graph (graphBallVertices g.graph o ell) (R/4) samples).card≤J := by
      by_contra h
      apply hj
      change canonicalBallSamplePredicate o ell (fun g S => sourceRejectionConstant Cq q<
        (rejectedResamplingIndices g.graph (graphBallVertices g.graph o ell) (R/4) S).card)
        (graphBallVertices g.graph o ell) g samples
      intro heq
      cases heq
      exact Nat.lt_of_not_ge h
    by_cases hw : g.SourceCavityWeightGood a c β C1 o z samples
    · have hgood := hcertificate g o z hz hzB hfloor badCount le_rfl hplus labels samples htarget hi hreject hw hTree
      exact False.elim (hf.2.2.2 hgood)
    · apply Or.inr ∘ Or.inr
      refine ⟨hplus,hTreeEll,?_⟩
      change canonicalBallSamplePredicate o ell (fun g S => ¬g.SourceCavityWeightGood a c β C1 o z S)
        (graphBallVertices g.graph o ell) g samples
      intro heq
      cases heq
      exact hw
  have hbound := eventMass_mono (ballLabelledWeight N d o ell) (ballLabelledWeight_nonnegative N d o ell) hcover
  have hu := eventMass_union_le (ballLabelledWeight N d o ell) (ballLabelledWeight_nonnegative N d o ell) P₁
    (fun ξ => P₂ ξ∨P₃ ξ)
  have hv := eventMass_union_le (ballLabelledWeight N d o ell) (ballLabelledWeight_nonnegative N d o ell) P₂ P₃
  have hi := hisolation o z hz hfloor Cq badCount
  have hj := hrejection o z r rn (finiteOmega d) Cq C1
  have hw := hweights o z hz hzB hfloor Cq
  exact hbound.trans ((hu.trans (add_le_add_left hv _)).trans (by
    change eventMass _ P₁+(eventMass _ P₂+eventMass _ P₃)≤_
    calc
      _ ≤ 3/(N:ℝ)^p+(1/(N:ℝ)^p+1/(N:ℝ)^p) := add_le_add hi (add_le_add hj hw)
      _ = _ := by ring))

end LocalLaw
