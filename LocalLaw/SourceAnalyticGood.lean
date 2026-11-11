import LocalLaw.SourceAnalyticKernel

/-! # Extract actual local analytic premises from the common good event

The extraction proves that the auxiliary retained set is the actual chosen
ball. It then transports the samples exactly once and returns all named
local premises with one rejection threshold.
-/

noncomputable section
namespace LocalLaw
local instance sourceAnalyticGoodDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem ballCanonicalSampleEvent_iff_of_chosen {N d : ℕ} (o : Fin N) (ell : ℕ)
    (P : ∀ g : RegularGraph N d, LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)→Prop)
    (ξ : BallLabelledSpace N d) (hT : graphBallVertices (ballLabelledProject ξ).graph o ell=ξ.1) :
    ballCanonicalSampleEvent o ell P ξ ↔
      P (ballLabelledProject ξ) (hT.symm ▸ globalLabelledSamples ξ.2) := by
  change (∀ h : graphBallVertices (ballLabelledProject ξ).graph o ell=ξ.1,
    P (ballLabelledProject ξ) (h.symm ▸ globalLabelledSamples ξ.2)) ↔ _
  constructor
  · exact fun h => h hT
  · intro h heq
    simpa only [Subsingleton.elim heq hT] using h

theorem ballCanonicalSampleEvent_chosen_of_not {N d : ℕ} (o : Fin N) (ell : ℕ)
    (P : ∀ g : RegularGraph N d, LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)→Prop)
    (ξ : BallLabelledSpace N d) (h : ¬ballCanonicalSampleEvent o ell P ξ) :
    graphBallVertices (ballLabelledProject ξ).graph o ell=ξ.1 := by
  by_contra hT
  apply h
  change ∀ heq : graphBallVertices (ballLabelledProject ξ).graph o ell=ξ.1,_
  exact fun heq => False.elim (hT heq)

namespace RegularGraph
variable {N d : ℕ}

def SourceAnalyticGood (g : RegularGraph N d) (a q Cq : ℕ) (c β C1 : ℝ) (o : Fin N) (z : ℂ)
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))) : Prop :=
  let ell := actualCavityDepth a d N z-1
  let R := logarithmicRadius (c/4) d N
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let φ := correlationThreshold (Real.log (N:ℝ)) a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
  ¬g.sourceGreenIsolationBad (graphBallVertices g.graph o ell) z φ (R/4) (Nat.ceil (Real.log (N:ℝ))) samples ∧
  (rejectedResamplingIndices g.graph (graphBallVertices g.graph o ell) (R/4) samples).card≤sourceRejectionConstant Cq q ∧
  g.SourceRetainedWeightGood a c β C1 o z samples ∧
  ((graphBall g.graph o ell).IsTree → g.SourceCavityWeightGood a c β C1 o z samples)

end RegularGraph

theorem sourceAnalyticGood_of_not_bad {N d : ℕ} (a q Cq : ℕ) (c β C1 : ℝ)
    (o : Fin N) (z : ℂ) (ξ : BallLabelledSpace N d)
    (h : ¬ballSourceAnalyticBad a q Cq c β C1 o z ξ) :
    ∃ hT : graphBallVertices (ballLabelledProject ξ).graph o (actualCavityDepth a d N z-1)=ξ.1,
      (ballLabelledProject ξ).SourceAnalyticGood a q Cq c β C1 o z
        (hT.symm ▸ globalLabelledSamples ξ.2) := by
  have hgood := ballSourceAnalyticBad_complement a q Cq c β C1 o z ξ h
  let ell := actualCavityDepth a d N z-1
  have hT := ballCanonicalSampleEvent_chosen_of_not o ell
    (fun g S => ¬g.SourceRetainedWeightGood a c β C1 o z S) ξ hgood.2.1
  refine ⟨hT,?_,?_,?_,?_⟩
  · intro hi
    apply hgood.1
    exact Or.inl ((ballCanonicalSampleEvent_iff_of_chosen o ell _ ξ hT).mpr hi)
  · by_contra hj
    apply hgood.1
    exact Or.inr ((ballCanonicalSampleEvent_iff_of_chosen o ell _ ξ hT).mpr (Nat.lt_of_not_ge hj))
  · by_contra hw
    apply hgood.2.1
    exact (ballCanonicalSampleEvent_iff_of_chosen o ell _ ξ hT).mpr hw
  · intro ht
    by_contra hw
    apply hgood.2.2 ht
    exact (ballCanonicalSampleEvent_iff_of_chosen o ell _ ξ hT).mpr hw

end LocalLaw
