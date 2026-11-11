import LocalLaw.GlobalLabelledResampling
import LocalLaw.ResamplingBallPreservation

/-!
# The graph-dependent ball-resampling probability kernel

Mix the fixed-T labelled spaces over all finite vertex subsets, retaining only
states whose T is the original radius-ell ball. The actual switching map
preserves that support. Marginality follows because each graph has exactly
one such T, and the ball-count budget proves that its sample fibers are
nonempty. This gives the literal graph-dependent local-resampling kernel.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

namespace LocalLaw

local instance ballMeasureDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- T is exactly the radius-ell neighborhood selected from the original graph. -/
def ChosenResamplingBall {N d : ℕ} (o : Fin N) (ell : ℕ) (T : Set (Fin N))
    (g : RegularGraph N d) : Prop := graphBallVertices g.graph o ell = T

/-- Forward preservation of the actual chosen ball under the fixed-T kernel. -/
theorem globalLabelled_chosenBall_forward (N d : ℕ) (T : Set (Fin N))
    (o : Fin N) (ell radius : ℕ) (ω : GlobalLabelledSpace N d T)
    (hBall : ChosenResamplingBall o ell T (globalLabelledProject ω)) :
    ChosenResamplingBall o ell T
      (globalLabelledProject (globalLabelledPermutation N d T radius ω)) := by
  let s := (labelledBlockStateEquiv N d ω.1.val T ω.2).val
  have hT : T = graphSetBall s.graph {o} ell := by
    rw [graphSetBall_singleton]
    exact hBall.symm
  have h := s.fullResample_ball radius {o} ell hT
  change graphBallVertices (s.fullResample radius).graph o ell = T
  simpa only [graphSetBall_singleton] using h

/-- Ball support invariance follows from actual ball preservation and the
proved involution; it is not assumed for the probability construction. -/
theorem globalLabelled_chosenBall_iff (N d : ℕ) (T : Set (Fin N))
    (o : Fin N) (ell radius : ℕ) (ω : GlobalLabelledSpace N d T) :
    ChosenResamplingBall o ell T
      (globalLabelledProject (globalLabelledPermutation N d T radius ω)) ↔
      ChosenResamplingBall o ell T (globalLabelledProject ω) := by
  constructor
  · intro h
    have h' := globalLabelled_chosenBall_forward N d T o ell radius
      (globalLabelledPermutation N d T radius ω) h
    have hinv : globalLabelledPermutation N d T radius
        (globalLabelledPermutation N d T radius ω) = ω :=
      globalLabelledResample_involutive N d T radius ω
    rw [hinv] at h'
    exact h'
  · exact globalLabelled_chosenBall_forward N d T o ell radius ω

/-- Fixed-T weights restricted to the event that T is the selected ball. -/
def ballRestrictedWeight (N d : ℕ) (T : Set (Fin N)) (o : Fin N) (ell : ℕ)
    (ω : GlobalLabelledSpace N d T) : ℝ :=
  if ChosenResamplingBall o ell T (globalLabelledProject ω) then globalLabelledWeight N d T ω else 0

/-- The restricted fixed-T space has the original graph marginal restricted
to its chosen-ball block. For large T both sides vanish by the ball-count budget. -/
theorem ballRestrictedWeight_projection (N d : ℕ) (T : Set (Fin N)) (o : Fin N) (ell : ℕ)
    (hN : 0 < N) (hd : 0 < d) (hbudget : 4 * (d + 1) ^ ell ≤ N)
    (P : RegularGraph N d → Prop) :
    eventMass (ballRestrictedWeight N d T o ell) (fun ω => P (globalLabelledProject ω)) =
      eventMass (finiteUniformWeight (RegularGraph N d))
        (fun g => ChosenResamplingBall o ell T g ∧ P g) := by
  by_cases hsmall : 4 * Nat.card T ≤ N
  · have hevent : eventMass (ballRestrictedWeight N d T o ell)
        (fun ω => P (globalLabelledProject ω)) = eventMass (globalLabelledWeight N d T)
          (fun ω => ChosenResamplingBall o ell T (globalLabelledProject ω) ∧
            P (globalLabelledProject ω)) := by
      unfold eventMass ballRestrictedWeight
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hB : ChosenResamplingBall o ell T (globalLabelledProject ω) <;>
        by_cases hP : P (globalLabelledProject ω) <;> simp [hB, hP]
    rw [hevent]
    exact globalLabelledWeight_projection N d T hN hd hsmall
      (fun g => ChosenResamplingBall o ell T g ∧ P g)
  · have hNoBall : ∀ g : RegularGraph N d, ¬ ChosenResamplingBall o ell T g := by
      intro g hBall
      apply hsmall
      have h := g.ball_small o ell hbudget
      rw [hBall] at h
      exact h
    simp [eventMass, ballRestrictedWeight, hNoBall]

/-- Finite enlarged space retaining the deterministic chosen ball as an
auxiliary index. Off-support states have weight zero. -/
def BallLabelledSpace (N d : ℕ) : Type := Σ T : Set (Fin N), GlobalLabelledSpace N d T

instance ballLabelledSpaceFintype (N d : ℕ) : Fintype (BallLabelledSpace N d) := by
  unfold BallLabelledSpace
  infer_instance

def ballLabelledProject {N d : ℕ} (ω : BallLabelledSpace N d) : RegularGraph N d :=
  globalLabelledProject ω.2

def ballLabelledWeight (N d : ℕ) (o : Fin N) (ell : ℕ) (ω : BallLabelledSpace N d) : ℝ :=
  ballRestrictedWeight N d ω.1 o ell ω.2

theorem ballLabelledWeight_nonnegative (N d : ℕ) (o : Fin N) (ell : ℕ)
    (ω : BallLabelledSpace N d) : 0 ≤ ballLabelledWeight N d o ell ω := by
  unfold ballLabelledWeight ballRestrictedWeight
  split
  · exact globalLabelledWeight_nonnegative N d ω.1 ω.2
  · exact le_rfl

/-- Perform the actual static-T permutation in each selected-ball component. -/
def ballLabelledResample (N d : ℕ) (radius : ℕ) (ω : BallLabelledSpace N d) : BallLabelledSpace N d :=
  ⟨ω.1, globalLabelledPermutation N d ω.1 radius ω.2⟩

theorem ballLabelledResample_involutive (N d radius : ℕ) :
    Function.Involutive (ballLabelledResample N d radius) := by
  rintro ⟨T, ω⟩
  exact congrArg (fun s : GlobalLabelledSpace N d T => (⟨T, s⟩ : BallLabelledSpace N d))
    (globalLabelledResample_involutive N d T radius ω)

def ballLabelledPermutation (N d radius : ℕ) : Equiv.Perm (BallLabelledSpace N d) :=
  Function.Involutive.toPerm (ballLabelledResample N d radius)
    (ballLabelledResample_involutive N d radius)

/-- All weights, including the graph-dependent chosen-ball support, are
preserved by the actual source permutation. -/
theorem ballLabelledWeight_preserved (N d : ℕ) (o : Fin N) (ell radius : ℕ) :
    ∀ ω, ballLabelledWeight N d o ell (ballLabelledPermutation N d radius ω) =
      ballLabelledWeight N d o ell ω := by
  rintro ⟨T, ω⟩
  change (if ChosenResamplingBall o ell T
      (globalLabelledProject (globalLabelledPermutation N d T radius ω))
    then globalLabelledWeight N d T (globalLabelledPermutation N d T radius ω) else 0) = _
  rw [globalLabelled_chosenBall_iff N d T o ell radius ω,
    globalLabelledWeight_preserved N d T radius ω]
  rfl

/-- Summing over all T selects each graph's one actual radius-ell ball. -/
theorem ballLabelledWeight_projection (N d : ℕ) (o : Fin N) (ell : ℕ)
    (hN : 0 < N) (hd : 0 < d) (hbudget : 4 * (d + 1) ^ ell ≤ N)
    (P : RegularGraph N d → Prop) :
    eventMass (ballLabelledWeight N d o ell) (fun ω => P (ballLabelledProject ω)) =
      eventMass (finiteUniformWeight (RegularGraph N d)) P := by
  calc
    eventMass (ballLabelledWeight N d o ell) (fun ω => P (ballLabelledProject ω)) =
        ∑ T : Set (Fin N), eventMass (ballRestrictedWeight N d T o ell)
          (fun ω => P (globalLabelledProject ω)) := by
      unfold eventMass
      exact Fintype.sum_sigma (fun ω : BallLabelledSpace N d =>
        if P (ballLabelledProject ω) then ballLabelledWeight N d o ell ω else 0)
    _ = ∑ T : Set (Fin N), eventMass (finiteUniformWeight (RegularGraph N d))
        (fun g => ChosenResamplingBall o ell T g ∧ P g) := by
      apply Finset.sum_congr rfl
      intro T _
      exact ballRestrictedWeight_projection N d T o ell hN hd hbudget P
    _ = eventMass (finiteUniformWeight (RegularGraph N d)) P := by
      unfold eventMass
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      by_cases hP : P g
      · simp [ChosenResamplingBall, hP]
      · simp [hP]

/-- The source's graph-dependent ball-resampling weights form a probability
law when the original regular-graph ensemble is nonempty. -/
theorem ballLabelledWeight_normalized (N d : ℕ) [Nonempty (RegularGraph N d)]
    (o : Fin N) (ell : ℕ) (hN : 0 < N) (hd : 0 < d) (hbudget : 4 * (d + 1) ^ ell ≤ N) :
    (∑ ω : BallLabelledSpace N d, ballLabelledWeight N d o ell ω) = 1 := by
  have h := ballLabelledWeight_projection N d o ell hN hd hbudget (fun _ => True)
  have hbase := finiteUniformWeight_total (Γ := RegularGraph N d)
  simpa only [eventMass, if_true, hbase] using h

/-- Proposition 3.5 for the actual graph-dependent radius-ball resampling,
with retained uniform boundary labels as permitted auxiliary randomness. -/
theorem ball_labelled_resampling_stationary (N d : ℕ) (o : Fin N) (ell radius : ℕ)
    (hN : 0 < N) (hd : 0 < d) (hbudget : 4 * (d + 1) ^ ell ≤ N)
    (P : RegularGraph N d → Prop) :
    eventMass (ballLabelledWeight N d o ell)
      (fun ω => P (ballLabelledProject (ballLabelledPermutation N d radius ω))) =
      eventMass (finiteUniformWeight (RegularGraph N d)) P := by
  calc
    _ = eventMass (ballLabelledWeight N d o ell) (fun ω => P (ballLabelledProject ω)) :=
      eventMass_pullback _ (ballLabelledPermutation N d radius)
        (ballLabelledWeight_preserved N d o ell radius) (fun ω => P (ballLabelledProject ω))
    _ = _ := ballLabelledWeight_projection N d o ell hN hd hbudget P

/-- Actual reversible extension for Theorem42Inputs at a center and depth.
Every probability/combinatorial field is derived, rather than postulated. -/
def ballLabelledReversibleExtension (N d : ℕ) (o : Fin N) (ell radius : ℕ)
    (hN : 0 < N) (hd : 0 < d) (hbudget : 4 * (d + 1) ^ ell ≤ N) :
    ReversibleExtension (RegularGraph N d) (finiteUniformWeight (RegularGraph N d)) where
  space := BallLabelledSpace N d
  finite := inferInstance
  weight := ballLabelledWeight N d o ell
  nonnegative := ballLabelledWeight_nonnegative N d o ell
  project := ballLabelledProject
  marginal := ballLabelledWeight_projection N d o ell hN hd hbudget
  switching := ballLabelledPermutation N d radius
  preserve := ballLabelledWeight_preserved N d o ell radius
  involution := ballLabelledResample_involutive N d radius

end LocalLaw
