import LocalLaw.OldTwoTargetAugmentation
import LocalLaw.SourceEndpointPerturbation
import LocalLaw.SourceEndpointMatrices

/-! # The old common surgery model captures the switched target balls

A newly created edge ends at a modified endpoint. After the last such edge,
the remaining walk is an old walk. The finite common model therefore
contains the actual switched pair neighborhood, without a post class claim.
-/

noncomputable section
namespace LocalLaw
local instance surgeryBallCaptureDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*}

theorem graphSetBall_perturbation_capture (G H : SimpleGraph V) (S E : Set V)
    (hnew : ∀ u v,H.Adj u v → G.Adj u v ∨ v∈E) (r : ℕ) :
    graphSetBall H S r⊆graphSetBall G S r∪graphSetBall G E r := by
  induction r with
  | zero =>
    simp only [graphSetBall_zero]
    exact Set.subset_union_left
  | succ r ih =>
    intro v hv
    rw [graphSetBall_succ_eq] at hv
    rcases hv with hv|⟨u,hu,huv⟩
    · rcases ih hv with hv|hv
      · exact Or.inl (graphSetBall_mono_radius G S (Nat.le_succ r) hv)
      · exact Or.inr (graphSetBall_mono_radius G E (Nat.le_succ r) hv)
    · rcases hnew u v huv with hold|hvE
      · rcases ih hu with hu|hu
        · left; rw [graphSetBall_succ_eq]; exact Or.inr ⟨u,hu,hold⟩
        · right; rw [graphSetBall_succ_eq]; exact Or.inr ⟨u,hu,hold⟩
      · exact Or.inr ⟨v,hvE,by simp⟩

theorem graphBall_perturbation_capture (G H : SimpleGraph V) (E : Set V)
    (hnew : ∀ u v,H.Adj u v → G.Adj u v ∨ v∈E) (x : V) (r : ℕ) :
    graphBallVertices H x r⊆graphBallVertices G x r∪graphSetBall G E r := by
  intro v hv
  have hh := graphSetBall_perturbation_capture G H {x} E hnew r
    (show v∈graphSetBall H {x} r from ⟨x,rfl,hv⟩)
  rcases hh with ⟨u,hu,hd⟩|hv
  · have heq : u=x := hu
    exact Or.inl (heq ▸ hd)
  · exact Or.inr hv

namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type*} [Fintype ι]

theorem fullResample_outside_ball_capture (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (x : (Tᶜ:Set V)) :
    graphBallVertices (outsideGraph (s.fullResample selector).graph T) x r⊆
      graphBallVertices (outsideGraph s.graph T) x r∪s.endpointModelVertices selector r := by
  apply graphBall_perturbation_capture
  intro u v huv
  by_cases hold : (outsideGraph s.graph T).Adj u v
  · exact Or.inl hold
  · right
    by_contra hv
    have hv' : v∉s.fullResampleOutsideEndpoints selector := fun h =>
      hv (s.fullResampleOutsideEndpoints_subset_modelRoots selector h)
    exact hold (((s.fullResample_outside_adj_of_away_left selector v u hv').mp huv.symm).symm)

theorem twoTargetEndpointVertices_contains_new_pair (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (x y : (Tᶜ:Set V)) :
    pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r⊆
      s.twoTargetEndpointVertices selector r x y := by
  intro v hv
  rcases hv with hx|hy
  · rcases s.fullResample_outside_ball_capture selector r x hx with hx|hK
    · exact Or.inr (Or.inl hx)
    · exact Or.inl hK
  · rcases s.fullResample_outside_ball_capture selector r y hy with hy|hK
    · exact Or.inr (Or.inr hy)
    · exact Or.inl hK

end LabelledResamplingState
end LocalLaw
