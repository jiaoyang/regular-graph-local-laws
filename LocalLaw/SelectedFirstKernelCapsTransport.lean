import LocalLaw.ActualPartialBInverseCaps
import LocalLaw.PartialFirstDeletionCaps

/-! # Sampled-block bounds on the literal selected vertex set -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance selectedFirstKernelTransportDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} [Fintype V] {T : Set V} {ι : Type} [Fintype ι]

omit [Fintype V] [Fintype ι] in
theorem partialFirst_removed_offdiagonal_of_indexed (s : LabelledResamplingState V T ι)
    (selector : ℕ) (S : Set (Tᶜ : Set V)) (G : Matrix S S ℂ) (δ : ℝ)
    (h : ∀i j : s.partialFirstMask selector S, i ≠ j →
      ‖G (s.partialFirstEmbedding selector S i) (s.partialFirstEmbedding selector S j)‖ ≤ δ) :
    ∀u v : s.partialFirstRemovedSet selector S, u ≠ v → ‖G u.val v.val‖ ≤ δ := by
  intro u v huv
  let e := s.partialFirstRemovalEquiv selector S
  have hi : s.partialFirstEmbedding selector S (e.symm u) = u.val :=
    congrArg Subtype.val (e.apply_symm_apply u)
  have hj : s.partialFirstEmbedding selector S (e.symm v) = v.val :=
    congrArg Subtype.val (e.apply_symm_apply v)
  have hne : e.symm u ≠ e.symm v := fun hh => huv (e.symm.injective hh)
  simpa only [hi,hj] using h (e.symm u) (e.symm v) hne

omit [Fintype V] in
theorem partialFirst_removed_diagonal_of_endpoint_rows (s : LabelledResamplingState V T ι)
    (selector : ℕ) (S : Set (Tᶜ : Set V)) (G : Matrix S S ℂ) (C : ℝ)
    (h : ∀i : s.PartialEndpointIndex selector S,
      ∑j : s.PartialEndpointIndex selector S,
        ‖G (s.partialEndpointEmbedding selector S i) (s.partialEndpointEmbedding selector S j)‖ ≤ C) :
    ∀u : s.partialFirstRemovedSet selector S, ‖G u.val u.val‖ ≤ C := by
  intro u
  let e := s.partialFirstRemovalEquiv selector S
  let i : s.PartialEndpointIndex selector S := .inr (.inl (e.symm u))
  have hi : s.partialEndpointEmbedding selector S i = u.val :=
    congrArg Subtype.val (e.apply_symm_apply u)
  have hsingle : ‖G (s.partialEndpointEmbedding selector S i) (s.partialEndpointEmbedding selector S i)‖ ≤
      ∑j : s.PartialEndpointIndex selector S,
        ‖G (s.partialEndpointEmbedding selector S i) (s.partialEndpointEmbedding selector S j)‖ :=
    Finset.single_le_sum (fun j _ => norm_nonneg (G (s.partialEndpointEmbedding selector S i)
      (s.partialEndpointEmbedding selector S j))) (Finset.mem_univ i)
  simpa only [hi] using hsingle.trans (h i)

end LabelledResamplingState
end LocalLaw
