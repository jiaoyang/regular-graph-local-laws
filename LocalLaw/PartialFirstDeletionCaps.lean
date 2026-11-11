import LocalLaw.TwoPivotModelCaps
import LocalLaw.SourcePartialWeakCovariance

/-! # Actual retained sampled-first deletion caps

The retained first-endpoint mask is explicitly equivalent to the actual
removed vertex set. Its pI covariance follows from the proved full partial
ABC covariance; the genuine deleted kernel cap then follows by Schur.
-/
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance partialFirstDeletionDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type}

def partialFirstRemovedSet (s:LabelledResamplingState V T ι)(selector:ℕ)
    (S:Set (Tᶜ:Set V)) : Set S := {v | v.val∈s.selectedFirstSet selector}

def partialFirstRemovalEquiv (s:LabelledResamplingState V T ι)(selector:ℕ)
    (S:Set (Tᶜ:Set V)) : s.partialFirstMask selector S≃s.partialFirstRemovedSet selector S :=
  Equiv.ofBijective (fun i=>⟨⟨s.admissibleSampleVertex selector i.val,i.property⟩,⟨i.val,rfl⟩⟩) (by
    constructor
    · intro i j h
      exact Subtype.ext ((s.selectedFirstEmbedding selector).injective
        (congrArg (fun v:s.partialFirstRemovedSet selector S=>v.val.val) h))
    · intro v
      obtain ⟨i,hi⟩:=v.property
      have hm:i∈s.partialFirstMask selector S := by
        change s.admissibleSampleVertex selector i∈S
        rw [show s.admissibleSampleVertex selector i=v.val.val from hi]
        exact v.val.property
      exact ⟨⟨i,hm⟩,Subtype.ext (Subtype.ext hi)⟩)

theorem partialFirst_covariance_block (s:LabelledResamplingState V T ι)(selector:ℕ)
    (S:Set (Tᶜ:Set V))(G:Matrix S S ℂ)(q p α:ℂ)(σ:ℝ)
    (hcov:∀i j,‖(G.submatrix (s.partialEndpointEmbedding selector S)
      (s.partialEndpointEmbedding selector S)-s.partialOldCovariance selector S G q p α) i j‖≤σ) :
    ∀i j:s.partialFirstRemovedSet selector S,
      ‖(G.submatrix (Subtype.val:(s.partialFirstRemovedSet selector S)→S)
        (Subtype.val:(s.partialFirstRemovedSet selector S)→S)-p•1) i j‖≤σ := by
  intro i j
  let e:=s.partialFirstRemovalEquiv selector S
  let bi:=e.symm i
  let bj:=e.symm j
  have hi:(s.partialEndpointEmbedding selector S) (.inr (.inl bi))=i.val :=
    congrArg Subtype.val (e.apply_symm_apply i)
  have hj:(s.partialEndpointEmbedding selector S) (.inr (.inl bj))=j.val :=
    congrArg Subtype.val (e.apply_symm_apply j)
  have hij:bi=bj ↔ i=j := e.symm.injective.eq_iff
  have hh:=hcov (.inr (.inl bi)) (.inr (.inl bj))
  simp only [Matrix.sub_apply,Matrix.submatrix_apply,partialOldCovariance,
    Matrix.fromBlocks_apply₂₂,partialSampleCovariance,Matrix.fromBlocks_apply₁₁,
    Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,hi,hj,hij] at hh ⊢
  exact hh

def partialFirstRemovalInterEquiv (s:LabelledResamplingState V T ι)(selector:ℕ)
    (S:Set (Tᶜ:Set V)) : s.partialFirstRemovedSet selector S≃
      {v:(Tᶜ:Set V) // v∈s.selectedFirstSet selector ∧ v∈S} where
  toFun v:=⟨v.val.val,v.property,v.val.property⟩
  invFun v:=⟨⟨v.val,v.property.2⟩,v.property.1⟩
  left_inv _:=rfl
  right_inv _:=rfl

variable [Fintype V] [Fintype ι]

theorem partialFirstRemovedSet_new_pair_card (s:LabelledResamplingState V T ι)
    (selector r:ℕ)(hsep:2*r≤selector)(x y:(Tᶜ:Set V)) :
    Nat.card (s.partialFirstRemovedSet selector
      (pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r))≤2 := by
  rw [Nat.card_congr (s.partialFirstRemovalInterEquiv selector _)]
  exact s.selectedFirst_new_pairBall_card selector r hsep x y

end LabelledResamplingState
end LocalLaw
