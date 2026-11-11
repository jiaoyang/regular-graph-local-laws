import LocalLaw.RestrictedCommonModel
import LocalLaw.DeficientGraphIso

/-! # Exact local reindexing of the common deleted augmented model

All selected first endpoints are retained by the augmented region. Its
correctly deficient deletion, restricted to a smaller region, therefore
agrees with the canonical common model used by the omitted-slot completion.
-/

noncomputable section
set_option maxHeartbeats 2500000
namespace LocalLaw
local instance restrictedCommonLocalDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type} [Fintype ι]

def selectedCommonLocalEquiv (s : LabelledResamplingState V T ι) (selector : ℕ)
    (A S : Set (Tᶜ : Set V)) (hSA : S ⊆ A) :
    {u : ((s.partialFirstRemovedSet selector A)ᶜ : Set A) | u.val.val ∈ S} ≃
      s.OmittedCore selector S where
  toFun u := ⟨⟨u.val.val.val,u.val.property⟩,u.property⟩
  invFun v := ⟨⟨⟨v.val.val,hSA v.property⟩,v.val.property⟩,v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end LabelledResamplingState
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

omit [Fintype ι] in
theorem restricted_common_local_Green (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (A S : Set (Tᶜ : Set (Fin N)))
    (hA : (g.admissibleState T labels samples).selectedFirstSet selector ⊆ A)
    (hSA : S ⊆ A) (q z : ℂ) :
    let s := g.admissibleState T labels samples
    let M := (g.deficient.delete T).restrict A
    let B := s.partialFirstRemovedSet selector A
    let K : Set (Bᶜ : Set A) := {u | u.val.val ∈ S}
    let e := s.selectedCommonLocalEquiv selector A S hSA
    ((g.omittedCommonModel T labels samples selector S).extensionGreen q z).submatrix e e =
      ((M.delete B).restrict K).extensionGreen q z := by
  dsimp only
  let s := g.admissibleState T labels samples
  let W := s.selectedFirstSet selector
  let old := g.deficient.delete T
  let M := old.restrict A
  let B := s.partialFirstRemovedSet selector A
  let K : Set (Bᶜ : Set A) := {u | u.val.val ∈ S}
  let e : ((M.delete B).restrict K).graph ≃g
      (g.omittedCommonModel T labels samples selector S).graph :=
    { toEquiv := s.selectedCommonLocalEquiv selector A S hSA
      map_rel_iff' := Iff.rfl }
  have hδ : ∀v,((M.delete B).restrict K).deficit v =
      (g.omittedCommonModel T labels samples selector S).deficit (e v) := by
    intro v
    exact old.restrictionDeletion_deficit A W B (fun _ => Iff.rfl) hA v.val
  exact (g.omittedCommonModel T labels samples selector S).extensionGreen_iso
    ((M.delete B).restrict K) e hδ q z

theorem switched_restricted_common_local_Green (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (A S : Set (Tᶜ : Set (Fin N)))
    (hA : (g.admissibleState T labels samples).selectedFirstSet selector ⊆ A)
    (hSA : S ⊆ A) (q z : ℂ) :
    let s := g.admissibleState T labels samples
    let M := (g.labelledResampledGraph T labels samples selector).deficient.delete T
    let B := s.partialFirstRemovedSet selector A
    let K : Set (Bᶜ : Set A) := {u | u.val.val ∈ S}
    let e := s.selectedCommonLocalEquiv selector A S hSA
    ((g.omittedCommonModel T labels samples selector S).extensionGreen q z).submatrix e e =
      (((M.restrict A).delete B).restrict K).extensionGreen q z := by
  dsimp only
  rw [g.restricted_selectedFirst_deletion_eq T labels samples selector A hA]
  exact g.restricted_common_local_Green T labels samples selector A S hA hSA q z

end RegularGraph
end LocalLaw
