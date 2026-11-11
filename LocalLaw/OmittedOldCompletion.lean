import LocalLaw.OmittedLeafBudget
import LocalLaw.DeletedLeafOriginalMap
import LocalLaw.ImmersionForest
import LocalLaw.PartialSampleTreeTail

/-! # The old lost-neighbor part of the actual omitted-slot completion

Its artificial leaves map to the literal removed B endpoints. This map is
locally injective, and its core deficit is exactly the inherited old deficit.
-/
noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance omittedOldCompletionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type}[Fintype V]{T : Set V}{ι : Type}[Fintype ι]

def omittedOldOriginalVertex (s : LabelledResamplingState V T ι)(selector : ℕ)
    (S : Set (Tᶜ : Set V)) : s.OmittedCore selector S ⊕ s.OmittedOldLeaves selector S → (Tᶜ : Set V) :=
  Sum.elim (fun v => v.val.val) (fun l => l.2.val.val)

def omittedOldOriginalHom (s : LabelledResamplingState V T ι)(selector : ℕ)
    (S : Set (Tᶜ : Set V)) :
    multiLeafGraph (((outsideGraph s.graph T).induce
      ((s.selectedFirstSet selector)ᶜ : Set (Tᶜ : Set V))).induce {v | v.val ∈ S})
      (Sigma.fst : s.OmittedOldLeaves selector S → s.OmittedCore selector S) →g outsideGraph s.graph T where
  toFun := s.omittedOldOriginalVertex selector S
  map_rel' := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact hab
      | inr b =>
        change a=b.1 at hab
        subst a
        exact b.2.property.symm
    | inr a =>
      cases b with
      | inl b =>
        change b=a.1 at hab
        subst b
        exact a.2.property
      | inr b => exact False.elim hab

omit [Fintype V] [Fintype ι] in
theorem omittedOldOriginal_locally_injective (s : LabelledResamplingState V T ι)(selector : ℕ)
    (S : Set (Tᶜ : Set V)) : GraphHomLocallyInjective (s.omittedOldOriginalHom selector S) := by
  intro x a b ha hb he
  cases x with
  | inl x =>
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext (Subtype.ext he))
      | inr b =>
        change a.val.val=b.2.val.val at he
        exact False.elim (a.val.property (he.symm ▸ b.2.val.property))
    | inr a =>
      cases b with
      | inl b =>
        change a.2.val.val=b.val.val at he
        exact False.elim (b.val.property (he ▸ a.2.val.property))
      | inr b =>
        rcases a with ⟨va,ta⟩
        rcases b with ⟨vb,tb⟩
        change x=va at ha
        change x=vb at hb
        subst va
        subst vb
        have ht : ta=tb := Subtype.ext (Subtype.ext he)
        subst tb
        rfl
  | inr x =>
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        change a=x.1 at ha
        change b=x.1 at hb
        exact congrArg Sum.inl (ha.trans hb.symm)
      | inr b => exact False.elim hb
    | inr a => exact False.elim ha

end LabelledResamplingState
namespace RegularGraph
variable {N d : ℕ}{ι : Type}[Fintype ι]

omit [Fintype ι] in
theorem omittedOldMate_restore_budget (g : RegularGraph N d)(T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T)(samples : LocalSamplingFiber g.graph T)
    (selector : ℕ)(S : Set (Tᶜ : Set (Fin N)))
    (v : (g.admissibleState T labels samples).OmittedCore selector S) :
    multiLeafMultiplicity (Sigma.fst : (g.admissibleState T labels samples).OmittedOldLeaves selector S →
      (g.admissibleState T labels samples).OmittedCore selector S) v ≤
        (g.omittedCommonModel T labels samples selector S).deficit v := by
  change Nat.card {l:(g.admissibleState T labels samples).OmittedOldLeaves selector S //l.1=v} ≤ _
  rw [Nat.card_congr ((g.admissibleState T labels samples).omittedOldFiberEquiv selector S v),
    g.omittedCommonModel_deficit]
  exact Nat.le_add_left _ _

def omittedOldCompletion (g : RegularGraph N d)(hd : 1 ≤ d)(T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T)(samples : LocalSamplingFiber g.graph T)
    (selector : ℕ)(S : Set (Tᶜ : Set (Fin N))) :=
  (g.omittedCommonModel T labels samples selector S).attachLeaves hd Sigma.fst
    (g.omittedOldMate_restore_budget T labels samples selector S)

omit [Fintype ι] in
theorem omittedOldCompletion_core_deficit (g : RegularGraph N d)(hd : 1 ≤ d)(T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T)(samples : LocalSamplingFiber g.graph T)
    (selector : ℕ)(S : Set (Tᶜ : Set (Fin N)))
    (v : (g.admissibleState T labels samples).OmittedCore selector S) :
    (g.omittedOldCompletion hd T labels samples selector S).deficit (.inl v) =
      (g.deficient.delete T).deficit v.val.val := by
  change (g.omittedCommonModel T labels samples selector S).deficit v -
    multiLeafMultiplicity Sigma.fst v = _
  rw [g.omittedCommonModel_deficit]
  change (g.deficient.delete T).deficit v.val.val + _ -
    Nat.card {l:(g.admissibleState T labels samples).OmittedOldLeaves selector S //l.1=v} = _
  rw [Nat.card_congr ((g.admissibleState T labels samples).omittedOldFiberEquiv selector S v)]
  exact Nat.add_sub_cancel _ _

omit [Fintype ι] in
theorem omittedOldCompletion_leaf_tree_zero (g : RegularGraph N d)(hd : 1 ≤ d)(T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T)(samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ)(hr : r+1 ≤ selector)(S : Set (Tᶜ : Set (Fin N)))
    (l : (g.admissibleState T labels samples).OmittedOldLeaves selector S) :
    let H := g.omittedOldCompletion hd T labels samples selector S
    (graphBall H.graph (.inr l) r).IsTree ∧
      ∀v ∈ graphBallVertices H.graph (.inr l) r,H.deficit v=0 := by
  dsimp only
  let s := g.admissibleState T labels samples
  let H := g.omittedOldCompletion hd T labels samples selector S
  let f := s.omittedOldOriginalHom selector S
  obtain ⟨i,hi⟩ := l.2.val.property
  have hp := g.eligible_sample_root_tree_zero_ball T labels samples selector r hr i
    l.2.val.val (Or.inl hi.symm)
  have hmap : ∀v ∈ graphBallVertices H.graph (.inr l) r,
      f v ∈ graphBallVertices (outsideGraph g.graph T) l.2.val.val r := by
    intro v hv
    exact (graphHom_edist_le f (.inr l) v).trans hv
  constructor
  · exact graphBall_tree_of_locally_injective_hom f
      (s.omittedOldOriginal_locally_injective selector S) (.inr l) r r hmap hp.1
  · intro v hv
    cases v with
    | inl v =>
      rw [g.omittedOldCompletion_core_deficit]
      exact hp.2 v.val.val (hmap (.inl v) hv)
    | inr k => rfl

end RegularGraph
end LocalLaw
