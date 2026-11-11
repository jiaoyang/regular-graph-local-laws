import LocalLaw.SelectedFirstDeletion
import LocalLaw.NewSampleGuardCaps

/-! # At most two selected first vertices meet a local pair ball

The J-test gives mutual separation in both the old and switched graphs.
Consequently one radius-h ball contains at most one selected first vertex,
and the union of two such balls contains at most two. The selected vertex
set itself is literally invariant under the actual labelled involution.
-/

noncomputable section
namespace LocalLaw
local instance selectedFirstPairDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type} [Fintype V]

theorem separated_set_ball_card_le_one (G : SimpleGraph V) (W : Set V)
    (selector h : ℕ) (hsep : 2*h ≤ selector)
    (hfar : ∀ a∈W,∀ b∈W,a≠b → (selector:ℕ∞)<G.edist a b) (x : V) :
    Nat.card {v : V // v∈W ∧ v∈graphBallVertices G x h} ≤ 1 := by
  apply (Finite.card_le_one_iff_subsingleton).mpr
  constructor
  intro a b
  apply Subtype.ext
  by_contra hab
  have hf := hfar a.val a.property.1 b.val b.property.1 hab
  have hh : G.edist a.val b.val ≤ (selector:ℕ∞) := by
    calc
      _ ≤ G.edist a.val x+G.edist x b.val := G.edist_triangle
      _ ≤ (h:ℕ∞)+(h:ℕ∞) := add_le_add
        (by simpa only [SimpleGraph.edist_comm] using a.property.2) b.property.2
      _ ≤ (selector:ℕ∞) := by
        simpa only [←Nat.cast_add] using (ENat.coe_le_coe.mpr (show h+h≤selector by omega))
  exact not_lt_of_ge hh hf

theorem separated_set_pairBall_card_le_two (G : SimpleGraph V) (W : Set V)
    (selector h : ℕ) (hsep : 2*h ≤ selector)
    (hfar : ∀ a∈W,∀ b∈W,a≠b → (selector:ℕ∞)<G.edist a b) (x y : V) :
    Nat.card {v : V // v∈W ∧ v∈pairBallVertices G x y h} ≤ 2 := by
  let A : Set V := {v | v∈W ∧ v∈graphBallVertices G x h}
  let B : Set V := {v | v∈W ∧ v∈graphBallVertices G y h}
  have heq : {v : V | v∈W ∧ v∈pairBallVertices G x y h}=A∪B := by
    ext v
    change (v∈W ∧ (v∈graphBallVertices G x h ∨ v∈graphBallVertices G y h)) ↔
      ((v∈W ∧ v∈graphBallVertices G x h) ∨ (v∈W ∧ v∈graphBallVertices G y h))
    tauto
  change Nat.card (↑{v : V | v∈W ∧ v∈pairBallVertices G x y h}) ≤ 2
  rw [heq]
  exact (Set.card_union_le A B).trans (Nat.add_le_add
    (separated_set_ball_card_le_one G W selector h hsep hfar x)
    (separated_set_ball_card_le_one G W selector h hsep hfar y))

namespace LabelledResamplingState
variable {T : Set V} {ι : Type} [Fintype ι]

omit [Fintype V] [Fintype ι] in
theorem selectedFirstSet_separated (s : LabelledResamplingState V T ι) (selector : ℕ) :
    ∀ a∈s.selectedFirstSet selector,∀ b∈s.selectedFirstSet selector,a≠b →
      (selector:ℕ∞)<(outsideGraph s.graph T).edist a b := by
  rintro a ⟨i,rfl⟩ b ⟨j,rfl⟩ hij
  exact s.selectedFirst_far selector i j (fun h=>hij (h ▸ rfl))

omit [Fintype V] in
theorem selectedFirstSet_fullResample (s : LabelledResamplingState V T ι) (selector : ℕ) :
    (s.fullResample selector).selectedFirstSet selector=s.selectedFirstSet selector := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    refine ⟨⟨i.val,(s.fullResample_eligible selector i.val).mp i.property⟩,?_⟩
    change s.sampledOutsideFirst i.val=(s.fullResample selector).sampledOutsideFirst i.val
    exact (s.fullResample_sampledOutsideFirst selector i.val).symm
  · rintro ⟨i,rfl⟩
    refine ⟨⟨i.val,(s.fullResample_eligible selector i.val).mpr i.property⟩,?_⟩
    change (s.fullResample selector).sampledOutsideFirst i.val=s.sampledOutsideFirst i.val
    exact s.fullResample_sampledOutsideFirst selector i.val

omit [Fintype ι] in
theorem selectedFirst_old_pairBall_card (s : LabelledResamplingState V T ι)
    (selector h : ℕ) (hsep : 2*h≤selector) (x y : (Tᶜ:Set V)) :
    Nat.card {v : (Tᶜ:Set V) // v∈s.selectedFirstSet selector ∧
      v∈pairBallVertices (outsideGraph s.graph T) x y h} ≤ 2 :=
  separated_set_pairBall_card_le_two _ _ selector h hsep (s.selectedFirstSet_separated selector) x y

theorem selectedFirst_new_pairBall_card (s : LabelledResamplingState V T ι)
    (selector h : ℕ) (hsep : 2*h≤selector) (x y : (Tᶜ:Set V)) :
    Nat.card {v : (Tᶜ:Set V) // v∈s.selectedFirstSet selector ∧
      v∈pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y h} ≤ 2 := by
  rw [←s.selectedFirstSet_fullResample selector]
  exact (s.fullResample selector).selectedFirst_old_pairBall_card selector h hsep x y

end LabelledResamplingState
end LocalLaw
