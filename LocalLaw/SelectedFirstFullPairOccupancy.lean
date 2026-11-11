import LocalLaw.PartialFirstDeletionCaps
import LocalLaw.BoundaryGuardAmbientDistance
import LocalLaw.PartialInnerMasks

/-! # Selected first vertices in full ambient pair neighborhoods

The accepted first vertices are guarded from T. Every short ambient walk
starting there stays outside T, so the selector separation is valid also
in the ambient metric. Hence every full pair ball meets at most two of them.
-/
noncomputable section
namespace LocalLaw
local instance selectedFirstFullPairDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type}

def selectedFirstAmbientSet (s : LabelledResamplingState V T ι) (selector : ℕ) : Set V :=
  Subtype.val '' s.selectedFirstSet selector

theorem selectedFirst_ambient_separated (s : LabelledResamplingState V T ι) (selector : ℕ) :
    ∀ a∈s.selectedFirstAmbientSet selector,∀ b∈s.selectedFirstAmbientSet selector,a≠b →
      (selector:ℕ∞)<s.graph.edist a b := by
  rintro a ⟨a0,⟨i,hi⟩,rfl⟩ b ⟨b0,hb,rfl⟩ hab
  have hguard:a0∈boundaryFarOutside s.graph T selector := by
    rw [←hi]
    exact s.admissibleSampleVertex_far_boundary selector i
  apply lt_of_not_ge
  intro hnear
  have hball:b0.val∈graphBallVertices s.graph a0.val selector:=hnear
  rw [boundaryFarOutside_ball_image s.graph T selector selector (by omega) a0 hguard] at hball
  obtain ⟨b1,hb1,heq⟩:=hball
  have heq':b1=b0:=Subtype.ext heq
  rw [heq'] at hb1
  exact not_lt_of_ge hb1 (s.selectedFirstSet_separated selector a0 ⟨i,hi⟩ b0 hb
    (fun h=>hab (congrArg Subtype.val h)))

variable [Fintype V]
theorem selectedFirst_old_full_pair_card (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (hsep : 2*r≤selector) (x y : V) :
    Nat.card {v : V // v∈s.selectedFirstAmbientSet selector ∧
      v∈pairBallVertices s.graph x y r}≤2 :=
  separated_set_pairBall_card_le_two _ _ selector r hsep (s.selectedFirst_ambient_separated selector) x y

variable [Fintype ι]
omit [Fintype V] in
theorem selectedFirstAmbientSet_fullResample (s : LabelledResamplingState V T ι) (selector : ℕ) :
    (s.fullResample selector).selectedFirstAmbientSet selector=s.selectedFirstAmbientSet selector := by
  unfold selectedFirstAmbientSet
  rw [s.selectedFirstSet_fullResample selector]

theorem selectedFirst_new_full_pair_card (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (hsep : 2*r≤selector) (x y : V) :
    Nat.card {v : V // v∈s.selectedFirstAmbientSet selector ∧
      v∈pairBallVertices (s.fullResample selector).graph x y r}≤2 := by
  rw [←s.selectedFirstAmbientSet_fullResample selector]
  exact (s.fullResample selector).selectedFirst_old_full_pair_card selector r hsep x y

theorem partialFirstRemovedSet_new_full_pair_card (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (hsep : 2*r≤selector) (x y : V) :
    Nat.card (s.partialFirstRemovedSet selector
      (s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r)))≤2 := by
  let S:=s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r)
  let f:s.partialFirstRemovedSet selector S→
      {v:V // v∈s.selectedFirstAmbientSet selector ∧
        v∈pairBallVertices (s.fullResample selector).graph x y r}:=
    fun v=>⟨v.val.val.val,⟨v.val.val,v.property,rfl⟩,v.val.property⟩
  have hf:Function.Injective f:=by
    intro u v huv
    have he:=congrArg (fun w:{v:V // v∈s.selectedFirstAmbientSet selector ∧
      v∈pairBallVertices (s.fullResample selector).graph x y r}=>w.val) huv
    change u.val.val.val=v.val.val.val at he
    exact Subtype.ext (Subtype.ext (Subtype.ext he))
  exact (Nat.card_le_card_of_injective f hf).trans (s.selectedFirst_new_full_pair_card selector r hsep x y)

end LabelledResamplingState
end LocalLaw
