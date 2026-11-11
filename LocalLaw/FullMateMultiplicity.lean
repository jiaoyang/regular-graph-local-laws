import LocalLaw.FullCoreMateModel

/-! # Repeated interior mates cost only the actual degree

Outer retained mates are unique. Inner mates may repeat, but their boundary
labels inject into actual neighbors, giving total leaf multiplicity at most d+1.
-/

noncomputable section
namespace LocalLaw
local instance fullMateMultiplicityDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} [Fintype V] {T : Set V} {ι : Type} [Fintype ι]

omit [Fintype V] [Fintype ι] in
theorem fullOuterMate_fiber_card (s : LabelledResamplingState V T ι) (selector : ℕ) (S : Set V)
    (k : s.fullCoreMask S) :
    Nat.card {i : s.fullFirstMask selector S // s.fullOuterMate selector S i.val = some k} ≤ 1 := by
  let f : {i : s.fullFirstMask selector S // s.fullOuterMate selector S i.val = some k} → PUnit.{1} := fun _ => PUnit.unit
  have hf : Function.Injective f := by
    intro i j _
    apply Subtype.ext
    apply Subtype.ext
    exact s.fullOuterMate_unique selector S i.val.val j.val.val k i.property j.property
  simpa only [Nat.card_unique] using Nat.card_le_card_of_injective f hf

theorem fullInnerMate_fiber_card (s : LabelledResamplingState V T ι) (selector : ℕ) (S : Set V)
    (k : s.fullCoreMask S) :
    Nat.card {i : s.fullSecondMask selector S // s.fullInnerMate selector S i.val = some k} ≤ s.graph.degree k.val := by
  let A := {i : s.fullSecondMask selector S // s.fullInnerMate selector S i.val = some k}
  let f : A → s.graph.neighborSet k.val := fun i =>
    ⟨(s.admissibleBoundaryVertex selector i.val.val).val,by
      have hi := (s.fullInnerMate_eq_some selector S i.val.val k).mp i.property
      have he : s.graph.Adj (s.quad i.val.val.val).a (s.admissibleBoundaryVertex selector i.val.val).val :=
        (s.boundary i.val.val.val).property.1
      simpa only [hi] using he⟩
  have hf : Function.Injective f := by
    intro i j he
    have hout := congrArg Subtype.val he
    have hi := (s.fullInnerMate_eq_some selector S i.val.val k).mp i.property
    have hj := (s.fullInnerMate_eq_some selector S j.val.val k).mp j.property
    have hboundary : s.boundary i.val.val.val = s.boundary j.val.val.val := by
      apply Subtype.ext
      apply Prod.ext
      · exact hi.trans hj.symm
      · exact hout
    exact Subtype.ext (Subtype.ext (Subtype.ext (s.boundary.injective hboundary)))
  have hh := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree] using hh

theorem fullLeafMate_multiplicity (s : LabelledResamplingState V T ι) (selector : ℕ) (S : Set V)
    (k : s.fullCoreMask S) :
    Nat.card {j : s.fullFirstMask selector S ⊕ s.fullSecondMask selector S //
      fullQuadLeafMate (s.fullInnerMate selector S) (s.fullOuterMate selector S)
        (s.fullFirstMask selector S) (s.fullSecondMask selector S) j = some k} ≤ s.graph.degree k.val + 1 := by
  have hsplit : Nat.card {j : s.fullFirstMask selector S ⊕ s.fullSecondMask selector S //
      fullQuadLeafMate (s.fullInnerMate selector S) (s.fullOuterMate selector S)
        (s.fullFirstMask selector S) (s.fullSecondMask selector S) j = some k} =
      Nat.card {i : s.fullFirstMask selector S // s.fullOuterMate selector S i.val = some k} +
      Nat.card {i : s.fullSecondMask selector S // s.fullInnerMate selector S i.val = some k} := by
    let φ : {j : s.fullFirstMask selector S ⊕ s.fullSecondMask selector S //
        fullQuadLeafMate (s.fullInnerMate selector S) (s.fullOuterMate selector S)
          (s.fullFirstMask selector S) (s.fullSecondMask selector S) j = some k} ≃
        ({i : s.fullFirstMask selector S // s.fullOuterMate selector S i.val = some k} ⊕
          {i : s.fullSecondMask selector S // s.fullInnerMate selector S i.val = some k}) :=
      { toFun := fun j => match j with
          | ⟨.inl b,hb⟩ => .inl ⟨b,hb⟩
          | ⟨.inr c,hc⟩ => .inr ⟨c,hc⟩
        invFun := fun j => match j with
          | .inl b => ⟨.inl b.val,b.property⟩
          | .inr c => ⟨.inr c.val,c.property⟩
        left_inv := by rintro ⟨j,hj⟩; rcases j with b | c <;> rfl
        right_inv := by rintro (⟨b,hb⟩ | ⟨c,hc⟩) <;> rfl }
    simpa only [Nat.card_sum] using Nat.card_congr φ
  rw [hsplit]
  have ho := s.fullOuterMate_fiber_card selector S k
  have hi := s.fullInnerMate_fiber_card selector S k
  omega

end LabelledResamplingState
end LocalLaw
