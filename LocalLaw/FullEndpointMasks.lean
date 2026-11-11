import LocalLaw.PartialSurgeryCoupling
import LocalLaw.FullEndpointPerturbation

/-! # Independent full switching masks in arbitrary vertex restrictions

The core contains every retained interior or old boundary vertex, so repeated
interior endpoints have a single index. The sampled masks are independent:
a full pair neighborhood can retain either sampled endpoint and can cut T.
-/

noncomputable section
namespace LocalLaw
local instance fullEndpointMasksDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type}

def fullCoreRoots (s : LabelledResamplingState V T ι) : Set V :=
  T ∪ Subtype.val '' outerBoundaryRoots s.graph T

def fullCoreMask (s : LabelledResamplingState V T ι) (S : Set V) : Set V :=
  S ∩ s.fullCoreRoots

def fullFirstMask (s : LabelledResamplingState V T ι) (selector : ℕ) (S : Set V) :
    Set (s.AdmissibleSampleIndex selector) :=
  {i | (s.admissibleSampleVertex selector i).val ∈ S}

def fullSecondMask (s : LabelledResamplingState V T ι) (selector : ℕ) (S : Set V) :
    Set (s.AdmissibleSampleIndex selector) :=
  {i | (s.admissibleSecondVertex selector i).val ∈ S}

def FullEndpointIndex (s : LabelledResamplingState V T ι) (selector : ℕ) (S : Set V) :=
  s.fullCoreMask S ⊕ (s.fullFirstMask selector S ⊕ s.fullSecondMask selector S)

def fullCoreEmbedding (s : LabelledResamplingState V T ι) (S : Set V) : s.fullCoreMask S ↪ S where
  toFun v := ⟨v.val, v.property.1⟩
  inj' v w h := by
    apply Subtype.ext
    exact congrArg (fun x : S => x.val) h

def fullPartialVertex (s : LabelledResamplingState V T ι) (selector : ℕ) (S : Set V) :
    s.FullEndpointIndex selector S → S
  | .inl v => s.fullCoreEmbedding S v
  | .inr (.inl b) => ⟨(s.admissibleSampleVertex selector b.val).val, b.property⟩
  | .inr (.inr c) => ⟨(s.admissibleSecondVertex selector c.val).val, c.property⟩

theorem farOutside_not_fullCore (s : LabelledResamplingState V T ι) (h : ℕ)
    (v : (Tᶜ : Set V)) (hfar : v ∈ boundaryFarOutside s.graph T h) :
    v.val ∉ s.fullCoreRoots := by
  rintro (hT | ⟨w, ⟨α, rfl⟩, he⟩)
  · exact v.property hT
  · have hv : v = boundaryOuterEndpoint s.graph T α := Subtype.ext he.symm
    have hd := hfar α
    rw [hv, SimpleGraph.edist_self] at hd
    exact (not_lt_of_ge (bot_le : (0 : ℕ∞) ≤ h)) hd

theorem admissibleFirst_not_fullCore (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i : s.AdmissibleSampleIndex selector) :
    (s.admissibleSampleVertex selector i).val ∉ s.fullCoreRoots :=
  s.farOutside_not_fullCore selector _ (s.admissibleSampleVertex_far_boundary selector i)

theorem admissibleSecond_not_fullCore (s : LabelledResamplingState V T ι) (selector : ℕ)
    (hs : 1 ≤ selector) (i : s.AdmissibleSampleIndex selector) :
    (s.admissibleSecondVertex selector i).val ∉ s.fullCoreRoots := by
  apply s.farOutside_not_fullCore (selector - 1)
  exact s.admissiblePairRoots_far_boundary selector hs i (by simp [admissiblePairRoots])

theorem fullPartialVertex_injective (s : LabelledResamplingState V T ι)
    (selector : ℕ) (S : Set V) (hs : 1 ≤ selector) :
    Function.Injective (s.fullPartialVertex selector S) := by
  intro u v huv
  have hv := congrArg Subtype.val huv
  rcases u with a | (b | c) <;> rcases v with a' | (b' | c')
  · exact congrArg Sum.inl ((s.fullCoreEmbedding S).injective huv)
  · exact False.elim (s.admissibleFirst_not_fullCore selector b'.val (hv ▸ a.property.2))
  · exact False.elim (s.admissibleSecond_not_fullCore selector hs c'.val (hv ▸ a.property.2))
  · exact False.elim (s.admissibleFirst_not_fullCore selector b.val (hv.symm ▸ a'.property.2))
  · have he := (s.admissibleSampleVertex_injective selector) (Subtype.ext hv)
    exact congrArg (fun x => Sum.inr (Sum.inl x)) (Subtype.ext he)
  · exact False.elim (s.admissibleFirst_eq_second_false selector b.val c'.val (Subtype.ext hv))
  · exact False.elim (s.admissibleSecond_not_fullCore selector hs c.val (hv.symm ▸ a'.property.2))
  · exact False.elim (s.admissibleFirst_eq_second_false selector b'.val c.val (Subtype.ext hv.symm))
  · have he := (s.admissibleSecond_eq_iff selector c.val c'.val).mp (Subtype.ext hv)
    exact congrArg (fun x => Sum.inr (Sum.inr x)) (Subtype.ext he)

def fullPartialEmbedding (s : LabelledResamplingState V T ι)
    (selector : ℕ) (S : Set V) (hs : 1 ≤ selector) : s.FullEndpointIndex selector S ↪ S where
  toFun := s.fullPartialVertex selector S
  inj' := s.fullPartialVertex_injective selector S hs

/-- The retained inner and outer mates are optional independently of B and C. -/
def fullInnerMate (s : LabelledResamplingState V T ι) (selector : ℕ) (S : Set V)
    (i : s.AdmissibleSampleIndex selector) : Option (s.fullCoreMask S) :=
  if hx : (s.quad i.val).a ∈ S then
    some ⟨(s.quad i.val).a, hx, Or.inl (sampledSwitching_root_mem s.graph T s.samples (s.boundary i.val))⟩
  else none

def fullOuterMate (s : LabelledResamplingState V T ι) (selector : ℕ) (S : Set V)
    (i : s.AdmissibleSampleIndex selector) : Option (s.fullCoreMask S) :=
  if hx : (s.admissibleBoundaryVertex selector i).val ∈ S then
    some ⟨(s.admissibleBoundaryVertex selector i).val, hx,
      Or.inr ⟨s.admissibleBoundaryVertex selector i, ⟨s.boundary i.val, rfl⟩, rfl⟩⟩
  else none

theorem fullInnerMate_eq_none (s : LabelledResamplingState V T ι) (selector : ℕ) (S : Set V)
    (i : s.AdmissibleSampleIndex selector) :
    s.fullInnerMate selector S i = none ↔ (s.quad i.val).a ∉ S := by
  simp [fullInnerMate]

theorem fullOuterMate_eq_none (s : LabelledResamplingState V T ι) (selector : ℕ) (S : Set V)
    (i : s.AdmissibleSampleIndex selector) :
    s.fullOuterMate selector S i = none ↔ (s.admissibleBoundaryVertex selector i).val ∉ S := by
  simp [fullOuterMate]

theorem fullInnerMate_eq_some (s : LabelledResamplingState V T ι) (selector : ℕ) (S : Set V)
    (i : s.AdmissibleSampleIndex selector) (v : s.fullCoreMask S) :
    s.fullInnerMate selector S i = some v ↔ (s.quad i.val).a = v.val := by
  unfold fullInnerMate
  split_ifs with hx
  · simp only [Option.some.injEq, Subtype.ext_iff]
  · simp only [reduceCtorEq, false_iff]
    intro he
    exact hx (he.symm ▸ v.property.1)

theorem fullOuterMate_eq_some (s : LabelledResamplingState V T ι) (selector : ℕ) (S : Set V)
    (i : s.AdmissibleSampleIndex selector) (v : s.fullCoreMask S) :
    s.fullOuterMate selector S i = some v ↔ (s.admissibleBoundaryVertex selector i).val = v.val := by
  unfold fullOuterMate
  split_ifs with hx
  · simp only [Option.some.injEq, Subtype.ext_iff]
  · simp only [reduceCtorEq, false_iff]
    intro he
    exact hx (he.symm ▸ v.property.1)

variable [Fintype V] [Fintype ι]
instance fullEndpointIndexFintype (s : LabelledResamplingState V T ι) (selector : ℕ) (S : Set V) :
    Fintype (s.FullEndpointIndex selector S) := by
  unfold FullEndpointIndex
  infer_instance

omit [Fintype V] [Fintype ι] in
/-- Every retained modified vertex is covered, including repeated inner roots. -/
theorem fullPartialEmbedding_captures (s : LabelledResamplingState V T ι)
    (selector : ℕ) (S : Set V) (hs : 1 ≤ selector) (x : S)
    (hx : x.val ∈ s.fullResampleEndpoints selector) :
    x ∈ Set.range (s.fullPartialEmbedding selector S hs) := by
  obtain ⟨i, hi, hx⟩ := hx
  let a : s.AdmissibleSampleIndex selector := ⟨i,hi⟩
  change x.val = (s.quad i).a ∨ x.val = (s.quad i).b ∨
    x.val = (s.quad i).c ∨ x.val = (s.quad i).d at hx
  rcases hx with h | h | h | h
  · refine ⟨Sum.inl ⟨x.val, x.property, Or.inl ?_⟩, ?_⟩
    · exact h ▸ sampledSwitching_root_mem s.graph T s.samples (s.boundary i)
    · rfl
  · refine ⟨Sum.inl ⟨x.val, x.property, Or.inr ?_⟩, ?_⟩
    · exact ⟨s.admissibleBoundaryVertex selector a, ⟨s.boundary i,rfl⟩, h.symm⟩
    · rfl
  · refine ⟨Sum.inr (Sum.inl ⟨a, ?_⟩), ?_⟩
    · change (s.quad i).c ∈ S
      exact h ▸ x.property
    · exact Subtype.ext h.symm
  · refine ⟨Sum.inr (Sum.inr ⟨a, ?_⟩), ?_⟩
    · change (s.quad i).d ∈ S
      exact h ▸ x.property
    · exact Subtype.ext h.symm

end LabelledResamplingState
end LocalLaw
