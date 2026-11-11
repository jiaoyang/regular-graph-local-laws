import LocalLaw.EndpointRootOccupancy
import LocalLaw.PartialDeficitRestoration

/-! # Actual endpoint masks in an arbitrary outside restriction

Only accepted labels are used. Their three exterior vertices are distinct
even when different boundary edges have the same interior endpoint. Thus
the included A, B and C masks give one genuine finite endpoint embedding.
-/

noncomputable section
namespace LocalLaw
local instance partialEndpointMasksDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type*}

def admissibleBoundaryVertex (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i : s.AdmissibleSampleIndex selector) : (Tᶜ : Set V) :=
  boundaryOuterEndpoint s.graph T (s.boundary i.val)

def admissibleTripleVertex (s : LabelledResamplingState V T ι) (selector : ℕ)
    (p : s.AdmissibleSampleIndex selector × Fin 3) : (Tᶜ : Set V) :=
  outsideTripleVertex s.graph T s.samples (s.boundary p.1.val) p.2

theorem admissibleTripleVertex_separated (s : LabelledResamplingState V T ι)
    (selector : ℕ) (i j : s.AdmissibleSampleIndex selector) (hij : i ≠ j)
    (k l : Fin 3) :
    (selector : ℕ∞) < (outsideGraph s.graph T).edist
      (s.admissibleTripleVertex selector (i,k)) (s.admissibleTripleVertex selector (j,l)) := by
  have hlabel : s.boundary j.val ≠ s.boundary i.val := by
    intro h
    exact hij (Subtype.ext (s.boundary.injective h).symm)
  exact i.property.2 (s.boundary j.val) hlabel _
    (outsideTripleVertex_mem _ _ _ _ k) _ (outsideTripleVertex_mem _ _ _ _ l)

theorem admissibleTripleVertex_injective (s : LabelledResamplingState V T ι)
    (selector : ℕ) : Function.Injective (s.admissibleTripleVertex selector) := by
  rintro ⟨i,k⟩ ⟨j,l⟩ he
  have hij : i = j := by
    by_contra hne
    have h := s.admissibleTripleVertex_separated selector i j hne k l
    rw [he, SimpleGraph.edist_self] at h
    exact (not_lt_of_ge (bot_le : (0 : ℕ∞) ≤ selector)) h
  subst j
  have ha := sampledSwitching_admissible s.graph T selector s.samples (s.boundary i.val)
    i.property.1 i.property.2
  have hv := congrArg Subtype.val he
  have hab := ha.bc_ne
  have hac := ha.bd_ne
  have hbc := ha.cd_ne
  have hkl : k = l := by
    fin_cases k <;> fin_cases l <;>
      simp_all [admissibleTripleVertex, outsideTripleVertex, boundaryOuterEndpoint,
        sampledFirstOutsideVertex, sampledSecondOutsideVertex, sampledSwitchingQuad]
  exact Prod.ext rfl hkl

def partialBoundaryMask (s : LabelledResamplingState V T ι) (selector : ℕ)
    (S : Set (Tᶜ : Set V)) : Set (s.AdmissibleSampleIndex selector) :=
  {i | s.admissibleBoundaryVertex selector i ∈ S}

def partialFirstMask (s : LabelledResamplingState V T ι) (selector : ℕ)
    (S : Set (Tᶜ : Set V)) : Set (s.AdmissibleSampleIndex selector) :=
  {i | s.admissibleSampleVertex selector i ∈ S}

def partialSecondMask (s : LabelledResamplingState V T ι) (selector : ℕ)
    (S : Set (Tᶜ : Set V)) : Set (s.AdmissibleSampleIndex selector) :=
  {i | s.admissibleSecondVertex selector i ∈ S}

def PartialEndpointIndex (s : LabelledResamplingState V T ι) (selector : ℕ)
    (S : Set (Tᶜ : Set V)) :=
  s.partialBoundaryMask selector S ⊕
    (s.partialFirstMask selector S ⊕ s.partialSecondMask selector S)

def partialEndpointCode (s : LabelledResamplingState V T ι) (selector : ℕ)
    (S : Set (Tᶜ : Set V)) : s.PartialEndpointIndex selector S →
      s.AdmissibleSampleIndex selector × Fin 3
  | .inl i => (i.val,0)
  | .inr (.inl i) => (i.val,1)
  | .inr (.inr i) => (i.val,2)

theorem partialEndpointCode_injective (s : LabelledResamplingState V T ι)
    (selector : ℕ) (S : Set (Tᶜ : Set V)) :
    Function.Injective (s.partialEndpointCode selector S) := by
  intro i j h
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (Subtype.ext (congrArg Prod.fst h))
    | inr j => cases j <;> have hh := congrArg Fin.val (congrArg Prod.snd h) <;> norm_num [partialEndpointCode] at hh
  | inr i =>
    cases i with
    | inl i =>
      cases j with
      | inl j => have hh := congrArg Fin.val (congrArg Prod.snd h); norm_num [partialEndpointCode] at hh
      | inr j =>
        cases j with
        | inl j => exact congrArg (fun x => Sum.inr (Sum.inl x)) (Subtype.ext (congrArg Prod.fst h))
        | inr j => have hh := congrArg Fin.val (congrArg Prod.snd h); norm_num [partialEndpointCode] at hh
    | inr i =>
      cases j with
      | inl j => have hh := congrArg Fin.val (congrArg Prod.snd h); norm_num [partialEndpointCode] at hh
      | inr j =>
        cases j with
        | inl j => have hh := congrArg Fin.val (congrArg Prod.snd h); norm_num [partialEndpointCode] at hh
        | inr j => exact congrArg (fun x => Sum.inr (Sum.inr x)) (Subtype.ext (congrArg Prod.fst h))

def partialEndpointVertex (s : LabelledResamplingState V T ι) (selector : ℕ)
    (S : Set (Tᶜ : Set V)) : s.PartialEndpointIndex selector S → S
  | .inl i => ⟨s.admissibleBoundaryVertex selector i.val,i.property⟩
  | .inr (.inl i) => ⟨s.admissibleSampleVertex selector i.val,i.property⟩
  | .inr (.inr i) => ⟨s.admissibleSecondVertex selector i.val,i.property⟩

theorem partialEndpointVertex_eq_code (s : LabelledResamplingState V T ι)
    (selector : ℕ) (S : Set (Tᶜ : Set V)) (i : s.PartialEndpointIndex selector S) :
    (s.partialEndpointVertex selector S i).val =
      s.admissibleTripleVertex selector (s.partialEndpointCode selector S i) := by
  rcases i with i | (i | i) <;>
    simp [partialEndpointVertex, partialEndpointCode, admissibleTripleVertex,
      outsideTripleVertex, admissibleBoundaryVertex, admissibleSampleVertex, admissibleSecondVertex]

def partialEndpointEmbedding (s : LabelledResamplingState V T ι) (selector : ℕ)
    (S : Set (Tᶜ : Set V)) : s.PartialEndpointIndex selector S ↪ S where
  toFun := s.partialEndpointVertex selector S
  inj' := by
    intro i j h
    apply s.partialEndpointCode_injective selector S
    apply s.admissibleTripleVertex_injective selector
    simpa only [← s.partialEndpointVertex_eq_code] using congrArg Subtype.val h

def partialBoundaryEmbedding (s : LabelledResamplingState V T ι) (selector : ℕ)
    (S : Set (Tᶜ : Set V)) : s.partialBoundaryMask selector S ↪ S where
  toFun i := ⟨s.admissibleBoundaryVertex selector i.val,i.property⟩
  inj' := by
    intro i j h
    have he := (s.partialEndpointEmbedding selector S).injective
      (show (s.partialEndpointEmbedding selector S) (.inl i) =
        (s.partialEndpointEmbedding selector S) (.inl j) from h)
    exact Sum.inl.inj he

theorem partialBoundaryEmbedding_range (s : LabelledResamplingState V T ι)
    (selector : ℕ) (S : Set (Tᶜ : Set V)) :
    Set.range (s.partialBoundaryEmbedding selector S) = s.includedEligibleBoundary selector S := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨i.val,rfl⟩
  · rintro ⟨i,hi⟩
    have hm : i ∈ s.partialBoundaryMask selector S := by
      change s.admissibleBoundaryVertex selector i ∈ S
      rw [show s.admissibleBoundaryVertex selector i = x.val from hi.symm]
      exact x.property
    exact ⟨⟨i,hm⟩,Subtype.ext hi.symm⟩

theorem partialBoundaryEmbedding_separated (s : LabelledResamplingState V T ι)
    (selector : ℕ) (S : Set (Tᶜ : Set V))
    (i j : s.partialBoundaryMask selector S) (hij : i ≠ j) :
    (selector : ℕ∞) < (outsideGraph s.graph T).edist
      ((s.partialBoundaryEmbedding selector S i).val)
      ((s.partialBoundaryEmbedding selector S j).val) := by
  have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  simpa [partialBoundaryEmbedding, admissibleTripleVertex, outsideTripleVertex,
    admissibleBoundaryVertex] using s.admissibleTripleVertex_separated selector i.val j.val hne 0 0

theorem partialEndpointEmbedding_range (s : LabelledResamplingState V T ι)
    (selector : ℕ) (S : Set (Tᶜ : Set V)) (x : S) :
    x ∈ Set.range (s.partialEndpointEmbedding selector S) ↔
      ∃ i : s.AdmissibleSampleIndex selector,
        x.val ∈ outsideTriple s.graph T s.samples (s.boundary i.val) := by
  constructor
  · rintro ⟨i,rfl⟩
    rcases i with i | (i | i)
    · exact ⟨i.val,(outsideTriple_mem_iff _ _ _ _ _).mpr (Or.inl rfl)⟩
    · exact ⟨i.val,(outsideTriple_mem_iff _ _ _ _ _).mpr (Or.inr (Or.inl rfl))⟩
    · exact ⟨i.val,(outsideTriple_mem_iff _ _ _ _ _).mpr (Or.inr (Or.inr rfl))⟩
  · rintro ⟨i,hi⟩
    rcases (outsideTriple_mem_iff _ _ _ _ _).mp hi with ha | hb | hc
    · have hm : i ∈ s.partialBoundaryMask selector S := by
        change s.admissibleBoundaryVertex selector i ∈ S
        rw [show s.admissibleBoundaryVertex selector i = x.val from ha.symm]
        exact x.property
      exact ⟨.inl ⟨i,hm⟩,Subtype.ext ha.symm⟩
    · have hm : i ∈ s.partialFirstMask selector S := by
        change s.admissibleSampleVertex selector i ∈ S
        rw [show s.admissibleSampleVertex selector i = x.val from hb.symm]
        exact x.property
      exact ⟨.inr (.inl ⟨i,hm⟩),Subtype.ext hb.symm⟩
    · have hm : i ∈ s.partialSecondMask selector S := by
        change s.admissibleSecondVertex selector i ∈ S
        rw [show s.admissibleSecondVertex selector i = x.val from hc.symm]
        exact x.property
      exact ⟨.inr (.inr ⟨i,hm⟩),Subtype.ext hc.symm⟩

theorem partialEndpoint_card_le [Fintype ι] (s : LabelledResamplingState V T ι)
    (selector : ℕ) (S : Set (Tᶜ : Set V)) :
    Nat.card (s.PartialEndpointIndex selector S) ≤ 3 * Nat.card (s.AdmissibleSampleIndex selector) := by
  exact (Nat.card_le_card_of_injective _ (s.partialEndpointCode_injective selector S)).trans_eq
    (by simp [Nat.card_prod, Nat.card_eq_fintype_card, Nat.mul_comm])

end LabelledResamplingState
end LocalLaw
