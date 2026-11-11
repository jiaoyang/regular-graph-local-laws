import SpectralConsequences.NestedRetainedPrecision
import SpectralConsequences.IndexedDeletionQuadratic
import LocalLaw.NestedDeletionSubset

/-! # A retained precision controls the actual own-deleted to common minor

Deleting a subset of retained indices restricts the retained precision. The
remaining deletion therefore has the same inverse row cap, independently of
how the original retained set was partitioned.
-/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance nestedCommonComparisonDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {A V : Type} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]

def remainingRetainedEquiv (e : V ↪ A) (Q : Set V) :
    (Qᶜ : Set V) ≃ {x : ((e '' Q)ᶜ : Set A) | x.val ∈ Set.range e} :=
  Equiv.ofBijective
    (fun v => ⟨embeddingOutsideImage e Q v,⟨v.val,rfl⟩⟩)
    (by
      constructor
      · intro i j hij
        exact Subtype.ext (e.injective (congrArg (fun x => x.val.val) hij))
      · rintro ⟨⟨a,ha⟩,v,hv⟩
        have hn : v ∉ Q := fun hq => ha ⟨v,hq,hv⟩
        refine ⟨⟨v,hn⟩,?_⟩
        apply Subtype.ext
        exact Subtype.ext hv)

theorem retained_nested_common_quadratic (H : Matrix A A ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (e : V ↪ A) (Q : Set V)
    (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hrows : ∀ i, ∑ j, ‖((green H z).submatrix e e)⁻¹ i j‖ ≤ C)
    (x y : ((Set.range e)ᶜ : Set A))
    (hx : ∀ v : (Qᶜ : Set V),
      ‖green (H.submatrix (Subtype.val : ((e '' Q)ᶜ : Set A) → A)
        (Subtype.val : ((e '' Q)ᶜ : Set A) → A)) z
        ⟨x.val,fun h => x.property (by obtain ⟨v,_,hv⟩:=h; exact ⟨v,hv⟩)⟩
        (embeddingOutsideImage e Q v)‖ ≤ δ)
    (hy : ∀ v : (Qᶜ : Set V),
      ‖green (H.submatrix (Subtype.val : ((e '' Q)ᶜ : Set A) → A)
        (Subtype.val : ((e '' Q)ᶜ : Set A) → A)) z
        (embeddingOutsideImage e Q v)
        ⟨y.val,fun h => y.property (by obtain ⟨v,_,hv⟩:=h; exact ⟨v,hv⟩)⟩‖ ≤ δ) :
    let xo : ((e '' Q)ᶜ : Set A) := ⟨x.val,fun h => x.property (by obtain ⟨v,_,hv⟩:=h;exact ⟨v,hv⟩)⟩
    let yo : ((e '' Q)ᶜ : Set A) := ⟨y.val,fun h => y.property (by obtain ⟨v,_,hv⟩:=h;exact ⟨v,hv⟩)⟩
    ‖green (H.submatrix (Subtype.val : ((e '' Q)ᶜ : Set A) → A)
        (Subtype.val : ((e '' Q)ᶜ : Set A) → A)) z xo yo -
      green (H.submatrix (Subtype.val : ((Set.range e)ᶜ : Set A) → A)
        (Subtype.val : ((Set.range e)ᶜ : Set A) → A)) z x y‖ ≤
        (Fintype.card V : ℝ)*C*δ^2 := by
  dsimp only
  let O : Set A := e '' Q
  let F : Set A := Set.range e
  have hOF : O ⊆ F := by rintro _ ⟨v,_,rfl⟩;exact ⟨v,rfl⟩
  let K := H.submatrix (Subtype.val : (Oᶜ : Set A) → A) (Subtype.val : (Oᶜ : Set A) → A)
  let W : Set (Oᶜ : Set A) := {v | v.val ∈ F}
  let φ : (Qᶜ : Set V) ≃ W := remainingRetainedEquiv e Q
  let xx : (Wᶜ : Set (Oᶜ : Set A)) := ⟨⟨x.val,fun h => x.property (hOF h)⟩,x.property⟩
  let yy : (Wᶜ : Set (Oᶜ : Set A)) := ⟨⟨y.val,fun h => y.property (hOF h)⟩,y.property⟩
  have hr := embedded_deleted_retained_inverse_rows H hH z hz e Q C hrows
  have hh := physical_indexed_deletion_quadratic_bound K (hH.submatrix _) W φ z hz C δ hC hδ hr xx yy hx hy
  let ψ := nestedDeletionSubsetEquiv O F hOF
  have hid : K.submatrix (Subtype.val : (Wᶜ : Set (Oᶜ : Set A)) → (Oᶜ : Set A))
      (Subtype.val : (Wᶜ : Set (Oᶜ : Set A)) → (Oᶜ : Set A)) =
      (H.submatrix (Subtype.val : (Fᶜ : Set A) → A) (Subtype.val : (Fᶜ : Set A) → A)).submatrix ψ ψ := by
    ext i j
    rfl
  rw [hid,green_reindex_equiv] at hh
  have hc : (Fintype.card (Qᶜ : Set V):ℝ) ≤ (Fintype.card V:ℝ) :=
    Nat.cast_le.mpr (Fintype.card_subtype_le _)
  exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hC) (sq_nonneg δ))

end SpectralConsequences
