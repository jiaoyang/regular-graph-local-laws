import LocalLaw.AttachedLeafSubfamily
import LocalLaw.LeafSchurRows

/-! # A genuine leaf-subfamily deletion in block Schur coordinates

The complement of an injected kept family indexes every deleted leaf once.
Reindexing by the resulting equivalence makes the actual kept precision the
literal first block. Both full and kept units follow from genuine deficient
models, so scalar covariance row/decay lemmas apply without another class.
-/

noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance attachedLeafPartitionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V L J : Type}[Fintype V][Fintype L][Fintype J]

abbrev LeafFamilyComplement (e : J↪L) := {l : L // l ∉ Set.range e}

def leafFamilyPartition (e : J↪L) : J ⊕ LeafFamilyComplement e ≃ L :=
  Equiv.ofBijective (Sum.elim e Subtype.val) (by
    constructor
    · intro a b h
      cases a with
      | inl a =>
        cases b with
        | inl b => exact congrArg Sum.inl (e.injective h)
        | inr b => exact False.elim (b.property ⟨a,h⟩)
      | inr a =>
        cases b with
        | inl b => exact False.elim (a.property ⟨b,h.symm⟩)
        | inr b => exact congrArg Sum.inr (Subtype.ext h)
    · intro l
      by_cases hl : l ∈ Set.range e
      · obtain ⟨j,hj⟩ := hl
        exact ⟨.inl j,hj⟩
      · exact ⟨.inr ⟨l,hl⟩,rfl⟩)

def leafBlockPartition (e : J↪L) : (V⊕J)⊕LeafFamilyComplement e ≃ V⊕L :=
  (Equiv.sumAssoc V J (LeafFamilyComplement e)).trans
    (Equiv.sumCongr (Equiv.refl V) (leafFamilyPartition e))

omit [Fintype V] [Fintype L] in
@[simp] theorem leafBlockPartition_core (e : J↪L)(v : V) :
    leafBlockPartition e (.inl (.inl v)) = .inl v := rfl
omit [Fintype V] [Fintype L] in
@[simp] theorem leafBlockPartition_kept (e : J↪L)(j : J) :
    leafBlockPartition (V:=V) e (.inl (.inr j)) = .inr (e j) := rfl
omit [Fintype V] [Fintype L] in
@[simp] theorem leafBlockPartition_removed (e : J↪L)(l : LeafFamilyComplement e) :
    leafBlockPartition (V:=V) e (.inr l) = .inr l.val := rfl

namespace DeficientGraph
variable {d : ℕ}

def leafSubfamilyMatrix (g : DeficientGraph V d)(hd : 3≤d)(mate : L→V)
    (hr : ∀v,multiLeafMultiplicity mate v≤g.deficit v)(e : J↪L)(q z : ℂ) :=
  ((g.attachLeaves (by omega) mate hr).extensionMatrix q z).submatrix
    (leafBlockPartition (V:=V) e) (leafBlockPartition (V:=V) e)

theorem leafSubfamilyMatrix_core (g : DeficientGraph V d)(hd : 3≤d)(mate : L→V)
    (hr : ∀v,multiLeafMultiplicity mate v≤g.deficit v)(e : J↪L)(q z : ℂ) :
    (g.leafSubfamilyMatrix hd mate hr e q z).toBlocks₁₁ =
      (g.attachLeaves (by omega) (mate∘e)
        (fun v => (subfamily_leaf_multiplicity_le mate e v).trans (hr v))).extensionMatrix q z := by
  have h := g.attachLeaves_subfamily_extensionMatrix hd mate hr e q z
  ext i j
  have hij := congrArg (fun M => M i j) h
  cases i <;> cases j <;>
    simpa only [leafSubfamilyMatrix,Matrix.toBlocks₁₁,Matrix.of_apply,Matrix.submatrix_apply,leafBlockPartition_core,
      leafBlockPartition_kept,Sum.map_inl,Sum.map_inr,id_eq] using hij

theorem leafSubfamilyMatrix_units (g : DeficientGraph V d)(hd : 3≤d)(mate : L→V)
    (hr : ∀v,multiLeafMultiplicity mate v≤g.deficit v)(e : J↪L)(q z : ℂ)
    (hz : 0<z.im)(hq : 0≤q.im) :
    IsUnit (g.leafSubfamilyMatrix hd mate hr e q z) ∧
      IsUnit (g.leafSubfamilyMatrix hd mate hr e q z).toBlocks₁₁ := by
  constructor
  · exact (Matrix.isUnit_submatrix_equiv (leafBlockPartition (V:=V) e)
      (leafBlockPartition (V:=V) e)).mpr
      ((g.attachLeaves (by omega) mate hr).extensionMatrix_isUnit hd q z hz hq)
  · rw [g.leafSubfamilyMatrix_core hd mate hr e q z]
    exact (g.attachLeaves (by omega) (mate∘e)
      (fun v => (subfamily_leaf_multiplicity_le mate e v).trans (hr v))).extensionMatrix_isUnit hd q z hz hq

theorem leafSubfamilyMatrix_inverse (g : DeficientGraph V d)(hd : 3≤d)(mate : L→V)
    (hr : ∀v,multiLeafMultiplicity mate v≤g.deficit v)(e : J↪L)(q z : ℂ) :
    (g.leafSubfamilyMatrix hd mate hr e q z)⁻¹ =
      ((g.attachLeaves (by omega) mate hr).extensionGreen q z).submatrix
        (leafBlockPartition (V:=V) e) (leafBlockPartition (V:=V) e) := by
  exact Matrix.inv_submatrix_equiv _ _ _

end DeficientGraph
end LocalLaw
