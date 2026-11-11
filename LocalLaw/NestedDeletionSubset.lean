import LocalLaw.DeficientGraphModel

/-! # Deleting an outer subset and then the remaining selected vertices

The exact principal extension-matrix identity supplies the Green transport
directly, retaining every physical deletion deficit without a new class.
-/

noncomputable section
namespace LocalLaw
local instance nestedDeletionSubsetDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type*}

def nestedDeletionSubsetEquiv (A B:Set V)(hAB:A⊆B) :
    ({v : (Aᶜ : Set V) | v.val ∈ B}ᶜ:Set (Aᶜ:Set V))≃(Bᶜ:Set V) where
  toFun v:=⟨v.val.val,v.property⟩
  invFun v:=⟨⟨v.val,fun ha=>v.property (hAB ha)⟩,v.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

namespace DeficientGraph
variable [Fintype V] [DecidableEq V] {d:ℕ}

theorem nested_delete_subset_extensionMatrix (g:DeficientGraph V d)(A B:Set V)(hAB:A⊆B)(q z:ℂ) :
    ((g.delete B).extensionMatrix q z).submatrix (nestedDeletionSubsetEquiv A B hAB)
      (nestedDeletionSubsetEquiv A B hAB)=
        ((g.delete A).delete {v : (Aᶜ : Set V) | v.val ∈ B}).extensionMatrix q z := by
  rw [g.extensionMatrix_delete,(g.delete A).extensionMatrix_delete,g.extensionMatrix_delete]
  ext i j
  rfl

theorem nested_delete_subset_extensionGreen (g:DeficientGraph V d)(A B:Set V)(hAB:A⊆B)(q z:ℂ) :
    ((g.delete B).extensionGreen q z).submatrix (nestedDeletionSubsetEquiv A B hAB)
      (nestedDeletionSubsetEquiv A B hAB)=
        ((g.delete A).delete {v : (Aᶜ : Set V) | v.val ∈ B}).extensionGreen q z := by
  let e:=nestedDeletionSubsetEquiv A B hAB
  have hh:=Matrix.inv_submatrix_equiv ((g.delete B).extensionMatrix q z) e e
  rw [g.nested_delete_subset_extensionMatrix A B hAB q z] at hh
  exact hh.symm

end DeficientGraph
end LocalLaw
