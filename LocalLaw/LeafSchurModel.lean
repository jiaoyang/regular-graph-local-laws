import LocalLaw.MultiLeafRestriction
import LocalLaw.BlockSchur
import LocalLaw.DiagonalSchurComparison

/-! # Exact leaf-completion Schur identities

Attaching the deficit-restoring leaves leaves the core precision unchanged.
Consequently the original model Green function is the completed Green
function minus its actual leaf Schur correction.  The same statement holds
after retaining a core set together with every leaf attached to that set.
All leaf blocks used below are proved nonsingular.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance leafSchurModelDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Matrix
variable {K L : Type} [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]

/-- Delete the leaf block from the inverse, retaining its actual Schur correction. -/
theorem core_inverse_leaf_schur (M : Matrix (K ⊕ L) (K ⊕ L) ℂ)
    (hM : IsUnit M) (hcore : IsUnit M.toBlocks₁₁) :
    IsUnit (M⁻¹).toBlocks₂₂ ∧
      M.toBlocks₁₁⁻¹ = (M⁻¹).toBlocks₁₁ -
        (M⁻¹).toBlocks₁₂ * (M⁻¹).toBlocks₂₂⁻¹ * (M⁻¹).toBlocks₂₁ := by
  have h22 := inverse_block22 M hM hcore
  have hleaf : IsUnit (M⁻¹).toBlocks₂₂ := by
    rw [h22.2]
    exact Matrix.isUnit_nonsing_inv_iff.mpr h22.1
  refine ⟨hleaf, ?_⟩
  have hh := inverse_inverse_block11 M⁻¹
    (Matrix.isUnit_nonsing_inv_iff.mpr hM) hleaf
  rw [Matrix.nonsing_inv_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hM)] at hh
  exact hh

theorem core_inverse_leaf_schur_bilinear (M : Matrix (K ⊕ L) (K ⊕ L) ℂ)
    (hM : IsUnit M) (hcore : IsUnit M.toBlocks₁₁) (i j : K) :
    M.toBlocks₁₁⁻¹ i j = M⁻¹ (.inl i) (.inl j) -
      schurBilinear (fun l : L => M⁻¹ (.inl i) (.inr l)) (M⁻¹).toBlocks₂₂⁻¹
        (fun l => M⁻¹ (.inr l) (.inl j)) := by
  have hh := congrArg (fun A : Matrix K K ℂ => A i j) (core_inverse_leaf_schur M hM hcore).2
  simp only [Matrix.sub_apply, Matrix.mul_apply, Finset.sum_mul] at hh
  rw [Finset.sum_comm] at hh
  exact hh

end Matrix

/-- The included leaf slots, embedded in the lifted vertex set. -/
def multiLeafLiftLeaf {V L : Type*} (mate : L → V) (S : Set V) :
    {l : L // mate l ∈ S} ↪ multiLeafLift mate S where
  toFun l := ⟨.inr l.val, l.property⟩
  inj' := by intro a b h; exact Subtype.ext (Sum.inr.inj (congrArg Subtype.val h))

namespace DeficientGraph
variable {V L : Type} [Fintype V] [Fintype L] {d : ℕ}

/-- The global leaf Green block is nonsingular, and deleting it recovers the
original deficient model exactly. -/
theorem attachLeaves_Green_leaf_schur (g : DeficientGraph V d) (hd : 3 ≤ d)
    (mate : L → V) (hrestore : ∀ v, multiLeafMultiplicity mate v ≤ g.deficit v)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let G := (g.attachLeaves (by omega) mate hrestore).extensionGreen q z
    IsUnit (G.submatrix Sum.inr Sum.inr) ∧
      ∀ i j, g.extensionGreen q z i j = G (.inl i) (.inl j) -
        schurBilinear (fun l : L => G (.inl i) (.inr l)) (G.submatrix Sum.inr Sum.inr)⁻¹
          (fun l => G (.inr l) (.inl j)) := by
  dsimp only
  let M := (g.attachLeaves (by omega) mate hrestore).extensionMatrix q z
  have hM : IsUnit M := (g.attachLeaves (by omega) mate hrestore).extensionMatrix_isUnit hd q z hz hq
  have hcore : M.toBlocks₁₁ = g.extensionMatrix q z := by
    have hh := g.attachLeaves_extensionMatrix_principal (by omega) mate hrestore q z
    exact hh
  have hc : IsUnit M.toBlocks₁₁ := hcore ▸ g.extensionMatrix_isUnit hd q z hz hq
  refine ⟨(core_inverse_leaf_schur M hM hc).1, ?_⟩
  intro i j
  have hh := core_inverse_leaf_schur_bilinear M hM hc i j
  rw [hcore] at hh
  exact hh

/-- Restricting the completed model to a lifted set gives the exact local
leaf correction for the original restricted model. -/
theorem attachLeaves_lift_Green_leaf_schur (g : DeficientGraph V d) (hd : 3 ≤ d)
    (mate : L → V) (hrestore : ∀ v, multiLeafMultiplicity mate v ≤ g.deficit v)
    (S : Set V) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let G := ((g.attachLeaves (by omega) mate hrestore).restrict (multiLeafLift mate S)).extensionGreen q z
    let leaf := multiLeafLiftLeaf mate S
    let core := multiLeafLiftCore mate S
    IsUnit (G.submatrix leaf leaf) ∧
      ∀ i j : S, (g.restrict S).extensionGreen q z i j = G (core i) (core j) -
        schurBilinear (fun l : {l : L // mate l ∈ S} => G (core i) (leaf l)) (G.submatrix leaf leaf)⁻¹
          (fun l => G (leaf l) (core j)) := by
  dsimp only
  let H := (g.attachLeaves (by omega) mate hrestore).restrict (multiLeafLift mate S)
  let e := (multiLeafLiftGraphIso g.graph mate S).toEquiv
  let M := (H.extensionMatrix q z).submatrix e e
  have hM : IsUnit M :=
    (Matrix.isUnit_submatrix_equiv e e).mpr (H.extensionMatrix_isUnit hd q z hz hq)
  have hcore : M.toBlocks₁₁ = (g.restrict S).extensionMatrix q z := by
    have hh := g.attachLeaves_lift_extensionMatrix_core (by omega) mate hrestore S q z
    exact hh
  have hc : IsUnit M.toBlocks₁₁ := hcore ▸ (g.restrict S).extensionMatrix_isUnit hd q z hz hq
  have hi : M⁻¹ = (H.extensionGreen q z).submatrix e e :=
    Matrix.inv_submatrix_equiv (H.extensionMatrix q z) e e
  have hleaf := (core_inverse_leaf_schur M hM hc).1
  rw [hi] at hleaf
  refine ⟨hleaf, ?_⟩
  intro i j
  have hh := core_inverse_leaf_schur_bilinear M hM hc i j
  rw [hcore, hi] at hh
  exact hh

end DeficientGraph
end LocalLaw
