import LocalLaw.BoundarySchurExpansion
import LocalLaw.LocalResamplingData

/-!
# Literal cut-incidence factorization of self energy

Boundary labels are actual oriented cut edges, including repeated inner or
outer endpoints. The coupling and deleted-kernel sandwich factor through
these labels exactly; no disjointness of endpoints is assumed.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance cutIncidenceDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

def cutInnerCoupling (G : SimpleGraph V) (d : ℕ) (T : Set V) :
    Matrix T (BoundaryOrientedEdge G T) ℂ :=
  fun i e => if i.val = e.val.1 then (↑((Real.sqrt ((d : ℝ) - 1))⁻¹) : ℂ) else 0

def cutOuterProjection (G : SimpleGraph V) (T : Set V) :
    Matrix (BoundaryOrientedEdge G T) (Tᶜ : Set V) ℂ :=
  fun e j => if e.val.2 = j.val then 1 else 0

/-- Every physical cut coupling is represented once by its actual edge. -/
theorem normalized_cut_incidence (G : SimpleGraph V) (d : ℕ) (T : Set V) :
    (normalizedAdjacency G d).submatrix (Subtype.val : T → V) (Subtype.val : (Tᶜ : Set V) → V) =
      cutInnerCoupling G d T * cutOuterProjection G T := by
  ext i j
  change normalizedAdjacency G d i.val j.val = ∑ e : BoundaryOrientedEdge G T,
    cutInnerCoupling G d T i e * cutOuterProjection G T e j
  by_cases hadj : G.Adj i.val j.val
  · let e0 : BoundaryOrientedEdge G T := ⟨(i.val, j.val), hadj, i.property, j.property⟩
    have hsum : (∑ e : BoundaryOrientedEdge G T,
        cutInnerCoupling G d T i e * cutOuterProjection G T e j) =
        cutInnerCoupling G d T i e0 * cutOuterProjection G T e0 j := by
      apply Finset.sum_eq_single e0
      · intro e _ he
        by_cases hi : i.val = e.val.1
        · by_cases hj : e.val.2 = j.val
          · exact False.elim (he (Subtype.ext (Prod.ext hi.symm hj)))
          · simp [cutOuterProjection, hj]
        · simp [cutInnerCoupling, hi]
      · simp
    rw [hsum]
    simp [normalizedAdjacency, SimpleGraph.adjMatrix_apply, hadj, cutInnerCoupling, cutOuterProjection, e0]
  · have hsum : (∑ e : BoundaryOrientedEdge G T,
        cutInnerCoupling G d T i e * cutOuterProjection G T e j) = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      by_cases hi : i.val = e.val.1
      · by_cases hj : e.val.2 = j.val
        · exact False.elim (hadj (hi ▸ hj ▸ e.property.1))
        · simp [cutOuterProjection, hj]
      · simp [cutInnerCoupling, hi]
    rw [hsum]
    simp [normalizedAdjacency, SimpleGraph.adjMatrix_apply, hadj]

/-- Repeated endpoint labels still select exactly the genuine deleted entry. -/
theorem cut_outer_kernel (G : SimpleGraph V) (T : Set V)
    (K : Matrix (Tᶜ : Set V) (Tᶜ : Set V) ℂ) :
    cutOuterProjection G T * K * (cutOuterProjection G T).transpose =
      K.submatrix (boundaryOutsideVertex G T) (boundaryOutsideVertex G T) := by
  ext e f
  have hleft (j : (Tᶜ : Set V)) : (cutOuterProjection G T * K) e j =
      K (boundaryOutsideVertex G T e) j := by
    change (∑ i : (Tᶜ : Set V), (if e.val.2 = i.val then 1 else 0) * K i j) = _
    have hpred (i : (Tᶜ : Set V)) : (e.val.2 = i.val) ↔ i = boundaryOutsideVertex G T e := by
      constructor
      · intro h; exact Subtype.ext h.symm
      · intro h; subst i; rfl
    simp only [hpred, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change (∑ j : (Tᶜ : Set V), (cutOuterProjection G T * K) e j * cutOuterProjection G T f j) = _
  simp only [hleft, cutOuterProjection]
  have hpred (j : (Tᶜ : Set V)) : (f.val.2 = j.val) ↔ j = boundaryOutsideVertex G T f := by
    constructor
    · intro h; exact Subtype.ext h.symm
    · intro h; subst j; rfl
  simp only [hpred, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

/-- Actual normalized-adjacency self energy factored over boundary edges. -/
theorem normalized_cut_selfEnergy (G : SimpleGraph V) (d : ℕ) (T : Set V)
    (K : Matrix (Tᶜ : Set V) (Tᶜ : Set V) ℂ) :
    (normalizedAdjacency G d).submatrix (Subtype.val : T → V) (Subtype.val : (Tᶜ : Set V) → V) * K *
      (normalizedAdjacency G d).submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V) =
    cutInnerCoupling G d T * K.submatrix (boundaryOutsideVertex G T) (boundaryOutsideVertex G T) *
      (cutInnerCoupling G d T).transpose := by
  have hright : (normalizedAdjacency G d).submatrix
      (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V) =
      ((normalizedAdjacency G d).submatrix
        (Subtype.val : T → V) (Subtype.val : (Tᶜ : Set V) → V)).transpose := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.transpose_apply, normalizedAdjacency, Matrix.smul_apply,
      smul_eq_mul, SimpleGraph.adjMatrix_apply, G.adj_comm]
  rw [hright, normalized_cut_incidence, Matrix.transpose_mul, ← cut_outer_kernel G T K]
  simp only [Matrix.mul_assoc]

end LocalLaw
