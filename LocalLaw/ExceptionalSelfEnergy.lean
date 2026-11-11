import LocalLaw.ExceptionalCutCounting

/-!
# Actual full Schur split into ordinary and exceptional components

The full normalized coupling is partitioned by the actual outside component
charge. Genuine inverse support removes both mixed products. The remaining
Schur correction is the proved ordinary diagonal plus an explicit exceptional
matrix, with no self-energy decomposition premise.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance exceptionalEnergyDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type} [Fintype V] [DecidableEq V]

def fullCutCoupling (G : SimpleGraph V) (d : ℕ) (S : Set V) : Matrix S (Sᶜ : Set V) ℂ :=
  fun u a => if G.Adj u.val a.val then treeEdgeWeight d else 0

def exceptionalCutCoupling (G : SimpleGraph V) (d : ℕ) (S : Set V) : Matrix S (Sᶜ : Set V) ℂ :=
  fun u a => if ¬ordinaryCutVertex G S a ∧ G.Adj u.val a.val then treeEdgeWeight d else 0

omit [DecidableEq V] in
theorem fullCutCoupling_split (G : SimpleGraph V) (d : ℕ) (S : Set V) :
    fullCutCoupling G d S = ordinaryCutCoupling G d S + exceptionalCutCoupling G d S := by
  ext u a
  by_cases ho : ordinaryCutVertex G S a <;> by_cases ha : G.Adj u.val a.val <;>
    simp [fullCutCoupling, ordinaryCutCoupling, exceptionalCutCoupling, ho, ha]

namespace DeficientGraph
variable {d : ℕ}

theorem ordinary_exceptional_deleted_zero (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (a b : (Sᶜ : Set V)) (ha : ordinaryCutVertex g.graph S a) (hb : ¬ordinaryCutVertex g.graph S b) :
    (g.delete S).extensionGreen q z a b = 0 := by
  apply g.deleted_extensionGreen_component_zero hd S q z hz hq a b
  intro heq
  apply hb
  change cutExcessCharge g.graph S ((outsideGraph g.graph S).connectedComponentMk b) = 0
  rw [← heq]
  exact ha

theorem mixed_cut_self_energy_zero (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    ordinaryCutCoupling g.graph d S * (g.delete S).extensionGreen q z *
      (exceptionalCutCoupling g.graph d S).transpose = 0 := by
  ext u v
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : ordinaryCutVertex g.graph S a ∧ g.graph.Adj u.val a.val
  · by_cases hb : ¬ordinaryCutVertex g.graph S b ∧ g.graph.Adj v.val b.val
    · rw [g.ordinary_exceptional_deleted_zero hd S q z hz hq a b ha.1 hb.1]
      simp
    · simp only [exceptionalCutCoupling, Matrix.transpose_apply, if_neg hb, mul_zero]
  · simp only [ordinaryCutCoupling, if_neg ha, zero_mul]

theorem reverse_mixed_cut_self_energy_zero (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    exceptionalCutCoupling g.graph d S * (g.delete S).extensionGreen q z *
      (ordinaryCutCoupling g.graph d S).transpose = 0 := by
  ext u v
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : ¬ordinaryCutVertex g.graph S a ∧ g.graph.Adj u.val a.val
  · by_cases hb : ordinaryCutVertex g.graph S b ∧ g.graph.Adj v.val b.val
    · have hzero : (g.delete S).extensionGreen q z a b = 0 := by
        apply g.deleted_extensionGreen_component_zero hd S q z hz hq a b
        intro heq
        apply ha.1
        change cutExcessCharge g.graph S ((outsideGraph g.graph S).connectedComponentMk a) = 0
        rw [heq]
        exact hb.1
      rw [hzero]
      simp
    · simp only [ordinaryCutCoupling, Matrix.transpose_apply, if_neg hb, mul_zero]
  · simp only [exceptionalCutCoupling, if_neg ha, zero_mul]

theorem full_cut_self_energy_split (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (hG : g.graph.Connected) (hS : S.Nonempty)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    fullCutCoupling g.graph d S * (g.delete S).extensionGreen q z *
      (fullCutCoupling g.graph d S).transpose = Matrix.diagonal (g.ordinarySelfEnergyDiagonal S q z) +
      exceptionalCutCoupling g.graph d S * (g.delete S).extensionGreen q z *
        (exceptionalCutCoupling g.graph d S).transpose := by
  rw [fullCutCoupling_split, Matrix.transpose_add]
  simp only [Matrix.add_mul, Matrix.mul_add,
    g.mixed_cut_self_energy_zero hd S q z hz hq,
    g.reverse_mixed_cut_self_energy_zero hd S q z hz hq,
    g.ordinary_cut_self_energy_eq_diagonal hd S hG hS q z hz hq, add_zero, zero_add]

def exceptionalSelfEnergy (g : DeficientGraph V d) (S : Set V) (q z : ℂ) : Matrix S S ℂ :=
  exceptionalCutCoupling g.graph d S * (g.delete S).extensionGreen q z *
    (exceptionalCutCoupling g.graph d S).transpose - q •
      (g.restrictionLossDiagonal S - Matrix.diagonal (fun u => (ordinaryCutCharge g.graph d S u : ℂ)))

theorem ordinaryErrorDiagonal_eq (g : DeficientGraph V d) (S : Set V) (q z : ℂ) :
    Matrix.diagonal (g.ordinarySelfEnergyError S q z) =
      Matrix.diagonal (g.ordinarySelfEnergyDiagonal S q z) -
        q • Matrix.diagonal (fun u => (ordinaryCutCharge g.graph d S u : ℂ)) := by
  ext u v
  by_cases huv : u = v
  · subst v
    simp only [Matrix.diagonal_apply_eq, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, g.ordinarySelfEnergyError_eq S q z u]
  · simp only [Matrix.diagonal_apply_ne _ huv, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, mul_zero, sub_self]

/-- The full correction is the derived ordinary diagonal plus the literal
exceptional coupling and its unmatched boundary charge. -/
theorem cut_self_energy_error_split (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (hG : g.graph.Connected) (hS : S.Nonempty)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    fullCutCoupling g.graph d S * (g.delete S).extensionGreen q z *
      (fullCutCoupling g.graph d S).transpose - q • g.restrictionLossDiagonal S =
        Matrix.diagonal (g.ordinarySelfEnergyError S q z) + g.exceptionalSelfEnergy S q z := by
  rw [g.full_cut_self_energy_split hd S hG hS q z hz hq,
    g.ordinaryErrorDiagonal_eq S q z, exceptionalSelfEnergy, smul_sub]
  abel

omit [DecidableEq V] in
theorem fullCutCoupling_eq_H (g : DeficientGraph V d) (S : Set V) :
    fullCutCoupling g.graph d S = g.H.submatrix (Subtype.val : S → V) (Subtype.val : (Sᶜ : Set V) → V) := by
  ext u a
  by_cases ha : g.graph.Adj u.val a.val <;>
    simp [fullCutCoupling, H, normalizedAdjacency, SimpleGraph.adjMatrix_apply, treeEdgeWeight, ha]

omit [DecidableEq V] in
theorem fullCutCoupling_transpose_eq_H (g : DeficientGraph V d) (S : Set V) :
    (fullCutCoupling g.graph d S).transpose =
      g.H.submatrix (Subtype.val : (Sᶜ : Set V) → V) (Subtype.val : S → V) := by
  ext a u
  have har : g.graph.Adj a.val u.val ↔ g.graph.Adj u.val a.val := g.graph.adj_comm a.val u.val
  by_cases ha : g.graph.Adj u.val a.val <;>
    simp [fullCutCoupling, H, normalizedAdjacency, SimpleGraph.adjMatrix_apply, treeEdgeWeight, ha,
      har]

/-- Actual restricted full inverse has exactly the ordinary/exceptional
Schur decomposition, with all physical units derived. -/
theorem retained_inverse_ordinary_exceptional_split (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (hG : g.graph.Connected) (hS : S.Nonempty)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    ((g.extensionGreen q z).submatrix (Subtype.val : S → V) (Subtype.val : S → V))⁻¹ =
      (g.restrict S).extensionMatrix q z - Matrix.diagonal (g.ordinarySelfEnergyError S q z) -
        g.exceptionalSelfEnergy S q z := by
  have hD : IsUnit ((g.extensionMatrix q z).submatrix
      (Subtype.val : (Sᶜ : Set V) → V) (Subtype.val : (Sᶜ : Set V) → V)) := by
    rw [← g.extensionMatrix_delete S q z]
    exact (g.delete S).extensionMatrix_isUnit hd q z hz hq
  have h := retained_principal_inverse S (g.extensionMatrix q z) (g.extensionMatrix_isUnit hd q z hz hq) hD
  rw [g.extensionMatrix_cross12 S q z, g.extensionMatrix_cross21 S q z,
    ← g.fullCutCoupling_eq_H S, ← g.fullCutCoupling_transpose_eq_H S,
    ← g.extensionMatrix_delete S q z] at h
  apply h.trans
  change _ = _
  calc
    _ = ((g.extensionMatrix q z).submatrix (Subtype.val : S → V) (Subtype.val : S → V) -
        q • g.restrictionLossDiagonal S) -
      (fullCutCoupling g.graph d S * (g.delete S).extensionGreen q z *
        (fullCutCoupling g.graph d S).transpose - q • g.restrictionLossDiagonal S) := by abel
    _ = _ := by
      rw [← g.restrict_extensionMatrix S q z, g.cut_self_energy_error_split hd S hG hS q z hz hq]
      abel

end DeficientGraph
end LocalLaw
