import LocalLaw.TreeKernelConvolution
import LocalLaw.MinorIdentity

/-!
# Exact leaf pruning of the full finite reference model

A degree-one vertex has scalar pivot m^-1. Its genuine Schur correction
exactly supplies the increased missing-degree boundary at its sole neighbor.
No acyclicity or connectedness assumption is needed for the pruning identity.
-/

open scoped BigOperators Matrix
set_option maxHeartbeats 1000000

namespace LocalLaw
noncomputable section
local instance leafReductionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section FiniteGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- Root-free full reference operator, on an arbitrary finite simple graph. -/
def fullReferenceMatrix (d : ℕ) (m z : ℂ) : Matrix V V ℂ :=
  boundaryMatrix (normalizedAdjacency G d) (treeBoundaryDiagonal G d) m z

theorem fullReferenceMatrix_inverse (d : ℕ) (m z : ℂ) :
    (fullReferenceMatrix G d m z)⁻¹ = fullTreeGreen G d m z := rfl

/-- Physical full reference operators are nonsingular, including graphs
containing cycles. -/
theorem fullReferenceMatrix_isUnit (d : ℕ) (hd : 3 ≤ d)
    (hdeg : ∀ v, G.degree v ≤ d) (m z : ℂ) (hz : 0 < z.im) (hmim : 0 ≤ m.im) :
    IsUnit (fullReferenceMatrix G d m z) := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  exact boundaryMatrix_isUnit _ (normalizedAdjacency_isHermitian G d)
    (treeBoundaryWeight G d)
    (fun v => div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr (hdeg v))) (by linarith)) m z hz hmim

omit [DecidableEq V] in
/-- The unique neighbor of an actual degree-one vertex determines all its
adjacencies. -/
theorem leaf_adj_iff (v u : V) (hv : G.degree v = 1) (hvu : G.Adj v u) (w : V) :
    G.Adj v w ↔ w = u := by
  have hcard : (G.neighborFinset v).card = 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree, hv]
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have hu : u = a := by
    have hh := (G.mem_neighborFinset v u).mpr hvu
    simpa only [ha, Finset.mem_singleton] using hh
  rw [← G.mem_neighborFinset, ha, Finset.mem_singleton, ← hu]

/-- Exact degree loss under deletion of one vertex, before any leaf
specialization. -/
theorem degree_delete_vertex (v : V) (i : {x : V // x ≠ v}) :
    (G.induce {x | x ≠ v}).degree i + (if G.Adj i.val v then 1 else 0) = G.degree i.val := by
  let e : {x : V // x ≠ v} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have heq : ((G.induce {x | x ≠ v}).neighborFinset i).map e = (G.neighborFinset i.val).erase v := by
    ext w
    simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset, Finset.mem_erase,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.property, ha⟩
    · rintro ⟨hw, hadj⟩
      exact ⟨⟨w, hw⟩, hadj, rfl⟩
  have hc := congrArg Finset.card heq
  simp only [Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree] at hc
  by_cases hadj : G.Adj i.val v
  · rw [if_pos hadj, hc]
    exact Finset.card_erase_add_one ((G.mem_neighborFinset i.val v).mpr hadj)
  · rw [if_neg hadj, add_zero, hc, Finset.erase_eq_of_not_mem ((G.mem_neighborFinset i.val v).not.mpr hadj),
      SimpleGraph.card_neighborFinset_eq_degree]

/-- Deleting an actual leaf increases the full boundary coefficient only at
its sole retained neighbor. -/
theorem leaf_boundary_coefficient (d : ℕ) (v u : V) (hv : G.degree v = 1) (hvu : G.Adj v u)
    (i : {x : V // x ≠ v}) :
    treeBoundaryWeight (G.induce {x | x ≠ v}) d i = treeBoundaryWeight G d i.val +
      (if i.val = u then 1 else 0) / ((d : ℝ) - 1) := by
  have hdegree := degree_delete_vertex G v i
  have hadj : G.Adj i.val v ↔ i.val = u := by rw [G.adj_comm]; exact leaf_adj_iff G v u hv hvu i.val
  simp only [hadj] at hdegree
  have hreal : ((G.induce {x | x ≠ v}).degree i : ℝ) + (if i.val = u then 1 else 0) = G.degree i.val := by
    exact_mod_cast hdegree
  dsimp only [treeBoundaryWeight]
  rw [← add_div]
  congr 1
  linarith

/-- Entry formula separates the normalized adjacency from the diagonal
spectral and missing-degree shifts. -/
theorem fullReferenceMatrix_apply (d : ℕ) (m z : ℂ) (i j : V) :
    fullReferenceMatrix G d m z i j = normalizedAdjacency G d i j -
      (if i = j then z + m * (treeBoundaryWeight G d i : ℂ) else 0) := by
  simp only [fullReferenceMatrix, boundaryMatrix, spectralMatrix, treeBoundaryDiagonal,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Matrix.diagonal_apply]
  by_cases hij : i = j <;> simp [hij]
  ring

/-- The leaf diagonal is exactly the genuine nonzero pivot m^-1. -/
theorem fullReferenceMatrix_leaf_pivot (d : ℕ) (hd : 3 ≤ d) (v : V) (hv : G.degree v = 1)
    (m z : ℂ) (hm : m ^ 2 + z * m + 1 = 0) :
    fullReferenceMatrix G d m z v v = m⁻¹ := by
  rw [fullReferenceMatrix_apply]
  have hzero : normalizedAdjacency G d v v = 0 := by
    simp [normalizedAdjacency, Matrix.smul_apply, smul_eq_mul, SimpleGraph.adjMatrix_apply]
  rw [hzero, if_pos rfl, zero_sub]
  have hD : (treeBoundaryWeight G d v : ℂ) = 1 := by
    dsimp [treeBoundaryWeight]
    rw [hv]
    have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
    norm_num only [Nat.cast_one]
    rw [div_self (by linarith : (d : ℝ) - 1 ≠ 0), Complex.ofReal_one]
  rw [hD, mul_one]
  have hm0 := cavity_root_ne_zero hm
  rw [← one_div]
  apply (eq_div_iff hm0).mpr
  linear_combination -hm

/-- Only the unique neighbor couples a retained vertex to the deleted leaf. -/
theorem fullReferenceMatrix_leaf_cross (d : ℕ) (v u : V) (hv : G.degree v = 1)
    (hvu : G.Adj v u) (m z : ℂ) (i : {x : V // x ≠ v}) :
    fullReferenceMatrix G d m z i.val v = if i.val = u then treeEdgeWeight d else 0 := by
  rw [fullReferenceMatrix_apply, if_neg i.property, sub_zero]
  have hadj : G.Adj i.val v ↔ i.val = u := by rw [G.adj_comm]; exact leaf_adj_iff G v u hv hvu i.val
  by_cases hi : i.val = u <;>
    simp [normalizedAdjacency, Matrix.smul_apply, smul_eq_mul, SimpleGraph.adjMatrix_apply,
      hadj, hi, hvu, hvu.symm, treeEdgeWeight]

theorem fullReferenceMatrix_leaf_cross_rev (d : ℕ) (v u : V) (hv : G.degree v = 1)
    (hvu : G.Adj v u) (m z : ℂ) (i : {x : V // x ≠ v}) :
    fullReferenceMatrix G d m z v i.val = if i.val = u then treeEdgeWeight d else 0 := by
  rw [fullReferenceMatrix_apply, if_neg (Ne.symm i.property), sub_zero]
  have hadj := leaf_adj_iff G v u hv hvu i.val
  by_cases hi : i.val = u <;>
    simp [normalizedAdjacency, Matrix.smul_apply, smul_eq_mul, SimpleGraph.adjMatrix_apply,
      hadj, hi, hvu, hvu.symm, treeEdgeWeight]

/-- The actual leaf Schur complement is exactly the full zero-deficit
reference operator of the induced remaining graph. -/
theorem leaf_reference_schur_matrix (d : ℕ) (hd : 3 ≤ d) (v u : V)
    (hv : G.degree v = 1) (hvu : G.Adj v u) (m z : ℂ)
    (hm : m ^ 2 + z * m + 1 = 0) :
    deletionInverseCandidate (fullReferenceMatrix G d m z) v =
      fullReferenceMatrix (G.induce {x | x ≠ v}) d m z := by
  ext i j
  change fullReferenceMatrix G d m z i.val j.val -
    fullReferenceMatrix G d m z i.val v * fullReferenceMatrix G d m z v j.val /
      fullReferenceMatrix G d m z v v = _
  rw [fullReferenceMatrix_leaf_cross G d v u hv hvu m z i,
    fullReferenceMatrix_leaf_cross_rev G d v u hv hvu m z j,
    fullReferenceMatrix_leaf_pivot G d hd v hv m z hm,
    fullReferenceMatrix_apply, fullReferenceMatrix_apply,
    normalizedAdjacency_induce_eq_submatrix]
  simp only [Matrix.submatrix_apply]
  rw [leaf_boundary_coefficient G d v u hv hvu i]
  have hcoe : i.val = j.val ↔ i = j := Subtype.coe_inj
  simp only [hcoe, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_sub,
    Complex.ofReal_natCast, Complex.ofReal_one, div_inv_eq_mul]
  by_cases hij : i = j
  · subst j
    by_cases hi : i.val = u
    · simp only [if_pos rfl, if_pos hi, Complex.ofReal_one, ite_true]
      have hsq := treeEdgeWeight_sq d hd
      linear_combination -m * hsq
    · simp only [if_pos rfl, if_neg hi, Complex.ofReal_zero, zero_div, add_zero,
        zero_mul, mul_zero, sub_zero]
  · by_cases hi : i.val = u
    · have hj : j.val ≠ u := by intro hj; exact hij (Subtype.ext (hi.trans hj.symm))
      simp only [if_neg hij, if_pos hi, if_neg hj, mul_zero, zero_mul, sub_zero]
    · simp only [if_neg hij, if_neg hi, zero_mul, mul_zero, sub_zero]

/-- Exact retained Green function after pruning one leaf. Every inverse is a
genuine physical inverse and the induced graph uses its own full boundary. -/
theorem leaf_reference_retained (d : ℕ) (hd : 3 ≤ d) (hdeg : ∀ x, G.degree x ≤ d)
    (v u : V) (hv : G.degree v = 1) (hvu : G.Adj v u) (m z : ℂ)
    (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im) (hmim : 0 ≤ m.im) :
    (fullTreeGreen G d m z).submatrix (Subtype.val : {x : V // x ≠ v} → V) Subtype.val =
      fullTreeGreen (G.induce {x | x ≠ v}) d m z := by
  letI : Fintype {x : V // x ≠ v} := inferInstance
  let A := fullReferenceMatrix G d m z
  let B := fullReferenceMatrix (G.induce {x | x ≠ v}) d m z
  have hA : IsUnit A := fullReferenceMatrix_isUnit G d hd hdeg m z hz hmim
  have hdegree : ∀ i : {x : V // x ≠ v}, (G.induce {x | x ≠ v}).degree i ≤ d := by
    intro i
    convert (induced_degree_le G {x | x ≠ v} i).trans (hdeg i.val) using 1
    apply congrArg (fun inst => @SimpleGraph.degree _ _ i inst)
    exact Subsingleton.elim _ _
  have hB : IsUnit B := fullReferenceMatrix_isUnit _ d hd hdegree m z hz hmim
  have hleft : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det _).mp hA)
  have hpivot : A v v ≠ 0 := by
    rw [show A v v = m⁻¹ from fullReferenceMatrix_leaf_pivot G d hd v hv m z hm]
    exact inv_ne_zero (cavity_root_ne_zero hm)
  have hh := deleted_matrix_inverse A⁻¹ A v hleft hpivot
  rw [leaf_reference_schur_matrix G d hd v u hv hvu m z hm] at hh
  have hret : IsUnit ((A⁻¹).submatrix (Subtype.val : {x : V // x ≠ v} → V) (Subtype.val : {x : V // x ≠ v} → V)) := by
    apply Matrix.isUnit_nonsing_inv_iff.mp
    rw [hh]
    exact hB
  have hinv := congrArg (fun M : Matrix {x : V // x ≠ v} {x : V // x ≠ v} ℂ => M⁻¹) hh
  dsimp only at hinv
  rw [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hret)] at hinv
  exact hinv

/-- Exact sparse row of the actual reference operator at a leaf. -/
theorem fullReferenceMatrix_leaf_row (d : ℕ) (hd : 3 ≤ d) (v u : V)
    (hv : G.degree v = 1) (hvu : G.Adj v u) (m z : ℂ)
    (hm : m ^ 2 + z * m + 1 = 0) (w : V) :
    fullReferenceMatrix G d m z v w =
      (if w = v then m⁻¹ else 0) + (if w = u then treeEdgeWeight d else 0) := by
  by_cases hw : w = v
  · subst w
    rw [fullReferenceMatrix_leaf_pivot G d hd v hv m z hm]
    simp only [if_pos rfl, if_neg hvu.ne, add_zero, ite_true]
  · rw [fullReferenceMatrix_leaf_cross_rev G d v u hv hvu m z ⟨w, hw⟩]
    simp only [if_neg hw, zero_add]

/-- Exact sparse column at the same leaf. -/
theorem fullReferenceMatrix_leaf_column (d : ℕ) (hd : 3 ≤ d) (v u : V)
    (hv : G.degree v = 1) (hvu : G.Adj v u) (m z : ℂ)
    (hm : m ^ 2 + z * m + 1 = 0) (w : V) :
    fullReferenceMatrix G d m z w v =
      (if w = v then m⁻¹ else 0) + (if w = u then treeEdgeWeight d else 0) := by
  by_cases hw : w = v
  · subst w
    rw [fullReferenceMatrix_leaf_pivot G d hd v hv m z hm]
    simp only [if_pos rfl, if_neg hvu.ne, add_zero, ite_true]
  · rw [fullReferenceMatrix_leaf_cross G d v u hv hvu m z ⟨w, hw⟩]
    simp only [if_neg hw, zero_add]

theorem fullReferenceMatrix_leaf_mul_row (d : ℕ) (hd : 3 ≤ d) (v u : V)
    (hv : G.degree v = 1) (hvu : G.Adj v u) (m z : ℂ)
    (hm : m ^ 2 + z * m + 1 = 0) (X : Matrix V V ℂ) (j : V) :
    (fullReferenceMatrix G d m z * X) v j = m⁻¹ * X v j + treeEdgeWeight d * X u j := by
  rw [Matrix.mul_apply]
  simp_rw [fullReferenceMatrix_leaf_row G d hd v u hv hvu m z hm, add_mul]
  rw [Finset.sum_add_distrib]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem fullReferenceMatrix_leaf_mul_column (d : ℕ) (hd : 3 ≤ d) (v u : V)
    (hv : G.degree v = 1) (hvu : G.Adj v u) (m z : ℂ)
    (hm : m ^ 2 + z * m + 1 = 0) (X : Matrix V V ℂ) (i : V) :
    (X * fullReferenceMatrix G d m z) i v = X i v * m⁻¹ + X i u * treeEdgeWeight d := by
  rw [Matrix.mul_apply]
  simp_rw [fullReferenceMatrix_leaf_column G d hd v u hv hvu m z hm, mul_add]
  rw [Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Exact cross entries after leaf pruning, in both row and column directions. -/
theorem leaf_reference_cross (d : ℕ) (hd : 3 ≤ d) (hdeg : ∀ x, G.degree x ≤ d)
    (v u : V) (hv : G.degree v = 1) (hvu : G.Adj v u) (m z : ℂ)
    (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im) (hmim : 0 ≤ m.im)
    (j : {x : V // x ≠ v}) :
    fullTreeGreen G d m z v j.val = (-m * treeEdgeWeight d) *
      fullTreeGreen (G.induce {x | x ≠ v}) d m z ⟨u, hvu.ne.symm⟩ j ∧
    fullTreeGreen G d m z j.val v = (-m * treeEdgeWeight d) *
      fullTreeGreen (G.induce {x | x ≠ v}) d m z j ⟨u, hvu.ne.symm⟩ := by
  let A := fullReferenceMatrix G d m z
  let P := fullTreeGreen G d m z
  have hA := fullReferenceMatrix_isUnit G d hd hdeg m z hz hmim
  have hAP : A * P = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA)
  have hPA : P * A = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hA)
  have hm0 := cavity_root_ne_zero hm
  have hret := leaf_reference_retained G d hd hdeg v u hv hvu m z hm hz hmim
  have hrow : m⁻¹ * P v j.val + treeEdgeWeight d * P u j.val = 0 := by
    have hh := congrArg (fun M : Matrix V V ℂ => M v j.val) hAP
    dsimp only at hh
    rw [fullReferenceMatrix_leaf_mul_row G d hd v u hv hvu m z hm] at hh
    simpa only [Matrix.one_apply, if_neg (Ne.symm j.property)] using hh
  have hcol : m⁻¹ * P j.val v + treeEdgeWeight d * P j.val u = 0 := by
    have hh := congrArg (fun M : Matrix V V ℂ => M j.val v) hPA
    dsimp only at hh
    rw [fullReferenceMatrix_leaf_mul_column G d hd v u hv hvu m z hm] at hh
    simpa only [Matrix.one_apply, if_neg j.property, mul_comm] using hh
  have hsolve : ∀ a b : ℂ, m⁻¹ * a + treeEdgeWeight d * b = 0 → a = (-m * treeEdgeWeight d) * b := by
    intro a b hab
    calc
      a = m * (m⁻¹ * a) := by rw [← mul_assoc, mul_inv_cancel₀ hm0, one_mul]
      _ = m * (-(treeEdgeWeight d * b)) := by rw [eq_neg_of_add_eq_zero_left hab]
      _ = _ := by ring
  constructor
  · have hh := hsolve _ _ hrow
    have hentry := congrArg (fun M : Matrix {x : V // x ≠ v} {x : V // x ≠ v} ℂ => M ⟨u, hvu.ne.symm⟩ j) hret
    dsimp only at hentry
    change P u j.val = _ at hentry
    rw [← hentry]
    exact hh
  · have hh := hsolve _ _ hcol
    have hentry := congrArg (fun M : Matrix {x : V // x ≠ v} {x : V // x ≠ v} ℂ => M j ⟨u, hvu.ne.symm⟩) hret
    dsimp only at hentry
    change P j.val u = _ at hentry
    rw [← hentry]
    exact hh

/-- Exact diagonal reconstruction of the pruned leaf. -/
theorem leaf_reference_diagonal (d : ℕ) (hd : 3 ≤ d) (hdeg : ∀ x, G.degree x ≤ d)
    (v u : V) (hv : G.degree v = 1) (hvu : G.Adj v u) (m z : ℂ)
    (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im) (hmim : 0 ≤ m.im) :
    fullTreeGreen G d m z v v = m + (m ^ 2 / ((d : ℂ) - 1)) *
      fullTreeGreen (G.induce {x | x ≠ v}) d m z ⟨u, hvu.ne.symm⟩ ⟨u, hvu.ne.symm⟩ := by
  let A := fullReferenceMatrix G d m z
  let P := fullTreeGreen G d m z
  have hA := fullReferenceMatrix_isUnit G d hd hdeg m z hz hmim
  have hAP : A * P = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA)
  have hh := congrArg (fun M : Matrix V V ℂ => M v v) hAP
  dsimp only at hh
  rw [fullReferenceMatrix_leaf_mul_row G d hd v u hv hvu m z hm] at hh
  simp only [Matrix.one_apply, if_pos rfl, ite_true] at hh
  have hm0 := cavity_root_ne_zero hm
  have hdiag : P v v + m * treeEdgeWeight d * P u v = m := by
    calc
      _ = m * (m⁻¹ * P v v + treeEdgeWeight d * P u v) := by
        rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hm0, one_mul]
        ring
      _ = m := by rw [hh, mul_one]
  dsimp only [P] at hdiag
  have hcross := (leaf_reference_cross G d hd hdeg v u hv hvu m z hm hz hmim ⟨u, hvu.ne.symm⟩).2
  dsimp only at hcross
  rw [hcross] at hdiag
  have hsq := treeEdgeWeight_sq d hd
  linear_combination hdiag +
    (m ^ 2 * fullTreeGreen (G.induce {x | x ≠ v}) d m z ⟨u, hvu.ne.symm⟩ ⟨u, hvu.ne.symm⟩) * hsq

end FiniteGraph
end
end LocalLaw
