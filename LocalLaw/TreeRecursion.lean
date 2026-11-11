import LocalLaw.ScalarRecursion

/-!
# Finite homogeneous cavity-tree matrices

The root entry of a genuine finite matrix inverse obeys the scalar cavity
recursion. The proof uses the Schur complement, independent branch blocks, and
the normalization k*α²=1. Nonsingularity is proved inductively from the scalar
recursive denominators, rather than assuming the desired root-entry identity.
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace LocalLaw

section RootSchur
variable {V : Type*} [Fintype V] [DecidableEq V]

def singletonScalarMatrix (a : ℂ) : Matrix Unit Unit ℂ := fun _ _ => a

def rootCouplingRow (b : V → ℂ) : Matrix Unit V ℂ := fun _ j => b j

def rootCouplingColumn (b : V → ℂ) : Matrix V Unit ℂ := fun i _ => b i

/-- One distinguished root joined symmetrically to an arbitrary branch matrix. -/
def rootBlockMatrix (a : ℂ) (b : V → ℂ) (D : Matrix V V ℂ) :
    Matrix (Unit ⊕ V) (Unit ⊕ V) ℂ :=
  Matrix.fromBlocks (singletonScalarMatrix a) (rootCouplingRow b) (rootCouplingColumn b) D

noncomputable def rootSchurValue (a : ℂ) (b : V → ℂ) (D : Matrix V V ℂ) : ℂ :=
  a - ∑ i, ∑ j, b i * D⁻¹ i j * b j

private theorem root_schur_matrix (a : ℂ) (b : V → ℂ) (D : Matrix V V ℂ)
    [Invertible D] :
    (singletonScalarMatrix a) - (rootCouplingRow b) * ⅟ D * (rootCouplingColumn b) =
      (singletonScalarMatrix (rootSchurValue a b D)) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, rootSchurValue,
    Matrix.invOf_eq_nonsing_inv, Finset.sum_mul,
    singletonScalarMatrix, rootCouplingRow, rootCouplingColumn]
  rw [Finset.sum_comm]

private theorem unit_singleton_matrix {a : ℂ} (ha : a ≠ 0) :
    IsUnit (singletonScalarMatrix a) := by
  rw [Matrix.isUnit_iff_isUnit_det,
    Matrix.det_eq_elem_of_subsingleton (singletonScalarMatrix a) ()]
  change IsUnit a
  exact isUnit_iff_ne_zero.mpr ha

/-- A root-plus-branches matrix is nonsingular when the branches and scalar
Schur complement are nonsingular; its inverse root entry is the reciprocal
Schur complement. -/
theorem rootBlock_inverse_root (a : ℂ) (b : V → ℂ) (D : Matrix V V ℂ)
    (hD : IsUnit D) (hs : rootSchurValue a b D ≠ 0) :
    IsUnit (rootBlockMatrix a b D) ∧
      (rootBlockMatrix a b D)⁻¹ (Sum.inl ()) (Sum.inl ()) =
        (rootSchurValue a b D)⁻¹ := by
  letI : Invertible D := Classical.choice hD.nonempty_invertible
  have hschur : IsUnit ((singletonScalarMatrix a) -
      (rootCouplingRow b) * ⅟ D * (rootCouplingColumn b)) := by
    rw [root_schur_matrix]
    exact unit_singleton_matrix hs
  letI : Invertible ((singletonScalarMatrix a) -
      (rootCouplingRow b) * ⅟ D * (rootCouplingColumn b)) :=
    Classical.choice hschur.nonempty_invertible
  letI := Matrix.fromBlocks₂₂Invertible (singletonScalarMatrix a)
    (rootCouplingRow b) (rootCouplingColumn b) D
  constructor
  · unfold rootBlockMatrix
    exact isUnit_of_invertible _
  · unfold rootBlockMatrix
    rw [← Matrix.invOf_eq_nonsing_inv, Matrix.invOf_fromBlocks₂₂_eq]
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.invOf_eq_nonsing_inv]
    have heq : singletonScalarMatrix a - rootCouplingRow b * D⁻¹ * rootCouplingColumn b =
        singletonScalarMatrix (rootSchurValue a b D) := by
      simpa only [Matrix.invOf_eq_nonsing_inv] using root_schur_matrix a b D
    rw [heq, Matrix.inv_subsingleton]
    simp [singletonScalarMatrix, Ring.inverse_eq_inv]


end RootSchur

section HomogeneousBranch
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- k disjoint, identical branch matrices. The vertex index is V×Fin k. -/
def identicalBranches (k : ℕ) (M : Matrix V V ℂ) :
    Matrix (V × Fin k) (V × Fin k) ℂ := Matrix.blockDiagonal (fun _ : Fin k => M)

/-- Each branch is joined to its distinguished vertex by edge weight α. -/
def branchRootCoupling (k : ℕ) (r : V) (α : ℂ) : V × Fin k → ℂ :=
  fun p => if p.1 = r then α else 0

theorem identicalBranches_isUnit (k : ℕ) (M : Matrix V V ℂ) (hM : IsUnit M) :
    IsUnit (identicalBranches k M) := by
  change IsUnit ((Matrix.blockDiagonalRingHom V (Fin k) ℂ) (fun _ => M))
  apply IsUnit.map (Matrix.blockDiagonalRingHom V (Fin k) ℂ)
  exact Pi.isUnit_iff.mpr (fun _ => hM)

theorem identicalBranches_inverse (k : ℕ) (M : Matrix V V ℂ) (hM : IsUnit M) :
    (identicalBranches k M)⁻¹ = identicalBranches k M⁻¹ := by
  apply Matrix.inv_eq_left_inv
  unfold identicalBranches
  rw [← Matrix.blockDiagonal_mul]
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M
    ((Matrix.isUnit_iff_isUnit_det M).mp hM)
  simp only [hinv]
  exact Matrix.blockDiagonal_one

/-- The root Schur term is the sum of k identical branch root entries. -/
theorem identicalBranches_self_energy (k : ℕ) (M : Matrix V V ℂ)
    (hM : IsUnit M) (r : V) (α : ℂ) :
    (∑ i, ∑ j, branchRootCoupling k r α i * (identicalBranches k M)⁻¹ i j *
      branchRootCoupling k r α j) = (k : ℂ) * α ^ 2 * M⁻¹ r r := by
  rw [identicalBranches_inverse k M hM]
  simp [branchRootCoupling, identicalBranches, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type, mul_assoc, mul_left_comm, mul_comm, pow_two]

/-- Exact finite-matrix cavity update after normalized homogeneous branching. -/
theorem homogeneous_branch_root_update (k : ℕ) (M : Matrix V V ℂ)
    (hM : IsUnit M) (r : V) (α z : ℂ) (hnorm : (k : ℂ) * α ^ 2 = 1)
    (hden : z + M⁻¹ r r ≠ 0) :
    IsUnit (rootBlockMatrix (-z) (branchRootCoupling k r α) (identicalBranches k M)) ∧
      (rootBlockMatrix (-z) (branchRootCoupling k r α) (identicalBranches k M))⁻¹
        (Sum.inl ()) (Sum.inl ()) = -(z + M⁻¹ r r)⁻¹ := by
  have hschur : rootSchurValue (-z) (branchRootCoupling k r α)
      (identicalBranches k M) = -(z + M⁻¹ r r) := by
    rw [rootSchurValue, identicalBranches_self_energy k M hM r α, hnorm]
    ring
  have hs : rootSchurValue (-z) (branchRootCoupling k r α)
      (identicalBranches k M) ≠ 0 := by
    rw [hschur]
    exact neg_ne_zero.mpr hden
  obtain ⟨hu, hi⟩ := rootBlock_inverse_root (-z) (branchRootCoupling k r α)
    (identicalBranches k M) (identicalBranches_isUnit k M hM) hs
  exact ⟨hu, by simpa only [hschur, inv_neg] using hi⟩

end HomogeneousBranch

/-- A finite rooted k-ary tree, with zero meaning a single root. Each successor
adds a distinguished root and k disjoint copies of the preceding tree. -/
def CavityTreeIndex (k : ℕ) : ℕ → Type
  | 0 => Unit
  | n + 1 => Unit ⊕ (CavityTreeIndex k n × Fin k)

private def cavityTreeFintype (k : ℕ) : (n : ℕ) → Fintype (CavityTreeIndex k n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => by
      letI := cavityTreeFintype k n
      exact inferInstanceAs (Fintype (Unit ⊕ (CavityTreeIndex k n × Fin k)))

instance (k n : ℕ) : Fintype (CavityTreeIndex k n) := cavityTreeFintype k n

private def cavityTreeDecidableEq (k : ℕ) : (n : ℕ) → DecidableEq (CavityTreeIndex k n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n + 1 => by
      letI := cavityTreeDecidableEq k n
      exact inferInstanceAs (DecidableEq (Unit ⊕ (CavityTreeIndex k n × Fin k)))

instance (k n : ℕ) : DecidableEq (CavityTreeIndex k n) := cavityTreeDecidableEq k n

/-- The actual distinguished index of the root. -/
def cavityTreeRoot (k : ℕ) : (n : ℕ) → CavityTreeIndex k n
  | 0 => ()
  | _n + 1 => Sum.inl ()

/-- Concrete spectral matrix of the finite homogeneous cavity tree. Internal
vertices have diagonal -z; depth-zero leaves have diagonal -z-w. -/
noncomputable def cavityTreeMatrix (k : ℕ) (α z w : ℂ) :
    (n : ℕ) → Matrix (CavityTreeIndex k n) (CavityTreeIndex k n) ℂ
  | 0 => singletonScalarMatrix (-z - w)
  | n + 1 => rootBlockMatrix (-z) (branchRootCoupling k (cavityTreeRoot k n) α)
      (identicalBranches k (cavityTreeMatrix k α z w n))

/-- Identification of a genuine finite tree matrix inverse with the scalar
cavity recursion. Only the scalar denominators, not the final identity or
matrix nonsingularity, are hypotheses. -/
theorem cavityTree_inverse_root (k : ℕ) (α z w : ℂ)
    (hnorm : (k : ℂ) * α ^ 2 = 1) (n : ℕ)
    (hden : ∀ j ≤ n, z + cavityIterate z w j ≠ 0) :
    IsUnit (cavityTreeMatrix k α z w n) ∧
      (cavityTreeMatrix k α z w n)⁻¹ (cavityTreeRoot k n) (cavityTreeRoot k n) =
        cavityIterate z w (n + 1) := by
  induction n with
  | zero =>
      have hd := hden 0 le_rfl
      simp only [cavityIterate] at hd
      have ha : -z - w ≠ 0 := by
        rw [show -z - w = -(z + w) by ring]
        exact neg_ne_zero.mpr hd
      constructor
      · exact unit_singleton_matrix ha
      · change (singletonScalarMatrix (-z - w))⁻¹ () () = -(z + w)⁻¹
        rw [Matrix.inv_subsingleton]
        simp only [Matrix.diagonal_apply_eq, singletonScalarMatrix, Ring.inverse_eq_inv]
        rw [show -z - w = -(z + w) by ring, inv_neg]
  | succ n ih =>
      obtain ⟨hu, hg⟩ := ih (fun j hj => hden j (Nat.le_trans hj (Nat.le_succ n)))
      have hd : z + (cavityTreeMatrix k α z w n)⁻¹
          (cavityTreeRoot k n) (cavityTreeRoot k n) ≠ 0 := by
        rw [hg]
        exact hden (n + 1) le_rfl
      obtain ⟨hu', hg'⟩ := homogeneous_branch_root_update k
        (cavityTreeMatrix k α z w n) hu (cavityTreeRoot k n) α z hnorm hd
      refine ⟨hu', ?_⟩
      change (rootBlockMatrix (-z) (branchRootCoupling k (cavityTreeRoot k n) α)
        (identicalBranches k (cavityTreeMatrix k α z w n)))⁻¹
          (Sum.inl ()) (Sum.inl ()) = cavityIterate z w (n + 1 + 1)
      rw [hg', hg]
      rfl

/-- The reference-root smallness hypothesis proves all tree nonsingularity and
all scalar recursive denominators automatically. -/
theorem cavityTree_inverse_root_of_small (k : ℕ) (α z w m : ℂ)
    (hnorm : (k : ℂ) * α ^ 2 = 1)
    (hm : m ^ 2 + z * m + 1 = 0) (hmnorm : ‖m‖ ≤ 1) (n : ℕ)
    (hsmall : ((n + 1 : ℕ) : ℝ) * ‖w - m‖ ≤ 1 / 2) :
    IsUnit (cavityTreeMatrix k α z w n) ∧
      (cavityTreeMatrix k α z w n)⁻¹ (cavityTreeRoot k n) (cavityTreeRoot k n) =
        cavityIterate z w (n + 1) := by
  apply cavityTree_inverse_root k α z w hnorm n
  intro j hj
  apply cavity_iterate_step_ne_zero hm j
  intro l hl
  exact cavityDenominator_all_ne_zero hmnorm (n + 1) hsmall l
    (Nat.le_trans hl (Nat.succ_le_succ hj))

/-- Closed fractional-linear root resolvent for the concrete finite tree. -/
theorem cavityTree_inverse_root_exact (k : ℕ) (α z w m : ℂ)
    (hnorm : (k : ℂ) * α ^ 2 = 1)
    (hm : m ^ 2 + z * m + 1 = 0) (hmnorm : ‖m‖ ≤ 1) (n : ℕ)
    (hsmall : ((n + 1 : ℕ) : ℝ) * ‖w - m‖ ≤ 1 / 2) :
    (cavityTreeMatrix k α z w n)⁻¹ (cavityTreeRoot k n) (cavityTreeRoot k n) =
      m + m ^ (2 * (n + 1)) * (w - m) / cavityDenominator m (w - m) (n + 1) := by
  rw [(cavityTree_inverse_root_of_small k α z w m hnorm hm hmnorm n hsmall).2]
  exact cavity_iterate_exact_of_small hm hmnorm (n + 1) hsmall

/-- The normalized adjacency edge for k homogeneous forward children. -/
noncomputable def normalizedCavityEdge (k : ℕ) : ℂ :=
  ↑((Real.sqrt (k : ℝ))⁻¹)

theorem normalizedCavityEdge_normalization (k : ℕ) (hk : 0 < k) :
    (k : ℂ) * normalizedCavityEdge k ^ 2 = 1 := by
  have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hs : Real.sqrt (k : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hkR)
  have hreal : (k : ℝ) * ((Real.sqrt (k : ℝ))⁻¹) ^ 2 = 1 := by
    field_simp
  unfold normalizedCavityEdge
  exact_mod_cast hreal

/-- The finite homogeneous cavity tree with the usual real normalized
adjacency edge has exactly the scalar root resolvent, with all inverses proved
legitimate by the reference-root smallness condition. -/
theorem normalized_cavityTree_inverse_root (k : ℕ) (hk : 0 < k) (z w m : ℂ)
    (hm : m ^ 2 + z * m + 1 = 0) (hmnorm : ‖m‖ ≤ 1) (n : ℕ)
    (hsmall : ((n + 1 : ℕ) : ℝ) * ‖w - m‖ ≤ 1 / 2) :
    IsUnit (cavityTreeMatrix k (normalizedCavityEdge k) z w n) ∧
      (cavityTreeMatrix k (normalizedCavityEdge k) z w n)⁻¹
        (cavityTreeRoot k n) (cavityTreeRoot k n) = cavityIterate z w (n + 1) :=
  cavityTree_inverse_root_of_small k (normalizedCavityEdge k) z w m
    (normalizedCavityEdge_normalization k hk) hm hmnorm n hsmall

end LocalLaw
