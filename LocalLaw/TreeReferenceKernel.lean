import LocalLaw.GraphModel
import LocalLaw.GraphPowerLocality

/-!
# Reference kernels on actual finite forests

The reference cavity column is verified on an arbitrary finite acyclic graph,
without assuming an isomorphism to a canonical homogeneous tree. The graph
geometry is the unique-path property of forests: one neighbor is closer to a
reachable root and every other neighbor is one step farther away.
-/

open scoped BigOperators Matrix

namespace LocalLaw

section ForestGeometry
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
/-- In a forest every simple path is the shortest path, by path uniqueness. -/
theorem acyclic_path_length_eq_dist (hG : G.IsAcyclic) {v w : V}
    (p : G.Walk v w) (hp : p.IsPath) : p.length = G.dist v w := by
  obtain ⟨q, hq, hlen⟩ := p.reachable.exists_path_of_dist
  have heq : p = q := congrArg Subtype.val (hG.path_unique ⟨p, hp⟩ ⟨q, hq⟩)
  simpa only [heq] using hlen

/-- Exact parent/children distance structure of a finite or infinite forest. -/
theorem forest_parent_distance (hG : G.IsAcyclic) (root v : V)
    (hr : G.Reachable v root) (hne : v ≠ root) :
    ∃ parent, G.Adj v parent ∧ G.dist parent root + 1 = G.dist v root ∧
      ∀ w, G.Adj v w → w ≠ parent → G.dist w root = G.dist v root + 1 := by
  obtain ⟨p, hp, hlen⟩ := hr.exists_path_of_dist
  cases p with
  | nil => exact False.elim (hne rfl)
  | @cons v parent root hvp tail =>
      have htail : tail.IsPath := hp.of_cons
      have htailLen := acyclic_path_length_eq_dist hG tail htail
      refine ⟨parent, hvp, ?_, ?_⟩
      · simpa only [SimpleGraph.Walk.length_cons, htailLen] using hlen
      · intro w hvw hwparent
        have hnot : w ∉ (tail.cons hvp).support := by
          intro hw
          have hwTail : w ∈ tail.support := by
            have hh := hw
            rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hh
            exact hh.resolve_left hvw.ne.symm
          have hpath := hp.takeUntil hw
          have heq : (tail.cons hvp).takeUntil w hw = SimpleGraph.Walk.cons hvw SimpleGraph.Walk.nil :=
            congrArg Subtype.val (hG.path_unique ⟨_, hpath⟩ (SimpleGraph.Path.singleton hvw))
          rw [SimpleGraph.Walk.takeUntil_cons hwTail hvw.ne] at heq
          have hfirst := congrArg (fun q : G.Walk v w => q.getVert 1) heq
          simp only [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.getVert_zero] at hfirst
          exact hwparent hfirst.symm
        have hnewPath : ((tail.cons hvp).cons hvw.symm).IsPath := hp.cons hnot
        have hnewLen := acyclic_path_length_eq_dist hG _ hnewPath
        calc
          G.dist w root = ((tail.cons hvp).cons hvw.symm).length := hnewLen.symm
          _ = (tail.cons hvp).length + 1 := SimpleGraph.Walk.length_cons _ _
          _ = G.dist v root + 1 := by rw [hlen]

end ForestGeometry

noncomputable section
local instance treeKernelDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The edge normalization used by the actual graph matrix. -/
def treeEdgeWeight (d : ℕ) : ℂ := ↑((Real.sqrt ((d : ℝ) - 1))⁻¹)

theorem treeEdgeWeight_sq (d : ℕ) (hd : 3 ≤ d) :
    treeEdgeWeight d ^ 2 = 1 / ((d : ℂ) - 1) := by
  have hk : (0 : ℝ) < d - 1 := by have : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd; linarith
  have hr : ((Real.sqrt ((d : ℝ) - 1))⁻¹) ^ 2 = 1 / ((d : ℝ) - 1) := by
    rw [inv_pow, Real.sq_sqrt hk.le, one_div]
  unfold treeEdgeWeight
  exact_mod_cast hr

/-- Exponentially decaying column on the root component, zero on other components. -/
def forestKernelColumn {V : Type*} (G : SimpleGraph V) (root : V) (c t : ℂ) (v : V) : ℂ :=
  if G.Reachable v root then c * t ^ G.dist v root else 0

@[simp] theorem forestKernelColumn_root {V : Type*} (G : SimpleGraph V) (root : V) (c t : ℂ) :
    forestKernelColumn G root c t root = c := by
  simp [forestKernelColumn, SimpleGraph.Reachable.refl, G.dist_self]

section FiniteForest
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

omit [DecidableEq V] in
theorem normalizedAdjacency_mulVec_neighbor (d : ℕ) (f : V → ℂ) (v : V) :
    (normalizedAdjacency G d *ᵥ f) v = treeEdgeWeight d * ∑ w ∈ G.neighborFinset v, f w := by
  unfold normalizedAdjacency treeEdgeWeight
  rw [Matrix.smul_mulVec_assoc]
  simp only [Pi.smul_apply, smul_eq_mul, G.adjMatrix_mulVec_apply]

/-- Sum of the candidate column over the neighbors of the root. -/
theorem forestKernelColumn_root_neighbor_sum (root : V) (c t : ℂ) :
    (∑ w ∈ G.neighborFinset root, forestKernelColumn G root c t w) =
      (G.degree root : ℂ) * c * t := by
  calc
    (∑ w ∈ G.neighborFinset root, forestKernelColumn G root c t w) =
        ∑ _w ∈ G.neighborFinset root, c * t := by
      apply Finset.sum_congr rfl
      intro w hw
      have hadj := (G.mem_neighborFinset root w).mp hw
      have hr : G.Reachable w root := hadj.symm.reachable
      have hd : G.dist w root = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm
      simp only [forestKernelColumn, if_pos hr, hd, pow_one]
    _ = (G.degree root : ℂ) * c * t := by simp [nsmul_eq_mul]; ring

/-- Exact neighbor sum at a nonroot reachable vertex, using its unique parent. -/
theorem forestKernelColumn_neighbor_sum (root v parent : V) (c t : ℂ)
    (hr : G.Reachable v root) (hvp : G.Adj v parent)
    (hp : G.dist parent root + 1 = G.dist v root)
    (hfar : ∀ w, G.Adj v w → w ≠ parent → G.dist w root = G.dist v root + 1) :
    (∑ w ∈ G.neighborFinset v, forestKernelColumn G root c t w) =
      ((G.degree v : ℂ) - 1) * c * t ^ (G.dist parent root + 2) + c * t ^ G.dist parent root := by
  have hmem : parent ∈ G.neighborFinset v := (G.mem_neighborFinset v parent).mpr hvp
  have hparentReach : G.Reachable parent root := hvp.symm.reachable.trans hr
  have hcardNat := Finset.card_erase_add_one hmem
  have hcard : ((G.neighborFinset v).erase parent).card + (1 : ℂ) = (G.degree v : ℂ) := by
    exact_mod_cast hcardNat
  have hcard' : (((G.neighborFinset v).erase parent).card : ℂ) = (G.degree v : ℂ) - 1 := by
    linear_combination hcard
  rw [← Finset.sum_erase_add (G.neighborFinset v) (forestKernelColumn G root c t) hmem]
  have hsum : (∑ w ∈ (G.neighborFinset v).erase parent, forestKernelColumn G root c t w) =
      (((G.neighborFinset v).erase parent).card : ℂ) * (c * t ^ (G.dist parent root + 2)) := by
    calc
      _ = ∑ _w ∈ (G.neighborFinset v).erase parent, c * t ^ (G.dist parent root + 2) := by
        apply Finset.sum_congr rfl
        intro w hw
        have hadj := (G.mem_neighborFinset v w).mp (Finset.mem_of_mem_erase hw)
        have hwr : G.Reachable w root := hadj.symm.reachable.trans hr
        have hd := hfar w hadj (Finset.mem_erase.mp hw).1
        have hd' : G.dist w root = G.dist parent root + 2 := by omega
        simp only [forestKernelColumn, if_pos hwr, hd']
      _ = _ := by simp [nsmul_eq_mul]
  rw [hsum, hcard']
  simp only [forestKernelColumn, if_pos hparentReach]
  ring

/-- A root deficit b is attached only at the distinguished vertex. -/
def forestBoundaryCoefficient (d : ℕ) (root : V) (b : ℕ) (v : V) : ℝ :=
  ((d : ℝ) - (if v = root then (b : ℝ) else 0) - (G.degree v : ℝ)) / ((d : ℝ) - 1)

def forestReferenceMatrix (d : ℕ) (root : V) (b : ℕ) (m z : ℂ) : Matrix V V ℂ :=
  boundaryMatrix (normalizedAdjacency G d)
    (Matrix.diagonal (fun v => (forestBoundaryCoefficient G d root b v : ℂ))) m z

/-- The finite model applied to any column, written using actual neighbors. -/
theorem forestReferenceMatrix_mulVec (d : ℕ) (root : V) (b : ℕ) (m z : ℂ) (f : V → ℂ) (v : V) :
    (forestReferenceMatrix G d root b m z *ᵥ f) v =
      treeEdgeWeight d * (∑ w ∈ G.neighborFinset v, f w) - z * f v -
        m * (forestBoundaryCoefficient G d root b v : ℂ) * f v := by
  unfold forestReferenceMatrix boundaryMatrix spectralMatrix
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
    Matrix.one_mulVec, Matrix.smul_mulVec_assoc]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal]
  rw [normalizedAdjacency_mulVec_neighbor]
  ring

theorem forestBoundaryCoefficient_complex (d : ℕ) (root : V) (b : ℕ) (v : V) :
    (forestBoundaryCoefficient G d root b v : ℂ) =
      ((d : ℂ) - (if v = root then (b : ℂ) else 0) - (G.degree v : ℂ)) / ((d : ℂ) - 1) := by
  by_cases h : v = root <;> simp [forestBoundaryCoefficient, h, Complex.ofReal_div,
    Complex.ofReal_sub, Complex.ofReal_natCast]

private theorem forest_root_scalar (α m z c D b degree : ℂ) (hα : α ^ 2 = 1 / (D - 1)) :
    α * (degree * c * (-m * α)) - z * c - m * ((D - b - degree) / (D - 1)) * c =
      c * (-z - (D - b) * m / (D - 1)) := by
  linear_combination -(degree * c * m) * hα

private theorem forest_nonroot_scalar (α m z c D degree : ℂ) (h : ℕ)
    (hD : D - 1 ≠ 0) (hm : m ^ 2 + z * m + 1 = 0) (hα : α ^ 2 = 1 / (D - 1)) :
    α * ((degree - 1) * c * (-m * α) ^ (h + 2) + c * (-m * α) ^ h) -
      z * (c * (-m * α) ^ (h + 1)) -
      m * ((D - degree) / (D - 1)) * (c * (-m * α) ^ (h + 1)) = 0 := by
  have ht : (-m * α) ^ 2 = m ^ 2 / (D - 1) := by
    rw [mul_pow, neg_sq, hα]
    ring
  rw [pow_add, pow_add, ht, pow_one]
  field_simp
  linear_combination ((D - 1) * c * (-m * α) ^ h * α) * hm

/-- Direct verification of the actual forest reference column against its
finite matrix. The root deficit is arbitrary; only the root normalization
on the right-hand side changes. -/
theorem forestReferenceMatrix_column (hG : G.IsAcyclic) (d : ℕ) (hd : 3 ≤ d)
    (root : V) (b : ℕ) (m z c : ℂ) (hm : m ^ 2 + z * m + 1 = 0) :
    forestReferenceMatrix G d root b m z *ᵥ
        forestKernelColumn G root c (-m * treeEdgeWeight d) =
      Pi.single root (c * (-z - ((d : ℂ) - b) * m / ((d : ℂ) - 1))) := by
  have hk : (d : ℂ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
    intro heq
    have hre := congrArg Complex.re heq
    simp at hre
    linarith
  funext v
  rw [forestReferenceMatrix_mulVec]
  by_cases hv : v = root
  · subst v
    rw [forestKernelColumn_root_neighbor_sum, forestKernelColumn_root,
      forestBoundaryCoefficient_complex]
    simp only [if_pos rfl, Pi.single_apply, ite_true]
    exact forest_root_scalar _ _ _ _ _ _ _ (treeEdgeWeight_sq d hd)
  · rw [Pi.single_apply, if_neg hv]
    by_cases hr : G.Reachable v root
    · obtain ⟨parent, hvp, hp, hfar⟩ := forest_parent_distance hG root v hr hv
      rw [forestKernelColumn_neighbor_sum G root v parent c _ hr hvp hp hfar,
        forestBoundaryCoefficient_complex, if_neg hv, sub_zero]
      have hf : forestKernelColumn G root c (-m * treeEdgeWeight d) v =
          c * (-m * treeEdgeWeight d) ^ (G.dist parent root + 1) := by
        simp only [forestKernelColumn, if_pos hr, hp]
      rw [hf]
      exact forest_nonroot_scalar _ _ _ _ _ _ _ hk hm (treeEdgeWeight_sq d hd)
    · have hsum : (∑ w ∈ G.neighborFinset v, forestKernelColumn G root c (-m * treeEdgeWeight d) w) = 0 := by
        apply Finset.sum_eq_zero
        intro w hw
        have hadj := (G.mem_neighborFinset v w).mp hw
        have hwr : ¬G.Reachable w root := fun h => hr (hadj.reachable.trans h)
        simp only [forestKernelColumn, if_neg hwr]
      rw [hsum]
      simp only [forestKernelColumn, if_neg hr, mul_zero, sub_zero]

/-- Nonnegative missing-degree coefficients, with the root deficit counted
explicitly in the actual graph's degree bound. -/
theorem forestBoundaryCoefficient_nonnegative (d : ℕ) (hd : 3 ≤ d) (root : V) (b : ℕ)
    (hdeg : ∀ v, G.degree v + (if v = root then b else 0) ≤ d) (v : V) :
    0 ≤ forestBoundaryCoefficient G d root b v := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hbound : (G.degree v : ℝ) + (if v = root then (b : ℝ) else 0) ≤ d := by
    exact_mod_cast hdeg v
  unfold forestBoundaryCoefficient
  apply div_nonneg (by linarith)
  linarith

/-- The actual forest boundary matrix has a genuine inverse in the physical
upper-half-plane boundary domain, independently of the forest condition. -/
theorem forestReferenceMatrix_isUnit (d : ℕ) (hd : 3 ≤ d) (root : V) (b : ℕ)
    (hdeg : ∀ v, G.degree v + (if v = root then b else 0) ≤ d)
    (m z : ℂ) (hz : 0 < z.im) (hmim : 0 ≤ m.im) :
    IsUnit (forestReferenceMatrix G d root b m z) :=
  boundaryMatrix_isUnit _ (normalizedAdjacency_isHermitian G d)
    _ (forestBoundaryCoefficient_nonnegative G d hd root b hdeg) m z hz hmim

/-- Verification of one finite inverse column only needs its matrix equation;
no inverse-entry formula is presupposed. -/
theorem inverse_column_of_mulVec (A : Matrix V V ℂ) (hA : IsUnit A) (f : V → ℂ) (root : V)
    (hAf : A *ᵥ f = Pi.single root 1) (v : V) : A⁻¹ v root = f v := by
  have hh := congrArg (fun x : V → ℂ => A⁻¹ *ᵥ x) hAf
  dsimp only at hh
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det _).mp hA),
    Matrix.one_mulVec] at hh
  have hv := congrFun hh v
  simpa [Matrix.mulVec_single] using hv.symm

/-- The exact cavity column on an arbitrary actual finite forest with one
root deficit. It equals m*(-m/sqrt(d-1))^distance on the root component. -/
theorem forestReference_cavity_column (hG : G.IsAcyclic) (d : ℕ) (hd : 3 ≤ d) (root : V)
    (hdeg : ∀ v, G.degree v + (if v = root then 1 else 0) ≤ d)
    (m z : ℂ) (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im) (hmim : 0 ≤ m.im) (v : V) :
    (forestReferenceMatrix G d root 1 m z)⁻¹ v root =
      forestKernelColumn G root m (-m * treeEdgeWeight d) v := by
  have hk : (d : ℂ) - 1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    have : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
    linarith
  have hscalar : m * (-z - ((d : ℂ) - 1) * m / ((d : ℂ) - 1)) = 1 := by
    rw [mul_div_cancel_left₀ m hk]
    linear_combination -hm
  have hcol := forestReferenceMatrix_column G hG d hd root 1 m z m hm
  simp only [Nat.cast_one] at hcol
  rw [hscalar] at hcol
  exact inverse_column_of_mulVec _ (forestReferenceMatrix_isUnit G d hd root 1 hdeg m z hz hmim)
    _ root hcol v

/-- The cavity root diagonal is exactly the physical semicircle root. -/
theorem forestReference_cavity_diagonal (hG : G.IsAcyclic) (d : ℕ) (hd : 3 ≤ d) (root : V)
    (hdeg : ∀ v, G.degree v + (if v = root then 1 else 0) ≤ d)
    (m z : ℂ) (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im) (hmim : 0 ≤ m.im) :
    (forestReferenceMatrix G d root 1 m z)⁻¹ root root = m := by
  rw [forestReference_cavity_column G hG d hd root hdeg m z hm hz hmim, forestKernelColumn_root]

/-- The exact zero-deficit column on any actual finite forest. -/
theorem forestReference_full_column (hG : G.IsAcyclic) (d : ℕ) (hd : 3 ≤ d) (root : V)
    (hdeg : ∀ v, G.degree v ≤ d) (m z : ℂ)
    (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im) (hmim : 0 ≤ m.im) (v : V) :
    (forestReferenceMatrix G d root 0 m z)⁻¹ v root =
      forestKernelColumn G root (kestenMcKayTransform d m z) (-m * treeEdgeWeight d) v := by
  have hkcast : (((d - 1 : ℕ) : ℂ)) = (d : ℂ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ d by omega), Nat.cast_one]
  have hden := kestenMcKay_denominator_ne_zero d m z hz hmim
  have hscalar : kestenMcKayTransform d m z * (-z - ((d : ℂ) - 0) * m / ((d : ℂ) - 1)) = 1 := by
    have heq : -z - ((d : ℂ) - 0) * m / ((d : ℂ) - 1) =
        -z - ((d : ℂ) / ((d - 1 : ℕ) : ℂ)) * m := by rw [hkcast]; ring
    rw [heq, kestenMcKayTransform]
    exact inv_mul_cancel₀ hden
  have hcol := forestReferenceMatrix_column G hG d hd root 0 m z (kestenMcKayTransform d m z) hm
  simp only [Nat.cast_zero] at hcol
  rw [hscalar] at hcol
  have hdeg' : ∀ v, G.degree v + (if v = root then 0 else 0) ≤ d := by simpa using hdeg
  exact inverse_column_of_mulVec _ (forestReferenceMatrix_isUnit G d hd root 0 hdeg' m z hz hmim)
    _ root hcol v

/-- The actual finite forest model diagonal is the Kesten--McKay transform. -/
theorem forestReference_full_diagonal (hG : G.IsAcyclic) (d : ℕ) (hd : 3 ≤ d) (root : V)
    (hdeg : ∀ v, G.degree v ≤ d) (m z : ℂ)
    (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im) (hmim : 0 ≤ m.im) :
    (forestReferenceMatrix G d root 0 m z)⁻¹ root root = kestenMcKayTransform d m z := by
  rw [forestReference_full_column G hG d hd root hdeg m z hm hz hmim, forestKernelColumn_root]

end FiniteForest
namespace RegularGraph
variable {N d : ℕ}

/-- The actual pair-neighborhood model has diagonal m_d whenever its finite
induced neighborhood is acyclic. This identifies the deterministic diagonal
used in the trace argument directly on the graph, with no tree isomorphism. -/
theorem P_diagonal_of_acyclic (g : RegularGraph N d) (hd : 3 ≤ d) (r : ℕ)
    (z m : ℂ) (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im) (hmim : 0 ≤ m.im)
    (i : Fin N) (hacyclic : (pairBallGraph g.graph i i r).IsAcyclic) :
    g.P r z m i i = kestenMcKayTransform d m z := by
  have hdeg : ∀ v : pairBallVertices g.graph i i r, (pairBallGraph g.graph i i r).degree v ≤ d := by
    intro v
    exact (induced_degree_le g.graph _ v).trans (g.regular v.val).le
  have hdiag := forestReference_full_diagonal (pairBallGraph g.graph i i r) hacyclic d hd
    (pairBallLeft g.graph i i r) hdeg m z hm hz hmim
  have hpoint : pairBallRight g.graph i i r = pairBallLeft g.graph i i r := Subtype.ext rfl
  simpa [P, boundaryGreen, forestReferenceMatrix, forestBoundaryCoefficient,
    pairBoundaryCoefficient, hpoint] using hdiag

/-- Semicircle-boundary specialization for the original local-law model. -/
theorem P_reference_diagonal_of_acyclic (g : RegularGraph N d) (hd : 3 ≤ d) (r : ℕ)
    (z : ℂ) (hz : 0 < z.im) (i : Fin N)
    (hacyclic : (pairBallGraph g.graph i i r).IsAcyclic) :
    g.P r z (semicircleRoot z) i i = graphKestenMcKayReference d z :=
  g.P_diagonal_of_acyclic hd r z (semicircleRoot z) (semicircleRoot_equation z) hz
    (semicircleRoot_im_pos hz).le i hacyclic

/-- Full actual pair-model reference kernel whenever the finite neighborhood
is acyclic; disconnected components have exactly zero cross entries. -/
theorem P_kernel_of_acyclic (g : RegularGraph N d) (hd : 3 ≤ d) (r : ℕ)
    (z m : ℂ) (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im) (hmim : 0 ≤ m.im)
    (i j : Fin N) (hacyclic : (pairBallGraph g.graph i j r).IsAcyclic) :
    g.P r z m i j = forestKernelColumn (pairBallGraph g.graph i j r)
      (pairBallRight g.graph i j r) (kestenMcKayTransform d m z) (-m * treeEdgeWeight d)
      (pairBallLeft g.graph i j r) := by
  have hdeg : ∀ v : pairBallVertices g.graph i j r, (pairBallGraph g.graph i j r).degree v ≤ d := by
    intro v
    exact (induced_degree_le g.graph _ v).trans (g.regular v.val).le
  have hcol := forestReference_full_column (pairBallGraph g.graph i j r) hacyclic d hd
    (pairBallRight g.graph i j r) hdeg m z hm hz hmim (pairBallLeft g.graph i j r)
  simpa [P, boundaryGreen, forestReferenceMatrix, forestBoundaryCoefficient,
    pairBoundaryCoefficient] using hcol

/-- At adjacent tree vertices the actual reference entry is m_d*(-m/sqrt(d-1)),
the identity used by the cavity-minor Schur formula in the exterior anchor. -/
theorem P_adjacent_of_acyclic (g : RegularGraph N d) (hd : 3 ≤ d) (r : ℕ)
    (z m : ℂ) (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im) (hmim : 0 ≤ m.im)
    (i j : Fin N) (hij : g.graph.Adj i j) (hacyclic : (pairBallGraph g.graph i j r).IsAcyclic) :
    g.P r z m i j = kestenMcKayTransform d m z * (-m * treeEdgeWeight d) := by
  rw [g.P_kernel_of_acyclic hd r z m hm hz hmim i j hacyclic]
  have hadj : (pairBallGraph g.graph i j r).Adj (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r) := hij
  have hr := hadj.reachable
  have hd' := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
  simp only [forestKernelColumn, if_pos hr, hd', pow_one]

end RegularGraph

end

end LocalLaw
