import LocalLaw.GraphModel
import LocalLaw.ExteriorResolvent

/-!
# Finite propagation and local moments

Powers of a matrix supported on graph edges (with diagonal entries allowed)
propagate at most one graph step per factor. These finite combinatorial facts
identify the first moments of an ambient graph and its finite pair-ball model.
No infinite tree or operator is used.
-/

open scoped BigOperators

namespace LocalLaw

section MatrixWalks
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Off-diagonal support on the graph; diagonal self-energy terms are allowed. -/
def GraphMatrixSupported (G : SimpleGraph V) (A : Matrix V V ℂ) : Prop :=
  ∀ i j, i ≠ j → ¬G.Adj i j → A i j = 0

/-- A nonzero matrix-power entry supplies an actual graph walk of at most
that many steps, even when the matrix has arbitrary diagonal entries. -/
theorem matrixPower_nonzero_walk (G : SimpleGraph V) (A : Matrix V V ℂ)
    (hs : GraphMatrixSupported G A) (n : ℕ) (i j : V) (hn : (A ^ n) i j ≠ 0) :
    ∃ p : G.Walk i j, p.length ≤ n := by
  classical
  induction n generalizing i with
  | zero =>
      have hij : i = j := by
        by_contra h
        simp [Matrix.one_apply, h] at hn
      subst j
      exact ⟨SimpleGraph.Walk.nil, le_rfl⟩
  | succ n ih =>
      rw [pow_succ', Matrix.mul_apply] at hn
      obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
      obtain ⟨hA, hp⟩ := mul_ne_zero_iff.mp hk
      obtain ⟨p, hlen⟩ := ih k hp
      by_cases hik : i = k
      · subst k
        exact ⟨p, hlen.trans (Nat.le_succ n)⟩
      · have hadj : G.Adj i k := by
          by_contra h
          exact hA (hs i k hik h)
        exact ⟨p.cons hadj, by simpa only [SimpleGraph.Walk.length_cons] using Nat.succ_le_succ hlen⟩

/-- Finite graph propagation: no matrix power can connect beyond its length. -/
theorem matrixPower_eq_zero_of_edist_gt (G : SimpleGraph V) (A : Matrix V V ℂ)
    (hs : GraphMatrixSupported G A) (n : ℕ) (i j : V) (hd : (n : ℕ∞) < G.edist i j) :
    (A ^ n) i j = 0 := by
  by_contra hn
  obtain ⟨p, hp⟩ := matrixPower_nonzero_walk G A hs n i j hn
  exact not_lt_of_ge ((SimpleGraph.edist_le p).trans (ENat.coe_le_coe.mpr hp)) hd

/-- A finite Duhamel principle at a single entry. It is proved by successively
replacing factors, so no commutation of A and B is assumed. -/
theorem matrix_power_entry_eq_of_mixed_zero (A B : Matrix V V ℂ) (n : ℕ) (i j : V)
    (hzero : ∀ l t : ℕ, l + t + 1 = n → (A ^ l * (A - B) * B ^ t) i j = 0) :
    (A ^ n) i j = (B ^ n) i j := by
  have hmix : ∀ l ≤ n, (A ^ l * B ^ (n - l)) i j = (B ^ n) i j := by
    intro l
    induction l with
    | zero => intro _; simp
    | succ l ih =>
        intro hl
        have hlprev : l ≤ n := by omega
        have hlt : l + (n - (l + 1)) + 1 = n := by omega
        have hz := hzero l (n - (l + 1)) hlt
        have hrel : A ^ l * (A - B) * B ^ (n - (l + 1)) =
            A ^ (l + 1) * B ^ (n - (l + 1)) - A ^ l * B ^ (n - l) := by
          rw [Matrix.mul_sub, Matrix.sub_mul, pow_succ]
          have hexp : n - l = (n - (l + 1)) + 1 := by omega
          rw [hexp, pow_succ', ← Matrix.mul_assoc]
        rw [hrel, Matrix.sub_apply] at hz
        exact (sub_eq_zero.mp hz).trans (ih hlprev)
  simpa using hmix n le_rfl

end MatrixWalks

noncomputable section
local instance powerLocalityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section MaskedMatrix
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Extend a principal submatrix back to V by zeros. -/
def maskedMatrix (A : Matrix V V ℂ) (S : Set V) : Matrix V V ℂ :=
  fun i j => if i ∈ S ∧ j ∈ S then A i j else 0

omit [DecidableEq V] in
private theorem sum_subtype_eq_sum_dite (S : Set V) (f : S → ℂ) :
    (∑ v : S, f v) = ∑ v : V, if h : v ∈ S then f ⟨v, h⟩ else 0 := by
  let g : V → ℂ := fun v => if h : v ∈ S then f ⟨v, h⟩ else 0
  have hs : (∑ v : S, g v.val) = ∑ v : S, f v := by
    apply Finset.sum_congr rfl
    intro v _
    simp only [g, dif_pos v.property]
  have hc : (∑ v : {v : V // v ∉ S}, g v.val) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    simp only [g, dif_neg v.property]
  have h := Fintype.sum_subtype_add_sum_subtype (fun v => v ∈ S) g
  rw [hs, hc, add_zero] at h
  exact h

/-- Powers of the zero-padded principal submatrix agree with its actual
subtype-indexed powers at every pair of retained vertices. -/
theorem maskedMatrix_power_entry (A : Matrix V V ℂ) (S : Set V) (n : ℕ) (i j : S) :
    (maskedMatrix A S ^ n) i.val j.val = (A.submatrix Subtype.val Subtype.val ^ n) i j := by
  induction n generalizing i with
  | zero => simp only [pow_zero, Matrix.one_apply, Subtype.ext_iff]
  | succ n ih =>
      rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply, sum_subtype_eq_sum_dite]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v ∈ S
      · rw [dif_pos hv]
        simp only [maskedMatrix, i.property, hv, and_self, if_true, Matrix.submatrix_apply]
        rw [ih ⟨v, hv⟩]
      · simp [maskedMatrix, hv]

omit [Fintype V] [DecidableEq V] in
theorem maskedMatrix_supported (G : SimpleGraph V) (A : Matrix V V ℂ)
    (hs : GraphMatrixSupported G A) (S : Set V) : GraphMatrixSupported G (maskedMatrix A S) := by
  intro i j hij hnot
  unfold maskedMatrix
  split_ifs <;> simp [hs i j hij hnot]

/-- If every short graph walk from i to j remains in S, zeroing rows and
columns outside S leaves the nth root-to-root moment unchanged. -/
theorem power_masked_eq_of_walks_stay (G : SimpleGraph V) (A : Matrix V V ℂ)
    (hs : GraphMatrixSupported G A) (S : Set V) (n : ℕ) (i j : V)
    (hstay : ∀ p : G.Walk i j, p.length ≤ n → ∀ v ∈ p.support, v ∈ S) :
    (A ^ n) i j = (maskedMatrix A S ^ n) i j := by
  apply matrix_power_entry_eq_of_mixed_zero
  intro l t hlength
  simp only [Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro y _
  apply Finset.sum_eq_zero
  intro x _
  by_cases hleft : (A ^ l) i x = 0
  · simp [hleft]
  by_cases hright : (maskedMatrix A S ^ t) y j = 0
  · simp [hright]
  by_cases hdelta : (A - maskedMatrix A S) x y = 0
  · simp [hdelta]
  have houtside : ¬(x ∈ S ∧ y ∈ S) := by
    intro hxy
    apply hdelta
    simp [Matrix.sub_apply, maskedMatrix, hxy]
  have hAxy : A x y ≠ 0 := by
    simpa only [Matrix.sub_apply, maskedMatrix, if_neg houtside, sub_zero] using hdelta
  obtain ⟨p, hp⟩ := matrixPower_nonzero_walk G A hs l i x hleft
  obtain ⟨q, hq⟩ := matrixPower_nonzero_walk G (maskedMatrix A S)
    (maskedMatrix_supported G A hs S) t y j hright
  have hcentral : ∃ w : G.Walk x y, w.length ≤ 1 := by
    by_cases hxy : x = y
    · subst y
      exact ⟨SimpleGraph.Walk.nil, by simp⟩
    · have hadj : G.Adj x y := by
        by_contra hnot
        exact hAxy (hs x y hxy hnot)
      exact ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, by simp⟩
  obtain ⟨w, hw⟩ := hcentral
  let full := p.append (w.append q)
  have hfull : full.length ≤ n := by
    simp only [full, SimpleGraph.Walk.length_append]
    omega
  have hxS : x ∈ S := hstay full hfull x (by
    rw [SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl p.end_mem_support)
  have hyS : y ∈ S := hstay full hfull y (by
    simp only [full, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr (Or.inr q.start_mem_support))
  exact False.elim (houtside ⟨hxS, hyS⟩)

omit [Fintype V] in
/-- Every vertex on a walk of length at most 2r+1 lies in one of the two
radius-r endpoint balls. This is the finite speed of graph propagation. -/
theorem walk_support_pairBall (G : SimpleGraph V) (i j : V) (r : ℕ)
    (p : G.Walk i j) (hlen : p.length ≤ 2 * r + 1) :
    ∀ v ∈ p.support, v ∈ pairBallVertices G i j r := by
  intro v hv
  let left := p.takeUntil v hv
  let right := p.dropUntil v hv
  have hsum : left.length + right.length = p.length := by
    rw [← SimpleGraph.Walk.length_append]
    exact congrArg SimpleGraph.Walk.length (p.take_spec hv)
  by_cases hl : left.length ≤ r
  · exact Or.inl ((SimpleGraph.edist_le left).trans (ENat.coe_le_coe.mpr hl))
  · have hr : right.length ≤ r := by omega
    exact Or.inr ((SimpleGraph.edist_le right.reverse).trans (by
      simpa only [SimpleGraph.Walk.length_reverse] using ENat.coe_le_coe.mpr hr))

/-- The finite pair-ball principal matrix has exactly the ambient moments
through order 2r+1 at the two distinguished endpoints. -/
theorem matrix_power_pairBall_eq (G : SimpleGraph V) (A : Matrix V V ℂ)
    (hs : GraphMatrixSupported G A) (i j : V) (r n : ℕ) (hn : n ≤ 2 * r + 1) :
    (A ^ n) i j =
      (A.submatrix Subtype.val Subtype.val ^ n) (pairBallLeft G i j r) (pairBallRight G i j r) := by
  calc
    (A ^ n) i j = (maskedMatrix A (pairBallVertices G i j r) ^ n) i j := by
      apply power_masked_eq_of_walks_stay G A hs
      intro p hp
      exact walk_support_pairBall G i j r p (hp.trans hn)
    _ = _ := maskedMatrix_power_entry A _ n (pairBallLeft G i j r) (pairBallRight G i j r)

omit [Fintype V] [DecidableEq V] in
/-- Restricting normalized adjacency gives the normalized adjacency of the
actual induced graph, with the same ambient normalization d. -/
theorem normalizedAdjacency_induce_eq_submatrix (G : SimpleGraph V) (d : ℕ) (S : Set V) :
    normalizedAdjacency (G.induce S) d = (normalizedAdjacency G d).submatrix Subtype.val Subtype.val := by
  ext i j
  simp [normalizedAdjacency, Matrix.smul_apply, SimpleGraph.adjMatrix_apply,
    SimpleGraph.induce, SimpleGraph.comap_adj]

/-- Actual normalized graph moments agree with the actual finite induced
pair-neighborhood matrix, rather than with an abstract postulated model. -/
theorem normalizedAdjacency_pairBall_power_eq (G : SimpleGraph V) (d : ℕ)
    (i j : V) (r n : ℕ) (hn : n ≤ 2 * r + 1) :
    (normalizedAdjacency G d ^ n) i j =
      (normalizedAdjacency (pairBallGraph G i j r) d ^ n)
        (pairBallLeft G i j r) (pairBallRight G i j r) := by
  unfold pairBallGraph
  rw [normalizedAdjacency_induce_eq_submatrix]
  apply matrix_power_pairBall_eq G _ _ i j r n hn
  intro x y _ hnot
  exact normalizedAdjacency_eq_zero_of_not_adj G d x y hnot

omit [Fintype V] in
/-- Diagonal perturbations do not change off-diagonal graph support. -/
theorem graphMatrixSupported_sub_diagonal (G : SimpleGraph V) (A : Matrix V V ℂ)
    (hs : GraphMatrixSupported G A) (b : V → ℂ) :
    GraphMatrixSupported G (A - Matrix.diagonal b) := by
  intro i j hij hnot
  simp only [Matrix.sub_apply, Matrix.diagonal_apply_ne b hij, sub_zero]
  exact hs i j hij hnot

/-- A diagonal boundary perturbation at distance at least r from both roots
cannot affect root-to-root powers through order 2r: reaching it, using its
diagonal, and returning takes at least 2r+1 factors. -/
theorem diagonal_boundary_power_eq (G : SimpleGraph V) (A : Matrix V V ℂ)
    (hs : GraphMatrixSupported G A) (b : V → ℂ) (i j : V) (r n : ℕ)
    (hb : ∀ v, b v ≠ 0 → (r : ℕ∞) ≤ G.edist i v ∧ (r : ℕ∞) ≤ G.edist v j)
    (hn : n ≤ 2 * r) :
    (A ^ n) i j = ((A - Matrix.diagonal b) ^ n) i j := by
  apply matrix_power_entry_eq_of_mixed_zero
  intro l t hlength
  rw [show A - (A - Matrix.diagonal b) = Matrix.diagonal b by abel]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  apply Finset.sum_eq_zero
  intro v _
  by_cases hl : (A ^ l) i v = 0
  · simp [hl]
  by_cases hr : ((A - Matrix.diagonal b) ^ t) v j = 0
  · simp [hr]
  by_cases hzero : b v = 0
  · simp [hzero]
  obtain ⟨p, hp⟩ := matrixPower_nonzero_walk G A hs l i v hl
  obtain ⟨q, hq⟩ := matrixPower_nonzero_walk G (A - Matrix.diagonal b)
    (graphMatrixSupported_sub_diagonal G A hs b) t v j hr
  obtain ⟨hdleft, hdright⟩ := hb v hzero
  have hrl : r ≤ l := (ENat.coe_le_coe.mp (hdleft.trans (SimpleGraph.edist_le p))).trans hp
  have hrt : r ≤ t := (ENat.coe_le_coe.mp (hdright.trans (SimpleGraph.edist_le q))).trans hq
  omega

omit [DecidableEq V] in
/-- If every ambient neighbor remains in S, deleting the complement does not
change the vertex degree. The proof is an explicit neighbor-set equivalence. -/
theorem induced_degree_eq_of_neighbors_inside (G : SimpleGraph V) (S : Set V) (v : S)
    (hinside : ∀ u, G.Adj v.val u → u ∈ S) : (G.induce S).degree v = G.degree v.val := by
  let e : (G.induce S).neighborSet v ≃ G.neighborSet v.val :=
    { toFun := fun u => ⟨u.val.val, u.property⟩
      invFun := fun u => ⟨⟨u.val, hinside u.val u.property⟩, u.property⟩
      left_inv := fun u => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun u => by apply Subtype.ext; rfl }
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using Fintype.card_congr e

omit [DecidableEq V] in
/-- A degree deficit witnesses an actual edge leaving the induced region. -/
theorem neighbor_outside_of_induced_degree_ne (G : SimpleGraph V) (S : Set V) (v : S)
    (hdeg : (G.induce S).degree v ≠ G.degree v.val) :
    ∃ u, G.Adj v.val u ∧ u ∉ S := by
  by_contra hnone
  push_neg at hnone
  exact hdeg (induced_degree_eq_of_neighbors_inside G S v hnone)

omit [Fintype V] [DecidableEq V] in
/-- Leaving an induced pair ball forces the incident inside vertex to have
distance at least r from each endpoint. -/
theorem pairBall_boundary_distance (G : SimpleGraph V) (i j v u : V) (r : ℕ)
    (hvu : G.Adj v u) (hu : u ∉ pairBallVertices G i j r) :
    (r : ℕ∞) ≤ G.edist i v ∧ (r : ℕ∞) ≤ G.edist j v := by
  constructor
  · apply graph_edist_lower_of_walk_lengths G i v r
    intro p
    by_contra hlen
    have hshort : (p.concat hvu).length ≤ r := by
      simp only [SimpleGraph.Walk.length_concat]
      omega
    exact hu (Or.inl ((SimpleGraph.edist_le (p.concat hvu)).trans (ENat.coe_le_coe.mpr hshort)))
  · apply graph_edist_lower_of_walk_lengths G j v r
    intro p
    by_contra hlen
    have hshort : (p.concat hvu).length ≤ r := by
      simp only [SimpleGraph.Walk.length_concat]
      omega
    exact hu (Or.inr ((SimpleGraph.edist_le (p.concat hvu)).trans (ENat.coe_le_coe.mpr hshort)))

omit [Fintype V] [DecidableEq V] in
/-- Distances in an induced graph are at least ambient graph distances. -/
theorem induced_edist_lower (G : SimpleGraph V) (S : Set V) (i j : S) (r : ℕ)
    (hd : (r : ℕ∞) ≤ G.edist i.val j.val) : (r : ℕ∞) ≤ (G.induce S).edist i j := by
  apply graph_edist_lower_of_walk_lengths (G.induce S) i j r
  intro p
  have hmap := SimpleGraph.edist_le (p.map (SimpleGraph.Embedding.induce S).toHom)
  have hh := ENat.coe_le_coe.mp (hd.trans hmap)
  simpa only [SimpleGraph.Walk.length_map] using hh

/-- Adding a diagonal to a zero-diagonal matrix adds exactly the magnitude of
that diagonal entry to each row absolute sum. -/
theorem row_sum_sub_diagonal (A : Matrix V V ℂ) (hdiag : ∀ i, A i i = 0)
    (b : V → ℂ) (i : V) :
    (∑ k, ‖(A - Matrix.diagonal b) i k‖) = (∑ k, ‖A i k‖) + ‖b i‖ := by
  have hoff : (∑ k ∈ Finset.univ.erase i, ‖(A - Matrix.diagonal b) i k‖) =
      ∑ k ∈ Finset.univ.erase i, ‖A i k‖ := by
    apply Finset.sum_congr rfl
    intro k hk
    have hki := (Finset.mem_erase.mp hk).1
    simp only [Matrix.sub_apply, Matrix.diagonal_apply_ne b hki.symm, sub_zero]
  have hA := Finset.sum_erase_add Finset.univ (fun k => ‖A i k‖) (Finset.mem_univ i)
  have hB := Finset.sum_erase_add Finset.univ
    (fun k => ‖(A - Matrix.diagonal b) i k‖) (Finset.mem_univ i)
  simp only [hdiag i, norm_zero, add_zero] at hA
  rw [← hB, hoff, hA]
  simp only [Matrix.sub_apply, Matrix.diagonal_apply_eq, hdiag i, zero_sub, norm_neg]

end MaskedMatrix
namespace RegularGraph
variable {N d : ℕ}

/-- A nonzero actual missing-degree coefficient is supported on the outer
pair boundary, at least r graph steps from both distinguished endpoints. -/
theorem pairBoundaryCoefficient_distance (g : RegularGraph N d) (i j : Fin N) (r : ℕ)
    (v : pairBallVertices g.graph i j r) (hc : g.pairBoundaryCoefficient i j r v ≠ 0) :
    (r : ℕ∞) ≤ (pairBallGraph g.graph i j r).edist (pairBallLeft g.graph i j r) v ∧
      (r : ℕ∞) ≤ (pairBallGraph g.graph i j r).edist v (pairBallRight g.graph i j r) := by
  have hdeg : (g.graph.induce (pairBallVertices g.graph i j r)).degree v ≠ g.graph.degree v.val := by
    intro heq
    apply hc
    unfold pairBoundaryCoefficient
    change ((d : ℝ) - ((g.graph.induce (pairBallVertices g.graph i j r)).degree v : ℝ)) /
      ((d : ℝ) - 1) = 0
    rw [heq, g.regular v.val]
    simp
  obtain ⟨u, hvu, hu⟩ := neighbor_outside_of_induced_degree_ne g.graph _ v hdeg
  obtain ⟨hi, hj⟩ := pairBall_boundary_distance g.graph i j v.val u r hvu hu
  constructor
  · exact induced_edist_lower g.graph _ (pairBallLeft g.graph i j r) v r hi
  · apply induced_edist_lower g.graph _ v (pairBallRight g.graph i j r) r
    change (r : ℕ∞) ≤ g.graph.edist v.val j
    rw [SimpleGraph.edist_comm]
    exact hj

/-- The adjacency-like finite pair model before subtraction of zI. -/
def pairExtensionMatrix (g : RegularGraph N d) (r : ℕ) (w : ℂ) (i j : Fin N) :
    Matrix (pairBallVertices g.graph i j r) (pairBallVertices g.graph i j r) ℂ :=
  normalizedAdjacency (pairBallGraph g.graph i j r) d -
    w • Matrix.diagonal (fun v => (g.pairBoundaryCoefficient i j r v : ℂ))

/-- Actual finite-model moments agree with the actual ambient graph moments
through order 2r, for every complex boundary weight w. -/
theorem pairExtension_power_eq (g : RegularGraph N d) (r : ℕ) (w : ℂ)
    (i j : Fin N) (n : ℕ) (hn : n ≤ 2 * r) :
    (g.H ^ n) i j = (g.pairExtensionMatrix r w i j ^ n)
      (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r) := by
  calc
    (g.H ^ n) i j = (normalizedAdjacency (pairBallGraph g.graph i j r) d ^ n)
        (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r) :=
      normalizedAdjacency_pairBall_power_eq g.graph d i j r n (by omega)
    _ = _ := by
      unfold pairExtensionMatrix
      rw [← Matrix.diagonal_smul]
      apply diagonal_boundary_power_eq (pairBallGraph g.graph i j r) _ _ _
        (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r) r n _ hn
      · intro x y _ hnot
        exact normalizedAdjacency_eq_zero_of_not_adj _ d x y hnot
      · intro v hv
        apply g.pairBoundaryCoefficient_distance i j r v
        intro hc
        apply hv
        simp [hc]

/-- The paper's finite extension Green entry is the genuine resolvent of the
adjacency-like pairExtensionMatrix; only additive rearrangement is involved. -/
theorem P_eq_green_pairExtension (g : RegularGraph N d) (r : ℕ) (z w : ℂ) (i j : Fin N) :
    g.P r z w i j = green (g.pairExtensionMatrix r w i j) z
      (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r) := by
  unfold P boundaryGreen green pairExtensionMatrix boundaryMatrix spectralMatrix
  have heq : normalizedAdjacency (pairBallGraph g.graph i j r) d - z • 1 -
        w • Matrix.diagonal (fun v => (g.pairBoundaryCoefficient i j r v : ℂ)) =
      (normalizedAdjacency (pairBallGraph g.graph i j r) d -
        w • Matrix.diagonal (fun v => (g.pairBoundaryCoefficient i j r v : ℂ))) - z • 1 := by abel
  rw [heq]

/-- The boundary model has the same row-sum cap as the original normalized
regular graph when |w|≤1. Each missing edge costs 1/(d-1) in diagonal mass,
which is no larger than its removed adjacency mass 1/sqrt(d-1). -/
theorem pairExtension_row_sum_bound (g : RegularGraph N d) (hd : 3 ≤ d)
    (r : ℕ) (w : ℂ) (hw : ‖w‖ ≤ 1) (i j : Fin N)
    (v : pairBallVertices g.graph i j r) :
    (∑ u, ‖g.pairExtensionMatrix r w i j v u‖) ≤
      (d : ℝ) / Real.sqrt ((d : ℝ) - 1) := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hkpos : 0 < (d : ℝ) - 1 := by linarith
  have hspos : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr hkpos
  have hsone : 1 ≤ Real.sqrt ((d : ℝ) - 1) := by
    have hh := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ d - 1 by linarith)
    simpa only [Real.sqrt_one] using hh
  have hks : Real.sqrt ((d : ℝ) - 1) ≤ (d : ℝ) - 1 := by
    nlinarith [Real.sq_sqrt hkpos.le]
  have hdegNat : (pairBallGraph g.graph i j r).degree v ≤ d :=
    (induced_degree_le g.graph _ v).trans (g.regular v.val).le
  have hdeg : ((pairBallGraph g.graph i j r).degree v : ℝ) ≤ d := Nat.cast_le.mpr hdegNat
  have hc : 0 ≤ g.pairBoundaryCoefficient i j r v := g.pairBoundaryCoefficient_nonnegative hd i j r v
  have hnorm : ‖w * (g.pairBoundaryCoefficient i j r v : ℂ)‖ ≤ g.pairBoundaryCoefficient i j r v := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    nlinarith [mul_le_mul_of_nonneg_right hw hc]
  unfold pairExtensionMatrix
  rw [← Matrix.diagonal_smul, row_sum_sub_diagonal _ (normalizedAdjacency_zero_diagonal _ d),
    normalizedAdjacency_row_sum]
  change ((pairBallGraph g.graph i j r).degree v : ℝ) / Real.sqrt ((d : ℝ) - 1) +
    ‖w * (g.pairBoundaryCoefficient i j r v : ℂ)‖ ≤ _
  calc
    _ ≤ ((pairBallGraph g.graph i j r).degree v : ℝ) / Real.sqrt ((d : ℝ) - 1) +
        g.pairBoundaryCoefficient i j r v := add_le_add_left hnorm _
    _ ≤ ((pairBallGraph g.graph i j r).degree v : ℝ) / Real.sqrt ((d : ℝ) - 1) +
        ((d : ℝ) - (pairBallGraph g.graph i j r).degree v) / Real.sqrt ((d : ℝ) - 1) := by
      apply add_le_add_left
      unfold pairBoundaryCoefficient
      exact div_le_div_of_nonneg_left (sub_nonneg.mpr hdeg) hspos hks
    _ = (d : ℝ) / Real.sqrt ((d : ℝ) - 1) := by rw [← add_div]; congr 1; ring

end RegularGraph

end

end LocalLaw
