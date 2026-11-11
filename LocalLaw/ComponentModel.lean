import LocalLaw.FiniteThresholdStability

/-!
# Actual component restriction of deficient extension models

An isolated vertex set gives an actual block of the extension matrix. Its
inverse is the corresponding full inverse block, and entries between different
components vanish. No inverse support or block identity is assumed.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance componentModelDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Matrices
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem inverse_zero_across_cut (A : Matrix V V ℂ) (hA : IsUnit A) (S : Set V)
    (hcut : ∀ i ∈ S, ∀ j ∉ S, A i j = 0)
    (i : V) (hi : i ∈ S) (j : V) (hj : j ∉ S) : A⁻¹ i j = 0 := by
  classical
  let b : V → ℕ := fun v => if v ∈ S then 1 else 0
  letI : Invertible A := Classical.choice hA.nonempty_invertible
  have htri : Matrix.BlockTriangular A b := by
    intro u v huv
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
    · simp [b, hu, hv] at huv
    · exact hcut u hu v hv
    · simp [b, hu, hv] at huv
    · simp [b, hu, hv] at huv
  exact Matrix.blockTriangular_inv_of_blockTriangular htri (by simp [b, hi, hj])

theorem inverse_principal_isolated (A : Matrix V V ℂ) (hA : IsUnit A) (S : Set V)
    (hcut : ∀ i ∈ S, ∀ j ∉ S, A i j = 0) :
    (A.submatrix (Subtype.val : S → V) (Subtype.val : S → V))⁻¹ =
      (A⁻¹).submatrix (Subtype.val : S → V) (Subtype.val : S → V) := by
  classical
  apply Matrix.inv_eq_right_inv
  ext i j
  have hfull := congrFun (congrFun (Matrix.mul_nonsing_inv A
    ((Matrix.isUnit_iff_isUnit_det A).mp hA)) i.val) j.val
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun v : V => v ∈ S)
    (fun v => A i.val v * A⁻¹ v j.val)
  have hzero : (∑ v : {v : V // v ∉ S}, A i.val v.val * A⁻¹ v.val j.val) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    rw [hcut i.val i.property v.val v.property, zero_mul]
  rw [hzero, add_zero] at hsplit
  simpa only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply,
    Subtype.ext_iff] using hsplit.trans (by simpa only [Matrix.mul_apply] using hfull)

end Matrices

section GraphDistances
variable {V : Type*} (G : SimpleGraph V)

theorem walk_restrict_isolated (S : Set V)
    (hcut : ∀ i ∈ S, ∀ j ∉ S, ¬G.Adj i j)
    {a b : V} (p : G.Walk a b) (ha : a ∈ S) (hb : b ∈ S) :
    ∃ q : (G.induce S).Walk ⟨a, ha⟩ ⟨b, hb⟩, q.length = p.length := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons a c b hac p ih =>
    have hc : c ∈ S := by
      by_contra hn
      exact hcut a ha c hn hac
    obtain ⟨q, hq⟩ := ih hc hb
    have hadj : (G.induce S).Adj ⟨a, ha⟩ ⟨c, hc⟩ := hac
    refine ⟨q.cons hadj, ?_⟩
    simp only [SimpleGraph.Walk.length_cons, hq]

/-- A literal isolated induced subgraph preserves intrinsic distance,
including the natural-distance convention at unreachable pairs. -/
theorem isolated_induce_distance (S : Set V)
    (hcut : ∀ i ∈ S, ∀ j ∉ S, ¬G.Adj i j) (a b : S) :
    (G.induce S).dist a b = G.dist a.val b.val := by
  apply Nat.le_antisymm
  · by_cases hreach : G.Reachable a.val b.val
    · obtain ⟨p, _, hp⟩ := hreach.exists_path_of_dist
      obtain ⟨q, hq⟩ := walk_restrict_isolated G S hcut p a.property b.property
      exact (SimpleGraph.dist_le q).trans_eq (hq.trans hp)
    · have hnot : ¬(G.induce S).Reachable a b := by
        rintro ⟨p⟩
        exact hreach ⟨p.map (SimpleGraph.Embedding.induce S).toHom⟩
      rw [SimpleGraph.dist_eq_zero_of_not_reachable hnot]
      exact Nat.zero_le _
  · by_cases hreach : (G.induce S).Reachable a b
    · obtain ⟨p, _, hp⟩ := hreach.exists_path_of_dist
      exact (SimpleGraph.dist_le (p.map (SimpleGraph.Embedding.induce S).toHom)).trans_eq
        (by simpa only [SimpleGraph.Walk.length_map] using hp)
    · rw [SimpleGraph.dist_eq_zero_of_not_reachable hreach]
      by_cases hamb : G.Reachable a.val b.val
      · obtain ⟨p⟩ := hamb
        obtain ⟨q, _⟩ := walk_restrict_isolated G S hcut p a.property b.property
        exact False.elim (hreach ⟨q⟩)
      · rw [SimpleGraph.dist_eq_zero_of_not_reachable hamb]

end GraphDistances

namespace DeficientGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

theorem extensionMatrix_zero_across_cut (g : DeficientGraph V d) (S : Set V)
    (hcut : ∀ i ∈ S, ∀ j ∉ S, ¬g.graph.Adj i j)
    (w z : ℂ) (i : V) (hi : i ∈ S) (j : V) (hj : j ∉ S) :
    g.extensionMatrix w z i j = 0 := by
  classical
  have hij : i ≠ j := by intro h; exact hj (h ▸ hi)
  simp [extensionMatrix, boundaryMatrix, spectralMatrix, H, normalizedAdjacency,
    SimpleGraph.adjMatrix_apply, hcut i hi j hj, boundaryDiagonal, Matrix.diagonal_apply,
    Matrix.one_apply, hij]

theorem extensionGreen_zero_across_cut (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (hcut : ∀ i ∈ S, ∀ j ∉ S, ¬g.graph.Adj i j)
    (w z : ℂ) (hz : 0 < z.im) (hw : 0 ≤ w.im)
    (i : V) (hi : i ∈ S) (j : V) (hj : j ∉ S) :
    g.extensionGreen w z i j = 0 :=
  inverse_zero_across_cut (g.extensionMatrix w z) (g.extensionMatrix_isUnit hd w z hz hw)
    S (g.extensionMatrix_zero_across_cut S hcut w z) i hi j hj

theorem restrict_boundaryCoefficient_of_isolated (g : DeficientGraph V d) (S : Set V)
    (hcut : ∀ i ∈ S, ∀ j ∉ S, ¬g.graph.Adj i j) (v : S) :
    (g.restrict S).boundaryCoefficient v = g.boundaryCoefficient v.val := by
  have hdegree : (g.graph.induce S).degree v = g.graph.degree v.val :=
    SimpleGraph.degree_induce_of_neighborSet_subset (by
      intro j hj
      by_contra hnot
      exact hcut v.val v.property j hnot hj)
  change ((d : ℝ) - (g.deficit v.val : ℝ) - ((g.graph.induce S).degree v : ℝ)) /
      ((d : ℝ) - 1) = ((d : ℝ) - (g.deficit v.val : ℝ) - (g.graph.degree v.val : ℝ)) /
      ((d : ℝ) - 1)
  rw [hdegree]

theorem restrict_boundaryDiagonal_of_isolated (g : DeficientGraph V d) (S : Set V)
    (hcut : ∀ i ∈ S, ∀ j ∉ S, ¬g.graph.Adj i j) :
    (g.restrict S).boundaryDiagonal = g.boundaryDiagonal.submatrix
      (Subtype.val : S → V) (Subtype.val : S → V) := by
  ext i j
  simp only [boundaryDiagonal, Matrix.submatrix_apply, Matrix.diagonal_apply,
    g.restrict_boundaryCoefficient_of_isolated S hcut]
  by_cases h : i = j
  · subst j; simp
  · have hval : i.val ≠ j.val := fun heq => h (Subtype.ext heq)
    simp [h, hval]

theorem restrict_extensionMatrix_of_isolated (g : DeficientGraph V d) (S : Set V)
    (hcut : ∀ i ∈ S, ∀ j ∉ S, ¬g.graph.Adj i j) (w z : ℂ) :
    (g.restrict S).extensionMatrix w z = (g.extensionMatrix w z).submatrix
      (Subtype.val : S → V) (Subtype.val : S → V) := by
  change spectralMatrix (g.restrict S).H z - w • (g.restrict S).boundaryDiagonal =
    (spectralMatrix g.H z - w • g.boundaryDiagonal).submatrix
      (Subtype.val : S → V) (Subtype.val : S → V)
  rw [g.H_restrict S, g.restrict_boundaryDiagonal_of_isolated S hcut,
    spectralMatrix_principal g.H z (Subtype.val : S → V) Subtype.val_injective]
  rfl

/-- An actual isolated induced model has exactly the full inverse block. -/
theorem restrict_extensionGreen_of_isolated (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (hcut : ∀ i ∈ S, ∀ j ∉ S, ¬g.graph.Adj i j)
    (w z : ℂ) (hz : 0 < z.im) (hw : 0 ≤ w.im) :
    (g.restrict S).extensionGreen w z = (g.extensionGreen w z).submatrix
      (Subtype.val : S → V) (Subtype.val : S → V) := by
  change ((g.restrict S).extensionMatrix w z)⁻¹ = _
  rw [g.restrict_extensionMatrix_of_isolated S hcut w z]
  exact inverse_principal_isolated _ (g.extensionMatrix_isUnit hd w z hz hw) S
    (g.extensionMatrix_zero_across_cut S hcut w z)

omit [DecidableEq V] in
theorem component_cut (g : DeficientGraph V d) (c : g.graph.ConnectedComponent) :
    ∀ i ∈ c.supp, ∀ j ∉ c.supp, ¬g.graph.Adj i j := by
  intro i hi j hj hadj
  exact hj ((c.mem_supp_congr_adj hadj).mp hi)

/-- Literal connected-component models inherit exactly the same boundary
diagonal, so their physical Green matrices are full inverse blocks. -/
theorem component_extensionGreen (g : DeficientGraph V d) (hd : 3 ≤ d)
    (c : g.graph.ConnectedComponent) (S : Set V) (hS : S = c.supp)
    (w z : ℂ) (hz : 0 < z.im) (hw : 0 ≤ w.im) :
    (g.restrict S).extensionGreen w z = (g.extensionGreen w z).submatrix
      (Subtype.val : S → V) (Subtype.val : S → V) := by
  apply g.restrict_extensionGreen_of_isolated hd S _ w z hz hw
  simpa only [hS] using g.component_cut c

end DeficientGraph

section FiniteBoundary
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}
namespace DeficientGraph

/-- A connected component can be estimated on its own and transferred to
the actual full matrix. The only component inputs are its literal complexity
budget and connectedness, not inverse support or reference estimates. -/
theorem isolated_finiteOmega_boundary_uniform_stability (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (hcut : ∀ i ∈ S, ∀ j ∉ S, ¬g.graph.Adj i j)
    (hconn : (g.restrict S).graph.Connected)
    (hbudget : (∑ v, (g.restrict S).deficit v) + graphExcess (g.restrict S).graph ≤ finiteOmega d)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * ((R : ℝ) + 1) ≤ 1 / 2)
    (i j : S) :
    ‖g.extensionGreen q z i.val j.val - g.extensionGreen (semicircleRoot z) z i.val j.val‖ ≤
      (8 * finiteReferenceConstant d ^ 2 * coreConvolutionConstant (finiteOmega d)) *
        ‖q - semicircleRoot z‖ := by
  have hdiam : ∀ a b, (g.restrict S).graph.dist a b ≤ R := by
    intro a b
    change (g.graph.induce S).dist a b ≤ R
    rw [isolated_induce_distance g.graph S hcut a b]
    exact hR a.val b.val
  have h := (g.restrict S).finiteOmega_boundary_uniform_stability hd hconn hbudget z q hz hq
    R hdiam small i j
  rw [g.restrict_extensionGreen_of_isolated hd S hcut q z hz hq,
    g.restrict_extensionGreen_of_isolated hd S hcut (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le] at h
  exact h

end DeficientGraph
end FiniteBoundary
end LocalLaw
