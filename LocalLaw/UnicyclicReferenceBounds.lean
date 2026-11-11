import LocalLaw.UnicyclicPruning
import LocalLaw.CycleDiagonalStability

/-!
# Actual unicyclic finite reference bounds

Connected excess-one graphs are reduced by genuine leaf Schur complements
until their actual two-regular cycle core is reached. Entry decay and the
relative diagonal correction remain uniform through all attached trees.
-/

open scoped BigOperators Matrix
set_option maxHeartbeats 1800000

namespace LocalLaw
universe u
noncomputable section
local instance unicyclicBoundsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section IsoHelpers
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- A genuine graph isomorphism preserves finite connected-graph distance. -/
theorem graphIso_distance (e : H ≃g G) (hG : G.Connected) (i j : W) :
    H.dist i j = G.dist (e i) (e j) := by
  have hH := e.connected_iff.mpr hG
  apply le_antisymm
  · obtain ⟨p, _, hlen⟩ := (hG.preconnected (e i) (e j)).exists_path_of_dist
    have hh := SimpleGraph.dist_le (p.map e.symm.toHom)
    change H.dist (e.symm (e i)) (e.symm (e j)) ≤ (p.map e.symm.toHom).length at hh
    simpa only [e.symm_apply_apply, SimpleGraph.Walk.length_map, hlen] using hh
  · obtain ⟨p, _, hlen⟩ := (hH.preconnected i j).exists_path_of_dist
    have hh := SimpleGraph.dist_le (p.map e.toHom)
    simpa only [SimpleGraph.Walk.length_map, hlen] using hh

end IsoHelpers

section FiniteGraph
variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- Reindexing an actual two-regular full reference operator gives the
literal cycle operator, including its actual missing-degree diagonal. -/
theorem two_regular_reference_reindex (hdeg : ∀ v, G.degree v = 2)
    (n d : ℕ) (e : SimpleGraph.cycleGraph (n + 3) ≃g G) (m z : ℂ) :
    (fullReferenceMatrix G d m z).submatrix e e = cycleReferenceMatrix n d m z := by
  ext i j
  simp only [fullReferenceMatrix, cycleReferenceMatrix, boundaryMatrix, spectralMatrix,
    treeBoundaryDiagonal, treeBoundaryWeight, hdeg, Matrix.submatrix_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply, Matrix.one_apply,
    normalizedAdjacency, SimpleGraph.adjMatrix_apply]
  rw [show G.Adj (e i) (e j) ↔ (SimpleGraph.cycleGraph (n + 3)).Adj i j from e.map_rel_iff']
  simp only [e.injective.eq_iff, Nat.cast_ofNat]

/-- The exact inverse also reindexes, with no assumed kernel formula on the
abstract two-regular graph. -/
theorem two_regular_reference_inverse_reindex (hdeg : ∀ v, G.degree v = 2)
    (n d : ℕ) (e : SimpleGraph.cycleGraph (n + 3) ≃g G) (m z : ℂ) (i j : Fin (n + 3)) :
    fullTreeGreen G d m z (e i) (e j) = (cycleReferenceMatrix n d m z)⁻¹ i j := by
  have hh := Matrix.inv_submatrix_equiv (fullReferenceMatrix G d m z) e.toEquiv e.toEquiv
  change ((fullReferenceMatrix G d m z).submatrix e e)⁻¹ =
    (fullReferenceMatrix G d m z)⁻¹.submatrix e e at hh
  rw [two_regular_reference_reindex G hdeg n d e m z] at hh
  exact (congrArg (fun M : Matrix (Fin (n + 3)) (Fin (n + 3)) ℂ => M i j) hh).symm

/-- Uniform reference conclusions on the actual two-regular core. -/
theorem two_regular_reference_bounds (hconn : G.Connected) (hdeg : ∀ v, G.degree v = 2)
    (d : ℕ) (hd : 3 ≤ d) (z : ℂ) (hz : 0 < z.im) :
    (∀ i j, ‖fullTreeGreen G d (semicircleRoot z) z i j‖ ≤
      8 * ‖-semicircleRoot z * treeEdgeWeight d‖ ^ G.dist i j) ∧
    (∀ i, ‖fullTreeGreen G d (semicircleRoot z) z i i -
      kestenMcKayTransform d (semicircleRoot z) z‖ ≤
        (3 / 2 : ℝ) * ‖kestenMcKayTransform d (semicircleRoot z) z‖) ∧
    (∀ i, ‖kestenMcKayTransform d (semicircleRoot z) z‖ / 4 ≤
      ‖fullTreeGreen G d (semicircleRoot z) z i i‖) := by
  obtain ⟨ell, hell, ⟨e⟩⟩ := connected_two_regular_cycle_iso G hconn hdeg
  obtain ⟨n, rfl⟩ : ∃ n, ell = n + 3 := ⟨ell - 3, by omega⟩
  constructor
  · intro i j
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, rfl⟩ := e.surjective j
    rw [two_regular_reference_inverse_reindex G hdeg n d e]
    rw [← graphIso_distance e hconn a b]
    exact cycleReferenceMatrix_inverse_decay n d hd z hz a b
  · constructor
    · intro i
      obtain ⟨a, rfl⟩ := e.surjective i
      rw [two_regular_reference_inverse_reindex G hdeg n d e]
      exact cycleReference_diagonal_deviation n d hd z hz a
    · intro i
      obtain ⟨a, rfl⟩ := e.surjective i
      rw [two_regular_reference_inverse_reindex G hdeg n d e]
      exact cycleReference_diagonal_relative_lower n d hd z hz a

/-- The regular-tree coefficient is fixed under one genuine leaf attachment. -/
theorem kestenMcKay_leaf_fixed_point (d : ℕ) (hd : 3 ≤ d) (z : ℂ) (hz : 0 < z.im) :
    kestenMcKayTransform d (semicircleRoot z) z = semicircleRoot z +
      (semicircleRoot z ^ 2 / ((d : ℂ) - 1)) * kestenMcKayTransform d (semicircleRoot z) z := by
  let m := semicircleRoot z
  have hkcast : ((d - 1 : ℕ) : ℂ) = (d : ℂ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hden := kestenMcKay_algebraic_denominator_ne_zero d hd m z (semicircleRoot_equation z) hz (semicircleRoot_im_pos hz).le
  have hh : kestenMcKayTransform d m z * (1 - m ^ 2 / ((d : ℂ) - 1)) = m := by
    rw [← hkcast, kestenMcKayTransform_eq d hd m z (semicircleRoot_equation z) hz (semicircleRoot_im_pos hz).le]
    exact div_mul_cancel₀ m hden
  linear_combination hh

/-- A new leaf contracts diagonal corrections by at least one half. -/
theorem physical_leaf_factor_norm (d : ℕ) (hd : 3 ≤ d) (z : ℂ) :
    ‖semicircleRoot z ^ 2 / ((d : ℂ) - 1)‖ ≤ 1 / 2 := by
  have hkcast : ((d - 1 : ℕ) : ℂ) = (d : ℂ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hkR : (2 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ d - 1 by omega)
  rw [← hkcast, norm_div, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ 1 / ((d - 1 : ℕ) : ℝ) := div_le_div_of_nonneg_right
      (pow_le_one₀ (norm_nonneg _) (semicircleRoot_norm_le_one z)) (by positivity)
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hkR

/-- Joint invariant retained by every genuine leaf-pruning step. -/
def UnicyclicReferenceControl (d : ℕ) (z : ℂ) : Prop :=
    (∀ i j, ‖fullTreeGreen G d (semicircleRoot z) z i j‖ ≤
      8 * ‖-semicircleRoot z * treeEdgeWeight d‖ ^ G.dist i j) ∧
    (∀ i, ‖fullTreeGreen G d (semicircleRoot z) z i i -
      kestenMcKayTransform d (semicircleRoot z) z‖ ≤
        (3 / 2 : ℝ) * ‖kestenMcKayTransform d (semicircleRoot z) z‖) ∧
    (∀ i, ‖kestenMcKayTransform d (semicircleRoot z) z‖ / 4 ≤
      ‖fullTreeGreen G d (semicircleRoot z) z i i‖)

/-- Exact analytic preservation of the joint invariant under a leaf attachment.
All graph distances and inverse identities are genuine deletion conclusions. -/
theorem leaf_reference_control (hconn : G.Connected) (d : ℕ) (hd : 3 ≤ d)
    (hdeg : ∀ x, G.degree x ≤ d) (v u : V) (hv : G.degree v = 1) (hvu : G.Adj v u)
    (z : ℂ) (hz : 0 < z.im)
    (hrem : UnicyclicReferenceControl (G.induce {x | x ≠ v}) d z) :
    UnicyclicReferenceControl G d z := by
  let m := semicircleRoot z
  let p := kestenMcKayTransform d m z
  let t := -m * treeEdgeWeight d
  let f := m ^ 2 / ((d : ℂ) - 1)
  let H := G.induce {x | x ≠ v}
  let u' : {x : V // x ≠ v} := ⟨u, hvu.ne.symm⟩
  rcases hrem with ⟨hentry, hdev, hlower⟩
  have hm := semicircleRoot_equation z
  have hmim := (semicircleRoot_im_pos hz).le
  have hret := leaf_reference_retained G d hd hdeg v u hv hvu m z hm hz hmim
  have hretEntry : ∀ a b : {x : V // x ≠ v}, fullTreeGreen G d m z a.val b.val = fullTreeGreen H d m z a b := by
    intro a b
    exact congrArg (fun M : Matrix {x : V // x ≠ v} {x : V // x ≠ v} ℂ => M a b) hret
  have hleafdiag := leaf_reference_diagonal G d hd hdeg v u hv hvu m z hm hz hmim
  have hpfix : p = m + f * p := kestenMcKay_leaf_fixed_point d hd z hz
  have hdiff : fullTreeGreen G d m z v v - p = f * (fullTreeGreen H d m z u' u' - p) := by
    linear_combination hleafdiag - hpfix
  have hcontract : ‖fullTreeGreen G d m z v v - p‖ ≤ (3 / 4 : ℝ) * ‖p‖ := by
    rw [hdiff, norm_mul]
    have hh := mul_le_mul (physical_leaf_factor_norm d hd z) (hdev u')
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    convert hh using 1
    dsimp [f, p, m]
    ring
  have hleaflower : ‖p‖ / 4 ≤ ‖fullTreeGreen G d m z v v‖ := by
    have hh := norm_sub_norm_le p (fullTreeGreen G d m z v v)
    rw [norm_sub_rev] at hh
    linarith [norm_nonneg p]
  have hleafnorm : ‖fullTreeGreen G d m z v v‖ ≤ 8 := by
    have hh := norm_sub_le p (p - fullTreeGreen G d m z v v)
    simp only [sub_sub_cancel, norm_sub_rev] at hh
    have hp := kestenMcKayTransform_norm_le_two d hd z hz
    change ‖p‖ ≤ 2 at hp
    linarith [norm_nonneg p]
  constructor
  · intro i j
    by_cases hi : i = v
    · subst i
      by_cases hj : j = v
      · subst j
        simpa only [G.dist_self, pow_zero, mul_one] using hleafnorm
      · have hc := (leaf_reference_cross G d hd hdeg v u hv hvu m z hm hz hmim ⟨j, hj⟩).1
        dsimp only at hc
        rw [hc, norm_mul, leaf_distance G hconn v u hv hvu ⟨j, hj⟩, pow_succ]
        have hh := mul_le_mul_of_nonneg_left (hentry u' ⟨j, hj⟩) (norm_nonneg t)
        convert hh using 1
        dsimp [t, u', H, m]
        ring
    · by_cases hj : j = v
      · subst j
        have hc := (leaf_reference_cross G d hd hdeg v u hv hvu m z hm hz hmim ⟨i, hi⟩).2
        dsimp only at hc
        have hdist : G.dist i v = H.dist u' ⟨i, hi⟩ + 1 := by
          rw [G.dist_comm]
          exact leaf_distance G hconn v u hv hvu ⟨i, hi⟩
        rw [hc, norm_mul, hdist, pow_succ]
        have hsymm : H.dist ⟨i, hi⟩ u' = H.dist u' ⟨i, hi⟩ := H.dist_comm
        have hh := mul_le_mul_of_nonneg_left (hentry ⟨i, hi⟩ u') (norm_nonneg t)
        rw [hsymm] at hh
        convert hh using 1
        dsimp [t, u', H, m]
        ring
      · rw [hretEntry ⟨i, hi⟩ ⟨j, hj⟩]
        have hh := hentry ⟨i, hi⟩ ⟨j, hj⟩
        rw [leaf_delete_distance G hconn v u hv hvu] at hh
        exact hh
  · constructor
    · intro i
      by_cases hi : i = v
      · subst i
        exact hcontract.trans (by nlinarith [norm_nonneg p])
      · rw [hretEntry ⟨i, hi⟩ ⟨i, hi⟩]
        exact hdev ⟨i, hi⟩
    · intro i
      by_cases hi : i = v
      · subst i; exact hleaflower
      · rw [hretEntry ⟨i, hi⟩ ⟨i, hi⟩]
        exact hlower ⟨i, hi⟩

/-- Strong finite-cardinality induction reduces every connected balanced
graph to its actual cycle core, using exact leaf deletion at every step. -/
theorem balanced_reference_control (hconn : G.Connected)
    (hsum : (∑ v, G.degree v) = 2 * Fintype.card V) (d : ℕ) (hd : 3 ≤ d)
    (hdeg : ∀ v, G.degree v ≤ d) (z : ℂ) (hz : 0 < z.im) :
    UnicyclicReferenceControl G d z := by
  have aux : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W),
      Fintype.card W = n → H.Connected → (∑ w, H.degree w) = 2 * Fintype.card W →
        (∀ w, H.degree w ≤ d) → UnicyclicReferenceControl H d z := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ H hcard hconnH hsumH hdegH
      rcases balanced_connected_two_regular_or_leaf H hconnH hsumH with htwo | ⟨v, hv⟩
      · exact two_regular_reference_bounds H hconnH htwo d hd z hz
      · obtain ⟨u, hvu⟩ := (H.degree_pos_iff_exists_adj v).mp (by omega : 0 < H.degree v)
        letI : Fintype {x : W // x ≠ v} := inferInstance
        have hcardDel := delete_vertex_card v
        have hlt : Fintype.card {x : W // x ≠ v} < n := by omega
        have hconnDel := leaf_delete_connected H hconnH v u hv hvu
        have hsumDel := leaf_delete_degree_sum H hsumH v u hv hvu
        have hdegDel : ∀ i : {x : W // x ≠ v}, (H.induce {x | x ≠ v}).degree i ≤ d := by
          intro i
          convert (induced_degree_le H {x | x ≠ v} i).trans (hdegH i.val) using 1
          apply congrArg (fun inst => @SimpleGraph.degree _ _ i inst)
          exact Subsingleton.elim _ _
        have hrem := ih (Fintype.card {x : W // x ≠ v}) hlt
          {x : W // x ≠ v} (H.induce {x | x ≠ v}) rfl hconnDel hsumDel hdegDel
        exact leaf_reference_control H hconnH d hd hdegH v u hv hvu z hz hrem
  exact aux (Fintype.card V) V G rfl hconn hsum hdeg

/-- Actual unicyclic reference control, with excess one as the graph input.
There is no assumed cycle decomposition, pruning certificate or kernel bound. -/
theorem unicyclic_reference_control (hconn : G.Connected) (hexcess : graphExcess G = 1)
    (d : ℕ) (hd : 3 ≤ d) (hdeg : ∀ v, G.degree v ≤ d) (z : ℂ) (hz : 0 < z.im) :
    UnicyclicReferenceControl G d z :=
  balanced_reference_control G hconn (unicyclic_degree_sum G hconn hexcess) d hd hdeg z hz

/-- Uniform actual reference entry decay for every finite connected excess-one
graph, including arbitrarily many attached trees. -/
theorem unicyclic_reference_entry_bound (hconn : G.Connected) (hexcess : graphExcess G = 1)
    (d : ℕ) (hd : 3 ≤ d) (hdeg : ∀ v, G.degree v ≤ d) (z : ℂ) (hz : 0 < z.im) (i j : V) :
    ‖fullTreeGreen G d (semicircleRoot z) z i j‖ ≤
      8 * ‖-semicircleRoot z * treeEdgeWeight d‖ ^ G.dist i j :=
  (unicyclic_reference_control G hconn hexcess d hd hdeg z hz).1 i j

/-- Actual unicyclic diagonals stay within three halves of the regular-tree
reference, uniformly through all leaf attachments. -/
theorem unicyclic_reference_diagonal_deviation (hconn : G.Connected) (hexcess : graphExcess G = 1)
    (d : ℕ) (hd : 3 ≤ d) (hdeg : ∀ v, G.degree v ≤ d) (z : ℂ) (hz : 0 < z.im) (i : V) :
    ‖fullTreeGreen G d (semicircleRoot z) z i i - kestenMcKayTransform d (semicircleRoot z) z‖ ≤
      (3 / 2 : ℝ) * ‖kestenMcKayTransform d (semicircleRoot z) z‖ :=
  (unicyclic_reference_control G hconn hexcess d hd hdeg z hz).2.1 i

/-- Fixed relative diagonal lower bound, retained through genuine pruning. -/
theorem unicyclic_reference_diagonal_relative_lower (hconn : G.Connected) (hexcess : graphExcess G = 1)
    (d : ℕ) (hd : 3 ≤ d) (hdeg : ∀ v, G.degree v ≤ d) (z : ℂ) (hz : 0 < z.im) (i : V) :
    ‖kestenMcKayTransform d (semicircleRoot z) z‖ / 4 ≤
      ‖fullTreeGreen G d (semicircleRoot z) z i i‖ :=
  (unicyclic_reference_control G hconn hexcess d hd hdeg z hz).2.2 i

/-- Concrete bounded-domain diagonal control for actual excess-one graphs. -/
theorem unicyclic_reference_diagonal_bounds (hconn : G.Connected) (hexcess : graphExcess G = 1)
    (d : ℕ) (hd : 3 ≤ d) (hdeg : ∀ v, G.degree v ≤ d) (z : ℂ) (hz : 0 < z.im)
    (B : ℝ) (hB : ‖z‖ ≤ B) (i : V) :
    1 / (4 * (B + 2)) ≤ ‖fullTreeGreen G d (semicircleRoot z) z i i‖ ∧
      ‖fullTreeGreen G d (semicircleRoot z) z i i‖ ≤ 8 := by
  constructor
  · have hh := div_le_div_of_nonneg_right (kestenMcKay_bounded_norm_lower d hd z hz B hB)
      (by norm_num : (0 : ℝ) ≤ 4)
    have hrate : (1 / (B + 2)) / 4 = 1 / (4 * (B + 2)) := by field_simp; ring
    rw [hrate] at hh
    exact hh.trans (unicyclic_reference_diagonal_relative_lower G hconn hexcess d hd hdeg z hz i)
  · simpa only [G.dist_self, pow_zero, mul_one] using
      unicyclic_reference_entry_bound G hconn hexcess d hd hdeg z hz i i

end FiniteGraph
end
end LocalLaw
