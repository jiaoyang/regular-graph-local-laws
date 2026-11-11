import LocalLaw.CavityMatrixPerturbation
import LocalLaw.ResolventComparisonWard

/-!
# Averaged cavity change under a graph perturbation

The rational Schur modulus is summed using exact regular-graph marginals.
Ward controls the mean Green changes; changed oriented edges are counted
separately. This is a finite deterministic ingredient for source (5.110).
-/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance cavityAveragePerturbDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Exact left marginal of the oriented edges of a regular graph. -/
theorem regular_edge_sum_left (G : SimpleGraph V) (d : ℕ)
    (hregular : G.IsRegularOfDegree d) (f : V → ℝ) :
    (∑ i, ∑ j, if G.Adj i j then f i else 0) = (d : ℝ) * ∑ i, f i := by
  have hrow : ∀ i, (∑ j, if G.Adj i j then f i else 0) = (d : ℝ) * f i := by
    intro i
    calc
      _ = (∑ j, if G.Adj i j then (1 : ℝ) else 0) * f i := by rw [Finset.sum_mul]; simp
      _ = (d : ℝ) * f i := by
        rw [← G.degree_eq_sum_if_adj (R := ℝ)]
        have hh := hregular i
        simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh ⊢
        rw [hh]
  simp_rw [hrow]
  exact (Finset.mul_sum ..).symm

omit [DecidableEq V] in
theorem regular_edge_sum_right (G : SimpleGraph V) (d : ℕ)
    (hregular : G.IsRegularOfDegree d) (f : V → ℝ) :
    (∑ i, ∑ j, if G.Adj i j then f j else 0) = (d : ℝ) * ∑ j, f j := by
  rw [Finset.sum_comm]
  simpa only [G.adj_comm] using regular_edge_sum_left G d hregular f

omit [DecidableEq V] in
theorem edge_sum_transpose (G : SimpleGraph V) (f : V → V → ℝ) :
    (∑ i, ∑ j, if G.Adj i j then f j i else 0) =
      ∑ i, ∑ j, if G.Adj i j then f i j else 0 := by
  rw [Finset.sum_comm]
  simp_rw [G.adj_comm]

omit [Fintype V] [DecidableEq V] in
/-- Uniform norm cap for a rational cavity term from its actual three factors. -/
theorem matrixCavityTerm_norm_bound (R : Matrix V V ℂ) (C L : ℝ)
    (hC : 0 ≤ C) (_hL : 0 ≤ L) (hR : ∀ i j, ‖R i j‖ ≤ C)
    (hRi : ∀ j, ‖(R j j)⁻¹‖ ≤ L) (i j : V) :
    ‖matrixCavityTerm R i j‖ ≤ C + C ^ 2 * L := by
  unfold matrixCavityTerm
  apply (norm_sub_le _ _).trans
  rw [div_eq_mul_inv, norm_mul, norm_mul]
  calc
    _ ≤ C + C * C * L := by
      have hp := mul_le_mul (hR i j) (hR j i) (norm_nonneg (R j i)) hC
      have hp2 := mul_le_mul hp (hRi j) (norm_nonneg ((R j j)⁻¹)) (mul_nonneg hC hC)
      exact add_le_add (hR i i) hp2
    _ = _ := by ring

omit [DecidableEq V] in
/-- Sum of the cavity modulus on one regular graph, before Ward is applied. -/
theorem regular_edge_cavity_difference (G : SimpleGraph V) (d : ℕ)
    (hregular : G.IsRegularOfDegree d) (R S : Matrix V V ℂ) (C L : ℝ)
    (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hR : ∀ i j, ‖R i j‖ ≤ C) (hS : ∀ i j, ‖S i j‖ ≤ C)
    (hRp : ∀ j, R j j ≠ 0) (hSp : ∀ j, S j j ≠ 0)
    (hRi : ∀ j, ‖(R j j)⁻¹‖ ≤ L) (hSi : ∀ j, ‖(S j j)⁻¹‖ ≤ L) :
    (∑ i, ∑ j, if G.Adj i j then ‖matrixCavityTerm R i j - matrixCavityTerm S i j‖ else 0) ≤
      ((d : ℝ) * (1 + C ^ 2 * L ^ 2)) * (∑ i, ‖R i i - S i i‖) +
        2 * C * L * (∑ i, ∑ j, if G.Adj i j then ‖R i j - S i j‖ else 0) := by
  calc
    _ ≤ ∑ i, ∑ j, if G.Adj i j then
        ‖R i i - S i i‖ + C * L * (‖R i j - S i j‖ + ‖R j i - S j i‖) +
          C ^ 2 * L ^ 2 * ‖R j j - S j j‖ else 0 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      split_ifs
      · exact matrixCavityTerm_difference_bound R S C L hC hL hR hS hRp hSp hRi hSi i j
      · exact le_rfl
    _ = _ := by
      have hsplit : ∀ i j,
          (if G.Adj i j then ‖R i i - S i i‖ + C * L * (‖R i j - S i j‖ + ‖R j i - S j i‖) +
              C ^ 2 * L ^ 2 * ‖R j j - S j j‖ else 0) =
            (if G.Adj i j then ‖R i i - S i i‖ else 0) +
            C * L * ((if G.Adj i j then ‖R i j - S i j‖ else 0) +
              (if G.Adj i j then ‖R j i - S j i‖ else 0)) +
            C ^ 2 * L ^ 2 * (if G.Adj i j then ‖R j j - S j j‖ else 0) := by
        intro i j
        split_ifs <;> ring
      simp_rw [hsplit, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
      have ht := edge_sum_transpose G (fun i j => ‖R i j - S i j‖)
      rw [regular_edge_sum_left G d hregular, regular_edge_sum_right G d hregular, ht]
      ring

/-- The number of ordered pairs on which the adjacency relations disagree. -/
def adjacencyDisagreement (G F : SimpleGraph V) : ℝ :=
  ∑ i, ∑ j, if (G.Adj i j ↔ F.Adj i j) then (0 : ℝ) else 1

omit [DecidableEq V] in
/-- Changing the edge indicator adds only an explicit disagreement count,
independently of the Green-function perturbation on retained edges. -/
theorem edge_cavity_sums_difference (G F : SimpleGraph V) (R S : Matrix V V ℂ)
    (M : ℝ)
    (hR : ∀ i j, ‖matrixCavityTerm R i j‖ ≤ M)
    (hS : ∀ i j, ‖matrixCavityTerm S i j‖ ≤ M) :
    ‖(∑ i, ∑ j, if G.Adj i j then matrixCavityTerm R i j else 0) -
      (∑ i, ∑ j, if F.Adj i j then matrixCavityTerm S i j else 0)‖ ≤
      (∑ i, ∑ j, if G.Adj i j then ‖matrixCavityTerm R i j - matrixCavityTerm S i j‖ else 0) +
        adjacencyDisagreement G F * M := by
  have hpoint : ∀ i j,
      ‖(if G.Adj i j then matrixCavityTerm R i j else 0) -
        (if F.Adj i j then matrixCavityTerm S i j else 0)‖ ≤
        (if G.Adj i j then ‖matrixCavityTerm R i j - matrixCavityTerm S i j‖ else 0) +
          (if (G.Adj i j ↔ F.Adj i j) then 0 else 1) * M := by
    intro i j
    by_cases hG : G.Adj i j <;> by_cases hF : F.Adj i j
    · simp [hG, hF]
    · simp only [hG, hF, iff_false, not_true_eq_false, if_true, if_false, sub_zero,
        one_mul]
      exact (hR i j).trans (by linarith [norm_nonneg (matrixCavityTerm R i j - matrixCavityTerm S i j)])
    · simpa [hG, hF] using hS i j
    · simp [hG, hF]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖(∑ j, if G.Adj i j then matrixCavityTerm R i j else 0) -
        (∑ j, if F.Adj i j then matrixCavityTerm S i j else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j,
        ((if G.Adj i j then ‖matrixCavityTerm R i j - matrixCavityTerm S i j‖ else 0) +
          (if (G.Adj i j ↔ F.Adj i j) then 0 else 1) * M) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← Finset.sum_sub_distrib]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => hpoint i j))
    _ = _ := by simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul]; rfl

/-- Ward supplies both finite Green-change sums in the exact cavity modulus.
The resulting bound depends on the genuine matrix perturbation mass. -/
theorem regular_edge_cavity_difference_ward (G : SimpleGraph V) (d : ℕ)
    (hregular : G.IsRegularOfDegree d) (H K : Matrix V V ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (C L I : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hR : ∀ i j, ‖green H z i j‖ ≤ C) (hS : ∀ i j, ‖green K z i j‖ ≤ C)
    (hRi : ∀ j, ‖(green H z j j)⁻¹‖ ≤ L) (hSi : ∀ j, ‖(green K z j j)⁻¹‖ ≤ L)
    (hHI : ∀ j, (green H z j j).im ≤ I) (hKI : ∀ j, (green K z j j).im ≤ I) :
    (∑ i, ∑ j, if G.Adj i j then
        ‖matrixCavityTerm (green H z) i j - matrixCavityTerm (green K z) i j‖ else 0) ≤
      ((d : ℝ) * (1 + C * L) ^ 2 * I / z.im) * (∑ u, ∑ v, ‖(K - H) u v‖) := by
  have hbase := regular_edge_cavity_difference G d hregular (green H z) (green K z) C L hC hL
    hR hS (green_diagonal_ne_zero H hH z hz) (green_diagonal_ne_zero K hK z hz) hRi hSi
  have hdiag := diagonal_green_difference_ward H K hH hK z hz I hHI hKI
  have hedge := regular_edge_green_difference_ward G d hregular H K hH hK z hz I hHI hKI
  apply hbase.trans
  calc
    _ ≤ ((d : ℝ) * (1 + C ^ 2 * L ^ 2)) *
        ((I / z.im) * (∑ u, ∑ v, ‖(K - H) u v‖)) +
        2 * C * L * (((d : ℝ) * I / z.im) * (∑ u, ∑ v, ‖(K - H) u v‖)) :=
      add_le_add (mul_le_mul_of_nonneg_left hdiag (by positivity))
        (mul_le_mul_of_nonneg_left hedge (by positivity))
    _ = _ := by ring

/-- Deterministic graph-cavity change, with the two genuinely different costs:
resolvent propagation from Ward and directly changed oriented edges. -/
theorem cavityAverage_graph_difference_ward (G F : SimpleGraph V) (d : ℕ)
    (hregular : G.IsRegularOfDegree d) (z : ℂ) (hz : 0 < z.im)
    (C L I : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hG : ∀ i j, ‖green (normalizedAdjacency G d) z i j‖ ≤ C)
    (hF : ∀ i j, ‖green (normalizedAdjacency F d) z i j‖ ≤ C)
    (hGi : ∀ j, ‖(green (normalizedAdjacency G d) z j j)⁻¹‖ ≤ L)
    (hFi : ∀ j, ‖(green (normalizedAdjacency F d) z j j)⁻¹‖ ≤ L)
    (hGI : ∀ j, (green (normalizedAdjacency G d) z j j).im ≤ I)
    (hFI : ∀ j, (green (normalizedAdjacency F d) z j j).im ≤ I) :
    ‖cavityAverage G d z - cavityAverage F d z‖ ≤
      ((Fintype.card V : ℝ) * (d : ℝ))⁻¹ *
        ((((d : ℝ) * (1 + C * L) ^ 2 * I / z.im) *
            (∑ u, ∑ v, ‖(normalizedAdjacency F d - normalizedAdjacency G d) u v‖)) +
          adjacencyDisagreement G F * (C + C ^ 2 * L)) := by
  let R := green (normalizedAdjacency G d) z
  let S := green (normalizedAdjacency F d) z
  have hsum := edge_cavity_sums_difference G F R S (C + C ^ 2 * L)
    (matrixCavityTerm_norm_bound R C L hC hL hG hGi)
    (matrixCavityTerm_norm_bound S C L hC hL hF hFi)
  have hward := regular_edge_cavity_difference_ward G d hregular
    (normalizedAdjacency G d) (normalizedAdjacency F d)
    (normalizedAdjacency_isHermitian G d) (normalizedAdjacency_isHermitian F d)
    z hz C L I hC hL hG hF hGi hFi hGI hFI
  have hbound := hsum.trans (add_le_add_right hward _)
  rw [cavityAverage_eq_matrixCavityTerm G d z hz, cavityAverage_eq_matrixCavityTerm F d z hz,
    ← mul_sub, norm_mul]
  simp only [norm_inv, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

namespace RegularGraph
variable {N d : ℕ}

/-- Source-specific Q perturbation with actual physical Green matrices. -/
theorem Q_graph_difference_ward (g h : RegularGraph N d) (z : ℂ) (hz : 0 < z.im)
    (C L I : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hg : ∀ i j, ‖g.G z i j‖ ≤ C) (hh : ∀ i j, ‖h.G z i j‖ ≤ C)
    (hgi : ∀ j, ‖(g.G z j j)⁻¹‖ ≤ L) (hhi : ∀ j, ‖(h.G z j j)⁻¹‖ ≤ L)
    (hgI : ∀ j, (g.G z j j).im ≤ I) (hhI : ∀ j, (h.G z j j).im ≤ I) :
    ‖g.Q z - h.Q z‖ ≤ ((N : ℝ) * (d : ℝ))⁻¹ *
      ((((d : ℝ) * (1 + C * L) ^ 2 * I / z.im) *
          (∑ u, ∑ v, ‖(h.H - g.H) u v‖)) +
        adjacencyDisagreement g.graph h.graph * (C + C ^ 2 * L)) := by
  simpa only [Fintype.card_fin] using cavityAverage_graph_difference_ward
    g.graph h.graph d g.regular z hz C L I hC hL hg hh hgi hhi hgI hhI

end RegularGraph

end
end LocalLaw
