import LocalLaw.PrincipalDeletionWard
import LocalLaw.GraphConcentration

/-!
# The physical cavity average after deleting a vertex set

This is the actual averaging comparison needed in source (6.6). The cost
retains the true inverse Green block on the removed vertices and the exact
number of removed incidences. No independence or concentration is assumed.
-/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance cavityDeleteAverageDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

def outsideSpanningGraph (G : SimpleGraph V) (T : Set V) : SimpleGraph V where
  Adj i j := G.Adj i j ∧ i ∉ T ∧ j ∉ T
  symm := by intro i j h; exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := by intro i h; exact G.loopless i h.1

def outsideOrientedCavityValue (G : SimpleGraph V) (d : ℕ) (T : Set V) (z : ℂ)
    (e : OutsideOrientedEdge G T) : ℂ :=
  matrixCavityTerm (green (normalizedAdjacency (outsideGraph G T) d) z)
    ⟨e.val.2, e.property.2.2⟩ ⟨e.val.1, e.property.2.1⟩

theorem outsideOrientedCavityValue_eq_deleted (G : SimpleGraph V) (d : ℕ) (T : Set V)
    (z : ℂ) (hz : 0 < z.im) (e : OutsideOrientedEdge G T) :
    outsideOrientedCavityValue G d T z e =
      green (deletedMatrix (normalizedAdjacency (outsideGraph G T) d)
        ⟨e.val.1, e.property.2.1⟩) z
          ⟨⟨e.val.2, e.property.2.2⟩, by
            intro h; exact e.property.1.ne' (congrArg Subtype.val h)⟩
          ⟨⟨e.val.2, e.property.2.2⟩, by
            intro h; exact e.property.1.ne' (congrArg Subtype.val h)⟩ := by
  rw [green_deleted_vertex _ (normalizedAdjacency_isHermitian (outsideGraph G T) d) z hz]
  rfl

theorem maskedDeletedGreen_caps (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (T : Set V) (z : ℂ) (hz : 0 < z.im) (C L : ℝ)
    (hR : ∀ i j, ‖green H z i j‖ ≤ C)
    (hRi : ∀ j, ‖(green H z j j)⁻¹‖ ≤ L)
    (hS : ∀ i j : (Tᶜ : Set V),
      ‖green (H.submatrix (Subtype.val : (Tᶜ : Set V) → V)
        (Subtype.val : (Tᶜ : Set V) → V)) z i j‖ ≤ C)
    (hSi : ∀ j : (Tᶜ : Set V),
      ‖(green (H.submatrix (Subtype.val : (Tᶜ : Set V) → V)
        (Subtype.val : (Tᶜ : Set V) → V)) z j j)⁻¹‖ ≤ L) :
    (∀ i j, ‖maskedDeletedGreen H T z i j‖ ≤ C) ∧
      (∀ j, maskedDeletedGreen H T z j j ≠ 0) ∧
        (∀ j, ‖(maskedDeletedGreen H T z j j)⁻¹‖ ≤ L) := by
  constructor
  · intro i j
    by_cases hi : i ∉ T
    · by_cases hj : j ∉ T
      · simpa only [maskedDeletedGreen, dif_pos hi, dif_pos hj] using hS ⟨i, hi⟩ ⟨j, hj⟩
      · simpa only [maskedDeletedGreen, dif_pos hi, dif_neg hj] using hR i j
    · simpa only [maskedDeletedGreen, dif_neg hi] using hR i j
  constructor
  · intro j
    by_cases hj : j ∉ T
    · simpa only [maskedDeletedGreen, dif_pos hj] using
        green_diagonal_ne_zero (H.submatrix (Subtype.val : (Tᶜ : Set V) → V)
          (Subtype.val : (Tᶜ : Set V) → V)) (hH.submatrix _) z hz ⟨j, hj⟩
    · simpa only [maskedDeletedGreen, dif_neg hj] using green_diagonal_ne_zero H hH z hz j
  · intro j
    by_cases hj : j ∉ T
    · simpa only [maskedDeletedGreen, dif_pos hj] using hSi ⟨j, hj⟩
    · simpa only [maskedDeletedGreen, dif_neg hj] using hRi j

theorem regular_edge_principalDeletion_difference_ward (G : SimpleGraph V) (d : ℕ)
    (hregular : G.IsRegularOfDegree d) (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (T : Set V) (z : ℂ) (hz : 0 < z.im) (C L I : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hR : ∀ i j, ‖green H z i j‖ ≤ C)
    (hRi : ∀ j, ‖(green H z j j)⁻¹‖ ≤ L)
    (hS : ∀ i j : (Tᶜ : Set V),
      ‖green (H.submatrix (Subtype.val : (Tᶜ : Set V) → V)
        (Subtype.val : (Tᶜ : Set V) → V)) z i j‖ ≤ C)
    (hSi : ∀ j : (Tᶜ : Set V),
      ‖(green (H.submatrix (Subtype.val : (Tᶜ : Set V) → V)
        (Subtype.val : (Tᶜ : Set V) → V)) z j j)⁻¹‖ ≤ L)
    (hI : ∀ u, (green H z u u).im ≤ I) :
    (∑ i, ∑ j, if G.Adj i j then
      ‖matrixCavityTerm (green H z) i j - matrixCavityTerm (maskedDeletedGreen H T z) i j‖ else 0) ≤
      ((d : ℝ) * (1 + C * L) ^ 2 * I / z.im) *
        (∑ u : T, ∑ v : T,
          ‖((green H z).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ u v‖) := by
  obtain ⟨hSm, hSp, hSim⟩ := maskedDeletedGreen_caps H hH T z hz C L hR hRi hS hSi
  have hbase := regular_edge_cavity_difference G d hregular (green H z) (maskedDeletedGreen H T z)
    C L hC hL hR hSm (green_diagonal_ne_zero H hH z hz) hSp hRi hSim
  have hdiag : (∑ i, ‖green H z i i - maskedDeletedGreen H T z i i‖) ≤
      (I / z.im) * (∑ u : T, ∑ v : T,
        ‖((green H z).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ u v‖) := by
    simpa only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.sum_ite_eq, Finset.mem_univ, if_true] using
      weighted_maskedDeletedGreen_difference_ward H hH T z hz (1 : Matrix V V ℝ) 1 I
        (by intro i j; simp only [Matrix.one_apply]; split_ifs <;> norm_num)
        (by norm_num) (by intro i; simp [Matrix.one_apply]) (by intro j; simp [Matrix.one_apply]) hI
  let W : Matrix V V ℝ := fun i j => if G.Adj i j then 1 else 0
  have hrow : ∀ i, ∑ j, W i j = (d : ℝ) := by
    intro i
    dsimp only [W]
    rw [← G.degree_eq_sum_if_adj (R := ℝ)]
    have hh := hregular i
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh ⊢
    exact_mod_cast hh
  have hcol : ∀ j, ∑ i, W i j = (d : ℝ) := by
    intro j
    simpa only [W, G.adj_comm] using hrow j
  have hedge := weighted_maskedDeletedGreen_difference_ward H hH T z hz W (d : ℝ) I
    (by intro i j; dsimp only [W]; split_ifs <;> norm_num) (Nat.cast_nonneg d) hrow hcol hI
  simp only [W, ite_mul, one_mul, zero_mul] at hedge
  apply hbase.trans
  calc
    _ ≤ ((d : ℝ) * (1 + C ^ 2 * L ^ 2)) *
        ((I / z.im) * (∑ u : T, ∑ v : T,
          ‖((green H z).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ u v‖)) +
        2 * C * L * (((d : ℝ) * I / z.im) * (∑ u : T, ∑ v : T,
          ‖((green H z).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ u v‖)) :=
      add_le_add (mul_le_mul_of_nonneg_left hdiag (by positivity))
        (mul_le_mul_of_nonneg_left hedge (by positivity))
    _ = _ := by ring

omit [DecidableEq V] in
theorem outsideSpanningGraph_disagreement (G : SimpleGraph V) (d : ℕ)
    (hregular : G.IsRegularOfDegree d) (T : Set V) :
    adjacencyDisagreement G (outsideSpanningGraph G T) ≤ 2 * (d : ℝ) * (Nat.card T : ℝ) := by
  have hp : ∀ i j, (if (G.Adj i j ↔ (outsideSpanningGraph G T).Adj i j) then (0 : ℝ) else 1) ≤
      (if G.Adj i j then (if i ∈ T then (1 : ℝ) else 0) + (if j ∈ T then 1 else 0) else 0) := by
    intro i j
    by_cases ha : G.Adj i j <;> by_cases hi : i ∈ T <;> by_cases hj : j ∈ T <;>
      simp [outsideSpanningGraph, ha, hi, hj]
  calc
    _ ≤ ∑ i, ∑ j, if G.Adj i j then
        (if i ∈ T then (1 : ℝ) else 0) + (if j ∈ T then 1 else 0) else 0 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hp i j))
    _ = (d : ℝ) * (∑ i : V, if i ∈ T then (1 : ℝ) else 0) +
        (d : ℝ) * (∑ j : V, if j ∈ T then (1 : ℝ) else 0) := by
      have hs : ∀ i j, (if G.Adj i j then
          (if i ∈ T then (1 : ℝ) else 0) + (if j ∈ T then 1 else 0) else 0) =
          (if G.Adj i j then (if i ∈ T then (1 : ℝ) else 0) else 0) +
            (if G.Adj i j then (if j ∈ T then (1 : ℝ) else 0) else 0) := by
        intro i j
        by_cases ha : G.Adj i j <;> simp [ha]
      simp_rw [hs, Finset.sum_add_distrib]
      rw [regular_edge_sum_left G d hregular, regular_edge_sum_right G d hregular]
    _ = _ := by
      have ht : (∑ i : V, if i ∈ T then (1 : ℝ) else 0) = (Nat.card T : ℝ) := by
        simp [← Finset.sum_filter, Nat.card_eq_fintype_card, Fintype.card_subtype]
      rw [ht]
      ring

/-- The actual sampled endpoint orientation is accounted for by transposing
the finite edge sum, rather than by an assumed endpoint distribution. -/
theorem outsideOrientedCavityValue_sum (G : SimpleGraph V) (d : ℕ) (T : Set V) (z : ℂ) :
    (∑ e : OutsideOrientedEdge G T, outsideOrientedCavityValue G d T z e) =
      ∑ i, ∑ j, if (outsideSpanningGraph G T).Adj i j then
        matrixCavityTerm (maskedDeletedGreen (normalizedAdjacency G d) T z) i j else 0 := by
  let f : V × V → ℂ := fun p =>
    matrixCavityTerm (maskedDeletedGreen (normalizedAdjacency G d) T z) p.2 p.1
  have he : ∀ e : OutsideOrientedEdge G T, outsideOrientedCavityValue G d T z e = f e.val := by
    intro e
    unfold outsideOrientedCavityValue f matrixCavityTerm
    simp only [maskedDeletedGreen, dif_pos e.property.2.1, dif_pos e.property.2.2]
    rfl
  rw [Finset.sum_congr rfl (fun e _ => he e)]
  have hs : (∑ p ∈ Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∉ T ∧ p.2 ∉ T), f p) =
      ∑ e : OutsideOrientedEdge G T, f e.val := by
    exact Finset.sum_subtype _ (by simp) _
  rw [← hs, Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [f, outsideSpanningGraph]
  congr 1
  exact propext (by rw [G.adj_comm]; tauto)

namespace RegularGraph
variable {N d : ℕ}

/-- Source (6.6), before its final numeric simplification. The minor-entry
and pivot caps are explicit analytic inputs, while the actual Schur/Ward
averaging, orientation, edge removal and normalization are proved here. -/
theorem Q_outside_cavity_average_difference (g : RegularGraph N d) (T : Set (Fin N))
    (z : ℂ) (hz : 0 < z.im) (C L I : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hR : ∀ i j, ‖g.G z i j‖ ≤ C)
    (hRi : ∀ j, ‖(g.G z j j)⁻¹‖ ≤ L)
    (hS : ∀ i j : (Tᶜ : Set (Fin N)),
      ‖green (normalizedAdjacency (outsideGraph g.graph T) d) z i j‖ ≤ C)
    (hSi : ∀ j : (Tᶜ : Set (Fin N)),
      ‖(green (normalizedAdjacency (outsideGraph g.graph T) d) z j j)⁻¹‖ ≤ L)
    (hI : ∀ u, (g.G z u u).im ≤ I) :
    ‖g.Q z - ((N : ℝ) * (d : ℝ))⁻¹ •
        ∑ e : OutsideOrientedEdge g.graph T, outsideOrientedCavityValue g.graph d T z e‖ ≤
      ((N : ℝ) * (d : ℝ))⁻¹ *
        ((((d : ℝ) * (1 + C * L) ^ 2 * I / z.im) *
          (∑ u : T, ∑ v : T,
            ‖((g.G z).submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N))⁻¹ u v‖)) +
            (2 * (d : ℝ) * (Nat.card T : ℝ)) * (C + C ^ 2 * L)) := by
  have hS' : ∀ i j : (Tᶜ : Set (Fin N)),
      ‖green (g.H.submatrix (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)
        (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)) z i j‖ ≤ C := hS
  have hSi' : ∀ j : (Tᶜ : Set (Fin N)),
      ‖(green (g.H.submatrix (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)
        (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)) z j j)⁻¹‖ ≤ L := hSi
  obtain ⟨hSm, _, hSim⟩ := maskedDeletedGreen_caps g.H
    (normalizedAdjacency_isHermitian g.graph d) T z hz C L hR hRi hS' hSi'
  have hsum := edge_cavity_sums_difference g.graph (outsideSpanningGraph g.graph T)
    (g.G z) (maskedDeletedGreen g.H T z) (C + C ^ 2 * L)
    (matrixCavityTerm_norm_bound (g.G z) C L hC hL hR hRi)
    (matrixCavityTerm_norm_bound _ C L hC hL hSm hSim)
  have hward := regular_edge_principalDeletion_difference_ward g.graph d g.regular g.H
    (normalizedAdjacency_isHermitian g.graph d) T z hz C L I hC hL hR hRi hS' hSi' hI
  have hcount := outsideSpanningGraph_disagreement g.graph d g.regular T
  have hbound := hsum.trans (add_le_add hward
    (mul_le_mul_of_nonneg_right hcount (by positivity : 0 ≤ C + C ^ 2 * L)))
  rw [outsideOrientedCavityValue_sum]
  change ‖cavityAverage g.graph d z - _‖ ≤ _
  rw [cavityAverage_eq_matrixCavityTerm g.graph d z hz]
  simp only [Fintype.card_fin, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_natCast, ← mul_sub, norm_mul, norm_inv, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

end RegularGraph

end
end LocalLaw
