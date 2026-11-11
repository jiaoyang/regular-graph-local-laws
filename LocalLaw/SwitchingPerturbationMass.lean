import LocalLaw.CavityAveragePerturbation
import LocalLaw.ResamplingSchedule

/-!
# Actual switching perturbation mass for the Ward/Q comparison

Each switch changes at most eight oriented adjacency entries. This budget
holds for an arbitrary schedule and therefore for the actual selected labelled
resampling involution, whose schedule length is at most the boundary size.
-/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance switchingMassDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Adjacency disagreement obeys the triangle inequality. -/
theorem adjacencyDisagreement_triangle (G F H : SimpleGraph V) :
    adjacencyDisagreement G H ≤ adjacencyDisagreement G F + adjacencyDisagreement F H := by
  unfold adjacencyDisagreement
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  by_cases hg : G.Adj i j <;> by_cases hf : F.Adj i j <;> by_cases hh : H.Adj i j <;> simp [hg, hf, hh]

omit [DecidableEq V] in
@[simp] theorem adjacencyDisagreement_self (G : SimpleGraph V) : adjacencyDisagreement G G = 0 := by
  simp [adjacencyDisagreement]

def switchingChangedPairs (q : SwitchingQuad V) : Finset (V × V) :=
  [(q.a, q.b), (q.b, q.a), (q.c, q.d), (q.d, q.c),
    (q.a, q.d), (q.d, q.a), (q.b, q.c), (q.c, q.b)].toFinset

omit [Fintype V] in
/-- Every changed entry is one of the two old or two new unordered edges. -/
theorem switching_changed_pair_mem (q : SwitchingQuad V) (G : SimpleGraph V) (i j : V)
    (hchange : ¬(G.Adj i j ↔ (q.apply G).Adj i j)) : (i, j) ∈ switchingChangedPairs q := by
  have hhit : (switchingRemoved q.a q.b q.c q.d).Adj i j ∨
      (switchingAdded q.a q.b q.c q.d).Adj i j := by
    by_contra hnone
    have hr : ¬(switchingRemoved q.a q.b q.c q.d).Adj i j := fun h => hnone (Or.inl h)
    have ha : ¬(switchingAdded q.a q.b q.c q.d).Adj i j := fun h => hnone (Or.inr h)
    apply hchange
    simp only [SwitchingQuad.apply, simpleSwitch, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj,
      hr, ha, not_false_eq_true, and_true, or_false]
  simp only [switchingRemoved, switchingAdded, SimpleGraph.sup_adj, SimpleGraph.edge_adj] at hhit
  simp only [switchingChangedPairs, List.mem_toFinset, List.mem_cons, List.mem_singleton,
    Prod.mk.injEq]
  aesop

/-- Eight is an upper bound without any distinctness/admissibility premise. -/
theorem switching_adjacencyDisagreement_le (q : SwitchingQuad V) (G : SimpleGraph V) :
    adjacencyDisagreement G (q.apply G) ≤ 8 := by
  have hpoint : ∀ p : V × V,
      (if G.Adj p.1 p.2 ↔ (q.apply G).Adj p.1 p.2 then (0 : ℝ) else 1) ≤
        if p ∈ switchingChangedPairs q then 1 else 0 := by
    intro p
    by_cases h : G.Adj p.1 p.2 ↔ (q.apply G).Adj p.1 p.2
    · rw [if_pos h]
      split_ifs <;> norm_num
    · have hm := switching_changed_pair_mem q G p.1 p.2 h
      simp only [if_neg h, if_pos hm]
      exact le_rfl
  have hcount : (switchingChangedPairs q).card ≤ 8 := by
    exact (List.toFinset_card_le _).trans (by norm_num)
  calc
    _ = ∑ p : V × V, if G.Adj p.1 p.2 ↔ (q.apply G).Adj p.1 p.2 then (0 : ℝ) else 1 := by
      rw [Fintype.sum_prod_type]
      rfl
    _ ≤ ∑ p : V × V, if p ∈ switchingChangedPairs q then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun p _ => hpoint p)
    _ = ((switchingChangedPairs q).card : ℝ) := by rw [← Finset.sum_filter]; simp
    _ ≤ 8 := by exact_mod_cast hcount

/-- Sequential switchings pay their actual number, without a disjointness
assumption or a separate matrix-compatibility hypothesis. -/
theorem applySwitches_adjacencyDisagreement_le (L : List (SwitchingQuad V)) (G : SimpleGraph V) :
    adjacencyDisagreement G (applySwitches L G) ≤ 8 * (L.length : ℝ) := by
  induction L generalizing G with
  | nil => simp
  | cons q L ih =>
    rw [applySwitches_cons]
    have htri := adjacencyDisagreement_triangle G (q.apply G) (applySwitches L (q.apply G))
    have hsum := add_le_add (switching_adjacencyDisagreement_le q G) (ih (q.apply G))
    apply (htri.trans hsum).trans_eq
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

omit [DecidableEq V] in
/-- Actual normalized matrix perturbation mass equals adjacency disagreement
times the edge normalization, entry by entry. -/
theorem normalizedAdjacency_difference_mass (G F : SimpleGraph V) (d : ℕ) :
    (∑ i, ∑ j, ‖(normalizedAdjacency F d - normalizedAdjacency G d) i j‖) =
      adjacencyDisagreement G F * (Real.sqrt ((d : ℝ) - 1))⁻¹ := by
  have hpoint : ∀ i j,
      ‖(normalizedAdjacency F d - normalizedAdjacency G d) i j‖ =
        (if G.Adj i j ↔ F.Adj i j then (0 : ℝ) else 1) *
          (Real.sqrt ((d : ℝ) - 1))⁻¹ := by
    intro i j
    by_cases hg : G.Adj i j <;> by_cases hf : F.Adj i j <;>
      simp [normalizedAdjacency, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        SimpleGraph.adjMatrix_apply, hg, hf, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  simp_rw [hpoint, ← Finset.sum_mul]
  rfl

namespace LabelledResamplingState
variable {T : Set V} {ι : Type*} [Fintype ι]

/-- Perturbation budget for the very same full labelled map used by the
stationary graph kernel. -/
theorem fullResample_adjacencyDisagreement_le (s : LabelledResamplingState V T ι) (radius : ℕ) :
    adjacencyDisagreement s.graph (s.fullResample radius).graph ≤
      8 * (Nat.card (BoundaryOrientedEdge s.graph T) : ℝ) := by
  rw [s.fullResample_graph_eq_applySwitches radius]
  apply (applySwitches_adjacencyDisagreement_le _ s.graph).trans
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (s.fullResample_selectedQuads_length radius)) (by norm_num)

theorem fullResample_normalized_difference_mass_le (s : LabelledResamplingState V T ι) (radius d : ℕ) :
    (∑ i, ∑ j, ‖(normalizedAdjacency (s.fullResample radius).graph d - normalizedAdjacency s.graph d) i j‖) ≤
      8 * (Nat.card (BoundaryOrientedEdge s.graph T) : ℝ) / Real.sqrt ((d : ℝ) - 1) := by
  rw [normalizedAdjacency_difference_mass]
  have hh := mul_le_mul_of_nonneg_right (s.fullResample_adjacencyDisagreement_le radius)
    (inv_nonneg.mpr (Real.sqrt_nonneg ((d : ℝ) - 1)))
  simpa only [div_eq_mul_inv] using hh

/-- The actual selected resampling schedule realizes the Ward/Q perturbation
budget. The only analytic inputs are genuine Green-entry and pivot caps. -/
theorem fullResample_cavityAverage_difference (s : LabelledResamplingState V T ι)
    (radius d : ℕ) (hregular : s.graph.IsRegularOfDegree d)
    (z : ℂ) (hz : 0 < z.im) (C L I : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) (hI : 0 ≤ I)
    (hG : ∀ i j, ‖green (normalizedAdjacency s.graph d) z i j‖ ≤ C)
    (hF : ∀ i j, ‖green (normalizedAdjacency (s.fullResample radius).graph d) z i j‖ ≤ C)
    (hGi : ∀ j, ‖(green (normalizedAdjacency s.graph d) z j j)⁻¹‖ ≤ L)
    (hFi : ∀ j, ‖(green (normalizedAdjacency (s.fullResample radius).graph d) z j j)⁻¹‖ ≤ L)
    (hGI : ∀ j, (green (normalizedAdjacency s.graph d) z j j).im ≤ I)
    (hFI : ∀ j, (green (normalizedAdjacency (s.fullResample radius).graph d) z j j).im ≤ I) :
    ‖cavityAverage s.graph d z - cavityAverage (s.fullResample radius).graph d z‖ ≤
      ((Fintype.card V : ℝ) * (d : ℝ))⁻¹ *
        (((d : ℝ) * (1 + C * L) ^ 2 * I / z.im) *
            (8 * (Nat.card (BoundaryOrientedEdge s.graph T) : ℝ) / Real.sqrt ((d : ℝ) - 1)) +
          8 * (Nat.card (BoundaryOrientedEdge s.graph T) : ℝ) * (C + C ^ 2 * L)) := by
  apply (cavityAverage_graph_difference_ward s.graph (s.fullResample radius).graph d
    hregular z hz C L I hC hL hG hF hGi hFi hGI hFI).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add
    (mul_le_mul_of_nonneg_left (s.fullResample_normalized_difference_mass_le radius d) (by positivity))
    (mul_le_mul_of_nonneg_right (s.fullResample_adjacencyDisagreement_le radius) (by positivity))

/-- A uniform actual entry cap also supplies the imaginary-part cap. -/
theorem fullResample_cavityAverage_difference_uniform (s : LabelledResamplingState V T ι)
    (radius d : ℕ) (hregular : s.graph.IsRegularOfDegree d)
    (z : ℂ) (hz : 0 < z.im) (C L : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hG : ∀ i j, ‖green (normalizedAdjacency s.graph d) z i j‖ ≤ C)
    (hF : ∀ i j, ‖green (normalizedAdjacency (s.fullResample radius).graph d) z i j‖ ≤ C)
    (hGi : ∀ j, ‖(green (normalizedAdjacency s.graph d) z j j)⁻¹‖ ≤ L)
    (hFi : ∀ j, ‖(green (normalizedAdjacency (s.fullResample radius).graph d) z j j)⁻¹‖ ≤ L) :
    ‖cavityAverage s.graph d z - cavityAverage (s.fullResample radius).graph d z‖ ≤
      ((Fintype.card V : ℝ) * (d : ℝ))⁻¹ *
        (((d : ℝ) * (1 + C * L) ^ 2 * C / z.im) *
            (8 * (Nat.card (BoundaryOrientedEdge s.graph T) : ℝ) / Real.sqrt ((d : ℝ) - 1)) +
          8 * (Nat.card (BoundaryOrientedEdge s.graph T) : ℝ) * (C + C ^ 2 * L)) :=
  s.fullResample_cavityAverage_difference radius d hregular z hz C L C hC hL hC hG hF hGi hFi
    (fun j => ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans (hG j j))
    (fun j => ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans (hF j j))

end LabelledResamplingState
end
end LocalLaw
