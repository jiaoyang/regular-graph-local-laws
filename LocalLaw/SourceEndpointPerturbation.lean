import LocalLaw.EmbeddedFiniteRankResolvent
import LocalLaw.SwitchingPerturbationMass
import LocalLaw.ResamplingEdgeAgreement
import LocalLaw.ExteriorResolvent

/-!
# Actual outside endpoint perturbations of labelled resampling

After deleting T, each selected switching changes edges only between its
three exterior vertices. The physical perturbation is therefore supported
on the actual accepted exterior union. Its endpoint row and column sums are
derived from the two graph degree bounds, independently of the sample count.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceEndpointPerturbationDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*}

theorem applySwitches_outside_adj_of_away_left (L : List (SwitchingQuad V)) (G : SimpleGraph V)
    (T : Set V) (hroot : ∀ q ∈ L, q.a ∈ T) (x y : (Tᶜ : Set V))
    (hx : ∀ q ∈ L, x.val ∉ q.exterior) :
    (outsideGraph (applySwitches L G) T).Adj x y ↔ (outsideGraph G T).Adj x y := by
  induction L generalizing G with
  | nil => rfl
  | cons q L ih =>
    rw [applySwitches_cons]
    have hnot : ¬q.footprint.Adj x.val y.val := by
      intro h
      have hs := q.footprint_left_mem_support h
      change x.val = q.a ∨ x.val ∈ q.exterior at hs
      rcases hs with heq | hext
      · exact x.property (heq ▸ hroot q (by simp))
      · exact hx q (by simp) hext
    exact (ih (q.apply G) (fun p hp => hroot p (by simp [hp]))
      (fun p hp => hx p (by simp [hp]))).trans (q.adj_outside_footprint G hnot)

section FiniteMatrices
variable [Fintype V] [DecidableEq V] {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem sum_norm_embedding_le (e : I ↪ V) (f : V → ℂ) :
    (∑ i, ‖f (e i)‖) ≤ ∑ v, ‖f v‖ := by
  calc
    _ = ∑ v ∈ Finset.univ.image e, ‖f v‖ := (Finset.sum_image (fun _ _ _ _ h => e.injective h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => norm_nonneg _)

omit [DecidableEq I] in
theorem normalizedAdjacency_difference_endpoint_row_bound (G F : SimpleGraph V) (d : ℕ)
    (hG : ∀ v, G.degree v ≤ d) (hF : ∀ v, F.degree v ≤ d) (e : I ↪ V) (i : I) :
    (∑ j, ‖((normalizedAdjacency F d - normalizedAdjacency G d).submatrix e e) i j‖) ≤
      2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1) := by
  apply (sum_norm_embedding_le e (fun v => (normalizedAdjacency F d - normalizedAdjacency G d) (e i) v)).trans
  calc
    _ ≤ ∑ v, (‖normalizedAdjacency F d (e i) v‖ + ‖normalizedAdjacency G d (e i) v‖) :=
      Finset.sum_le_sum (fun _ _ => norm_sub_le _ _)
    _ = (F.degree (e i) : ℝ) / Real.sqrt ((d : ℝ) - 1) +
        (G.degree (e i) : ℝ) / Real.sqrt ((d : ℝ) - 1) := by
      rw [Finset.sum_add_distrib, normalizedAdjacency_row_sum, normalizedAdjacency_row_sum]
    _ ≤ (d : ℝ) / Real.sqrt ((d : ℝ) - 1) + (d : ℝ) / Real.sqrt ((d : ℝ) - 1) :=
      add_le_add (div_le_div_of_nonneg_right (Nat.cast_le.mpr (hF (e i))) (Real.sqrt_nonneg _))
        (div_le_div_of_nonneg_right (Nat.cast_le.mpr (hG (e i))) (Real.sqrt_nonneg _))
    _ = _ := by ring

omit [DecidableEq I] in
theorem normalizedAdjacency_difference_endpoint_column_bound (G F : SimpleGraph V) (d : ℕ)
    (hG : ∀ v, G.degree v ≤ d) (hF : ∀ v, F.degree v ≤ d) (e : I ↪ V) (j : I) :
    (∑ i, ‖((normalizedAdjacency F d - normalizedAdjacency G d).submatrix e e) i j‖) ≤
      2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1) := by
  have hsymm : ∀ x y, (normalizedAdjacency F d - normalizedAdjacency G d) x y =
      (normalizedAdjacency F d - normalizedAdjacency G d) y x := by
    intro x y
    simp only [Matrix.sub_apply, normalizedAdjacency, Matrix.smul_apply, smul_eq_mul, SimpleGraph.adjMatrix_apply]
    rw [F.adj_comm, G.adj_comm]
  have hh := normalizedAdjacency_difference_endpoint_row_bound G F d hG hF e j
  simpa only [Matrix.submatrix_apply, hsymm] using hh

end FiniteMatrices

namespace LabelledResamplingState
variable {T : Set V} {ι : Type*} [Fintype ι]

def fullResampleOutsideEndpoints (s : LabelledResamplingState V T ι) (selector : ℕ) : Set (Tᶜ : Set V) :=
  {x | ∃ i, s.Eligible selector i ∧ x.val ∈ (s.quad i).exterior}

theorem fullResample_outside_adj_of_away_left (s : LabelledResamplingState V T ι) (selector : ℕ)
    (x y : (Tᶜ : Set V)) (hx : x ∉ s.fullResampleOutsideEndpoints selector) :
    (outsideGraph (s.fullResample selector).graph T).Adj x y ↔ (outsideGraph s.graph T).Adj x y := by
  rw [s.fullResample_graph_eq_applySwitches selector]
  apply applySwitches_outside_adj_of_away_left
  · intro q hq
    obtain ⟨i, _, _, hqi⟩ := (s.mem_selectedQuads selector _ q).mp hq
    subst q
    exact sampledSwitching_root_mem s.graph T s.samples (s.boundary i)
  · intro q hq hxt
    obtain ⟨i, _, hi, hqi⟩ := (s.mem_selectedQuads selector _ q).mp hq
    subst q
    exact hx ⟨i, hi, hxt⟩

variable [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem fullResample_outside_difference_supported (s : LabelledResamplingState V T ι)
    (selector d : ℕ) (x y : (Tᶜ : Set V))
    (haway : x ∉ s.fullResampleOutsideEndpoints selector ∨ y ∉ s.fullResampleOutsideEndpoints selector) :
    (normalizedAdjacency (outsideGraph (s.fullResample selector).graph T) d -
      normalizedAdjacency (outsideGraph s.graph T) d) x y = 0 := by
  have hagree : (outsideGraph (s.fullResample selector).graph T).Adj x y ↔
      (outsideGraph s.graph T).Adj x y := by
    rcases haway with hx | hy
    · exact s.fullResample_outside_adj_of_away_left selector x y hx
    · rw [(outsideGraph (s.fullResample selector).graph T).adj_comm, (outsideGraph s.graph T).adj_comm]
      exact s.fullResample_outside_adj_of_away_left selector y x hy
  simp only [Matrix.sub_apply, normalizedAdjacency, Matrix.smul_apply, smul_eq_mul, SimpleGraph.adjMatrix_apply]
  rw [hagree, sub_self]

theorem fullResample_outside_endpoint_updates {I : Type*} [Fintype I]
    (s : LabelledResamplingState V T ι) (selector d : ℕ) (e : I ↪ (Tᶜ : Set V))
    (hcapture : s.fullResampleOutsideEndpoints selector ⊆ Set.range e) (z : ℂ) (hz : 0 < z.im) :
    let H := normalizedAdjacency (outsideGraph s.graph T) d
    let K := normalizedAdjacency (outsideGraph (s.fullResample selector).graph T) d
    let R := (green H z).submatrix e e
    let U := (green K z).submatrix e e
    let W := (K - H).submatrix e e
    (U + R * W * U = R) ∧ (U + U * W * R = R) := by
  apply green_embedded_finite_rank_updates _ _ (normalizedAdjacency_isHermitian _ _)
    (normalizedAdjacency_isHermitian _ _) e _ z hz
  intro x y hxy
  apply s.fullResample_outside_difference_supported selector d x y
  exact hxy.imp (fun hx hs => hx (hcapture hs)) (fun hy hs => hy (hcapture hs))

theorem fullResample_outside_endpoint_mass {I : Type*} [Fintype I]
    (s : LabelledResamplingState V T ι) (selector d : ℕ) (hdegree : ∀ v, s.graph.degree v ≤ d)
    (e : I ↪ (Tᶜ : Set V)) :
    let W := (normalizedAdjacency (outsideGraph (s.fullResample selector).graph T) d -
      normalizedAdjacency (outsideGraph s.graph T) d).submatrix e e
    (∀ i, ∑ j, ‖W i j‖ ≤ 2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1)) ∧
      (∀ j, ∑ i, ‖W i j‖ ≤ 2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1)) := by
  have hG : ∀ v, (outsideGraph s.graph T).degree v ≤ d := by
    intro v
    have hh := (induced_degree_le s.graph Tᶜ v).trans (hdegree v.val)
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh ⊢
    exact hh
  have hF : ∀ v, (outsideGraph (s.fullResample selector).graph T).degree v ≤ d := by
    intro v
    have hh := induced_degree_le (s.fullResample selector).graph Tᶜ v
    have heq := s.fullResample_degree selector v.val
    have hmax := hdegree v.val
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh heq hmax ⊢
    exact hh.trans (heq.le.trans hmax)
  exact ⟨normalizedAdjacency_difference_endpoint_row_bound _ _ d hG hF e,
    normalizedAdjacency_difference_endpoint_column_bound _ _ d hG hF e⟩

end LabelledResamplingState
end LocalLaw
