import LocalLaw.CavitySwitchingEdgeCaps
import LocalLaw.SwitchingQParameters

/-!
# Actual Q-change absorption from old and new edge Green caps

The literal switching schedule and graph/matrix perturbation counts are
combined with the local-cap Ward comparison. The source logarithmic scale
absorbs its genuine Q change; only union-adjacency caps are required for the new matrix.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance switchingQEdgeParametersDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace LabelledResamplingState
variable {T : Set V} {ι : Type*} [Fintype ι]

theorem fullResample_cavityAverage_difference_edges (s : LabelledResamplingState V T ι)
    (radius d : ℕ) (hregular : s.graph.IsRegularOfDegree d)
    (z : ℂ) (hz : 0 < z.im) (C L I : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) (hI : 0 ≤ I)
    (hGd : ∀ i, ‖green (normalizedAdjacency s.graph d) z i i‖ ≤ C)
    (hGe : ∀ i j, s.graph.Adj i j → ‖green (normalizedAdjacency s.graph d) z i j‖ ≤ C)
    (hFd : ∀ i, ‖green (normalizedAdjacency (s.fullResample radius).graph d) z i i‖ ≤ C)
    (hFe : ∀ i j, (s.graph ⊔ (s.fullResample radius).graph).Adj i j →
      ‖green (normalizedAdjacency (s.fullResample radius).graph d) z i j‖ ≤ C)
    (hGi : ∀ j, ‖(green (normalizedAdjacency s.graph d) z j j)⁻¹‖ ≤ L)
    (hFi : ∀ j, ‖(green (normalizedAdjacency (s.fullResample radius).graph d) z j j)⁻¹‖ ≤ L)
    (hGI : ∀ j, (green (normalizedAdjacency s.graph d) z j j).im ≤ I)
    (hFI : ∀ j, (green (normalizedAdjacency (s.fullResample radius).graph d) z j j).im ≤ I) :
    ‖cavityAverage s.graph d z - cavityAverage (s.fullResample radius).graph d z‖ ≤
      ((Fintype.card V : ℝ) * (d : ℝ))⁻¹ *
        (((d : ℝ) * (1 + C * L) ^ 2 * I / z.im) *
            (8 * (Nat.card (BoundaryOrientedEdge s.graph T) : ℝ) / Real.sqrt ((d : ℝ) - 1)) +
          8 * (Nat.card (BoundaryOrientedEdge s.graph T) : ℝ) * (C + C ^ 2 * L)) := by
  apply (cavityAverage_graph_difference_union_local_ward s.graph (s.fullResample radius).graph d
    hregular z hz C L I hC hL hGd hGe hFd hFe hGi hFi hGI hFI).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add
    (mul_le_mul_of_nonneg_left (s.fullResample_normalized_difference_mass_le radius d) (by positivity))
    (mul_le_mul_of_nonneg_right (s.fullResample_adjacencyDisagreement_le radius) (by positivity))

/-- A uniform actual entry cap also supplies the imaginary-part cap. -/
theorem fullResample_cavityAverage_difference_edges_uniform (s : LabelledResamplingState V T ι)
    (radius d : ℕ) (hregular : s.graph.IsRegularOfDegree d)
    (z : ℂ) (hz : 0 < z.im) (C L : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hGd : ∀ i, ‖green (normalizedAdjacency s.graph d) z i i‖ ≤ C)
    (hGe : ∀ i j, s.graph.Adj i j → ‖green (normalizedAdjacency s.graph d) z i j‖ ≤ C)
    (hFd : ∀ i, ‖green (normalizedAdjacency (s.fullResample radius).graph d) z i i‖ ≤ C)
    (hFe : ∀ i j, (s.graph ⊔ (s.fullResample radius).graph).Adj i j →
      ‖green (normalizedAdjacency (s.fullResample radius).graph d) z i j‖ ≤ C)
    (hGi : ∀ j, ‖(green (normalizedAdjacency s.graph d) z j j)⁻¹‖ ≤ L)
    (hFi : ∀ j, ‖(green (normalizedAdjacency (s.fullResample radius).graph d) z j j)⁻¹‖ ≤ L) :
    ‖cavityAverage s.graph d z - cavityAverage (s.fullResample radius).graph d z‖ ≤
      ((Fintype.card V : ℝ) * (d : ℝ))⁻¹ *
        (((d : ℝ) * (1 + C * L) ^ 2 * C / z.im) *
            (8 * (Nat.card (BoundaryOrientedEdge s.graph T) : ℝ) / Real.sqrt ((d : ℝ) - 1)) +
          8 * (Nat.card (BoundaryOrientedEdge s.graph T) : ℝ) * (C + C ^ 2 * L)) :=
  s.fullResample_cavityAverage_difference_edges radius d hregular z hz C L C hC hL hC hGd hGe hFd hFe hGi hFi
    (fun j => ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans (hGd j))
    (fun j => ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans (hFd j))

theorem eventually_fullResample_cavity_change_edges_small (a b d : ℕ) (C L B M : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (T : Set (Fin N)) (ι : Type) [Fintype ι]
      (s : LabelledResamplingState (Fin N) T ι) (radius r : ℕ) (z : ℂ),
      s.graph.IsRegularOfDegree d → 0 < z.im → ‖z‖ ≤ B →
      Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      (Nat.card (BoundaryOrientedEdge s.graph T) : ℝ) ≤ M * Real.log (N : ℝ) ^ (2 * a) →
      (∀ i, ‖green (normalizedAdjacency s.graph d) z i i‖ ≤ C) →
      (∀ i j, s.graph.Adj i j → ‖green (normalizedAdjacency s.graph d) z i j‖ ≤ C) →
      (∀ i, ‖green (normalizedAdjacency (s.fullResample radius).graph d) z i i‖ ≤ C) →
      (∀ i j, (s.graph ⊔ (s.fullResample radius).graph).Adj i j →
        ‖green (normalizedAdjacency (s.fullResample radius).graph d) z i j‖ ≤ C) →
      (∀ j, ‖(green (normalizedAdjacency s.graph d) z j j)⁻¹‖ ≤ L) →
      (∀ j, ‖(green (normalizedAdjacency (s.fullResample radius).graph d) z j j)⁻¹‖ ≤ L) →
      ‖cavityAverage s.graph d z - cavityAverage (s.fullResample radius).graph d z‖ ≤
        graphPaperError a d N r z / Real.log (N : ℝ) ^ 16 := by
  have hK := switchingQConstant_nonnegative C L B hC hL hB
  filter_upwards [eventually_switching_change_absorption a b d (switchingQConstant C L B) M
    ha hb hK hM, Filter.eventually_ge_atTop 1] with N habs hN
  intro T ι _ s radius r z hregular hz hzB hscale hμ hGd hGe hFd hFe hGi hFi
  apply habs z r (Nat.card (BoundaryOrientedEdge s.graph T) : ℝ) _ hz hscale hμ
  have hraw := s.fullResample_cavityAverage_difference_edges_uniform radius d hregular z hz C L hC hL hGd hGe hFd hFe hGi hFi
  have hraw' := switching_Q_budget_le N d (Nat.card (BoundaryOrientedEdge s.graph T) : ℝ)
    C L B z.im (by omega) hd (Nat.cast_nonneg _) hC hL hz
    (((le_abs_self z.im).trans (Complex.abs_im_le_norm z)).trans hzB)
  simp only [Fintype.card_fin] at hraw
  exact hraw.trans hraw'

/-- The actual selected-radius boundary count is supplied by sharp graph
counting, so it is no longer an input in this source resampling corollary. -/
theorem eventually_selected_fullResample_cavity_change_edges_small (a b d : ℕ) (C L B : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ∀ (ι : Type) [Fintype ι]
        (s : LabelledResamplingState (Fin N)
          (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)) ι)
        (radius r : ℕ), s.graph = g.graph →
      (∀ i, ‖green (normalizedAdjacency s.graph d) z i i‖ ≤ C) →
      (∀ i j, s.graph.Adj i j → ‖green (normalizedAdjacency s.graph d) z i j‖ ≤ C) →
      (∀ i, ‖green (normalizedAdjacency (s.fullResample radius).graph d) z i i‖ ≤ C) →
      (∀ i j, (s.graph ⊔ (s.fullResample radius).graph).Adj i j →
        ‖green (normalizedAdjacency (s.fullResample radius).graph d) z i j‖ ≤ C) →
      (∀ j, ‖(green (normalizedAdjacency s.graph d) z j j)⁻¹‖ ≤ L) →
      (∀ j, ‖(green (normalizedAdjacency (s.fullResample radius).graph d) z j j)⁻¹‖ ≤ L) →
      ‖g.Q z - cavityAverage (s.fullResample radius).graph d z‖ ≤
        graphPaperError a d N r z / Real.log (N : ℝ) ^ 16 := by
  filter_upwards [eventually_fullResample_cavity_change_edges_small a b d C L B
    ((d : ℝ) * ((d : ℝ) + 1)) ha hb hd hC hL hB (by positivity),
    eventually_actual_boundary_card_log_bound a d hd (by omega)] with N habs hμ
  intro g o z hz hzB hscale ι _ s radius r hs hGd hGe hFd hFe hGi hFi
  have hreg : s.graph.IsRegularOfDegree d := by rw [hs]; exact g.regular
  have hcount : (Nat.card (BoundaryOrientedEdge s.graph
      (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))) : ℝ) ≤
      (d : ℝ) * ((d : ℝ) + 1) * Real.log (N : ℝ) ^ (2 * a) := by
    simpa only [hs] using hμ g o z
  have hh := habs _ ι s radius r z hreg hz hzB hscale hcount hGd hGe hFd hFe hGi hFi
  simpa only [hs, RegularGraph.Q] using hh

end LabelledResamplingState
end LocalLaw
