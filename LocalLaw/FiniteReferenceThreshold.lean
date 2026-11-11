import LocalLaw.GoodThresholdOne
import LocalLaw.ResolventPole

/-!
# A finite reference threshold with a proved positive maximum

The source's reference class is used only on finite models in this project.
We formulate that class with a relative diagonal lower bound, which remains
valid on the unbounded upper half-plane. A closed complete graph supplies a
finite obstruction, so the class has a largest natural complexity threshold.
No assertion about arbitrary infinite graph operators is made here.
-/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance finiteReferenceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Uniform reference estimates on every finite connected deficient graph
with the specified total deficit-plus-excess budget. -/
def FiniteReferenceThreshold (d ω : ℕ) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (g : DeficientGraph V d),
    g.graph.Connected → (∑ v, g.deficit v) + graphExcess g.graph ≤ ω →
    ∀ (z : ℂ), 0 < z.im →
      (∀ i j, ‖g.extensionGreen (semicircleRoot z) z i j‖ ≤
        C * ‖-semicircleRoot z * treeEdgeWeight d‖ ^ g.graph.dist i j) ∧
      (∀ i j, |(g.extensionGreen (semicircleRoot z) z i j).im| ≤
        C * (kestenMcKayTransform d (semicircleRoot z) z).im) ∧
      (∀ i, ‖kestenMcKayTransform d (semicircleRoot z) z‖ / C ≤
        ‖g.extensionGreen (semicircleRoot z) z i i‖)

theorem finiteReferenceThreshold_mono {d ω ω' : ℕ} (h : FiniteReferenceThreshold d ω)
    (hω : ω' ≤ ω) : FiniteReferenceThreshold d ω' := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hC, fun V _ _ g hconn hbudget z hz => h V g hconn (hbudget.trans hω) z hz⟩

/-- The proved tree, root-deficit tree and unicyclic kernels give a positive
uniform finite threshold with concrete constant 192. -/
theorem finiteReferenceThreshold_one (d : ℕ) (hd : 3 ≤ d) : FiniteReferenceThreshold d 1 := by
  refine ⟨192, by norm_num, ?_⟩
  intro V _ _ g hconn hbudget z hz
  have h := g.finite_good_threshold_one hd hconn hbudget z hz
  refine ⟨?_, h.imaginary, ?_⟩
  · intro i j
    exact (h.entry i j).trans (mul_le_mul_of_nonneg_right
      (by norm_num : (8 : ℝ) ≤ 192) (pow_nonneg (norm_nonneg _) _))
  · intro i
    exact (div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num : (0 : ℝ) < 4)
      (by norm_num : (4 : ℝ) ≤ 192)).trans (h.diagonal i)

/-- Canonical degree counting avoids dependence on the adjacency decision procedure. -/
theorem completeFin_neighbor_card (d : ℕ) (v : Fin (d + 1)) :
    Nat.card ((⊤ : SimpleGraph (Fin (d + 1))).neighborSet v) = d := by
  have h := SimpleGraph.complete_graph_degree v
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h ⊢
  have hfin : Nat.card (Fin (d + 1)) = d + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  simpa only [hfin, Nat.add_sub_cancel] using h

/-- The complete closed d-regular graph carries zero extension boundary. -/
def closedClique (d : ℕ) : DeficientGraph (Fin (d + 1)) d where
  graph := ⊤
  deficit := fun _ => 0
  degree_deficit_le := by
    intro v
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    rw [completeFin_neighbor_card]
    omega

@[simp] theorem closedClique_degree (d : ℕ) (v : Fin (d + 1)) :
    (closedClique d).graph.degree v = d := by
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  exact completeFin_neighbor_card d v

theorem closedClique_boundary_zero (d : ℕ) : (closedClique d).boundaryDiagonal = 0 := by
  have hc : ∀ v, (closedClique d).boundaryCoefficient v = 0 := by
    intro v
    simp only [DeficientGraph.boundaryCoefficient, closedClique_degree]
    change ((d : ℝ) - (0 : ℕ) - (d : ℝ)) / ((d : ℝ) - 1) = 0
    simp
  simp only [DeficientGraph.boundaryDiagonal, hc, Complex.ofReal_zero, Matrix.diagonal_zero]

/-- Its actual finite extension inverse is the closed graph resolvent. -/
theorem closedClique_extensionGreen (d : ℕ) (w z : ℂ) :
    (closedClique d).extensionGreen w z = green (closedClique d).H z := by
  simp only [DeficientGraph.extensionGreen, boundaryGreen, closedClique_boundary_zero,
    smul_zero, sub_zero, green, boundaryMatrix]

/-- The constant eigenvector and eigenvalue are derived from the actual
normalized adjacency row, not supplied as a spectral assumption. -/
theorem closedClique_row_sum (d : ℕ) (i : Fin (d + 1)) :
    (∑ j, (closedClique d).H i j) =
      (((d : ℝ) / Real.sqrt ((d : ℝ) - 1) : ℝ) : ℂ) := by
  simp only [DeficientGraph.H, normalizedAdjacency, Matrix.smul_apply, smul_eq_mul,
    SimpleGraph.adjMatrix_apply]
  rw [← Finset.mul_sum, ← (closedClique d).graph.degree_eq_sum_if_adj (R := ℂ) i,
    closedClique_degree]
  simp only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_inv]
  ring

/-- The clique's complexity is a fixed finite upper obstruction. -/
def finiteReferenceObstruction (d : ℕ) : ℕ := graphExcess (closedClique d).graph

theorem not_finiteReferenceThreshold_obstruction (d : ℕ) (hd : 3 ≤ d) :
    ¬FiniteReferenceThreshold d (finiteReferenceObstruction d) := by
  rintro ⟨C, hC, h⟩
  have hconn : (closedClique d).graph.Connected := SimpleGraph.top_connected
  have hbudget : (∑ v, (closedClique d).deficit v) + graphExcess (closedClique d).graph ≤
      finiteReferenceObstruction d := by simp [closedClique, finiteReferenceObstruction]
  obtain ⟨z, hz, _, i, j, hij⟩ :=
    resolvent_entries_unbounded_near_constant_eigenvalue (closedClique d).H
      (normalizedAdjacency_isHermitian (closedClique d).graph d)
      ((d : ℝ) / Real.sqrt ((d : ℝ) - 1)) (closedClique_row_sum d) C
  have hbound := (h (Fin (d + 1)) (closedClique d) hconn hbudget z hz).1 i j
  have ht : ‖-semicircleRoot z * treeEdgeWeight d‖ ≤ 1 := by
    rw [norm_mul, norm_neg]
    have hm := semicircleRoot_norm_le_one z
    have he : ‖treeEdgeWeight d‖ ≤ 1 := by
      simp only [treeEdgeWeight, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
      apply (inv_le_one₀ (Real.sqrt_pos.mpr (by have hh : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd; linarith))).mpr
      exact Real.one_le_sqrt.mpr (by have hh : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd; linarith)
    nlinarith [norm_nonneg (semicircleRoot z), norm_nonneg (treeEdgeWeight d)]
  have hpow : ‖-semicircleRoot z * treeEdgeWeight d‖ ^ ((closedClique d).graph.dist i j) ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) ht
  rw [closedClique_extensionGreen] at hbound
  have hh := mul_le_mul_of_nonneg_left hpow (show 0 ≤ C by linarith)
  linarith

/-- A largest finite threshold exists and is positive. -/
theorem exists_maximal_finiteReferenceThreshold (d : ℕ) (hd : 3 ≤ d) :
    ∃ ω : ℕ, 1 ≤ ω ∧ FiniteReferenceThreshold d ω ∧
      ∀ ω' : ℕ, FiniteReferenceThreshold d ω' → ω' ≤ ω := by
  let U := finiteReferenceObstruction d
  let good : Finset ℕ := (Finset.range (U + 1)).filter (FiniteReferenceThreshold d)
  have hone := finiteReferenceThreshold_one d hd
  have hU : 1 < U := by
    by_contra hle
    have hh : U ≤ 1 := by omega
    exact not_finiteReferenceThreshold_obstruction d hd (finiteReferenceThreshold_mono hone hh)
  have hmem : 1 ∈ good := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hone⟩
  let hne : good.Nonempty := ⟨1, hmem⟩
  refine ⟨good.max' hne, Finset.le_max' good 1 hmem,
    (Finset.mem_filter.mp (Finset.max'_mem good hne)).2, ?_⟩
  intro ω' hω'
  have hless : ω' < U := by
    by_contra hge
    exact not_finiteReferenceThreshold_obstruction d hd
      (finiteReferenceThreshold_mono hω' (by omega))
  apply Finset.le_max' good ω'
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hω'⟩

/-- The largest good complexity threshold for the finite reference models.
The value below degree three is immaterial to the source theorem. -/
def finiteOmega (d : ℕ) : ℕ :=
  if hd : 3 ≤ d then Classical.choose (exists_maximal_finiteReferenceThreshold d hd) else 0

theorem finiteOmega_positive (d : ℕ) (hd : 3 ≤ d) : 1 ≤ finiteOmega d := by
  unfold finiteOmega
  rw [dif_pos hd]
  exact (Classical.choose_spec (exists_maximal_finiteReferenceThreshold d hd)).1

theorem finiteOmega_good (d : ℕ) (hd : 3 ≤ d) : FiniteReferenceThreshold d (finiteOmega d) := by
  unfold finiteOmega
  rw [dif_pos hd]
  exact (Classical.choose_spec (exists_maximal_finiteReferenceThreshold d hd)).2.1

theorem finiteOmega_maximal (d : ℕ) (hd : 3 ≤ d) (ω : ℕ)
    (hω : FiniteReferenceThreshold d ω) : ω ≤ finiteOmega d := by
  unfold finiteOmega
  rw [dif_pos hd]
  exact (Classical.choose_spec (exists_maximal_finiteReferenceThreshold d hd)).2.2 ω hω

/-- The actual uniform reference constant chosen at the maximal threshold. -/
def finiteReferenceConstant (d : ℕ) : ℝ :=
  if hd : 3 ≤ d then Classical.choose (finiteOmega_good d hd) else 1

theorem finiteReferenceConstant_ge_one (d : ℕ) (hd : 3 ≤ d) :
    1 ≤ finiteReferenceConstant d := by
  unfold finiteReferenceConstant
  rw [dif_pos hd]
  exact (Classical.choose_spec (finiteOmega_good d hd)).1

/-- The source finite models at the constructed maximal threshold have all
three reference estimates, with a fixed degree-dependent constant. -/
theorem finiteOmega_reference_bounds (d : ℕ) (hd : 3 ≤ d)
    {V : Type} [Fintype V] [DecidableEq V] (g : DeficientGraph V d)
    (hconn : g.graph.Connected)
    (hbudget : (∑ v, g.deficit v) + graphExcess g.graph ≤ finiteOmega d)
    (z : ℂ) (hz : 0 < z.im) :
    (∀ i j, ‖g.extensionGreen (semicircleRoot z) z i j‖ ≤
      finiteReferenceConstant d * ‖-semicircleRoot z * treeEdgeWeight d‖ ^ g.graph.dist i j) ∧
    (∀ i j, |(g.extensionGreen (semicircleRoot z) z i j).im| ≤
      finiteReferenceConstant d * (kestenMcKayTransform d (semicircleRoot z) z).im) ∧
    (∀ i, ‖kestenMcKayTransform d (semicircleRoot z) z‖ / finiteReferenceConstant d ≤
      ‖g.extensionGreen (semicircleRoot z) z i i‖) := by
  unfold finiteReferenceConstant
  rw [dif_pos hd]
  exact (Classical.choose_spec (finiteOmega_good d hd)).2 V g hconn hbudget z hz

/-- Diagonal comparability on a bounded spectral domain follows from the
relative bound; it is never asserted with a positive global constant at infinity. -/
theorem finiteOmega_reference_diagonal_bounds (d : ℕ) (hd : 3 ≤ d)
    {V : Type} [Fintype V] [DecidableEq V] (g : DeficientGraph V d)
    (hconn : g.graph.Connected)
    (hbudget : (∑ v, g.deficit v) + graphExcess g.graph ≤ finiteOmega d)
    (z : ℂ) (hz : 0 < z.im) (B : ℝ) (hB : ‖z‖ ≤ B) (i : V) :
    1 / (finiteReferenceConstant d * (B + 2)) ≤
      ‖g.extensionGreen (semicircleRoot z) z i i‖ ∧
      ‖g.extensionGreen (semicircleRoot z) z i i‖ ≤ finiteReferenceConstant d := by
  have h := finiteOmega_reference_bounds d hd g hconn hbudget z hz
  have hC : 0 ≤ finiteReferenceConstant d := by have hh := finiteReferenceConstant_ge_one d hd; linarith
  constructor
  · have hh := div_le_div_of_nonneg_right (kestenMcKay_bounded_norm_lower d hd z hz B hB) hC
    have heq : (1 / (B + 2)) / finiteReferenceConstant d =
        1 / (finiteReferenceConstant d * (B + 2)) := by rw [div_div, mul_comm (B + 2)]
    rw [heq] at hh
    exact hh.trans (h.2.2 i)
  · simpa only [g.graph.dist_self, pow_zero, mul_one] using h.1 i i

end
end LocalLaw
