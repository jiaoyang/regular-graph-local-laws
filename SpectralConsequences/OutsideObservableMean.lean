import SpectralConsequences.OutsideEdgeMeans
import LocalLaw.CavityMatrixPerturbation

/-! # The one-edge cavity mean in Proposition 7.5

The observation is a singleton minor of the original full graph, not a
minor of the graph already deleted on T. Its unrestricted mean is exactly Q.
-/
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
namespace SpectralConsequences
open LocalLaw
local instance outsideObservableDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V]

/-- Summing a function over darts equals the adjacency-filtered double sum. -/
theorem dart_sum_function (G : SimpleGraph V) (f : V → V → ℂ) :
    (∑ e : G.Dart, f e.fst e.snd) = ∑ i, ∑ j, if G.Adj i j then f i j else 0 := by
  calc
    _ = ∑ e : Σ i : V, G.neighborSet i, f e.1 e.2.val := by
      apply Fintype.sum_equiv (dartNeighborEquiv G)
      intro _
      rfl
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_filter]
      change (∑ y : G.neighborSet i, f i y.val) =
        ∑ a ∈ Finset.univ.filter (fun a => G.Adj i a), f i a
      exact (Finset.sum_subtype (p := fun a => G.Adj i a)
        (Finset.univ.filter (fun a => G.Adj i a))
        (by intro j; simp only [Finset.mem_filter,Finset.mem_univ,true_and]) (f i)).symm

namespace RegularGraph
variable {N d : ℕ}

/-- Restricting any bounded directed-edge observable to edges outside T has
an explicit removed-vertex-density cost. -/
theorem outside_observable_mean (g : LocalLaw.RegularGraph N d)
    (T : Set (Fin N)) (hN : 0 < N) (hd : 0 < d) (hT : 4*Nat.card T ≤ N)
    (f : g.graph.Dart → ℂ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ e, ‖f e‖ ≤ M) :
    ‖finiteComplexMean (fun e : OutsideOrientedEdge g.graph T => f ⟨e.val,e.property.1⟩) -
        finiteComplexMean f‖ ≤ 4*M*(Nat.card T:ℝ)/(N:ℝ) := by
  let A : g.graph.Dart → Prop := fun e => e.fst ∉ T ∧ e.snd ∉ T
  letI : Nonempty (OutsideOrientedEdge g.graph T) := g.outside_edge_nonempty T hN hd hT
  letI : Nonempty g.graph.Dart := ⟨⟨(Classical.choice (inferInstance : Nonempty
    (OutsideOrientedEdge g.graph T))).val,(Classical.choice (inferInstance : Nonempty
    (OutsideOrientedEdge g.graph T))).property.1⟩⟩
  letI : Nonempty {e : g.graph.Dart // A e} :=
    ⟨(outsideDartEquiv g.graph T) (Classical.choice inferInstance)⟩
  have hres := finiteComplexMean_restriction_difference A f M hM hf
  have heq : finiteComplexMean (fun e : OutsideOrientedEdge g.graph T => f ⟨e.val,e.property.1⟩) =
      finiteComplexMean (fun e : {e : g.graph.Dart // A e} => f e.val) :=
    finiteComplexMean_equiv (outsideDartEquiv g.graph T) (fun e : {e : g.graph.Dart // A e} => f e.val)
  rw [← heq,norm_sub_rev] at hres
  apply hres.trans
  have hc : (Nat.card {e : g.graph.Dart // ¬A e}:ℝ) ≤ 2*(d:ℝ)*(Nat.card T:ℝ) := by
    exact_mod_cast excluded_darts_card g T
  have hcount : (Fintype.card g.graph.Dart:ℝ) = (N:ℝ)*(d:ℝ) := by
    have h := g.oriented_edge_count
    rw [Nat.card_eq_fintype_card] at h
    exact_mod_cast h
  rw [hcount]
  calc
    _ ≤ 2*M*(2*(d:ℝ)*(Nat.card T:ℝ))/((N:ℝ)*(d:ℝ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by
      have hn : (N:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
      have hdn : (d:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hd
      field_simp
      ring

/-- Original singleton-deleted diagonal, written using its exact Schur entry. -/
def fullEdgeCavity (g : LocalLaw.RegularGraph N d) (z : ℂ) (e : g.graph.Dart) : ℂ :=
  matrixCavityTerm (g.G z) e.snd e.fst

theorem fullEdgeCavity_eq_minor (g : LocalLaw.RegularGraph N d) (z : ℂ) (hz : 0 < z.im)
    (e : g.graph.Dart) :
    fullEdgeCavity g z e = g.minorG e.fst z ⟨e.snd,e.adj.ne.symm⟩ ⟨e.snd,e.adj.ne.symm⟩ := by
  rw [LocalLaw.RegularGraph.minorG, LocalLaw.RegularGraph.minorH, LocalLaw.RegularGraph.H,
    green_deleted_vertex _ (normalizedAdjacency_isHermitian g.graph d) z hz e.fst]
  rfl

/-- The exact full directed-edge mean is the actual cavity average Q. -/
theorem fullEdgeCavity_mean (g : LocalLaw.RegularGraph N d) (z : ℂ) (hz : 0 < z.im) :
    finiteComplexMean (fullEdgeCavity g z) = g.Q z := by
  have hcount : Fintype.card g.graph.Dart = N*d := by
    simpa only [Nat.card_eq_fintype_card] using g.oriented_edge_count
  rw [LocalLaw.RegularGraph.Q, cavityAverage_eq_matrixCavityTerm g.graph d z hz]
  unfold finiteComplexMean fullEdgeCavity
  rw [dart_sum_function g.graph (fun i j => matrixCavityTerm (g.G z) j i)]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast,
    hcount, Nat.cast_mul, Fintype.card_fin, Complex.ofReal_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [g.graph.adj_comm]
  rfl

/-- Equation (7.22) with an explicit cap and exact finite normalization. -/
theorem outside_full_cavity_mean (g : LocalLaw.RegularGraph N d)
    (T : Set (Fin N)) (hN : 0 < N) (hd : 0 < d) (hT : 4*Nat.card T ≤ N)
    (z : ℂ) (hz : 0 < z.im) (C P : ℝ) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hG : ∀ i j, ‖g.G z i j‖ ≤ C) (hGi : ∀ i, ‖(g.G z i i)⁻¹‖ ≤ P) :
    ‖finiteComplexMean (fun e : OutsideOrientedEdge g.graph T =>
        fullEdgeCavity g z ⟨e.val,e.property.1⟩) - g.Q z‖ ≤
      4*(C+C^2*P)*(Nat.card T:ℝ)/(N:ℝ) := by
  rw [← fullEdgeCavity_mean g z hz]
  apply outside_observable_mean g T hN hd hT _ (C+C^2*P) (by positivity)
  intro e
  exact matrixCavityTerm_norm_bound _ C P hC hP hG hGi e.snd e.fst

end RegularGraph
end SpectralConsequences
