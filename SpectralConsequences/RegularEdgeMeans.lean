import LocalLaw.GraphConcentration
import LocalLaw.ResolventPole
import LocalLaw.FullRetainedPrecision

/-!
# Exact means of independently sampled regular-graph endpoints

The constant-vector resolvent equation, rather than an independence heuristic,
produces the trivial-eigenvalue pole used in Proposition 7.5.
-/
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
namespace SpectralConsequences
open LocalLaw
local instance regularEdgeMeansDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V]

/-- An oriented edge is exactly its first endpoint and one neighbor. -/
def dartNeighborEquiv (G : SimpleGraph V) : G.Dart ≃ Σ v : V, G.neighborSet v where
  toFun e := ⟨e.fst, ⟨e.snd, e.adj⟩⟩
  invFun e := ⟨(e.1,e.2.val),e.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem dart_sum_first (G : SimpleGraph V) (d : ℕ) (hreg : G.IsRegularOfDegree d)
    (f : V → ℂ) : (∑ e : G.Dart, f e.fst) = (d : ℂ) * ∑ v, f v := by
  have hdegree : ∀ v, G.degree v = d := hreg
  calc
    _ = ∑ e : Σ v : V, G.neighborSet v, f e.1 := by
      apply Fintype.sum_equiv (dartNeighborEquiv G)
      intro _
      rfl
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_const, Finset.card_univ,
        SimpleGraph.card_neighborSet_eq_degree, hdegree, nsmul_eq_mul, Finset.mul_sum]

theorem dart_sum_second (G : SimpleGraph V) (d : ℕ) (hreg : G.IsRegularOfDegree d)
    (f : V → ℂ) : (∑ e : G.Dart, f e.snd) = (d : ℂ) * ∑ v, f v := by
  let rev : G.Dart ≃ G.Dart :=
    { toFun := fun e => ⟨(e.snd,e.fst),e.adj.symm⟩
      invFun := fun e => ⟨(e.snd,e.fst),e.adj.symm⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    _ = ∑ e : G.Dart, f e.fst := by
      apply Fintype.sum_equiv rev
      intro _
      rfl
    _ = _ := dart_sum_first G d hreg f

namespace RegularGraph
variable {N d : ℕ}

/-- Both endpoints of a uniformly drawn oriented edge are genuinely uniform
vertices. This is an exact regularity identity. -/
theorem dart_first_mean (g : LocalLaw.RegularGraph N d) (hN : 0 < N) (hd : 0 < d)
    (f : Fin N → ℂ) :
    finiteComplexMean (fun e : g.graph.Dart => f e.fst) = finiteComplexMean f := by
  have hcount : Fintype.card g.graph.Dart = N*d := by
    simpa only [Nat.card_eq_fintype_card] using g.oriented_edge_count
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have hdn : (d : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  simp only [finiteComplexMean, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_natCast, hcount, Nat.cast_mul, Fintype.card_fin,
    dart_sum_first g.graph d g.regular f]
  field_simp
  ring

theorem dart_second_mean (g : LocalLaw.RegularGraph N d) (hN : 0 < N) (hd : 0 < d)
    (f : Fin N → ℂ) :
    finiteComplexMean (fun e : g.graph.Dart => f e.snd) = finiteComplexMean f := by
  have hcount : Fintype.card g.graph.Dart = N*d := by
    simpa only [Nat.card_eq_fintype_card] using g.oriented_edge_count
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have hdn : (d : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  simp only [finiteComplexMean, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_natCast, hcount, Nat.cast_mul, Fintype.card_fin,
    dart_sum_second g.graph d g.regular f]
  field_simp
  ring

/-- Exact Green row sum at the regular-graph eigenvalue tau. -/
theorem green_row_sum (g : LocalLaw.RegularGraph N d) (z : ℂ) (hz : 0 < z.im)
    (i : Fin N) :
    ∑ j, g.G z i j = (treeEdgeWeight d * (d : ℂ) - z)⁻¹ := by
  have hrow : ∀ j, ∑ k, g.H j k =
      ((Real.sqrt ((d : ℝ)-1))⁻¹ * (d : ℝ) : ℝ) := by
    intro j
    rw [LocalLaw.RegularGraph.H, normalizedAdjacency_complex_row_sum, g.regular j]
    simp only [treeEdgeWeight, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
  have hid := green_constant_row_sum g.H (normalizedAdjacency_isHermitian g.graph d)
    ((Real.sqrt ((d : ℝ)-1))⁻¹ * (d : ℝ)) hrow z hz i
  have hne : treeEdgeWeight d * (d : ℂ) - z ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, treeEdgeWeight, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
      mul_zero, zero_mul, add_zero, zero_sub, Complex.zero_im] at hi
    linarith
  change (∑ j, green g.H z i j) = _
  rw [← one_div (treeEdgeWeight d * (d : ℂ) - z)]
  apply (eq_div_iff hne).2
  simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
    treeEdgeWeight] using hid

/-- Two independent uniform sampled endpoints have the trivial-pole mean.
This is the exact unrestricted counterpart of equation (7.26). -/
theorem independent_second_green_mean (g : LocalLaw.RegularGraph N d)
    (hN : 0 < N) (hd : 0 < d) (z : ℂ) (hz : 0 < z.im) :
    finiteComplexMean (fun e : g.graph.Dart => finiteComplexMean
      (fun f : g.graph.Dart => g.G z e.snd f.snd)) =
      (N : ℂ)⁻¹ * (treeEdgeWeight d * (d : ℂ) - z)⁻¹ := by
  calc
    _ = finiteComplexMean (fun e : g.graph.Dart =>
        finiteComplexMean (fun j : Fin N => g.G z e.snd j)) := by
      congr 1
      funext e
      exact dart_second_mean g hN hd (fun j => g.G z e.snd j)
    _ = finiteComplexMean (fun i : Fin N =>
        finiteComplexMean (fun j : Fin N => g.G z i j)) :=
      dart_second_mean g hN hd (fun i : Fin N => finiteComplexMean (fun j : Fin N => g.G z i j))
    _ = _ := by
      unfold finiteComplexMean
      simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast,
        Fintype.card_fin, green_row_sum g z hz]
      have hn : (N : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hN
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

end RegularGraph
end SpectralConsequences
