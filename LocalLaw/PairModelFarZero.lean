import LocalLaw.ComponentFiniteLocalization

/-! # Actual pair-local extension kernels vanish beyond twice their radius -/

noncomputable section
namespace LocalLaw
local instance pairModelFarZeroDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem P_eq_zero_of_edist_gt (g : DeficientGraph V d) (hd : 3 ≤ d) (r : ℕ)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (i j : V)
    (hfar : ((2 * r + 1 : ℕ) : ℕ∞) < g.graph.edist i j) : g.P r z q i j = 0 := by
  let M := g.restrict (pairBallVertices g.graph i j r)
  let S : Set (pairBallVertices g.graph i j r) := {x | g.graph.edist i x.val ≤ (r : ℕ∞)}
  have hcut : ∀ x ∈ S, ∀ y ∉ S, ¬M.graph.Adj x y := by
    intro x hx y hy hxy
    have hyr : g.graph.edist j y.val ≤ (r : ℕ∞) := y.property.resolve_left hy
    have hxy' : g.graph.Adj x.val y.val := hxy
    have hedge : g.graph.edist x.val y.val ≤ 1 :=
      SimpleGraph.edist_le (SimpleGraph.Walk.cons hxy' SimpleGraph.Walk.nil)
    have hh := (g.graph.edist_triangle (u := i) (v := x.val) (w := j)).trans
      (add_le_add_left (g.graph.edist_triangle (u := x.val) (v := y.val) (w := j)) _)
    have hbound : g.graph.edist i j ≤ (r : ℕ∞) + (1 + (r : ℕ∞)) := hh.trans
      (add_le_add hx (add_le_add hedge (by simpa only [g.graph.edist_comm] using hyr)))
    have hsum : (r : ℕ∞) + (1 + (r : ℕ∞)) = ((2 * r + 1 : ℕ) : ℕ∞) := by
      norm_cast
      omega
    exact (not_lt_of_ge (hbound.trans_eq hsum)) hfar
  have hi : pairBallLeft g.graph i j r ∈ S := by simp [S, pairBallLeft]
  have hj : pairBallRight g.graph i j r ∉ S := by
    intro hh
    have hri : (r : ℕ∞) ≤ ((2 * r + 1 : ℕ) : ℕ∞) := ENat.coe_le_coe.mpr (by omega)
    exact (not_lt_of_ge hh) (hri.trans_lt hfar)
  exact M.extensionGreen_zero_across_cut hd S hcut q z hz hq _ hi _ hj

end DeficientGraph
end LocalLaw
