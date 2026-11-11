import LocalLaw.CavityMinorModelBounds

/-! # A deterministic finite family of all neighbor-deleted cavity weights

The family is indexed by actual neighbors of the fixed old root and has at
most N members. A zero fallback defines the event for small radii; all source
uses eventually have radius at least two and use the genuine minor weights.
-/

noncomputable section
namespace LocalLaw
local instance cavityWeightFamilyDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}

def cavityNeighborInBall (g : RegularGraph N d) (o : Fin N) (ell : ℕ) (hell : 2 ≤ ell)
    (j : g.graph.neighborSet o) : graphBallVertices g.graph o ell :=
  ⟨j.val, by
    change g.graph.edist o j.val ≤ (ell : ℕ∞)
    rw [SimpleGraph.edist_eq_one_iff_adj.mpr j.property]
    exact_mod_cast (show 1 ≤ ell by omega)⟩

def cavityMinorWeights (g : RegularGraph N d) (o : Fin N) (ell : ℕ) (q z : ℂ) :
    g.graph.neighborSet o → BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell) → ℂ :=
  fun j a => if hell : 2 ≤ ell then
    g.truncatedCavityWeight o ell hell (g.cavityNeighborInBall o ell hell j) j.property.symm q z a else 0

theorem cavityNeighborFamily_card_le (g : RegularGraph N d) (o : Fin N) :
    Fintype.card (g.graph.neighborSet o) ≤ N := by
  rw [← Nat.card_eq_fintype_card]
  have hfin : Nat.card (Fin N) = N := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  exact (Nat.card_le_card_of_injective
    (Subtype.val : g.graph.neighborSet o → Fin N) Subtype.val_injective).trans_eq hfin

theorem cavityMinorWeights_eq (g : RegularGraph N d) (o : Fin N) (ell : ℕ) (hell : 2 ≤ ell)
    (q z : ℂ) (j : g.graph.neighborSet o) (a : BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) :
    g.cavityMinorWeights o ell q z j a =
      g.truncatedCavityWeight o ell hell (g.cavityNeighborInBall o ell hell j) j.property.symm q z a := by
  simp only [cavityMinorWeights, dif_pos hell]

theorem cavityMinorWeights_log_bounds (g : RegularGraph N d) (hd : 3 ≤ d) (o : Fin N)
    (ell : ℕ) (hell : 2 ≤ ell) (hTree : (graphBall g.graph o ell).IsTree)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d * coreConvolutionConstant (finiteOmega d + 1) *
      ((((finiteOmega d + 1) * (4 * ell + 1) : ℕ) : ℝ) + 1) ≤ 1 / 2)
    (A L : ℝ) (hA : 0 ≤ A) (hL : 1 ≤ L)
    (hRlog : ((((finiteOmega d + 1) * (4 * ell + 1) : ℕ) : ℝ) + 1) ≤ A * L) :
    (∀ j, ∑ a, ‖g.cavityMinorWeights o ell q z j a‖ ≤
      (8 * (d : ℝ) * finiteExtraReferenceConstant d ^ 2 * A) * L) ∧
    (∀ j, Real.sqrt (∑ a, ‖g.cavityMinorWeights o ell q z j a‖ ^ 2) ≤
      (32 * (d : ℝ) * finiteExtraReferenceConstant d ^ 4 * A + 1) * L / resamplingDecayDenominator d ell) ∧
    (∀ j a, ‖g.cavityMinorWeights o ell q z j a‖ ≤
      4 * finiteExtraReferenceConstant d ^ 2 / resamplingDecayDenominator d ell) := by
  have hw (j : g.graph.neighborSet o) := g.truncatedCavityWeight_log_bounds hd o ell hell
    (g.cavityNeighborInBall o ell hell j) j.property.symm hTree q z hz hq small A L hA hL hRlog
  simp only [cavityMinorWeights, dif_pos hell]
  exact ⟨fun j => (hw j).1, fun j => (hw j).2.1, fun j a => (hw j).2.2 a⟩

end RegularGraph
end LocalLaw
