import LocalLaw.SourceMinorPerturbation
import LocalLaw.SourceCorrelationGoodSet

/-!
# Actual old correlations to the other selected surgery endpoints

An isolated source label is uncorrelated with every old boundary root and
every other sampled pair. These literal source relations supply both old
rows needed by the principal-minor surgery comparison.
-/

noncomputable section
namespace LocalLaw
local instance sourceMinorCorrelationsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type*}

theorem source_good_other_exterior_norm_small (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (z : ℂ) (φ : ℝ) (radius : ℕ) (i : ι)
    (hi : labels i ∈ g.sourceCorrelationGoodLabels T z φ radius samples)
    (x : (Tᶜ : Set (Fin N)))
    (hx : ∃ j, j ≠ i ∧ x.val ∈ (sampledSwitchingQuad g.graph T samples (labels j)).exterior)
    (σ : Bool) :
    ‖green (normalizedAdjacency (outsideGraph g.graph T) d) z
      (g.outsideEdgePoint T (samples (labels i)) σ) x‖ ≤ φ := by
  let H := outsideGraph g.graph T
  let own := g.outsideEdgePoint T (samples (labels i)) σ
  have hself (v : (Tᶜ : Set (Fin N))) : v ∈ closedNeighborFinset H v := by simp [closedNeighborFinset]
  have hsymm : (green (normalizedAdjacency H d) z).IsSymm := by
    have hh := (g.deficient.delete T).extensionGreen_isSymm (0 : ℂ) z
    simpa only [DeficientGraph.extensionGreen, DeficientGraph.H, boundaryGreen, boundaryMatrix,
      zero_smul, sub_zero, green] using hh
  obtain ⟨j, hji, hx⟩ := hx
  have hlabels : labels j ≠ labels i := fun h => hji (labels.injective h)
  simp only [sampledSwitchingQuad, SwitchingQuad.exterior, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with ha | hb | hc
  · have hxeq : x = boundaryOutsideVertex g.graph T (labels j) := Subtype.ext ha
    rw [hxeq]
    have hh := g.sourceCorrelationGood_old_norm_small T z φ radius samples (labels i) hi (labels j) σ
      (boundaryOutsideVertex g.graph T (labels j)) own (hself _) (hself _)
    rw [← hsymm.apply (boundaryOutsideVertex g.graph T (labels j)) own] at hh
    exact hh.le
  · have hxeq : x = g.outsideEdgePoint T (samples (labels j)) false := Subtype.ext hb
    rw [hxeq]
    exact (g.sourceCorrelationGood_other_norm_small T z φ radius samples (labels i) hi (labels j)
      hlabels σ false own (g.outsideEdgePoint T (samples (labels j)) false) (hself _) (hself _)).le
  · have hxeq : x = g.outsideEdgePoint T (samples (labels j)) true := Subtype.ext hc
    rw [hxeq]
    exact (g.sourceCorrelationGood_other_norm_small T z φ radius samples (labels i) hi (labels j)
      hlabels σ true own (g.outsideEdgePoint T (samples (labels j)) true) (hself _) (hself _)).le

end RegularGraph
end LocalLaw
