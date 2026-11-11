import LocalLaw.SourceCavityTreeIdentity
import LocalLaw.SourceSingletonObservation
import LocalLaw.CavityDeletionAverage

/-!
# The literal source observation on a good edge

The actual masked random variable Z agrees with the physical outside-edge
cavity value minus the homogeneous finite-tree iterate. Every finite model,
deficit and matrix-minor identification is derived.
-/

noncomputable section
namespace LocalLaw
local instance sourceObservationTreeDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}

theorem sourceSingletonObservation_eq_on_good_edge (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (r farRadius : ℕ) (hmargin : r + 2 ≤ farRadius)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (e : OutsideOrientedEdge g.graph T)
    (hTree : (graphBall g.graph e.val.2 (r + 1)).IsTree)
    (hfar : ∀ α : BoundaryOrientedEdge g.graph T,
      (farRadius : ℕ∞) < (outsideGraph g.graph T).edist
        ⟨e.val.1, e.property.2.1⟩ (boundaryOuterEndpoint g.graph T α)) :
    g.sourceSingletonObservation T r farRadius z q e =
      outsideOrientedCavityValue g.graph d T z e - cavityIterate z q (r + 1) := by
  let D := g.deficient.delete T
  let b : (Tᶜ : Set (Fin N)) := ⟨e.val.1, e.property.2.1⟩
  let c : (Tᶜ : Set (Fin N)) := ⟨e.val.2, e.property.2.2⟩
  let hbc : (outsideGraph g.graph T).Adj b c := e.property.1
  let cc : {v : (Tᶜ : Set (Fin N)) // v ≠ b} := ⟨c, hbc.ne.symm⟩
  have hfar' : ∀ α : BoundaryOrientedEdge g.graph T,
      ((r + 2 : ℕ) : ℕ∞) < (outsideGraph g.graph T).edist b (boundaryOuterEndpoint g.graph T α) := by
    intro α
    exact lt_of_le_of_lt (by exact_mod_cast hmargin) (hfar α)
  have href := g.source_cavity_tree_identity hd T b c hbc r hTree hfar' q z hz hq
  have hphysical : (D.deleteVertex b).G z cc cc = outsideOrientedCavityValue g.graph d T z e := by
    rw [D.deleteVertex_G, outsideOrientedCavityValue_eq_deleted g.graph d T z hz e]
    rfl
  change (if (∀ α : BoundaryOrientedEdge g.graph T,
      (farRadius : ℕ∞) < (outsideGraph g.graph T).edist b (boundaryOuterEndpoint g.graph T α)) then
      (D.deleteVertex b).G z cc cc - (D.deleteVertex b).P r z q cc cc else 0) = _
  rw [if_pos hfar, href, hphysical]

end RegularGraph
end LocalLaw
