import LocalLaw.OldEndpointSharpDiameter
import LocalLaw.TwoHubContact

/-! Ambient original-graph geometry of old endpoint components. -/
noncomputable section
namespace LocalLaw
local instance oldEndpointAmbientDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type}

theorem pair_roots_ambient_edist_bound (G : SimpleGraph V) (a b : V) (hab : G.Adj a b)
    (r : ℕ) (u v : V)
    (hu : G.edist a u ≤ (r : ℕ∞) ∨ G.edist b u ≤ (r : ℕ∞))
    (hv : G.edist a v ≤ (r : ℕ∞) ∨ G.edist b v ≤ (r : ℕ∞)) :
    G.edist u v ≤ ((2*r+1 : ℕ) : ℕ∞) := by
  have edge : G.edist a b ≤ 1 := SimpleGraph.edist_le hab.toWalk
  have close (x y z : V) (hx : G.edist x u ≤ (r : ℕ∞))
      (hy : G.edist y v ≤ (r : ℕ∞)) (hxy : G.edist x y ≤ 1) :
      G.edist u v ≤ ((2*r+1 : ℕ) : ℕ∞) := by
    have hh := (SimpleGraph.edist_triangle (G := G) (u := u) (v := x) (w := v)).trans
      (add_le_add (by simpa only [SimpleGraph.edist_comm] using hx)
      ((SimpleGraph.edist_triangle (G := G) (u := x) (v := y) (w := v)).trans (add_le_add hxy hy)))
    exact hh.trans_eq (by push_cast; ring)
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact close a a a hu hv (by simp)
  · exact close a b a hu hv edge
  · exact close b a a hu hv (by simpa only [SimpleGraph.edist_comm] using edge)
  · exact close b b a hu hv (by simp)

namespace RegularGraph
variable {N d : ℕ} {ι : Type*}

/-- Even a large central component lies in the original ball of radius
`ell+r+1`; sampled components lie in their own adjacent two-root cell. -/
theorem endpointModel_old_component_ambient_diameter (g : RegularGraph N d) (o : Fin N)
    (ell selector r : ℕ) (hsep : 2*r+2 ≤ selector)
    (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) :
    let T := graphBallVertices g.graph o ell
    let s := g.admissibleState T boundary samples
    ∀ c : ((outsideGraph s.graph T).induce (s.endpointModelVertices selector r)).ConnectedComponent,
      ∀ u v : (Tᶜ : Set (Fin N)),
      u ∈ liftedComponent (outsideGraph s.graph T) (s.endpointModelVertices selector r) c →
      v ∈ liftedComponent (outsideGraph s.graph T) (s.endpointModelVertices selector r) c →
      g.graph.edist u.val v.val ≤ ((2*r+2*ell+2 : ℕ) : ℕ∞) := by
  dsimp only
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary samples
  let H := outsideGraph s.graph T
  let K := s.endpointModelVertices selector r
  intro c u v hu hv
  obtain ⟨huK,huc⟩ := hu
  obtain ⟨hvK,hvc⟩ := hv
  let uu : K := ⟨u,huK⟩
  let vv : K := ⟨v,hvK⟩
  rcases s.endpointModelVertices_cell_cover selector r u huK with huC | ⟨i,huI⟩
  · have hsub := induced_component_subset_of_closed H K (s.centralEndpointPatch r)
      (s.endpointModel_central_closed selector r hsep) c ⟨uu,huc⟩ huC
    have hvC := hsub ⟨vv,hvc⟩
    have hleft := centralBoundaryVertices_subset_original_ball g.graph o ell r (ell+r+1) le_rfl u huC
    have hright := centralBoundaryVertices_subset_original_ball g.graph o ell r (ell+r+1) le_rfl v hvC
    have hh := (SimpleGraph.edist_triangle (G := g.graph) (u := u.val) (v := o) (w := v.val)).trans
      (add_le_add (by simpa only [SimpleGraph.edist_comm] using hleft) hright)
    exact hh.trans_eq (by push_cast; ring)
  · have hsub := induced_component_subset_of_closed H K (s.sampledEndpointPatch selector r i)
      (s.endpointModel_sampled_closed selector r hsep i) c ⟨uu,huc⟩ huI
    have hvI := hsub ⟨vv,hvc⟩
    have huP : H.edist (s.admissibleSampleVertex selector i) u ≤ (r : ℕ∞) ∨
        H.edist (s.admissibleSecondVertex selector i) u ≤ (r : ℕ∞) := by
      rw [s.sampledEndpointPatch_eq_pairBall selector r i] at huI
      exact huI
    have hvP : H.edist (s.admissibleSampleVertex selector i) v ≤ (r : ℕ∞) ∨
        H.edist (s.admissibleSecondVertex selector i) v ≤ (r : ℕ∞) := by
      rw [s.sampledEndpointPatch_eq_pairBall selector r i] at hvI
      exact hvI
    have hnear := pair_roots_ambient_edist_bound H (s.admissibleSampleVertex selector i)
      (s.admissibleSecondVertex selector i) (s.samples (s.boundary i.val)).property.1 r u v huP hvP
    exact ((graphHom_edist_le (SimpleGraph.Embedding.induce (G := g.graph) Tᶜ).toHom u v).trans hnear).trans
      (ENat.coe_le_coe.mpr (by omega))

end RegularGraph
end LocalLaw
