import LocalLaw.OldFullEndpointGeometry
import LocalLaw.OldEndpointAmbientDiameter

/-! # Ambient diameter of every old full endpoint component -/

noncomputable section
namespace LocalLaw
local instance fullOldComponentAmbientDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type}

theorem fullEndpoint_old_component_ambient_diameter (g : RegularGraph N d)
    (o : Fin N) (ell selector r : ℕ) (hsep : 2*r+2 ≤ selector)
    (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) :
    let T := graphBallVertices g.graph o ell
    let s := g.admissibleState T labels samples
    let K := filledExteriorVertices T (s.endpointModelVertices selector r)
    ∀ c : (g.graph.induce K).ConnectedComponent, ∀ u v : Fin N,
      u ∈ liftedComponent g.graph K c → v ∈ liftedComponent g.graph K c →
      g.graph.edist u v ≤ ((2*r+2*ell+2 : ℕ) : ℕ∞) := by
  dsimp only
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T labels samples
  let K := filledExteriorVertices T (s.endpointModelVertices selector r)
  let L := filledExteriorVertices T (s.centralEndpointPatch r)
  have hL : L = graphBallVertices g.graph o (ell+r+1) := filled_centralBoundary_eq_ball g.graph o ell r
  intro c u v hu hv
  obtain ⟨huK,huc⟩ := hu
  obtain ⟨hvK,hvc⟩ := hv
  let uu : K := ⟨u,huK⟩
  let vv : K := ⟨v,hvK⟩
  by_cases huL : u ∈ L
  · have hsub := induced_component_subset_of_closed s.graph K L
      (s.fullEndpoint_old_core_closed selector r hsep) c ⟨uu,huc⟩ huL
    have hvL := hsub ⟨vv,hvc⟩
    have huB := hL ▸ huL
    have hvB := hL ▸ hvL
    have hh := (SimpleGraph.edist_triangle (G := g.graph) (u := u) (v := o) (w := v)).trans
      (add_le_add (by simpa only [SimpleGraph.edist_comm] using huB) hvB)
    exact hh.trans_eq (by push_cast; ring)
  · have huT : u ∉ T := fun ht => huL (Or.inl ht)
    let ua : (Tᶜ : Set (Fin N)) := ⟨u,huT⟩
    have huOut := (filledExterior_outside_mem T (s.endpointModelVertices selector r) ua).mp huK
    rcases s.endpointModelVertices_cell_cover selector r ua huOut with hcentral | ⟨i,hi⟩
    · exact False.elim (huL (Or.inr ⟨ua,hcentral,rfl⟩))
    · have hsub := induced_component_subset_of_closed s.graph K (s.fullSampledPatch selector r i)
        (s.fullEndpoint_old_sampled_closed selector r hsep i) c ⟨uu,huc⟩ ⟨ua,hi,rfl⟩
      obtain ⟨va,hva,hveq⟩ := hsub ⟨vv,hvc⟩
      have huPair := hi
      have hvPair := hva
      rw [s.sampledEndpointPatch_eq_pairBall selector r i] at huPair hvPair
      have hh := pair_roots_ambient_edist_bound (outsideGraph s.graph T)
        (s.admissibleSampleVertex selector i) (s.admissibleSecondVertex selector i)
        (s.samples (s.boundary i.val)).property.1 r ua va huPair hvPair
      have hfull := (graphHom_edist_le (SimpleGraph.Embedding.induce (G := s.graph) Tᶜ).toHom ua va).trans hh
      change s.graph.edist ua.val va.val ≤ _ at hfull
      rw [hveq] at hfull
      exact hfull.trans (ENat.coe_le_coe.mpr (by omega))

end RegularGraph
end LocalLaw
