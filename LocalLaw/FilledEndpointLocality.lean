import LocalLaw.SwitchedRetainedReference
import LocalLaw.SourceRetainedExpansion
import LocalLaw.PairRestrictionIdentity

/-! # Exact capture of inner local models by the full endpoint model -/

noncomputable section
namespace LocalLaw
local instance filledEndpointLocalityDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type}

def filledInnerVertex (T : Set V) (K : Set (Tᶜ : Set V)) (x : T) : filledExteriorVertices T K :=
  ⟨x.val,Or.inl x.property⟩

theorem filled_captures_inner_ball (G : SimpleGraph V) (T : Set V) (K : Set (Tᶜ : Set V)) (r : ℕ)
    (hballs : ∀ a : BoundaryOrientedEdge G T,graphBallVertices (outsideGraph G T)
      (boundaryOutsideVertex G T a) r⊆K) (x : T) :
    graphBallVertices G x.val (r+1)⊆filledExteriorVertices T K := by
  intro y hy
  by_cases hyt : y∈T
  · exact Or.inl hyt
  · obtain ⟨p,hp⟩ := graphBall_exists_walk_length_le G x.val y (r+1) hy
    rcases walk_outside_or_last_exit G T p hyt with ⟨hx,_,_⟩ | ⟨a,pref,q,hlen⟩
    · exact False.elim (hx x.property)
    · exact Or.inr ⟨⟨y,hyt⟩,hballs a ((SimpleGraph.edist_le q).trans
        (ENat.coe_le_coe.mpr (show q.length≤r by omega))),rfl⟩

namespace LabelledResamplingState
variable {T : Set V} {ι : Type} [Fintype ι]

theorem endpointModel_contains_new_boundary_ball (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (a : BoundaryOrientedEdge (s.fullResample selector).graph T) :
    graphBallVertices (outsideGraph (s.fullResample selector).graph T)
      (boundaryOutsideVertex (s.fullResample selector).graph T a) r⊆s.endpointModelVertices selector r := by
  obtain ⟨i,rfl⟩ := (s.fullResample selector).boundary.surjective a
  intro y hy
  rw [s.endpointModelVertices_fullResample selector r]
  refine ⟨boundaryOutsideVertex (s.fullResample selector).graph T ((s.fullResample selector).boundary i),?_,hy⟩
  have he := s.endpointFinalBoundaryRoot_outer selector i
  exact Eq.mp (congrArg (fun v => v ∈ s.endpointModelRoots selector) he)
    (s.endpointFinalBoundaryRoot selector i).property

theorem filledEndpoint_captures_inner_ball (s : LabelledResamplingState V T ι) (selector r : ℕ) (x : T) :
    graphBallVertices (s.fullResample selector).graph x.val (r+1)⊆
      filledExteriorVertices T (s.endpointModelVertices selector r) :=
  filled_captures_inner_ball _ T _ r (s.endpointModel_contains_new_boundary_ball selector r) x

end LabelledResamplingState

namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

/-- The actual pair model is literally the pair restriction of this full
finite model. This identity includes the inherited deficit convention. -/
theorem filledEndpoint_pair_P (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (q z : ℂ) (x y : T) :
    let s := g.admissibleState T labels samples
    let gnew := g.labelledResampledGraph T labels samples selector
    let K := s.endpointModelVertices selector r
    (gnew.filledExteriorModel T K).P r z q (filledInnerVertex T K x) (filledInnerVertex T K y) =
      gnew.P r z q x.val y.val := by
  dsimp only
  let s := g.admissibleState T labels samples
  let gnew := g.labelledResampledGraph T labels samples selector
  let K := s.endpointModelVertices selector r
  have hcapture (v : T) : graphBallVertices gnew.graph v.val r⊆filledExteriorVertices T K :=
    (graphBallVertices_mono gnew.graph v.val (Nat.le_succ r)).trans
      (s.filledEndpoint_captures_inner_ball selector r v)
  exact (gnew.deficient.restrict_pair_P (filledExteriorVertices T K) (filledInnerVertex T K x)
    (filledInnerVertex T K y) r (hcapture x) (hcapture y) q z).trans
      (gnew.deficient_P r z q x.val y.val)

/-- All boundary parameters share the same exact fixed retained reference. -/
theorem switchedFilled_reference_entry (g : RegularGraph N d) (hd : 3≤d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hsep : 2*r+2≤selector) (hr : r+2≤selector)
    (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) (x y : T) :
    let s := g.admissibleState T labels samples
    let gnew := g.labelledResampledGraph T labels samples selector
    let K := s.endpointModelVertices selector r
    (gnew.filledExteriorModel T K).extensionGreen q z (filledInnerVertex T K x) (filledInnerVertex T K y) =
      g.sourceRetainedReference T r q z x y := by
  have hh := g.switched_filled_reference_eq_old_central hd T labels samples selector r hsep hr q z hz hq
  exact congrFun (congrFun hh x) y

end RegularGraph
end LocalLaw
