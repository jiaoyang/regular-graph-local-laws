import LocalLaw.TwoBallAugmentation
import LocalLaw.TwoHubEnclosure
import LocalLaw.OldEndpointAmbientDiameter
import LocalLaw.DeletedConnectedBudget
import LocalLaw.EffectiveAugmentedMargins

/-!
# Genuine old two-target augmentation budgets

The endpoint neighborhood can have arbitrarily many isolated sampled
cells. Adding two target balls requires at most three old component
segments in an intrinsic connection. Each actual augmented component is
enclosed in one original strong-radius ball, yielding its finite reference
class without a total-boundary-size factor.
-/
noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance oldTwoTargetDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) oldTwoTargetComponentDecidable
    {A : Type*} (G : SimpleGraph A) (c : G.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _

namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type*}

def twoTargetEndpointVertices (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (x y : (Tᶜ : Set V)) : Set (Tᶜ : Set V) :=
  twoBallAugment (outsideGraph s.graph T) (s.endpointModelVertices selector r) x y r

theorem endpointModelVertices_subset_twoTargetEndpointVertices
    (s : LabelledResamplingState V T ι) (selector r : ℕ) (x y : (Tᶜ : Set V)) :
    s.endpointModelVertices selector r ⊆ s.twoTargetEndpointVertices selector r x y :=
  fun _ hv => Or.inl hv

theorem twoTargetEndpointVertices_contains_pair (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (x y : (Tᶜ : Set V)) :
    pairBallVertices (outsideGraph s.graph T) x y r ⊆ s.twoTargetEndpointVertices selector r x y :=
  fun _ hv => Or.inr hv

end LabelledResamplingState

namespace RegularGraph
variable {N d : ℕ} {ι : Type*}

theorem old_twoTargetEndpoint_distance_bound (g : RegularGraph N d) (hd : 3 ≤ d)
    (o : Fin N) (ell selector r R : ℕ) (hmargin : ell+r+1 ≤ R) (hsep : 2*r+2 ≤ selector)
    (hbudget : graphBallExcess g.graph o R ≤ finiteOmega d)
    (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (x y : ((graphBallVertices g.graph o ell)ᶜ : Set (Fin N))) :
    let T := graphBallVertices g.graph o ell
    let s := g.admissibleState T boundary samples
    ∀ a b : s.twoTargetEndpointVertices selector r x y,
      ((outsideGraph g.graph T).induce (s.twoTargetEndpointVertices selector r x y)).dist a b ≤
        augmentedObservationDiameter d r := by
  dsimp only
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary samples
  apply twoBallAugment_distance_bound (outsideGraph g.graph T) (s.endpointModelVertices selector r)
    x y r ((finiteOmega d+1)*(2*r+1))
  exact g.endpointModel_old_distance_bound_sharp o ell selector r R (finiteOmega d)
    (finiteOmega_positive d hd) hmargin hsep hbudget boundary samples

/-- The class of each OLD augmented component follows from the original
strong-radius excess event. No class for the switched augmentation is
asserted or used. -/
theorem old_twoTargetEndpoint_component_budget (g : RegularGraph N d) (o : Fin N)
    (ell selector r R : ℕ) (hmargin : 7*r+6*ell+8 ≤ R) (hsep : 2*r+2 ≤ selector)
    (hballs : ∀ v, graphBallExcess g.graph v R ≤ finiteOmega d)
    (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (x y : ((graphBallVertices g.graph o ell)ᶜ : Set (Fin N))) :
    let T := graphBallVertices g.graph o ell
    let s := g.admissibleState T boundary samples
    ((g.deficient.delete T).restrict (s.twoTargetEndpointVertices selector r x y)).ComponentFiniteReferenceBudget := by
  dsimp only
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary samples
  let H := outsideGraph g.graph T
  let K := s.endpointModelVertices selector r
  let S := s.twoTargetEndpointVertices selector r x y
  let l := twoBallLeft H K x y r
  let m := twoBallRight H K x y r
  let f : (H.induce S) →g g.graph :=
    { toFun := fun v => v.val.val
      map_rel' := fun h => h }
  have hK : ∀ c : (H.induce K).ConnectedComponent, ∀ u v : S,
      u.val ∈ liftedComponent H K c → v.val ∈ liftedComponent H K c →
      g.graph.edist (f u) (f v) ≤ ((2*r+2*ell+2 : ℕ) : ℕ∞) := by
    intro c u v hu hv
    exact g.endpointModel_old_component_ambient_diameter o ell selector r hsep boundary samples c u.val v.val hu hv
  intro c
  obtain ⟨a,ha,hnear⟩ := twoHub_component_enclosure H K (graphBallVertices H x r) (graphBallVertices H y r)
    g.graph f l m (center_mem_graphBall H x r) (center_mem_graphBall H y r) (2*r+2*ell+2) r hK
    (twoBall_left_radial H K x y r g.graph f) (twoBall_right_radial H K x y r g.graph f) c
  let flat : c.supp → (Tᶜ : Set (Fin N)) := fun v => v.val.val
  have hflat : Function.Injective flat := fun _ _ h => Subtype.ext (Subtype.ext h)
  let C := Set.range flat
  letI : Fintype C := @Subtype.fintype (Tᶜ : Set (Fin N)) (fun v => v ∈ C)
    (fun _ => Classical.propDecidable _) inferInstance
  let e : (((g.deficient.delete T).restrict S).graph.induce c.supp) ≃g
      (g.deficient.delete T).graph.induce C :=
    { toEquiv := Equiv.ofInjective flat hflat
      map_rel_iff' := Iff.rfl }
  have hC : ((outsideGraph g.graph T).induce C).Connected := e.connected_iff.mp c.connected_induce_supp
  have hOld : ∀ v ∈ C, g.graph.edist a.val.val v.val ≤ ((7*r+4*ell+7 : ℕ) : ℕ∞) := by
    rintro _ ⟨v,rfl⟩
    exact (hnear v.val v.property).trans_eq (by congr 1; omega)
  have hfinite := g.deleted_connected_local_finiteReferenceBudget o ell (7*r+4*ell+7) R
    (by omega) hballs a.val C hC hOld
  exact ((g.deficient.delete T).restrict C).finiteReferenceBudget_of_iso
    (((g.deficient.delete T).restrict S).restrict c.supp) e (fun _ => rfl) hfinite

end RegularGraph
end LocalLaw
