import LocalLaw.ResamplingParentComponents
import LocalLaw.EvenPatternRestriction

/-!
# Localizing the actual cyclic core through the interior ball

A tree-connected even generator avoiding eligible exterior vertices lies in
one component of the punctured parent tree. A component disjoint from T is
an actual I-forest and cannot contain a nonempty even pattern. Every remaining
component meets T; its unchanged parent paths put the supported vertices in
the original radius-(ell+2r) core ball. Edge agreement is explicit here and is
supplied by the actual resampling schedule in the subsequent specialization.
-/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw

local instance resamplingCoreLocalizationDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {U : Type*} [Fintype U]

omit [Fintype U] in
theorem connected_support_in_cut_component (H : SimpleGraph U) (A S : Set U)
    (hconn : (H.induce S).Connected) (havoid : ∀ x ∈ S, x ∉ A) :
    ∃ C : CutComponent H A, S ⊆ Set.range (fun y : C.supp => y.val.val) := by
  obtain ⟨x⟩ := hconn.nonempty
  let C : CutComponent H A := (outsideGraph H A).connectedComponentMk ⟨x.val, havoid x.val x.property⟩
  refine ⟨C, ?_⟩
  intro v hv
  let f : H.induce S →g outsideGraph H A :=
    { toFun := fun y => ⟨y.val, havoid y.val y.property⟩
      map_rel' := fun h => h }
  obtain ⟨p⟩ := hconn x ⟨v, hv⟩
  have heq := SimpleGraph.ConnectedComponent.sound (p.map f).reverse.reachable
  exact ⟨⟨⟨v, havoid v hv⟩, heq⟩, rfl⟩

namespace LabelledResamplingState
variable {V : Type*} [Fintype V] {T : Set V} {ι : Type*}

theorem even_generator_support_in_original_core (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (hsmall : 2 * r ≤ selector) (center : V)
    (G : SimpleGraph V) (o : V) (ell : ℕ)
    (hT : T ⊆ graphBallVertices G o ell)
    (hremoved : (s.eligibleExteriorInBall selector center r).Nonempty)
    (hagree : ∀ x y : graphBallVertices s.graph center r,
      x ∉ s.eligibleExteriorInBall selector center r →
      y ∉ s.eligibleExteriorInBall selector center r →
      (s.graph.Adj x.val y.val ↔ G.Adj x.val y.val))
    (F : EvenEdgeSubgraph (graphBall s.graph center r))
    (hconn : ((ballHeightParentData s.graph center r).tree.induce F.val.support).Connected)
    (havoid : ∀ x ∈ F.val.support, x ∉ s.eligibleExteriorInBall selector center r)
    (hne : F.val ≠ ⊥) :
    ∀ x ∈ F.val.support, x.val ∈ graphBallVertices G o (ell + 2 * r) := by
  let D := ballHeightParentData s.graph center r
  let A := s.eligibleExteriorInBall selector center r
  have hDB : D.tree ≤ graphBall s.graph center r :=
    D.tree_le _ (ballHeightParentData_parent_adj s.graph center r)
  obtain ⟨C, hsupport⟩ := connected_support_in_cut_component D.tree A F.val.support hconn havoid
  let inc : C.supp ↪ graphBallVertices s.graph center r :=
    ⟨fun y => y.val.val, fun y z h => Subtype.ext (Subtype.ext h)⟩
  have hsupport' : F.val.support ⊆ Set.range inc := hsupport
  have hmeets : ∃ y : C.supp, y.val.val.val ∈ T := by
    by_contra hnone
    have haway : ∀ y : C.supp, y.val.val.val ∉ T := by simpa only [not_exists] using hnone
    have hforest := s.parent_component_acyclic_away_interior selector r hsmall center hremoved C haway
    have hle : F.val.comap inc ≤ s.parentComponentAmbientGraph selector center r C :=
      fun _ _ h => F.property.1 h
    exact hne (even_pattern_eq_bot_of_comap_forest F.val inc hsupport' F.property.2
      (graph_acyclic_of_le hle hforest))
  obtain ⟨t, ht⟩ := hmeets
  intro x hx
  obtain ⟨v, rfl⟩ := hsupport hx
  obtain ⟨p, hp⟩ := C.connected_induce_supp.exists_isPath t v
  let fTree : cutComponentGraph D.tree A C →g D.tree :=
    { toFun := fun y => y.val.val
      map_rel' := fun h => h }
  have hfTree : Function.Injective fTree := by
    intro y z h
    exact Subtype.ext (Subtype.ext h)
  have hlen : p.length ≤ 2 * r := by
    have h := D.path_length_le_twice_height r (ballVertexHeight_le s.graph center r)
      (p.map fTree) (SimpleGraph.Walk.map_isPath_of_injective hfTree hp)
    simpa only [SimpleGraph.Walk.length_map] using h
  let fOld : cutComponentGraph D.tree A C →g G :=
    { toFun := fun y => y.val.val.val
      map_rel' := fun {y z} h => (hagree y.val.val z.val.val y.val.property z.val.property).mp (hDB h) }
  have hold : G.edist t.val.val.val v.val.val.val ≤ ((2 * r : ℕ) : ℕ∞) :=
    (G.edist_le (p.map fOld)).trans (by
      simpa only [SimpleGraph.Walk.length_map] using ENat.coe_le_coe.mpr hlen)
  change G.edist o v.val.val.val ≤ ((ell + 2 * r : ℕ) : ℕ∞)
  calc
    _ ≤ G.edist o t.val.val.val + G.edist t.val.val.val v.val.val.val := G.edist_triangle
    _ ≤ (ell : ℕ∞) + ((2 * r : ℕ) : ℕ∞) := add_le_add (hT ht) hold
    _ = ((ell + 2 * r : ℕ) : ℕ∞) := by simp only [Nat.cast_add]

end LabelledResamplingState
end LocalLaw
