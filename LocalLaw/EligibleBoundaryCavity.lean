import LocalLaw.EligibleCentralIsolation
import LocalLaw.BoundaryDeficitFibers
import LocalLaw.HomogeneousCavityBall
import LocalLaw.OldEndpointComponentCounts
import LocalLaw.SourceCavityTreeIdentity

/-! # The old accepted boundary branch is the exact scalar cavity model

I gives its genuine finite tree, J excludes every other boundary label, and
regularity gives the actual one-root deficit and saturated interior degrees.
-/

noncomputable section
set_option maxHeartbeats 2000000
namespace LocalLaw
local instance eligibleBoundaryCavityDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type*} {T : Set V} {ι : Type*}

theorem eligible_boundary_ball_isTree (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hr : r ≤ selector) (i : s.AdmissibleSampleIndex selector) :
    (graphBall (outsideGraph s.graph T) (boundaryOuterEndpoint s.graph T (s.boundary i.val)) r).IsTree := by
  let H := outsideGraph s.graph T
  let a := boundaryOuterEndpoint s.graph T (s.boundary i.val)
  let X := outsideTripleNeighborhood s.graph T selector s.samples (s.boundary i.val)
  let f : graphBall H a r →g
      ((H ⊔ SimpleGraph.edge a (s.admissibleSampleVertex selector i)).induce X) :=
    { toFun := fun v => ⟨v.val, ⟨a,
        (outsideTriple_mem_iff s.graph T s.samples _ _).mpr (Or.inl rfl),
        v.property.trans (ENat.coe_le_coe.mpr hr)⟩⟩
      map_rel' := fun h => Or.inl h }
  constructor
  · exact graphBall_connected _ _ _
  · intro v p hp
    exact i.property.1.tree.IsAcyclic (p.map f) (hp.map
      (fun _ _ h => Subtype.ext (congrArg (fun x : X => x.val) h)))

theorem eligible_boundary_label_unique_in_ball (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hr : r ≤ selector) (i : s.AdmissibleSampleIndex selector) (v : (Tᶜ : Set V))
    (hv : v ∈ graphBallVertices (outsideGraph s.graph T)
      (boundaryOuterEndpoint s.graph T (s.boundary i.val)) r)
    (β : BoundaryOrientedEdge s.graph T) (hβ : boundaryOuterEndpoint s.graph T β = v) :
    β = s.boundary i.val := by
  by_contra hneq
  have hfar := s.eligible_boundary_root_far selector i β hneq
  rw [hβ] at hfar
  exact not_lt_of_ge (hv.trans (ENat.coe_le_coe.mpr hr)) hfar

end LabelledResamplingState

namespace RegularGraph
variable {N d : ℕ} {ι : Type*}

theorem eligible_boundary_one_root_deficit (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hr : r ≤ selector)
    (i : (g.admissibleState T boundary S).AdmissibleSampleIndex selector)
    (v : (Tᶜ : Set (Fin N))) (hv : v ∈ graphBallVertices (outsideGraph g.graph T)
      (boundaryOuterEndpoint g.graph T (boundary i.val)) r) :
    (g.deficient.delete T).deficit v = if v = boundaryOuterEndpoint g.graph T (boundary i.val) then 1 else 0 := by
  let s := g.admissibleState T boundary S
  have hlabels : ∀ j : ι, (boundary j).val.2 = v.val → j = i.val := by
    intro j hj
    have he := s.eligible_boundary_label_unique_in_ball selector r hr i v hv (boundary j) (Subtype.ext hj)
    exact boundary.injective he
  have hcard := Nat.card_congr (s.boundaryNeighborLabelEquiv v)
  change Nat.card {t : T // g.graph.Adj t.val v.val} =
    Nat.card {j : ι // (boundary j).val.2 = v.val} at hcard
  rw [g.deficient.delete_deficit_eq_removed_neighbors]
  change 0 + Nat.card {t : T // g.graph.Adj t.val v.val} = _
  rw [zero_add, hcard]
  by_cases he : v = boundaryOuterEndpoint g.graph T (boundary i.val)
  · rw [if_pos he]
    let canonical : {j : ι // (boundary j).val.2 = v.val} := ⟨i.val, (congrArg Subtype.val he).symm⟩
    letI : Unique {j : ι // (boundary j).val.2 = v.val} :=
      ⟨⟨canonical⟩, fun j => Subtype.ext (hlabels j.val j.property)⟩
    exact Nat.card_unique
  · rw [if_neg he]
    letI : IsEmpty {j : ι // (boundary j).val.2 = v.val} := ⟨fun j => by
      have hj := hlabels j.val j.property
      apply he
      exact Subtype.ext (by simpa only [hj] using j.property.symm)⟩
    exact Nat.card_of_isEmpty

theorem eligible_boundary_ball_diagonal (g : RegularGraph N d) (hd : 3 ≤ d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hr : r ≤ selector)
    (i : (g.admissibleState T boundary S).AdmissibleSampleIndex selector)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let H := outsideGraph g.graph T
    let a := boundaryOuterEndpoint g.graph T (boundary i.val)
    ((g.deficient.delete T).restrict (graphBallVertices H a r)).extensionGreen q z
      (cavityBallRoot H a r) (cavityBallRoot H a r) = cavityIterate z q (r + 1) := by
  dsimp only
  let s := g.admissibleState T boundary S
  exact (g.deficient.delete T).homogeneous_cavity_ball_diagonal hd _ r
    (s.eligible_boundary_ball_isTree selector r hr i)
    (fun v hv => g.eligible_boundary_one_root_deficit T boundary S selector r hr i v hv)
    (fun v _ => g.deleted_degree_deficit_saturated T v) q z hz hq

end RegularGraph
end LocalLaw
