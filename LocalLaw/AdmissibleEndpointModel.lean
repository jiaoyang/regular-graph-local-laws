import LocalLaw.AdmissibleEndpointPatches
import LocalLaw.AdmissibleGreenBlock
import LocalLaw.IsolatedCellBudget
import LocalLaw.CoreAttachments

/-! # The actual endpoint-only finite reference model

The central boundary patch is a genuine connected-deletion restriction of
one original small ball. Every selected sampled pair patch is a zero-deficit
tree. Their proved old separation makes each component belong to one cell,
so the full endpoint model has a derived componentwise finite budget.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw

local instance admissibleEndpointModelDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) canonicalAdmissibleEndpointModelMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _

namespace RegularGraph
variable {N d : ℕ} {ι : Type*}

def endpointModel (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) :=
  (g.deficient.delete T).restrict ((g.admissibleState T boundary S).endpointModelVertices selector r)

theorem centralEndpointPatch_component_budget (g : RegularGraph N d) (o : Fin N)
    (ell r R : ℕ) (hmargin : ell + r + 1 ≤ R)
    (hbudget : graphBallExcess g.graph o R ≤ finiteOmega d)
    (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) :
    ((g.deficient.delete (graphBallVertices g.graph o ell)).restrict
      ((g.admissibleState (graphBallVertices g.graph o ell) boundary S).centralEndpointPatch r)).ComponentFiniteReferenceBudget := by
  let T := graphBallVertices g.graph o ell
  let H := outsideGraph g.graph T
  let s := g.admissibleState T boundary S
  let M := graphBallVertices g.graph o (ell + r + 1)
  have hTM : T ⊆ M := graphBallVertices_mono g.graph o (by omega)
  have hKM : ∀ v ∈ s.centralEndpointPatch r, v.val ∈ M := by
    rintro v ⟨a, ⟨α, rfl⟩, hd⟩
    have hhead : α.val.2 ∈ graphBallVertices g.graph o (ell + 1) :=
      adjacent_inner_mem_outer_ball g.graph o le_rfl α.property.2.1 α.property.1
    have htail := (graphHom_edist_le (SimpleGraph.Embedding.induce (G := g.graph) Tᶜ).toHom
      (boundaryOuterEndpoint g.graph T α) v).trans hd
    apply ((SimpleGraph.edist_triangle (G := g.graph) (u := o) (v := α.val.2)).trans
      (add_le_add hhead htail)).trans_eq
    exact_mod_cast (show ell + 1 + r = ell + r + 1 by omega)
  have hMbudget : graphExcess (g.graph.induce M) ≤ finiteOmega d :=
    (graphBallExcess_mono_radius g.graph o hmargin).trans hbudget
  exact g.deficient.deleted_restriction_componentFiniteReferenceBudget M T (fun _ => rfl)
    (graphBall_connected g.graph o _) (graphBall_connected g.graph o ell) hTM hMbudget
    (s.centralEndpointPatch r) hKM

theorem sampledEndpointPatch_base_budget (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hmargin : r + 1 ≤ selector)
    (i : (g.admissibleState T boundary S).AdmissibleSampleIndex selector) :
    let M := (g.deficient.delete T).restrict ((g.admissibleState T boundary S).sampledEndpointPatch selector r i)
    (∑ v, M.deficit v) + graphExcess M.graph ≤ finiteOmega d := by
  let s := g.admissibleState T boundary S
  let H := outsideGraph g.graph T
  let K := s.sampledEndpointPatch selector r i
  let M := (g.deficient.delete T).restrict K
  have htree : M.graph.IsTree := s.sampledEndpointPatch_isTree selector r (by omega) i
  have hzero : ∀ v, M.deficit v = 0 := by
    intro v
    have hv : v.val ∈ pairBallVertices H (s.admissibleSampleVertex selector i)
        (s.admissibleSecondVertex selector i) r := by
      change v.val ∈ pairBallVertices (outsideGraph s.graph T) (s.admissibleSampleVertex selector i)
        (s.admissibleSecondVertex selector i) r
      rw [← s.sampledEndpointPatch_eq_pairBall selector r i]
      exact v.property
    have hd := pairBall_subset_succ_of_eq_or_adjacent H (s.admissibleSampleVertex selector i)
      (s.admissibleSecondVertex selector i) r
      (Or.inr (show H.Adj _ _ from (S (boundary i.val)).property.1)) hv
    exact g.boundaryFarOutside_zero_deficit T selector (s.admissibleSampleVertex selector i)
      (s.admissibleSampleVertex_far_boundary selector i) v.val
      (hd.trans (ENat.coe_le_coe.mpr hmargin))
  have hex : graphExcess M.graph = 0 := tree_graphExcess_zero M.graph htree
  change (∑ v, M.deficit v) + graphExcess M.graph ≤ finiteOmega d
  simp only [hzero, Finset.sum_const_zero, zero_add, hex]
  exact Nat.zero_le _

theorem endpointModel_component_budget (g : RegularGraph N d) (o : Fin N)
    (ell selector r R : ℕ) (hcentral : ell + r + 1 ≤ R) (hsep : 2 * r + 2 ≤ selector)
    (hbudget : graphBallExcess g.graph o R ≤ finiteOmega d)
    (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) :
    (g.endpointModel (graphBallVertices g.graph o ell) boundary S selector r).ComponentFiniteReferenceBudget := by
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary S
  let H := outsideGraph g.graph T
  let D := g.deficient.delete T
  let cell : Option (s.AdmissibleSampleIndex selector) → Set (Tᶜ : Set (Fin N)) :=
    fun i => match i with
      | none => s.centralEndpointPatch r
      | some i => s.sampledEndpointPatch selector r i
  have hcover : ∀ v ∈ s.endpointModelVertices selector r, ∃ i, v ∈ cell i := by
    rintro v ⟨a, ha, hd⟩
    rcases ha with ha | ha
    · exact ⟨none, a, ha, hd⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
      exact ⟨some i, a, hi, hd⟩
  have hcross : ∀ i j, i ≠ j → ∀ v ∈ cell i, ∀ w ∈ cell j, ¬D.graph.Adj v w := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j => exact (s.central_sampledEndpointPatch_disjoint_no_edge selector r hsep j).2
    | some i =>
      cases j with
      | none =>
        intro v hv w hw hvw
        exact (s.central_sampledEndpointPatch_disjoint_no_edge selector r hsep i).2 w hw v hv hvw.symm
      | some j => exact (s.sampledEndpointPatches_disjoint_no_edge selector r (by omega) i j
          (fun h => hij (congrArg some h))).2
  have hcells : ∀ i, (D.restrict (cell i)).ComponentFiniteReferenceBudget := by
    intro i
    cases i with
    | none => exact g.centralEndpointPatch_component_budget o ell r R hcentral hbudget boundary S
    | some i =>
      intro c
      have htree := s.sampledEndpointPatch_isTree selector r (by omega) i
      have hb := g.sampledEndpointPatch_base_budget T boundary S selector r (by omega) i
      exact (D.restrict (cell (some i))).restrict_finiteReferenceBudget c.supp htree.isConnected
        c.connected_induce_supp (Or.inl hb)
  exact D.componentFiniteBudget_of_isolated_cover (s.endpointModelVertices selector r) cell hcover hcross hcells

end RegularGraph
end LocalLaw
