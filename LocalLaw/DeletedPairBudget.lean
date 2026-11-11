import LocalLaw.DeletedConnectedBudget
import LocalLaw.PairBallGeometry

/-!
# Actual old deleted pair models from the original strong structural event

Every connected pair component has diameter at most 4r+1. Its literal
ambient image therefore satisfies the connected deleted-neighborhood
criterion. This statement deliberately uses the original strong radius;
it does not assert a pair budget from the weaker target eighth-radius event.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance deletedPairBudgetDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) canonicalDeletedPairBudgetMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _
namespace RegularGraph
variable {N d : ℕ}

theorem deleted_pair_component_finiteReferenceBudget (g : RegularGraph N d) (o : Fin N)
    (ell r R : ℕ) (hmargin : 4 * r + 2 * ell + 2 ≤ R)
    (hballs : ∀ v, graphBallExcess g.graph v R ≤ finiteOmega d)
    (i j : ((graphBallVertices g.graph o ell)ᶜ : Set (Fin N))) :
    ((g.deficient.delete (graphBallVertices g.graph o ell)).restrict
      (pairBallVertices (outsideGraph g.graph (graphBallVertices g.graph o ell)) i j r)).ComponentFiniteReferenceBudget := by
  let T := graphBallVertices g.graph o ell
  let H := outsideGraph g.graph T
  let M := (g.deficient.delete T).restrict (pairBallVertices H i j r)
  intro c
  let K : Set (Tᶜ : Set (Fin N)) := (Subtype.val : pairBallVertices H i j r → (Tᶜ : Set (Fin N))) '' c.supp
  letI : DecidablePred (fun v => v ∈ K) := fun _ => Classical.propDecidable _
  letI : Fintype K := Subtype.fintype _
  let e : M.graph.induce c.supp ≃g H.induce K :=
    { toEquiv := Equiv.Set.image (Subtype.val : pairBallVertices H i j r → (Tᶜ : Set (Fin N)))
        c.supp Subtype.val_injective
      map_rel_iff' := Iff.rfl }
  have hK : (H.induce K).Connected := e.connected_iff.mp c.connected_induce_supp
  obtain ⟨a, ha⟩ := c.nonempty_supp
  let root : c.supp := ⟨a, ha⟩
  have hcut : ∀ x ∈ c.supp, ∀ y ∉ c.supp, ¬M.graph.Adj x y := by
    intro x hx y hy hxy
    exact hy ((c.mem_supp_congr_adj hxy).mp hx)
  let f : M.graph.induce c.supp →g g.graph :=
    { toFun := fun x => x.val.val.val
      map_rel' := fun h => h }
  have hOld : ∀ v ∈ K, g.graph.edist a.val.val v.val ≤ ((4 * r + 1 : ℕ) : ℕ∞) := by
    rintro v ⟨w, hw, rfl⟩
    obtain ⟨p, hp⟩ := c.connected_induce_supp.exists_walk_length_eq_dist root ⟨w, hw⟩
    have hdist := pairBall_isolated_distance_bound H i j r c.supp hcut root ⟨w, hw⟩
    have hh := SimpleGraph.edist_le (p.map f)
    simp only [SimpleGraph.Walk.length_map, hp] at hh
    exact hh.trans (ENat.coe_le_coe.mpr hdist)
  have hh := g.deleted_connected_local_finiteReferenceBudget o ell (4 * r + 1) R
    (by omega) hballs a.val K hK hOld
  exact ((g.deficient.delete T).restrict K).finiteReferenceBudget_of_iso (M.restrict c.supp)
    e (fun _ => rfl) hh

end RegularGraph
end LocalLaw
