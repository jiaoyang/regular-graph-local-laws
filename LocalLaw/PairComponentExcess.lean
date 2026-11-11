import LocalLaw.PairBallGeometry
import LocalLaw.GraphExcessSurgery
import LocalLaw.SourceSpectralEvents

/-!
# Actual pair-model component excess from the structural ball event

Each component of the union of two radius-r balls has intrinsic diameter at
most 4r+1. It embeds into the ambient radius-R ball around any of its vertices
when 4r+1<=R. Excess monotonicity supplies the actual source reference budget
componentwise, including disconnected pair models.
-/

set_option maxHeartbeats 1400000

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance pairComponentDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) canonicalPairComponentMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Every actual component of the pair neighborhood inherits the structural
excess bound, with a true intrinsic-diameter containment argument. -/
theorem pairBall_component_excess_bound (G : SimpleGraph V) (i j : V) (r R ω : ℕ)
    (hmargin : 4 * r + 1 ≤ R) (hballs : ∀ a, graphBallExcess G a R ≤ ω)
    (c : (pairBallGraph G i j r).ConnectedComponent) :
    graphExcess ((pairBallGraph G i j r).induce c.supp) ≤ ω := by
  let H := pairBallGraph G i j r
  have hconn : (H.induce c.supp).Connected := c.connected_induce_supp
  obtain ⟨a, ha⟩ := c.nonempty_supp
  let root : c.supp := ⟨a, ha⟩
  have hcut : ∀ x ∈ c.supp, ∀ y ∉ c.supp, ¬H.Adj x y := by
    intro x hx y hy hxy
    exact hy ((c.mem_supp_congr_adj hxy).mp hx)
  let f : H.induce c.supp →g G :=
    { toFun := fun x => x.val.val
      map_rel' := fun h => h }
  have hball : ∀ x : c.supp, x.val.val ∈ graphBallVertices G a.val R := by
    intro x
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist root x
    have hcap := pairBall_isolated_distance_bound G i j r c.supp hcut root x
    have he := SimpleGraph.edist_le (p.map f)
    simp only [SimpleGraph.Walk.length_map, hp] at he
    exact he.trans (by exact_mod_cast hcap.trans hmargin)
  let e : H.induce c.supp →g graphBall G a.val R :=
    { toFun := fun x => ⟨x.val.val, hball x⟩
      map_rel' := fun h => h }
  have he : Function.Injective e := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : graphBallVertices G a.val R => z.val) h))
  have hmono := connected_embedding_graphExcess_le (H.induce c.supp) (graphBall G a.val R)
    hconn (graphBall_connected G a.val R) e he
  exact hmono.trans (hballs a.val)

namespace RegularGraph
variable {N d : ℕ}

def pairModel (g : RegularGraph N d) (i j : Fin N) (r : ℕ) :
    DeficientGraph (pairBallVertices g.graph i j r) d :=
  g.deficient.restrict (pairBallVertices g.graph i j r)

theorem pairModel_graph (g : RegularGraph N d) (i j : Fin N) (r : ℕ) :
    (g.pairModel i j r).graph = pairBallGraph g.graph i j r := rfl

theorem pairModel_zero_deficit (g : RegularGraph N d) (i j : Fin N) (r : ℕ)
    (v : pairBallVertices g.graph i j r) : (g.pairModel i j r).deficit v = 0 := rfl

/-- The physical pair extension is the same actual deficient model identifier. -/
theorem pairModel_P (g : RegularGraph N d) (i j : Fin N) (r : ℕ) (q z : ℂ) :
    (g.pairModel i j r).extensionGreen q z (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r) =
      g.P r z q i j := g.deficient_P r z q i j

/-- No pair-component reference budget is assumed: it follows from the
actual zero deficit, intrinsic geometry and structural ball bound. -/
theorem pairModel_component_budget (g : RegularGraph N d) (i j : Fin N) (r R : ℕ)
    (hmargin : 4 * r + 1 ≤ R) (hballs : ∀ a, graphBallExcess g.graph a R ≤ finiteOmega d)
    (c : (g.pairModel i j r).graph.ConnectedComponent) :
    (∑ v, ((g.pairModel i j r).restrict c.supp).deficit v) +
      graphExcess ((g.pairModel i j r).restrict c.supp).graph ≤ finiteOmega d := by
  have hzero : ∀ v, ((g.pairModel i j r).restrict c.supp).deficit v = 0 := fun _ => rfl
  simp only [hzero, Finset.sum_const_zero, zero_add]
  exact pairBall_component_excess_bound g.graph i j r R (finiteOmega d) hmargin hballs c

end RegularGraph
end
end LocalLaw
