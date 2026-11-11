import LocalLaw.BoundaryWeightSums
import LocalLaw.FiniteBallCover

/-!
# Actual boundary depth and embedded incidence fibers

An inner endpoint of a ball boundary lies exactly on its last distance layer.
The same depth holds in any induced model containing the entire ball. Mapping
boundary labels into that model still repeats each vertex at most d times.
-/

noncomputable section
namespace LocalLaw
local instance boundaryDepthDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*}

theorem ball_boundary_inner_edist (G : SimpleGraph V) (o : V) (ell : ℕ)
    (e : BoundaryOrientedEdge G (graphBallVertices G o ell)) :
    G.edist o e.val.1 = (ell : ℕ∞) := by
  have hle : G.edist o e.val.1 ≤ (ell : ℕ∞) := e.property.2.1
  have hfinite := ne_top_of_le_ne_top (ENat.coe_ne_top ell) hle
  let n := (G.edist o e.val.1).toNat
  have hn : G.edist o e.val.1 = (n : ℕ∞) := (ENat.coe_toNat hfinite).symm
  have hnle : n ≤ ell := ENat.coe_le_coe.mp (hn ▸ hle)
  by_cases heq : n = ell
  · exact hn.trans (congrArg (fun x : ℕ => (x : ℕ∞)) heq)
  · have hsucc : n + 1 ≤ ell := by omega
    apply False.elim
    apply e.property.2.2
    change G.edist o e.val.2 ≤ (ell : ℕ∞)
    calc
      _ ≤ G.edist o e.val.1 + G.edist e.val.1 e.val.2 := G.edist_triangle
      _ = (n : ℕ∞) + 1 := by rw [hn, SimpleGraph.edist_eq_one_iff_adj.mpr e.property.1]
      _ ≤ (ell : ℕ∞) := by exact_mod_cast hsucc

def inducedBoundaryInner (G : SimpleGraph V) (o : V) (ell : ℕ) (S : Set V)
    (hS : graphBallVertices G o ell ⊆ S)
    (e : BoundaryOrientedEdge G (graphBallVertices G o ell)) : S :=
  ⟨e.val.1, hS e.property.2.1⟩

theorem induced_boundary_inner_distance (G : SimpleGraph V) (o : V) (ell : ℕ) (S : Set V)
    (hS : graphBallVertices G o ell ⊆ S)
    (e : BoundaryOrientedEdge G (graphBallVertices G o ell)) :
    (G.induce S).dist ⟨o, hS (center_mem_graphBall G o ell)⟩ (inducedBoundaryInner G o ell S hS e) = ell := by
  let root : S := ⟨o, hS (center_mem_graphBall G o ell)⟩
  let leaf := inducedBoundaryInner G o ell S hS e
  have hlower : (ell : ℕ∞) ≤ (G.induce S).edist root leaf := by
    have hh := graphHom_edist_le (SimpleGraph.Embedding.induce (G := G) S).toHom root leaf
    change G.edist o e.val.1 ≤ _ at hh
    simpa only [ball_boundary_inner_edist G o ell e] using hh
  obtain ⟨p, hp⟩ := graphBall_walk_from_center G o ell ⟨e.val.1, e.property.2.1⟩
  let f : graphBall G o ell →g G.induce S :=
    { toFun := fun v => ⟨v.val, hS v.property⟩
      map_rel' := fun h => h }
  have hupper : (G.induce S).edist root leaf ≤ (ell : ℕ∞) :=
    ((G.induce S).edist_le (p.map f)).trans (by
      simpa only [SimpleGraph.Walk.length_map] using ENat.coe_le_coe.mpr hp)
  have heq : (G.induce S).edist root leaf = (ell : ℕ∞) := le_antisymm hupper hlower
  change ((G.induce S).edist root leaf).toNat = ell
  rw [heq, ENat.toNat_coe]

variable [Fintype V]

theorem inducedBoundaryInner_fiber_bound (G : SimpleGraph V) (o : V) (ell : ℕ) (S : Set V)
    (hS : graphBallVertices G o ell ⊆ S) (d : ℕ) (hdegree : ∀ v, G.degree v ≤ d) (v : S) :
    Nat.card {e : BoundaryOrientedEdge G (graphBallVertices G o ell) //
      inducedBoundaryInner G o ell S hS e = v} ≤ d := by
  let F : {e : BoundaryOrientedEdge G (graphBallVertices G o ell) //
      inducedBoundaryInner G o ell S hS e = v} →
      {e : BoundaryOrientedEdge G (graphBallVertices G o ell) // e.val.1 = v.val} :=
    fun e => ⟨e.val, congrArg Subtype.val e.property⟩
  have hF : Function.Injective F := by
    intro x y h
    exact Subtype.ext (congrArg (fun w : {e : BoundaryOrientedEdge G (graphBallVertices G o ell) //
      e.val.1 = v.val} => w.val) h)
  exact (Nat.card_le_card_of_injective F hF).trans
    ((boundary_inner_fiber_card G _ v.val).trans (hdegree v.val))

end LocalLaw
