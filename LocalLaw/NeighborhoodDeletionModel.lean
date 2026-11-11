import LocalLaw.FiniteBallCover
import LocalLaw.PairComponentExcess
import LocalLaw.ComponentwiseReferenceBounds

/-!
# The actual finite neighborhood used before deleting a root ball

The model contains B_(ell+r)(o), B_r(i), and B_r(j). Thus it contains every
radius-r neighborhood of a removed vertex or target vertex. Its actual
components have diameter at most 6*(ell+r)+2, inherit structural excess,
and its inner root ball has exactly the original removed vertex set.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance neighborhoodDeletionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) canonicalNeighborhoodDeletionMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _

variable {V : Type*}

theorem mem_tripleBallVertices (G : SimpleGraph V) (o i j v : V) (r0 r1 r2 : ℕ) :
    v ∈ tripleBallVertices G o i j r0 r1 r2 ↔
      v ∈ graphBallVertices G o r0 ∨ v ∈ graphBallVertices G i r1 ∨ v ∈ graphBallVertices G j r2 := by
  constructor
  · rintro ⟨k, hk⟩
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
    · exact Or.inr (Or.inr hk)
  · rintro (h | h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩

def deletionNeighborhoodVertices (G : SimpleGraph V) (o i j : V) (ell r : ℕ) : Set V :=
  tripleBallVertices G o i j (ell + r) r r

abbrev deletionNeighborhoodGraph (G : SimpleGraph V) (o i j : V) (ell r : ℕ) :=
  G.induce (deletionNeighborhoodVertices G o i j ell r)

def deletionNeighborhoodRoot (G : SimpleGraph V) (o i j : V) (ell r : ℕ) :
    deletionNeighborhoodVertices G o i j ell r :=
  ⟨o, (mem_tripleBallVertices G o i j o (ell + r) r r).mpr
    (Or.inl (center_mem_graphBall G o _))⟩

def deletionNeighborhoodLeft (G : SimpleGraph V) (o i j : V) (ell r : ℕ) :
    deletionNeighborhoodVertices G o i j ell r :=
  ⟨i, (mem_tripleBallVertices G o i j i (ell + r) r r).mpr
    (Or.inr (Or.inl (center_mem_graphBall G i _)))⟩

def deletionNeighborhoodRight (G : SimpleGraph V) (o i j : V) (ell r : ℕ) :
    deletionNeighborhoodVertices G o i j ell r :=
  ⟨j, (mem_tripleBallVertices G o i j j (ell + r) r r).mpr
    (Or.inr (Or.inr (center_mem_graphBall G j _)))⟩

/-- Any induced subgraph containing the whole ambient root ball has exactly
the same root ball at that radius. No acyclicity or global isolation is needed. -/
theorem induced_root_ball_mem (G : SimpleGraph V) (S : Set V) (o : V) (ho : o ∈ S)
    (ell : ℕ) (hball : graphBallVertices G o ell ⊆ S) (v : S) :
    v ∈ graphBallVertices (G.induce S) ⟨o, ho⟩ ell ↔ v.val ∈ graphBallVertices G o ell := by
  constructor
  · intro hv
    exact (graphHom_edist_le (SimpleGraph.Embedding.induce S).toHom ⟨o, ho⟩ v).trans hv
  · intro hv
    obtain ⟨p, hp⟩ := graphBall_walk_from_center G o ell ⟨v.val, hv⟩
    let f : graphBall G o ell →g G.induce S :=
      { toFun := fun x => ⟨x.val, hball x.property⟩
        map_rel' := fun h => h }
    have hh := SimpleGraph.edist_le (p.map f)
    exact hh.trans (by simpa only [SimpleGraph.Walk.length_map] using ENat.coe_le_coe.mpr hp)

theorem induced_root_ball_image (G : SimpleGraph V) (S : Set V) (o : V) (ho : o ∈ S)
    (ell : ℕ) (hball : graphBallVertices G o ell ⊆ S) :
    (Subtype.val : S → V) '' graphBallVertices (G.induce S) ⟨o, ho⟩ ell = graphBallVertices G o ell := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (induced_root_ball_mem G S o ho ell hball x).mp hx
  · intro hv
    exact ⟨⟨v, hball hv⟩, (induced_root_ball_mem G S o ho ell hball _).mpr hv, rfl⟩

theorem deletionNeighborhood_contains_root_ball (G : SimpleGraph V) (o i j : V) (ell r : ℕ) :
    graphBallVertices G o ell ⊆ deletionNeighborhoodVertices G o i j ell r := by
  intro v hv
  exact (mem_tripleBallVertices G o i j v (ell + r) r r).mpr
    (Or.inl (graphBallVertices_mono G o (Nat.le_add_right _ _) hv))

theorem deletionNeighborhood_inner_ball_image (G : SimpleGraph V) (o i j : V) (ell r : ℕ) :
    (Subtype.val : deletionNeighborhoodVertices G o i j ell r → V) ''
      graphBallVertices (deletionNeighborhoodGraph G o i j ell r)
        (deletionNeighborhoodRoot G o i j ell r) ell = graphBallVertices G o ell :=
  induced_root_ball_image G _ o _ ell (deletionNeighborhood_contains_root_ball G o i j ell r)

/-- The required small neighborhoods around all actual Schur indices lie
inside this one finite model. -/
theorem deletionNeighborhood_contains_schur_ball (G : SimpleGraph V) (o i j x : V) (ell r : ℕ)
    (hx : x ∈ graphBallVertices G o ell ∨ x = i ∨ x = j) :
    graphBallVertices G x r ⊆ deletionNeighborhoodVertices G o i j ell r := by
  intro v hv
  apply (mem_tripleBallVertices G o i j v (ell + r) r r).mpr
  rcases hx with hx | rfl | rfl
  · left
    calc
      G.edist o v ≤ G.edist o x + G.edist x v := G.edist_triangle
      _ ≤ (ell : ℕ∞) + (r : ℕ∞) := add_le_add hx hv
      _ = ((ell + r : ℕ) : ℕ∞) := by simp only [Nat.cast_add]
  · exact Or.inr (Or.inl hv)
  · exact Or.inr (Or.inr hv)

theorem deletionNeighborhood_distance_bound (G : SimpleGraph V) (o i j : V) (ell r : ℕ)
    (a b : deletionNeighborhoodVertices G o i j ell r) :
    (deletionNeighborhoodGraph G o i j ell r).dist a b ≤ 6 * (ell + r) + 2 :=
  tripleBall_distance_bound G o i j (ell + r) r r (ell + r) le_rfl (by omega) (by omega) a b

section Finite
variable [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Every actual component inherits the structural excess at the original
root scale; a total-excess bound on the disconnected model is not assumed. -/
theorem deletionNeighborhood_component_excess_bound (G : SimpleGraph V) (o i j : V)
    (ell r R ω : ℕ) (hmargin : 6 * (ell + r) + 2 ≤ R)
    (hballs : ∀ a, graphBallExcess G a R ≤ ω)
    (c : (deletionNeighborhoodGraph G o i j ell r).ConnectedComponent) :
    graphExcess ((deletionNeighborhoodGraph G o i j ell r).induce c.supp) ≤ ω := by
  let H := deletionNeighborhoodGraph G o i j ell r
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
    have hcap : (H.induce c.supp).dist root x ≤ 6 * (ell + r) + 2 := by
      rw [isolated_induce_distance H c.supp hcut]
      exact deletionNeighborhood_distance_bound G o i j ell r root.val x.val
    have he := SimpleGraph.edist_le (p.map f)
    simp only [SimpleGraph.Walk.length_map, hp] at he
    exact he.trans (by exact_mod_cast hcap.trans hmargin)
  let e : H.induce c.supp →g graphBall G a.val R :=
    { toFun := fun x => ⟨x.val.val, hball x⟩
      map_rel' := fun h => h }
  have he : Function.Injective e := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : graphBallVertices G a.val R => z.val) h))
  exact (connected_embedding_graphExcess_le (H.induce c.supp) (graphBall G a.val R)
    hconn (graphBall_connected G a.val R) e he).trans (hballs a.val)

end Finite

namespace RegularGraph
variable {N d : ℕ}

def deletionNeighborhoodModel (g : RegularGraph N d) (o i j : Fin N) (ell r : ℕ) :
    DeficientGraph (deletionNeighborhoodVertices g.graph o i j ell r) d :=
  g.deficient.restrict (deletionNeighborhoodVertices g.graph o i j ell r)

theorem deletionNeighborhoodModel_zero_deficit (g : RegularGraph N d) (o i j : Fin N) (ell r : ℕ)
    (v : deletionNeighborhoodVertices g.graph o i j ell r) :
    (g.deletionNeighborhoodModel o i j ell r).deficit v = 0 := rfl

theorem deletionNeighborhoodModel_component_budget (g : RegularGraph N d) (o i j : Fin N)
    (ell r R : ℕ) (hmargin : 6 * (ell + r) + 2 ≤ R)
    (hballs : ∀ a, graphBallExcess g.graph a R ≤ finiteOmega d) :
    (g.deletionNeighborhoodModel o i j ell r).ComponentReferenceBudget := by
  intro c
  have hzero : ∀ v, ((g.deletionNeighborhoodModel o i j ell r).restrict c.supp).deficit v = 0 := fun _ => rfl
  simp only [hzero, Finset.sum_const_zero, zero_add]
  exact deletionNeighborhood_component_excess_bound g.graph o i j ell r R (finiteOmega d) hmargin hballs c

end RegularGraph
end LocalLaw
