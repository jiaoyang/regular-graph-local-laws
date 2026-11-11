import LocalLaw.NeighborhoodDeletionModel
import LocalLaw.DeficientGraphIso

/-!
# Exact pair models under a neighborhood restriction

If the larger vertex set contains both full radius-r endpoint balls, its
intrinsic pair neighborhood is exactly the original one. The inherited source
deficits and the normalized inverse are identified by an actual isomorphism.
-/

noncomputable section
namespace LocalLaw
local instance pairRestrictionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} (G : SimpleGraph V) (S : Set V) (i j : S) (r : ℕ)
    (hi : graphBallVertices G i.val r ⊆ S) (hj : graphBallVertices G j.val r ⊆ S)
include hi hj

theorem induced_pairBall_image :
    (Subtype.val : S → V) '' pairBallVertices (G.induce S) i j r = pairBallVertices G i.val j.val r := by
  change (Subtype.val : S → V) '' (graphBallVertices (G.induce S) i r ∪
    graphBallVertices (G.induce S) j r) = graphBallVertices G i.val r ∪ graphBallVertices G j.val r
  rw [Set.image_union, induced_root_ball_image G S i.val i.property r hi,
    induced_root_ball_image G S j.val j.property r hj]

def inducedPairBallEquiv :
    pairBallVertices (G.induce S) i j r ≃ pairBallVertices G i.val j.val r :=
  (Equiv.Set.image (Subtype.val : S → V) _ Subtype.val_injective).trans
    (Equiv.setCongr (induced_pairBall_image G S i j r hi hj))

def inducedPairBallIso : pairBallGraph (G.induce S) i j r ≃g pairBallGraph G i.val j.val r where
  toEquiv := inducedPairBallEquiv G S i j r hi hj
  map_rel_iff' := Iff.rfl

@[simp] theorem inducedPairBallIso_val (v : pairBallVertices (G.induce S) i j r) :
    (inducedPairBallIso G S i j r hi hj v).val = v.val.val := rfl

end LocalLaw

namespace LocalLaw.DeficientGraph
local instance pairRestrictionModelDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

/-- The actual finite pair Green value is unchanged by a larger inherited-
deficit restriction that contains its full endpoint balls. -/
theorem restrict_pair_P (g : DeficientGraph V d) (S : Set V) (i j : S) (r : ℕ)
    (hi : graphBallVertices g.graph i.val r ⊆ S) (hj : graphBallVertices g.graph j.val r ⊆ S)
    (q z : ℂ) :
    (g.restrict S).P r z q i j = g.P r z q i.val j.val := by
  let φ := inducedPairBallIso g.graph S i j r hi hj
  let localModel := (g.restrict S).restrict (pairBallVertices (g.graph.induce S) i j r)
  let globalModel := g.restrict (pairBallVertices g.graph i.val j.val r)
  have hdeficit : ∀ v, localModel.deficit v = globalModel.deficit (φ v) := fun _ => rfl
  have hh := globalModel.extensionGreen_iso localModel φ hdeficit q z
  exact (congrFun (congrFun hh (pairBallLeft (g.graph.induce S) i j r))
    (pairBallRight (g.graph.induce S) i j r)).symm

end LocalLaw.DeficientGraph
