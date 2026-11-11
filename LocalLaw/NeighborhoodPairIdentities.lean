import LocalLaw.RestrictionDeletionIdentity
import LocalLaw.PairModelIso
import LocalLaw.PairRestrictionIdentity
import LocalLaw.NeighborhoodDeletionComparison

/-!
# Literal pair-model identities used in the source deletion proof

The larger neighborhood's pair models are the original pair models at every
Schur index. After actual deletion, restriction/deletion covariance and full
endpoint-ball containment identify its intrinsic pair model with the source
deletedP, including the inherited nonzero deficits.
-/

noncomputable section
namespace LocalLaw
local instance neighborhoodPairDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace DeficientGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

theorem restriction_delete_pair_P (g : DeficientGraph V d) (S T : Set V) (Tm : Set S)
    (hTm : ∀ v : S, v ∈ Tm ↔ v.val ∈ T) (hTS : T ⊆ S)
    (i j : (Tmᶜ : Set S)) (r : ℕ)
    (hi : graphBallVertices (outsideGraph g.graph T)
      ((restrictionDeletionGraphIso g.graph S T Tm hTm) i).val r ⊆ {v : (Tᶜ : Set V) | v.val ∈ S})
    (hj : graphBallVertices (outsideGraph g.graph T)
      ((restrictionDeletionGraphIso g.graph S T Tm hTm) j).val r ⊆ {v : (Tᶜ : Set V) | v.val ∈ S})
    (q z : ℂ) :
    ((g.restrict S).delete Tm).P r z q i j =
      (g.delete T).P r z q ((restrictionDeletionGraphIso g.graph S T Tm hTm) i).val
        ((restrictionDeletionGraphIso g.graph S T Tm hTm) j).val := by
  let φ := restrictionDeletionGraphIso g.graph S T Tm hTm
  let h := ((g.delete T).restrict {v : (Tᶜ : Set V) | v.val ∈ S})
  have hiso := h.P_iso ((g.restrict S).delete Tm) φ
    (g.restrictionDeletion_deficit S T Tm hTm hTS) r q z i j
  exact hiso.trans ((g.delete T).restrict_pair_P _ (φ i) (φ j) r hi hj q z)

end DeficientGraph

namespace RegularGraph
variable {N d : ℕ}

/-- Every pair model at the actual Schur indices of Go is literally the
original physical pair model, not an approximation assumption. -/
theorem deletionNeighborhoodModel_P_schur (g : RegularGraph N d) (o i j : Fin N) (ell r : ℕ)
    (x y : deletionNeighborhoodVertices g.graph o i j ell r)
    (hx : x.val ∈ graphBallVertices g.graph o ell ∨ x.val = i ∨ x.val = j)
    (hy : y.val ∈ graphBallVertices g.graph o ell ∨ y.val = i ∨ y.val = j) (q z : ℂ) :
    (g.deletionNeighborhoodModel o i j ell r).P r z q x y = g.P r z q x.val y.val := by
  have hh := g.deficient.restrict_pair_P (deletionNeighborhoodVertices g.graph o i j ell r) x y r
    (deletionNeighborhood_contains_schur_ball g.graph o i j x.val ell r hx)
    (deletionNeighborhood_contains_schur_ball g.graph o i j y.val ell r hy) q z
  rw [g.deficient_P] at hh
  exact hh

/-- The deleted large model's intrinsic pair value is exactly the source
deletedP on the original graph, with its genuine inherited deficit. -/
theorem deletionNeighborhoodModel_deleted_P (g : RegularGraph N d) (o i j : Fin N) (ell r : ℕ)
    (hi : i ∉ graphBallVertices g.graph o ell) (hj : j ∉ graphBallVertices g.graph o ell) (q z : ℂ) :
    ((g.deletionNeighborhoodModel o i j ell r).delete
      (deletionNeighborhoodInnerSet g.graph o i j ell r)).P r z q
      (deletionNeighborhoodOutsideLeft g.graph o i j ell r hi)
      (deletionNeighborhoodOutsideRight g.graph o i j ell r hj) =
        g.deletedP (graphBallVertices g.graph o ell) r z q ⟨i, hi⟩ ⟨j, hj⟩ := by
  let S := deletionNeighborhoodVertices g.graph o i j ell r
  let T := graphBallVertices g.graph o ell
  let Tm := deletionNeighborhoodInnerSet g.graph o i j ell r
  have hTm : ∀ v : S, v ∈ Tm ↔ v.val ∈ T := deletionNeighborhood_inner_mem g.graph o i j ell r
  have hTS : T ⊆ S := deletionNeighborhood_contains_root_ball g.graph o i j ell r
  let ii := deletionNeighborhoodOutsideLeft g.graph o i j ell r hi
  let jj := deletionNeighborhoodOutsideRight g.graph o i j ell r hj
  let φ := restrictionDeletionGraphIso g.graph S T Tm hTm
  let f := (SimpleGraph.Embedding.induce (G := g.graph) Tᶜ).toHom
  have hleft : graphBallVertices (outsideGraph g.graph T) (φ ii).val r ⊆
      {v : (Tᶜ : Set (Fin N)) | v.val ∈ S} := by
    intro v hv
    apply (mem_tripleBallVertices g.graph o i j v.val (ell + r) r r).mpr
    right; left
    exact (graphHom_edist_le f (φ ii).val v).trans hv
  have hright : graphBallVertices (outsideGraph g.graph T) (φ jj).val r ⊆
      {v : (Tᶜ : Set (Fin N)) | v.val ∈ S} := by
    intro v hv
    apply (mem_tripleBallVertices g.graph o i j v.val (ell + r) r r).mpr
    right; right
    exact (graphHom_edist_le f (φ jj).val v).trans hv
  exact g.deficient.restriction_delete_pair_P S T Tm hTm hTS ii jj r hleft hright q z

end RegularGraph
end LocalLaw
