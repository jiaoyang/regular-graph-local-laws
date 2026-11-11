import LocalLaw.DeficientGraphIso
import LocalLaw.ComponentBallGeometry
import LocalLaw.ExcessCutset

/-!
# Restriction commutes with source deletion when the removed set is retained

The pointwise source deficit is rewritten as its inherited deficit plus the
actual number of removed neighbors. A literal removed-neighbor equivalence
then identifies the two correctly deficient finite graphs and their inverses.
-/

noncomputable section
namespace LocalLaw
local instance restrictionDeletionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*}

section Counts
variable [Fintype V]

theorem degree_loss_eq_removed_neighbor_count (G : SimpleGraph V) (T : Set V)
    (v : (Tᶜ : Set V)) :
    G.degree v.val - (outsideGraph G T).degree v = Nat.card {t : T // G.Adj t.val v.val} := by
  have hh := Nat.card_congr (neighborCutEquiv G T v)
  rw [Nat.card_sum] at hh
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  omega

end Counts

def removedNeighborRestrictionEquiv (G : SimpleGraph V) (S T : Set V) (Tm : Set S)
    (hTm : ∀ v : S, v ∈ Tm ↔ v.val ∈ T) (hTS : T ⊆ S) (v : S) :
    {t : Tm // (G.induce S).Adj t.val v} ≃ {t : T // G.Adj t.val v.val} where
  toFun t := ⟨⟨t.val.val.val, (hTm t.val.val).mp t.val.property⟩, t.property⟩
  invFun t := ⟨⟨⟨t.val.val, hTS t.val.property⟩,
    (hTm ⟨t.val.val, hTS t.val.property⟩).mpr t.val.property⟩, t.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def restrictionDeletionGraphIso (G : SimpleGraph V) (S T : Set V) (Tm : Set S)
    (hTm : ∀ v : S, v ∈ Tm ↔ v.val ∈ T) :
    outsideGraph (G.induce S) Tm ≃g
      (outsideGraph G T).induce {v : (Tᶜ : Set V) | v.val ∈ S} where
  toFun v := ⟨⟨v.val.val, fun hh => v.property ((hTm v.val).mpr hh)⟩, v.val.property⟩
  invFun v := ⟨⟨v.val.val, v.property⟩, fun hh => v.val.property
    ((hTm ⟨v.val.val, v.property⟩).mp hh)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

namespace DeficientGraph
variable [Fintype V] [DecidableEq V] {d : ℕ}

omit [DecidableEq V] in
theorem delete_deficit_eq_removed_neighbors (g : DeficientGraph V d) (T : Set V)
    (v : (Tᶜ : Set V)) :
    (g.delete T).deficit v = g.deficit v.val + Nat.card {t : T // g.graph.Adj t.val v.val} := by
  rw [g.delete_deficit]
  congr 1
  have hh := degree_loss_eq_removed_neighbor_count g.graph T v
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh ⊢
  exact hh

omit [DecidableEq V] in
theorem restrictionDeletion_deficit (g : DeficientGraph V d) (S T : Set V) (Tm : Set S)
    (hTm : ∀ v : S, v ∈ Tm ↔ v.val ∈ T) (hTS : T ⊆ S)
    (v : (Tmᶜ : Set S)) :
    ((g.restrict S).delete Tm).deficit v =
      ((g.delete T).restrict {v : (Tᶜ : Set V) | v.val ∈ S}).deficit
        ((restrictionDeletionGraphIso g.graph S T Tm hTm) v) := by
  change ((g.restrict S).delete Tm).deficit v = (g.delete T).deficit _
  rw [(g.restrict S).delete_deficit_eq_removed_neighbors, g.delete_deficit_eq_removed_neighbors]
  change g.deficit v.val.val + Nat.card {t : Tm // (g.graph.induce S).Adj t.val v.val} =
    g.deficit v.val.val + Nat.card {t : T // g.graph.Adj t.val v.val.val}
  rw [Nat.card_congr (removedNeighborRestrictionEquiv g.graph S T Tm hTm hTS v.val)]

/-- Exact covariance of the correctly deficient restricted/deleted inverse.
The deficits are derived from actual lost neighbors, including preexisting
nonzero deficits and removed vertices with deficit larger than one. -/
theorem restriction_delete_extensionGreen (g : DeficientGraph V d) (S T : Set V) (Tm : Set S)
    (hTm : ∀ v : S, v ∈ Tm ↔ v.val ∈ T) (hTS : T ⊆ S) (q z : ℂ) :
    (((g.delete T).restrict {v : (Tᶜ : Set V) | v.val ∈ S}).extensionGreen q z).submatrix
      (restrictionDeletionGraphIso g.graph S T Tm hTm) (restrictionDeletionGraphIso g.graph S T Tm hTm) =
        ((g.restrict S).delete Tm).extensionGreen q z := by
  exact ((g.delete T).restrict {v : (Tᶜ : Set V) | v.val ∈ S}).extensionGreen_iso
    ((g.restrict S).delete Tm) (restrictionDeletionGraphIso g.graph S T Tm hTm)
    (g.restrictionDeletion_deficit S T Tm hTm hTS) q z

end DeficientGraph
end LocalLaw
