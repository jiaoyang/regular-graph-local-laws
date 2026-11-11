import SpectralConsequences.AllCorePaddedExtension
import SpectralConsequences.GraphGreenEmbedding
import SpectralConsequences.LocalGraphResolventLimit

/-! The literal arbitrary-core extension embeds as a neighbor-closed component
of its padded realization. Eventual core neighbor and deficit agreement then
gives convergence of the genuine extension Green entries. -/

open Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace SpectralConsequences
open LocalLaw
local instance allCorePaddedEmbeddingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace AllCoreGraph
variable {V : Type} [DecidableEq V] {d : ℕ}

def paddedSlotEmbedding (g : AllCoreGraph V d) : g.Slots ↪ (V × Fin d) where
  toFun s := (s.1, g.slotEmbedding s.1 s.2)
  inj' := by
    rintro ⟨v,i⟩ ⟨w,j⟩ h
    have hv : v=w := congrArg Prod.fst h
    cases hv
    have hij : i=j := Fin.ext (congrArg (fun p : V × Fin d => p.2.val) h)
    cases hij
    rfl

def paddedEmbedding (g : AllCoreGraph V d) : g.Vertex ↪ PaddedVertex V d where
  toFun x := match x with
    | Sum.inl v => Sum.inl v
    | Sum.inr p => Sum.inr (p.1,g.paddedSlotEmbedding p.2)
  inj' := by
    intro x y h
    cases x with
    | inl v =>
      cases y with
      | inl w => exact congrArg Sum.inl (Sum.inl.inj h)
      | inr p => cases h
    | inr p =>
      cases y with
      | inl w => cases h
      | inr q =>
        have hp := Sum.inr.inj h
        have hfirst : p.1=q.1 := congrArg (fun t : List (Fin (d-1)) × (V × Fin d) => t.1) hp
        have hsecond : p.2=q.2 := g.paddedSlotEmbedding.injective
          (congrArg (fun t : List (Fin (d-1)) × (V × Fin d) => t.2) hp)
        exact congrArg Sum.inr (Prod.ext hfirst hsecond)

omit [DecidableEq V] in
@[simp] theorem paddedEmbedding_core (g : AllCoreGraph V d) (v : V) :
    g.paddedEmbedding (Sum.inl v) = Sum.inl v := rfl

omit [DecidableEq V] in
@[simp] theorem paddedEmbedding_tree (g : AllCoreGraph V d)
    (w : List (Fin (d-1))) (s : g.Slots) :
    g.paddedEmbedding (Sum.inr (w,s)) = Sum.inr (w,g.paddedSlotEmbedding s) := rfl

omit [DecidableEq V] in
theorem paddedSlot_active (g : AllCoreGraph V d) (s : g.Slots) :
    g.active (g.paddedSlotEmbedding s) := s.2.isLt

omit [DecidableEq V] in
theorem paddedEmbedding_adj (g : AllCoreGraph V d) (x y : g.Vertex) :
    g.padded.Adj (g.paddedEmbedding x) (g.paddedEmbedding y) ↔ g.extension.Adj x y := by
  cases x with
  | inl v =>
    cases y with
    | inl w => rfl
    | inr p =>
      change (p.1=[] ∧ (g.paddedSlotEmbedding p.2).1=v ∧ g.active (g.paddedSlotEmbedding p.2)) ↔
        (p.1=[] ∧ p.2.1=v)
      simp only [g.paddedSlot_active, and_true]
      rfl
  | inr p =>
    cases y with
    | inl w =>
      change (p.1=[] ∧ (g.paddedSlotEmbedding p.2).1=w ∧ g.active (g.paddedSlotEmbedding p.2)) ↔
        (p.1=[] ∧ p.2.1=w)
      simp only [g.paddedSlot_active, and_true]
      rfl
    | inr q =>
      change (g.paddedSlotEmbedding p.2=g.paddedSlotEmbedding q.2 ∧
        g.active (g.paddedSlotEmbedding p.2) ∧ wordTreeAdj p.1 q.1) ↔
        (p.2=q.2 ∧ wordTreeAdj p.1 q.1)
      simp only [g.paddedSlot_active,
        true_and, g.paddedSlotEmbedding.injective.eq_iff]

omit [DecidableEq V] in
theorem paddedEmbedding_closed (g : AllCoreGraph V d) (x : g.Vertex)
    (y : PaddedVertex V d) (h : g.padded.Adj (g.paddedEmbedding x) y) :
    ∃ z, g.paddedEmbedding z = y := by
  cases x with
  | inl v =>
    cases y with
    | inl w => exact ⟨Sum.inl w,rfl⟩
    | inr p =>
      rcases p with ⟨w,u,k⟩
      have hk : k.val < g.missing u := h.2.2
      refine ⟨Sum.inr (w,⟨u,⟨k.val,hk⟩⟩),?_⟩
      apply congrArg Sum.inr
      apply Prod.ext rfl
      apply Prod.ext rfl
      exact Fin.ext rfl
  | inr p =>
    cases y with
    | inl w => exact ⟨Sum.inl w,rfl⟩
    | inr q =>
      refine ⟨Sum.inr (q.1,p.2),?_⟩
      exact congrArg Sum.inr (Prod.ext rfl h.1)

theorem paddedGreen_eq (g : AllCoreGraph V d) (hd : 1≤d)
    (z : ℂ) (hz : z.im≠0) (i j : V) :
    g.padded.infiniteGreen d (g.padded_degree_le hd) z (Sum.inl i) (Sum.inl j) =
      g.green hd z i j :=
  green_eq_of_neighbor_closed_embedding g.extension g.padded g.paddedEmbedding
    g.paddedEmbedding_adj g.paddedEmbedding_closed d (g.extension_degree_le hd)
    (g.padded_degree_le hd) z hz (Sum.inl i) (Sum.inl j)

theorem padded_neighbors_eventually (g : AllCoreGraph V d) (gn : ℕ → AllCoreGraph V d)
    (hNeighbors : ∀ v, ∀ᶠ n : ℕ in atTop,
      (gn n).graph.neighborFinset v = g.graph.neighborFinset v)
    (hDeficit : ∀ v, ∀ᶠ n : ℕ in atTop, (gn n).deficit v = g.deficit v)
    (x : PaddedVertex V d) :
    ∀ᶠ n : ℕ in atTop, (gn n).padded.neighborFinset x = g.padded.neighborFinset x := by
  have hmissing (v : V) : ∀ᶠ n : ℕ in atTop, (gn n).missing v = g.missing v := by
    filter_upwards [hNeighbors v,hDeficit v] with n hn hd
    have hdegree : (gn n).graph.degree v = g.graph.degree v := congrArg Finset.card hn
    simp only [missing,hd,hdegree]
  cases x with
  | inl v =>
    filter_upwards [hNeighbors v,hmissing v] with n hn hm
    rw [(gn n).padded_neighborFinset,g.padded_neighborFinset]
    have hs : (gn n).slotFinset v = g.slotFinset v := by
      ext k
      simp only [mem_slotFinset,hm]
    simp only [paddedNeighbors,hn,hs]
  | inr p =>
    filter_upwards [hmissing p.2.1] with n hm
    rw [(gn n).padded_neighborFinset,g.padded_neighborFinset]
    simp only [paddedNeighbors,active,hm,paddedParent]

theorem green_tendsto_of_core_agreement (g : AllCoreGraph V d)
    (gn : ℕ → AllCoreGraph V d) (hd : 1≤d)
    (hNeighbors : ∀ v, ∀ᶠ n : ℕ in atTop,
      (gn n).graph.neighborFinset v = g.graph.neighborFinset v)
    (hDeficit : ∀ v, ∀ᶠ n : ℕ in atTop, (gn n).deficit v = g.deficit v)
    (z : ℂ) (hz : 0<z.im) (i j : V) :
    Tendsto (fun n => (gn n).green hd z i j) atTop (𝓝 (g.green hd z i j)) := by
  have hh := green_tendsto_of_neighbor_agreement g.padded (fun n => (gn n).padded) d
    (g.padded_degree_le hd) (fun n => (gn n).padded_degree_le hd)
    (g.padded_neighbors_eventually gn hNeighbors hDeficit) z hz (Sum.inl i) (Sum.inl j)
  simpa only [paddedGreen_eq _ hd z (ne_of_gt hz)] using hh

end AllCoreGraph
end SpectralConsequences
