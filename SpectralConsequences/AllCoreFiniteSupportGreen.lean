import SpectralConsequences.AllCoreReferenceThreshold
import SpectralConsequences.AllCoreFiniteSupport
import SpectralConsequences.AllCorePaddedEmbedding

/-! The actual finite-support approximation has exactly the genuine Green
function of its finite induced core. Isolated ambient vertices and inactive
padded slots are excluded by a neighbor-closed embedding, not by an assumed
inverse-block identity. -/
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
namespace SpectralConsequences
open LocalLaw
local instance allCoreFiniteSupportGreenDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace AllCoreGraph
variable {V : Type} [DecidableEq V] {d : ℕ}

def finiteSupportNeighborEquiv (g : AllCoreGraph V d) (S : Finset V) (i : S) :
    (g.graph.induce (S:Set V)).neighborSet i ≃
      (g.finiteSupport S).graph.neighborSet i.val where
  toFun v := ⟨v.val.val,⟨i.property,v.val.property,v.property⟩⟩
  invFun v := ⟨⟨v.val,v.property.2.1⟩,v.property.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem finiteSupport_degree_subtype (g : AllCoreGraph V d) (S : Finset V) (i : S) :
    (g.finiteSupport S).graph.degree i.val=(g.finiteRestriction S).graph.degree i := by
  have hh := (Nat.card_congr (g.finiteSupportNeighborEquiv S i)).symm
  simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using hh

theorem finiteSupport_missing_subtype (g : AllCoreGraph V d) (S : Finset V) (i : S) :
    (g.finiteSupport S).missing i.val=(ofFinite (g.finiteRestriction S)).missing i := by
  simp only [missing,g.finiteSupport_deficit S i.val i.property,
    g.finiteSupport_degree_subtype S i,ofFinite_deficit,ofFinite_graph]
  rfl

/-- Fixed-slot padded inclusion of a finite core into its ambient core. -/
def finitePaddedEmbedding (S : Finset V) : PaddedVertex S d ↪ PaddedVertex V d where
  toFun x := match x with
    | Sum.inl i => Sum.inl i.val
    | Sum.inr p => Sum.inr (p.1,(p.2.1.val,p.2.2))
  inj' := by
    intro x y h
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
      | inr q => cases h
    | inr p =>
      cases y with
      | inl j => cases h
      | inr q =>
        have hh := Sum.inr.inj h
        have hw : p.1=q.1 := congrArg (fun t : List (Fin (d-1)) × (V × Fin d)=>t.1) hh
        have hv : p.2.1=q.2.1 :=
          Subtype.ext (congrArg (fun t : List (Fin (d-1)) × (V × Fin d)=>t.2.1) hh)
        have hk : p.2.2=q.2.2 :=
          congrArg (fun t : List (Fin (d-1)) × (V × Fin d)=>t.2.2) hh
        exact congrArg Sum.inr (Prod.ext hw (Prod.ext hv hk))

omit [DecidableEq V] in
@[simp] theorem finitePaddedEmbedding_core (S : Finset V) (i : S) :
    finitePaddedEmbedding (d:=d) S (Sum.inl i)=Sum.inl i.val := rfl

omit [DecidableEq V] in
@[simp] theorem finitePaddedEmbedding_tree (S : Finset V)
    (w : List (Fin (d-1))) (i : S) (k : Fin d) :
    finitePaddedEmbedding S (Sum.inr (w,(i,k)))=Sum.inr (w,(i.val,k)) := rfl

theorem finiteSupportPadded_adj (g : AllCoreGraph V d) (S : Finset V)
    (x y : PaddedVertex S d) :
    (g.finiteSupport S).padded.Adj (finitePaddedEmbedding S x) (finitePaddedEmbedding S y) ↔
      (ofFinite (g.finiteRestriction S)).padded.Adj x y := by
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      change (i.val∈S ∧ j.val∈S ∧ g.graph.Adj i.val j.val)↔g.graph.Adj i.val j.val
      simp only [i.property,j.property,true_and]
    | inr q =>
      rcases q with ⟨w,j,k⟩
      simp only [finitePaddedEmbedding_core,finitePaddedEmbedding_tree,padded,active,
        g.finiteSupport_missing_subtype S j,Subtype.val_inj]
  | inr p =>
    rcases p with ⟨w,i,k⟩
    cases y with
    | inl j =>
      simp only [finitePaddedEmbedding_core,finitePaddedEmbedding_tree,padded,active,
        g.finiteSupport_missing_subtype S i,Subtype.val_inj]
    | inr q =>
      rcases q with ⟨v,j,l⟩
      simp only [finitePaddedEmbedding_tree,padded,active,g.finiteSupport_missing_subtype S i,
        Prod.mk.injEq,Subtype.val_inj]

theorem finiteSupportPadded_closed (g : AllCoreGraph V d) (S : Finset V)
    (x : PaddedVertex S d) (y : PaddedVertex V d)
    (h : (g.finiteSupport S).padded.Adj (finitePaddedEmbedding S x) y) :
    ∃z,finitePaddedEmbedding S z=y := by
  cases x with
  | inl i =>
    cases y with
    | inl j => exact ⟨Sum.inl ⟨j,h.2.1⟩,rfl⟩
    | inr q =>
      rcases q with ⟨w,j,k⟩
      have hij : i.val=j := h.2.1.symm
      have hj : j∈S := by rw [←hij]; exact i.property
      exact ⟨Sum.inr (w,(⟨j,hj⟩,k)),rfl⟩
  | inr p =>
    rcases p with ⟨w,i,k⟩
    cases y with
    | inl j =>
      have hij : i.val=j := h.2.1
      have hj : j∈S := by rw [←hij]; exact i.property
      exact ⟨Sum.inl ⟨j,hj⟩,rfl⟩
    | inr q =>
      rcases q with ⟨v,j,l⟩
      have hij : i.val=j := congrArg Prod.fst h.1
      have hj : j∈S := by rw [←hij]; exact i.property
      exact ⟨Sum.inr (v,(⟨j,hj⟩,l)),rfl⟩

/-- Genuine finite-support and finite-core tree-extension Green entries agree. -/
theorem finiteSupport_green_eq_finiteRestriction (g : AllCoreGraph V d) (S : Finset V)
    (hd : 3≤d) (z : ℂ) (hz : 0<z.im) (i j : S) :
    (g.finiteSupport S).green (by omega) z i.val j.val=
      (g.finiteRestriction S).treeExtensionGreen (by omega) z i j := by
  have hh := green_eq_of_neighbor_closed_embedding
    (ofFinite (g.finiteRestriction S)).padded (g.finiteSupport S).padded
    (finitePaddedEmbedding S) (g.finiteSupportPadded_adj S) (g.finiteSupportPadded_closed S)
    d ((ofFinite (g.finiteRestriction S)).padded_degree_le (by omega))
    ((g.finiteSupport S).padded_degree_le (by omega)) z (ne_of_gt hz) (Sum.inl i) (Sum.inl j)
  have hD : 1≤d := by omega
  simpa only [finitePaddedEmbedding_core,paddedGreen_eq _ hD z (ne_of_gt hz),
    ofFinite_green _ hd z hz] using hh

end AllCoreGraph
end SpectralConsequences
#print axioms SpectralConsequences.AllCoreGraph.finiteSupport_green_eq_finiteRestriction
