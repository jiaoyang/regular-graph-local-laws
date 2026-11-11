import LocalLaw.RestrictionDeletionIdentity
import LocalLaw.PairBoundaryDepth

/-! # Exact charge when the deleted set is not contained in a restriction

Deleting only the retained part of a global set does not commute with
restriction. The discrepancy is exactly the number of omitted deleted
neighbors. In a target pair ball this correction is supported on its actual
outer layer. These identities retain the charge instead of assuming it zero.
-/

noncomputable section
namespace LocalLaw
local instance partialDeletionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*}

/-- Partition every removed neighbor into those retained and those omitted. -/
def removedNeighborPartitionEquiv (G : SimpleGraph V) (S T : Set V) (Tm : Set S)
    (hTm : ∀ v : S, v ∈ Tm ↔ v.val ∈ T) (v : S) :
    {t : T // G.Adj t.val v.val} ≃
      {t : Tm // (G.induce S).Adj t.val v} ⊕
        {t : T // t.val ∉ S ∧ G.Adj t.val v.val} where
  toFun t := if hs : t.val.val ∈ S then
    Sum.inl ⟨⟨⟨t.val.val,hs⟩,(hTm ⟨t.val.val,hs⟩).mpr t.val.property⟩,t.property⟩
    else Sum.inr ⟨t.val,hs,t.property⟩
  invFun t := match t with
    | Sum.inl t => ⟨⟨t.val.val.val,(hTm t.val.val).mp t.val.property⟩,t.property⟩
    | Sum.inr t => ⟨t.val,t.property.2⟩
  left_inv t := by
    by_cases hs : t.val.val ∈ S
    · simp only [dif_pos hs]
    · simp only [dif_neg hs]
  right_inv t := by
    rcases t with t | t
    · dsimp
      simp only [dif_pos t.val.val.property]
    · dsimp
      simp only [dif_neg t.property.1]

section Counts
variable [Fintype V]

theorem removed_neighbor_count_partition (G : SimpleGraph V) (S T : Set V) (Tm : Set S)
    (hTm : ∀ v : S, v ∈ Tm ↔ v.val ∈ T) (v : S) :
    Nat.card {t : T // G.Adj t.val v.val} =
      Nat.card {t : Tm // (G.induce S).Adj t.val v} +
        Nat.card {t : T // t.val ∉ S ∧ G.Adj t.val v.val} := by
  rw [Nat.card_congr (removedNeighborPartitionEquiv G S T Tm hTm v),Nat.card_sum]

namespace DeficientGraph
variable [DecidableEq V] {d : ℕ}

omit [DecidableEq V] in
theorem partial_restrictionDeletion_deficit (g : DeficientGraph V d)
    (S T : Set V) (Tm : Set S) (hTm : ∀ v : S, v ∈ Tm ↔ v.val ∈ T)
    (v : (Tmᶜ : Set S)) :
    ((g.delete T).restrict {v : (Tᶜ : Set V) | v.val ∈ S}).deficit
        ((restrictionDeletionGraphIso g.graph S T Tm hTm) v) =
      ((g.restrict S).delete Tm).deficit v +
        Nat.card {t : T // t.val ∉ S ∧ g.graph.Adj t.val v.val.val} := by
  change (g.delete T).deficit _ = _
  rw [g.delete_deficit_eq_removed_neighbors,(g.restrict S).delete_deficit_eq_removed_neighbors]
  change g.deficit v.val.val + Nat.card {t : T // g.graph.Adj t.val v.val.val} =
    g.deficit v.val.val + Nat.card {t : Tm // (g.graph.induce S).Adj t.val v.val} + _
  rw [removed_neighbor_count_partition g.graph S T Tm hTm v.val]
  omega

omit [DecidableEq V] in
theorem partial_restrictionDeletion_boundaryCoefficient (g : DeficientGraph V d)
    (S T : Set V) (Tm : Set S) (hTm : ∀ v : S, v ∈ Tm ↔ v.val ∈ T)
    (v : (Tmᶜ : Set S)) :
    ((g.delete T).restrict {v : (Tᶜ : Set V) | v.val ∈ S}).boundaryCoefficient
        ((restrictionDeletionGraphIso g.graph S T Tm hTm) v) =
      ((g.restrict S).delete Tm).boundaryCoefficient v -
        (Nat.card {t : T // t.val ∉ S ∧ g.graph.Adj t.val v.val.val} : ℝ) / ((d:ℝ)-1) := by
  let e := restrictionDeletionGraphIso g.graph S T Tm hTm
  have hdegree : ((g.restrict S).delete Tm).graph.degree v =
      ((g.delete T).restrict {v : (Tᶜ : Set V) | v.val ∈ S}).graph.degree (e v) := by
    have hh := Nat.card_congr (e.mapNeighborSet v)
    simp only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card]
    exact hh
  have hdef := g.partial_restrictionDeletion_deficit S T Tm hTm v
  have hreal :
      (((g.delete T).restrict {v : (Tᶜ : Set V) | v.val ∈ S}).deficit (e v) : ℝ) =
      (((g.restrict S).delete Tm).deficit v : ℝ) +
        (Nat.card {t : T // t.val ∉ S ∧ g.graph.Adj t.val v.val.val} : ℝ) := by
    exact_mod_cast hdef
  unfold boundaryCoefficient
  rw [hreal,←hdegree]
  ring

/-- Exact precision correction after the literal graph reindexing. The
additional diagonal records removed vertices omitted from the restriction. -/
theorem partial_restrictionDeletion_extensionMatrix (g : DeficientGraph V d)
    (S T : Set V) (Tm : Set S) (hTm : ∀ v : S, v ∈ Tm ↔ v.val ∈ T)
    (q z : ℂ) :
    (((g.delete T).restrict {v : (Tᶜ : Set V) | v.val ∈ S}).extensionMatrix q z).submatrix
        (restrictionDeletionGraphIso g.graph S T Tm hTm)
        (restrictionDeletionGraphIso g.graph S T Tm hTm) =
      ((g.restrict S).delete Tm).extensionMatrix q z + q • Matrix.diagonal
        (fun v => (Nat.card {t : T // t.val ∉ S ∧ g.graph.Adj t.val v.val.val} : ℂ) /
          ((d:ℂ)-1)) := by
  let common := (g.delete T).restrict {v : (Tᶜ : Set V) | v.val ∈ S}
  let localModel := (g.restrict S).delete Tm
  let e := restrictionDeletionGraphIso g.graph S T Tm hTm
  let charge : Matrix (Tmᶜ : Set S) (Tmᶜ : Set S) ℂ := Matrix.diagonal
    (fun v => (Nat.card {t : T // t.val ∉ S ∧ g.graph.Adj t.val v.val.val} : ℂ) /
      ((d:ℂ)-1))
  have hH : common.H.submatrix e e = localModel.H := by
    ext i j
    simp only [H,normalizedAdjacency,Matrix.submatrix_apply,Matrix.smul_apply,
      smul_eq_mul,SimpleGraph.adjMatrix_apply]
    rw [show common.graph.Adj (e i) (e j) ↔ localModel.graph.Adj i j from e.map_rel_iff']
  have hD : common.boundaryDiagonal.submatrix e e = localModel.boundaryDiagonal-charge := by
    ext i j
    simp only [boundaryDiagonal,charge,Matrix.submatrix_apply,Matrix.sub_apply,
      Matrix.diagonal_apply,e.injective.eq_iff]
    by_cases hij:i=j
    · subst j
      simp only [if_pos rfl]
      have hh := congrArg Complex.ofReal (g.partial_restrictionDeletion_boundaryCoefficient S T Tm hTm i)
      push_cast at hh
      exact hh
    · simp only [if_neg hij,sub_zero]
  have hS := spectralMatrix_principal common.H z e e.injective
  rw [hH] at hS
  change (common.extensionMatrix q z).submatrix e e = localModel.extensionMatrix q z+q•charge
  unfold extensionMatrix boundaryMatrix
  change (spectralMatrix common.H z).submatrix e e-q•common.boundaryDiagonal.submatrix e e =
    spectralMatrix localModel.H z-q•localModel.boundaryDiagonal+q•charge
  rw [←hS,hD,smul_sub]
  abel

end DeficientGraph
end Counts

/-- Every nonzero omitted-neighbor correction for a pair restriction is
supported on the actual outer layer of both target balls. -/
theorem omitted_neighbor_pair_boundary_depth (G : SimpleGraph V) (x y : V) (r : ℕ)
    (T : Set V) (v : pairBallVertices G x y r)
    (h : ∃ t : T, t.val ∉ pairBallVertices G x y r ∧ G.Adj t.val v.val) :
    (r:ℕ∞) ≤ G.edist x v.val ∧ (r:ℕ∞) ≤ G.edist y v.val := by
  obtain ⟨t,ht,hvt⟩ := h
  exact pair_boundary_inner_edist_lower G x y r
    ⟨(v.val,t.val),G.adj_symm hvt,v.property,ht⟩

theorem omitted_neighbor_pair_charge_zero_interior (G : SimpleGraph V) (x y : V) (r : ℕ)
    (T : Set V) (v : V)
    (hnear : G.edist x v<(r:ℕ∞) ∨ G.edist y v<(r:ℕ∞)) :
    Nat.card {t : T // t.val∉pairBallVertices G x y r ∧ G.Adj t.val v}=0 := by
  haveI : IsEmpty {t : T // t.val∉pairBallVertices G x y r ∧ G.Adj t.val v} :=
    ⟨fun t=>pair_near_vertex_no_crossing_edge G x y r v t.val.val hnear t.property.1
      (G.adj_symm t.property.2)⟩
  simp

end LocalLaw
