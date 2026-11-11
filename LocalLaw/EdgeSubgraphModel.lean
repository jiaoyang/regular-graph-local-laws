import LocalLaw.HereditaryReferenceBounds

/-! # Removing edges while retaining the actual deficit

Finite reference budgets are preserved by arbitrary edge removal. Intrinsic
diameters are controlled using ambient simple paths, even if the removed
edges were shortcuts. The model precision records the missing-degree charge.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000
namespace LocalLaw
local instance edgeSubgraphModelDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type} [Fintype V] [DecidableEq V]

theorem componentwise_subgraph_intrinsic_diameter (G H : SimpleGraph V) (hHG : H≤G) (Ω D : ℕ)
    (hΩ : ∀ C : G.ConnectedComponent,graphExcess (G.induce C.supp)≤Ω)
    (hD : ∀ a b,G.dist a b≤D) (a b : V) : H.dist a b≤(Ω+1)*(2*D+1) := by
  by_cases hr : H.Reachable a b
  · obtain ⟨p,hp,hlen⟩:=hr.exists_path_of_dist
    have hh:=componentwise_path_length_le_excess_diameter G Ω D hΩ hD
      (p.mapLe hHG) (hp.mapLe hHG)
    simpa only [SimpleGraph.Walk.length_map,hlen] using hh
  · rw [SimpleGraph.dist_eq_zero_of_not_reachable hr]
    exact Nat.zero_le _

namespace DeficientGraph
variable {d : ℕ}

def edgeSubgraph (g : DeficientGraph V d) (H : SimpleGraph V) (hHG : H≤g.graph) : DeficientGraph V d where
  graph:=H
  deficit:=g.deficit
  degree_deficit_le v:= (Nat.add_le_add_right (SimpleGraph.degree_le_of_le hHG) _).trans (g.degree_deficit_le v)

omit [DecidableEq V] in
theorem edgeSubgraph_componentFiniteReferenceBudget (g : DeficientGraph V d)
    (H : SimpleGraph V) (hHG : H≤g.graph) (hbudget : g.ComponentFiniteReferenceBudget) :
    (g.edgeSubgraph H hHG).ComponentFiniteReferenceBudget := by
  intro C
  letI : DecidablePred (fun v : V=>v∈C.supp) := fun _=>Classical.propDecidable _
  have hInd : H.induce C.supp≤g.graph.induce C.supp := fun _ _ h=>hHG h
  have hconnH : (H.induce C.supp).Connected := C.connected_induce_supp
  have hconnG : (g.graph.induce C.supp).Connected := SimpleGraph.Connected.mono hInd hconnH
  have hex:=connected_graphExcess_mono hInd hconnH hconnG
  have hb:=g.connected_restrict_finiteReferenceBudget C.supp hconnG hbudget
  rcases hb with hb|⟨hb,hpos⟩
  · apply Or.inl
    change (∑v:C.supp,g.deficit v.val)+graphExcess (H.induce C.supp)≤finiteOmega d
    change (∑v:C.supp,g.deficit v.val)+graphExcess (g.graph.induce C.supp)≤finiteOmega d at hb
    omega
  · apply Or.inr
    refine ⟨?_,hpos⟩
    change (∑v:C.supp,g.deficit v.val)+graphExcess (H.induce C.supp)≤finiteOmega d+1
    change (∑v:C.supp,g.deficit v.val)+graphExcess (g.graph.induce C.supp)≤finiteOmega d+1 at hb
    omega

theorem edgeSubgraph_intrinsic_diameter (g : DeficientGraph V d) (H : SimpleGraph V) (hHG : H≤g.graph)
    (hbudget : g.ComponentFiniteReferenceBudget) (D : ℕ) (hD : ∀ a b,g.graph.dist a b≤D) (a b : V) :
    (g.edgeSubgraph H hHG).graph.dist a b≤hereditaryReferenceRadius d D := by
  have hΩ : ∀ C : g.graph.ConnectedComponent,graphExcess (g.graph.induce C.supp)≤finiteOmega d+1 := by
    intro C
    simp only [graphExcess,SimpleGraph.edgeFinset_card,←Nat.card_eq_fintype_card]
    letI : DecidablePred (fun v : V=>v∈C.supp) := fun _=>Classical.propDecidable _
    have hh:=(hbudget C).complexity_le
    have he : graphExcess (g.restrict C.supp).graph≤finiteOmega d+1 := by omega
    simpa only [graphExcess,SimpleGraph.edgeFinset_card,←Nat.card_eq_fintype_card] using he
  exact componentwise_subgraph_intrinsic_diameter g.graph H hHG (finiteOmega d+1) D hΩ hD a b

omit [DecidableEq V] in
theorem edgeSubgraph_boundaryCoefficient_difference (g : DeficientGraph V d)
    (H : SimpleGraph V) (hHG : H≤g.graph) (v : V) :
    (g.edgeSubgraph H hHG).boundaryCoefficient v-g.boundaryCoefficient v=
      ((g.graph.degree v-H.degree v:ℕ):ℝ)/((d:ℝ)-1) := by
  have hdeg : H.degree v≤g.graph.degree v := SimpleGraph.degree_le_of_le hHG
  simp only [boundaryCoefficient,edgeSubgraph,Nat.cast_sub hdeg]
  ring

theorem edgeSubgraph_extensionMatrix_difference (g : DeficientGraph V d)
    (H : SimpleGraph V) (hHG : H≤g.graph) (q z : ℂ) :
    (g.edgeSubgraph H hHG).extensionMatrix q z-g.extensionMatrix q z=
      normalizedAdjacency H d-g.H-
        q • Matrix.diagonal (fun v=>((g.graph.degree v-H.degree v:ℕ):ℂ)/((d:ℂ)-1)) := by
  have hcoef (v : V) : ((g.edgeSubgraph H hHG).boundaryCoefficient v:ℂ)-(g.boundaryCoefficient v:ℂ)=
      ((g.graph.degree v-H.degree v:ℕ):ℂ)/((d:ℂ)-1) := by
    rw [←Complex.ofReal_sub,g.edgeSubgraph_boundaryCoefficient_difference H hHG v]
    push_cast
    rfl
  have hD : (g.edgeSubgraph H hHG).boundaryDiagonal-g.boundaryDiagonal=
      Matrix.diagonal (fun v=>((g.graph.degree v-H.degree v:ℕ):ℂ)/((d:ℂ)-1)) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simpa only [boundaryDiagonal,Matrix.sub_apply,Matrix.diagonal_apply_eq] using hcoef i
    · simp only [boundaryDiagonal,Matrix.sub_apply,Matrix.diagonal_apply_ne _ hij,sub_self]
  have hH : (g.edgeSubgraph H hHG).H=normalizedAdjacency H d := rfl
  rw [←hD]
  unfold extensionMatrix boundaryMatrix
  rw [hH]
  ext i j
  simp only [spectralMatrix,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring

end DeficientGraph
end LocalLaw
