import SpectralConsequences.ParentEvenLocalization

/-! Finite cycle-space assembly transfers localization of connected tree
fundamental cycles to the entire excess of a ball. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace SpectralConsequences
open LocalLaw
local instance connectedCycleTransferDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {U V:Type*}[Fintype U][Fintype V]

omit [Fintype V] in
theorem acyclic_of_connected_generators_empty (B:SimpleGraph U)(D:HeightParentData U)
    (hDB:D.tree≤B)
    (hempty:∀F:EvenEdgeSubgraph B,(D.tree.induce F.val.support).Connected→F.val=⊥):
    B.IsAcyclic:=by
  have hBD:B≤D.tree:=by
    intro a b hab
    by_contra hnot
    obtain ⟨p,hp⟩:=D.tree_isTree.isConnected.exists_isPath b a
    obtain ⟨F,hcode,_,hconn⟩:=
      fundamental_even_cycle_with_connected_tree_support B D.tree hDB hab hnot p hp
    have he:(⟨s(a,b),hab,hnot⟩:(B\D.tree).edgeSet)∈evenSubgraphCode B D.tree F:=by
      rw [hcode]
      exact Set.mem_singleton _
    change s(a,b)∈F.val.edgeSet at he
    rw [hempty F hconn] at he
    exact he
  exact graph_acyclic_of_le hBD D.tree_isTree.IsAcyclic

theorem all_even_support_of_connected_generators (B:SimpleGraph U)(D:HeightParentData U)
    (hDB:D.tree≤B)(S:Set U)
    (hlocal:∀F:EvenEdgeSubgraph B,(D.tree.induce F.val.support).Connected→F.val.support⊆S)
    (C:EvenEdgeSubgraph B):C.val.support⊆S:=by
  let A:Set U:=Sᶜ
  have hgens:∀e:(B\D.tree).edgeSet,∃F:EvenEdgeSubgraph B,
      evenSubgraphCode B D.tree F={e} ∧∀v∈A,v∉F.val.support:=by
    rintro ⟨z,hz⟩
    induction z using Sym2.inductionOn with
    | _ a b =>
      change B.Adj a b ∧¬D.tree.Adj a b at hz
      obtain ⟨p,hp⟩:=D.tree_isTree.isConnected.exists_isPath b a
      obtain ⟨F,hcode,_,hconn⟩:=
        fundamental_even_cycle_with_connected_tree_support B D.tree hDB hz.1 hz.2 p hp
      refine ⟨F,hcode,?_⟩
      intro v hv hm
      exact hv (hlocal F hconn hm)
  let gen:(B\D.tree).edgeSet→EvenEdgeSubgraph B:=fun e=>Classical.choose (hgens e)
  have hcode:∀e,evenSubgraphCode B D.tree (gen e)={e}:=fun e=>(Classical.choose_spec (hgens e)).1
  have havoid:∀e,∀v∈A,v∉(gen e).val.support:=fun e=>(Classical.choose_spec (hgens e)).2
  have hall:=even_subgraphs_avoid_of_generators B D.tree D.tree_isTree.IsAcyclic A gen hcode havoid C
  intro v hv
  by_contra hs
  exact hall v hs hv

theorem excess_le_of_connected_generators (B:SimpleGraph U)(D:HeightParentData U)
    (hDB:D.tree≤B)(hB:B.Connected)(G:SimpleGraph V)(f:U↪V)(S:Set V)
    (hedges:∀C:EvenEdgeSubgraph B,C.val.map f≤G)
    (hlocal:∀F:EvenEdgeSubgraph B,(D.tree.induce F.val.support).Connected→
      ∀v∈F.val.support,f v∈S):graphExcess B≤graphExcess (G.induce S):=by
  apply graphExcess_le_of_even_pattern_localization_general B G f S hB hedges
  intro C x hx
  obtain ⟨y,hxy⟩:=((C.val.map f).mem_support).mp hx
  obtain ⟨a,b,hab,rfl,rfl⟩:=(SimpleGraph.map_adj f C.val x y).mp hxy
  exact all_even_support_of_connected_generators B D hDB (f⁻¹' S)
    (fun F hF=>hlocal F hF) C ((C.val.mem_support).mpr ⟨b,hab⟩)

end SpectralConsequences
