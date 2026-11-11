import SpectralConsequences.ProtectedSamplePatches
import LocalLaw.BadSampleAddedEdges
import LocalLaw.ShortPatchWalks

/-! Literal changed-edge and short-walk adapters for protected sample patches. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance protectedPatchEdgesDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type*}{T:Set V}{ι:Type*}[Fintype ι]

/-- Every genuinely new edge is one of the two added edges of an originally
selected coordinate, with its actual accepted index supplied. -/
theorem fullResample_new_edge_cases (s:LocalLaw.LabelledResamplingState V T ι)(selector:ℕ)
    {x y:V}(hnew:(s.fullResample selector).graph.Adj x y)(hold:¬s.graph.Adj x y):
    ∃i:ι,s.Eligible selector i ∧
      ((x=(s.quad i).a ∧ y=(s.quad i).d)∨(x=(s.quad i).d ∧ y=(s.quad i).a)∨
       (x=(s.quad i).b ∧ y=(s.quad i).c)∨(x=(s.quad i).c ∧ y=(s.quad i).b)):=by
  have hh:(applySwitches (s.selectedQuads selector (Finset.univ:Finset ι).toList) s.graph).Adj x y:=by
    rw [←s.fullResample_graph_eq_applySwitches selector]
    exact hnew
  rcases applySwitches_edge_provenance _ s.graph hh with h|⟨q,hq,hadded⟩
  · exact False.elim (hold h)
  · obtain ⟨i,_,hi,hqi⟩:=(s.mem_selectedQuads selector _ q).mp hq
    refine ⟨i,hi,?_⟩
    rw [←hqi] at hadded
    simp only [switchingAdded,SimpleGraph.sup_adj,SimpleGraph.edge_adj] at hadded
    exact hadded.elim (fun h=>h.1.elim (fun h=>Or.inl h) (fun h=>Or.inr (Or.inl h)))
      (fun h=>h.1.elim (fun h=>Or.inr (Or.inr (Or.inl h))) (fun h=>Or.inr (Or.inr (Or.inr h))))

variable {s:LocalLaw.LabelledResamplingState V T ι}{selector R:ℕ}

theorem ProtectedPatches.inside (h:ProtectedPatches s selector R)(i:ι)
    (u v:protectedPatch s R i)(huv:(s.fullResample selector).graph.Adj u.val v.val):
    ((s.graph.induce (protectedPatch s R i))\SimpleGraph.edge
      (⟨(s.quad i).c,Or.inl (center_mem_graphBall _ _ _)⟩:protectedPatch s R i)
      (⟨(s.quad i).d,Or.inr (center_mem_graphBall _ _ _)⟩:protectedPatch s R i)).Adj u v:=by
  have ha:(s.quad i).a∉protectedPatch s R i:=fun hv=>Set.disjoint_left.mp (h.inner_disjoint i) hv
    (sampledSwitching_root_mem s.graph T s.samples (s.boundary i))
  exact (s.quad i).apply_inside_patch s.graph (protectedPatch s R i) ha (h.boundary_avoided i i)
    (Or.inl (center_mem_graphBall _ _ _)) (Or.inr (center_mem_graphBall _ _ _)) u v
    ((h.incident_exact i u.val u.property v.val).mp huv)

theorem ProtectedPatches.cross (h:ProtectedPatches s selector R)(i:ι)
    (u:V)(hu:u∈protectedPatch s R i)(v:V)(hv:v∉protectedPatch s R i)
    (huv:(s.fullResample selector).graph.Adj u v):
    s.graph.Adj u v∨(u=(s.quad i).c ∧ v=(s.quad i).b)∨(u=(s.quad i).d ∧ v=(s.quad i).a):=by
  have ha:(s.quad i).a∉protectedPatch s R i:=fun hx=>Set.disjoint_left.mp (h.inner_disjoint i) hx
    (sampledSwitching_root_mem s.graph T s.samples (s.boundary i))
  exact (s.quad i).apply_cross_patch s.graph (protectedPatch s R i) ha (h.boundary_avoided i i) hu hv
    ((h.incident_exact i u hu v).mp huv)

/-- Any short walk from the first sample root avoiding its own new attachment
stays in the corresponding branch of the old tree with b-c removed. -/
theorem ProtectedPatches.first_short_walk (h:ProtectedPatches s selector R)(i:ι)
    {v:V}(p:(s.fullResample selector).graph.Walk (s.quad i).c v)
    (hlen:p.length≤2*R+1)(hentry:s((s.quad i).c,(s.quad i).b)∉p.edges):
    ∃hv:v∈protectedPatch s R i,∃q:((s.graph.induce (protectedPatch s R i))\SimpleGraph.edge
      (⟨(s.quad i).c,Or.inl (center_mem_graphBall _ _ _)⟩:protectedPatch s R i)
      (⟨(s.quad i).d,Or.inr (center_mem_graphBall _ _ _)⟩:protectedPatch s R i)).Walk
        ⟨(s.quad i).c,Or.inl (center_mem_graphBall _ _ _)⟩ ⟨v,hv⟩,
      q.length=p.length ∧ ∀w∈p.support,w∈protectedPatch s R i:=by
  exact short_walk_avoiding_patch_entry_with_support s.graph (s.fullResample selector).graph
    (protectedPatch s R i) (s.quad i).c (s.quad i).d (s.quad i).b (s.quad i).a
    (Or.inl (center_mem_graphBall _ _ _)) (Or.inr (center_mem_graphBall _ _ _))
    (s.samples (s.boundary i)).property.1 (h.tree i) (2*R+1)
    (fun w hw=>lt_of_not_ge (fun hnear=>hw (Or.inl hnear)))
    (h.inside i) (h.cross i) p hlen hentry

/-- The other split branch has the same support statement, with the two
attachments interchanged. -/
theorem ProtectedPatches.second_short_walk_support (h:ProtectedPatches s selector R)(i:ι)
    {v:V}(p:(s.fullResample selector).graph.Walk (s.quad i).d v)
    (hlen:p.length≤2*R+1)(hentry:s((s.quad i).d,(s.quad i).a)∉p.edges):
    ∀w∈p.support,w∈protectedPatch s R i:=by
  have hinside:∀u v:protectedPatch s R i,(s.fullResample selector).graph.Adj u.val v.val→
      ((s.graph.induce (protectedPatch s R i))\SimpleGraph.edge
        (⟨(s.quad i).d,Or.inr (center_mem_graphBall _ _ _)⟩:protectedPatch s R i)
        (⟨(s.quad i).c,Or.inl (center_mem_graphBall _ _ _)⟩:protectedPatch s R i)).Adj u v:=by
    intro u v huv
    rw [SimpleGraph.edge_comm]
    exact h.inside i u v huv
  have hcross:∀u∈protectedPatch s R i,∀v∉protectedPatch s R i,
      (s.fullResample selector).graph.Adj u v→s.graph.Adj u v∨
        (u=(s.quad i).d ∧ v=(s.quad i).a)∨(u=(s.quad i).c ∧ v=(s.quad i).b):=by
    intro u hu v hv huv
    rcases h.cross i u hu v hv huv with hold|hc|hd
    · exact Or.inl hold
    · exact Or.inr (Or.inr hc)
    · exact Or.inr (Or.inl hd)
  obtain ⟨_,_,_,hs⟩:=short_walk_avoiding_patch_entry_with_support s.graph (s.fullResample selector).graph
    (protectedPatch s R i) (s.quad i).d (s.quad i).c (s.quad i).a (s.quad i).b
    (Or.inr (center_mem_graphBall _ _ _)) (Or.inl (center_mem_graphBall _ _ _))
    (s.samples (s.boundary i)).property.1.symm (h.tree i) (2*R+1)
    (fun w hw=>lt_of_not_ge (fun hnear=>hw (Or.inr hnear))) hinside hcross p hlen hentry
  exact hs

private theorem reverse_path_avoids_entry (H:SimpleGraph V){x b a:V}(p:H.Walk x b)
    (hba:H.Adj b a)(hp:(p.concat hba).IsPath):s(b,a)∉p.reverse.edges:=by
  have hnot:a∉p.support:=by
    have hr:=hp.reverse
    rw [SimpleGraph.Walk.reverse_concat] at hr
    have ha:=(SimpleGraph.Walk.cons_isPath_iff _ _).mp hr |>.2
    simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using ha
  intro he
  rw [SimpleGraph.Walk.edges_reverse,List.mem_reverse] at he
  exact hnot (p.snd_mem_support_of_mem_edges he)

/-- A path about to leave the first branch started inside that same OLD branch. -/
theorem ProtectedPatches.first_path_before_entry (h:ProtectedPatches s selector R)(i:ι)
    {center:V}(p:(s.fullResample selector).graph.Walk center (s.quad i).c)
    (hentry:(s.fullResample selector).graph.Adj (s.quad i).c (s.quad i).b)
    (hp:(p.concat hentry).IsPath)(hlen:p.length≤2*R+1):
    ∃hc:center∈protectedPatch s R i,∃q:((s.graph.induce (protectedPatch s R i))\SimpleGraph.edge
      (⟨(s.quad i).c,Or.inl (center_mem_graphBall _ _ _)⟩:protectedPatch s R i)
      (⟨(s.quad i).d,Or.inr (center_mem_graphBall _ _ _)⟩:protectedPatch s R i)).Walk
        ⟨(s.quad i).c,Or.inl (center_mem_graphBall _ _ _)⟩ ⟨center,hc⟩,q.length=p.length:=by
  obtain ⟨hc,q,hq,_⟩:=h.first_short_walk i p.reverse
    (by simpa only [SimpleGraph.Walk.length_reverse] using hlen)
    (reverse_path_avoids_entry _ p hentry hp)
  exact ⟨hc,q,by simpa only [SimpleGraph.Walk.length_reverse] using hq⟩

/-- The analogous OLD-branch path at the second port and its inner attachment. -/
theorem ProtectedPatches.second_path_before_entry (h:ProtectedPatches s selector R)(i:ι)
    {center:V}(p:(s.fullResample selector).graph.Walk center (s.quad i).d)
    (hentry:(s.fullResample selector).graph.Adj (s.quad i).d (s.quad i).a)
    (hp:(p.concat hentry).IsPath)(hlen:p.length≤2*R+1):
    ∃hc:center∈protectedPatch s R i,∃q:((s.graph.induce (protectedPatch s R i))\SimpleGraph.edge
      (⟨(s.quad i).d,Or.inr (center_mem_graphBall _ _ _)⟩:protectedPatch s R i)
      (⟨(s.quad i).c,Or.inl (center_mem_graphBall _ _ _)⟩:protectedPatch s R i)).Walk
        ⟨(s.quad i).d,Or.inr (center_mem_graphBall _ _ _)⟩ ⟨center,hc⟩,q.length=p.length:=by
  have hinside:∀u v:protectedPatch s R i,(s.fullResample selector).graph.Adj u.val v.val→
      ((s.graph.induce (protectedPatch s R i))\SimpleGraph.edge
        (⟨(s.quad i).d,Or.inr (center_mem_graphBall _ _ _)⟩:protectedPatch s R i)
        (⟨(s.quad i).c,Or.inl (center_mem_graphBall _ _ _)⟩:protectedPatch s R i)).Adj u v:=by
    intro u v huv
    rw [SimpleGraph.edge_comm]
    exact h.inside i u v huv
  have hcross:∀u∈protectedPatch s R i,∀v∉protectedPatch s R i,
      (s.fullResample selector).graph.Adj u v→s.graph.Adj u v∨
        (u=(s.quad i).d ∧ v=(s.quad i).a)∨(u=(s.quad i).c ∧ v=(s.quad i).b):=by
    intro u hu v hv huv
    rcases h.cross i u hu v hv huv with hold|hc|hd
    · exact Or.inl hold
    · exact Or.inr (Or.inr hc)
    · exact Or.inr (Or.inl hd)
  obtain ⟨hc,q,hq,_⟩:=short_walk_avoiding_patch_entry_with_support s.graph (s.fullResample selector).graph
    (protectedPatch s R i) (s.quad i).d (s.quad i).c (s.quad i).a (s.quad i).b
    (Or.inr (center_mem_graphBall _ _ _)) (Or.inl (center_mem_graphBall _ _ _))
    (s.samples (s.boundary i)).property.1.symm (h.tree i) (2*R+1)
    (fun w hw=>lt_of_not_ge (fun hnear=>hw (Or.inr hnear))) hinside hcross p.reverse
    (by simpa only [SimpleGraph.Walk.length_reverse] using hlen)
    (reverse_path_avoids_entry _ p hentry hp)
  exact ⟨hc,q,by simpa only [SimpleGraph.Walk.length_reverse] using hq⟩

variable [Fintype V]

/-- Every even pattern in an actual radius-R ball avoids BOTH protected sample
ports. This statement needs no sampling event or reference-model premise. -/
theorem ProtectedPatches.ball_even_avoids_sample (h:ProtectedPatches s selector R)(i:ι)
    (center:V)(C:EvenEdgeSubgraph (graphBall (s.fullResample selector).graph center R)):
    ∀v:graphBallVertices (s.fullResample selector).graph center R,
      v.val=(s.quad i).c∨v.val=(s.quad i).d→v∉C.val.support:=by
  let A:Set V:={(s.quad i).c,(s.quad i).d}
  apply ball_even_patterns_avoid_of_small_patterns (s.fullResample selector).graph center R A ?_ C
  intro F hF heven hsize
  have hh:=even_pattern_avoids_split_tree_roots s.graph (s.fullResample selector).graph
    (protectedPatch s R i) (s.quad i).c (s.quad i).d (s.quad i).b (s.quad i).a
    (Or.inl (center_mem_graphBall _ _ _)) (Or.inr (center_mem_graphBall _ _ _))
    (s.samples (s.boundary i)).property.1 (h.tree i) (2*R+1)
    (fun w hw=>lt_of_not_ge (fun hnear=>hw (Or.inl hnear)))
    (fun w hw=>lt_of_not_ge (fun hnear=>hw (Or.inr hnear)))
    (h.inside i) (h.cross i) F hF heven (hsize.trans (by omega))
  intro x hx
  rcases hx with rfl|rfl
  · exact hh.1
  · exact hh.2

end LabelledResamplingState
end SpectralConsequences
#print axioms SpectralConsequences.LabelledResamplingState.fullResample_new_edge_cases
#print axioms SpectralConsequences.LabelledResamplingState.ProtectedPatches.first_short_walk
