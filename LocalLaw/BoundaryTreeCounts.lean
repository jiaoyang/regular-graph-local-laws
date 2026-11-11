import LocalLaw.BoundaryNearCounts
import LocalLaw.GraphExcessSurgery

/-!
# Only few boundary branches have non-tree outside neighborhoods

A cyclic annulus component spends at least its attachment multiplicity in
the exact cutset Euler charge. Hence at most omega actual boundary labels
belong to cyclic components. A short outside ball at a boundary endpoint
embeds into its actual annulus component, so non-tree such balls are counted
by this same deterministic omega budget.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
namespace LocalLaw

local instance boundaryTreeCountsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V]

theorem cyclic_attachment_sum_bound (G : SimpleGraph V) (T : Set V)
    (hG : G.Connected) (hT : (G.induce T).Connected) :
    (∑ C ∈ (Finset.univ : Finset (CutComponent G T)).filter
      (fun C => 0 < graphExcess (cutComponentGraph G T C)), cutMultiplicity G T C) ≤ graphExcess G := by
  have hTnonempty : T.Nonempty := by
    obtain ⟨t⟩ := hT.nonempty
    exact ⟨t.val, t.property⟩
  have hpoint : ∀ C, 0 < graphExcess (cutComponentGraph G T C) →
      cutMultiplicity G T C ≤ cutExcessCharge G T C := by
    intro C hpos
    have h := cutExcessCharge_add_one G T hG hTnonempty C
    omega
  have hEuler := connected_cutset_excess_identity G T hG hT
  calc
    _ ≤ ∑ C ∈ (Finset.univ : Finset (CutComponent G T)).filter
        (fun C => 0 < graphExcess (cutComponentGraph G T C)), cutExcessCharge G T C :=
      Finset.sum_le_sum (fun C hC => hpoint C (Finset.mem_filter.mp hC).2)
    _ ≤ ∑ C : CutComponent G T, cutExcessCharge G T C :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
    _ ≤ graphExcess G := by omega

theorem connected_nonTree_excess_positive (G : SimpleGraph V) (hG : G.Connected)
    (hnot : ¬ G.IsTree) : 0 < graphExcess G := by
  by_contra hnonpos
  have hzero : graphExcess G = 0 := by omega
  have heuler := connected_graph_excess_euler G hG
  have hcard : Nat.card G.edgeSet + 1 = Nat.card V := by
    unfold graphEdgeCount at heuler
    omega
  exact hnot (SimpleGraph.isTree_iff_connected_and_card.mpr ⟨hG, hcard⟩)

/-- An actual outside boundary ball embeds into its actual annulus component. -/
theorem boundary_ball_excess_le_annulus_component (G : SimpleGraph V) (o : V)
    (ell R h : ℕ) (hmargin : ell + 1 + h ≤ R)
    (e : BoundaryOrientedEdge G (graphBallVertices G o ell)) :
    graphBallExcess (outsideGraph G (graphBallVertices G o ell))
      (boundaryOuterEndpoint G _ e) h ≤
      graphExcess (cutComponentGraph (graphBall G o R) (ballCutInner G o ell R)
        (ambientBoundaryComponent G o (show ell + 1 ≤ R by omega) e)) := by
  let T := graphBallVertices G o ell
  let a := boundaryOuterEndpoint G T e
  let C := ambientBoundaryComponent G o (show ell + 1 ≤ R by omega) e
  have hvertices : ∀ v : graphBallVertices (outsideGraph G T) a h,
      ∃ w : C.supp, w.val.val.val = v.val.val := by
    intro v
    obtain ⟨hv, hc⟩ := boundary_near_annulus_component G o ell R h hmargin e v.val v.property
    exact ⟨⟨⟨⟨v.val.val, hv⟩, v.val.property⟩, hc.symm⟩, rfl⟩
  let f : graphBall (outsideGraph G T) a h →g
      cutComponentGraph (graphBall G o R) (ballCutInner G o ell R) C :=
    { toFun := fun v => Classical.choose (hvertices v)
      map_rel' := by
        intro v w hvw
        change G.Adj (Classical.choose (hvertices v)).val.val.val
          (Classical.choose (hvertices w)).val.val.val
        rw [Classical.choose_spec (hvertices v), Classical.choose_spec (hvertices w)]
        exact hvw }
  have hf : Function.Injective f := by
    intro v w hvw
    have heq := congrArg (fun y : C.supp => y.val.val.val) hvw
    have hraw : v.val.val = w.val.val :=
      (Classical.choose_spec (hvertices v)).symm.trans (heq.trans (Classical.choose_spec (hvertices w)))
    exact Subtype.ext (Subtype.ext hraw)
  have hbound := connected_embedding_graphExcess_le _ _
    (graphBall_connected (outsideGraph G T) a h) C.connected_induce_supp f hf
  simp only [graphBallExcess, graphExcess, SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card] at hbound ⊢
  exact hbound

def boundaryNonTreeIndices (G : SimpleGraph V) (o : V) (ell h : ℕ) :
    Finset (BoundaryOrientedEdge G (graphBallVertices G o ell)) :=
  Finset.univ.filter (fun e => ¬ (graphBall (outsideGraph G (graphBallVertices G o ell))
    (boundaryOuterEndpoint G _ e) h).IsTree)

/-- Only omega actual boundary labels can have a non-tree short outside
ball. This bound keeps repeated labels at a shared outside vertex distinct. -/
theorem boundary_nonTree_ball_count (G : SimpleGraph V) (o : V)
    (ell R h ω : ℕ) (hmargin : ell + 1 + h ≤ R) (hbudget : graphBallExcess G o R ≤ ω) :
    (boundaryNonTreeIndices G o ell h).card ≤ ω := by
  let hR : ell + 1 ≤ R := by omega
  let F := ambientBoundaryComponent G o hR
  let cyclic := (Finset.univ : Finset (BallAnnulusComponent G o ell R)).filter
    (fun C => 0 < graphExcess (cutComponentGraph (graphBall G o R) (ballCutInner G o ell R) C))
  have hmaps : Set.MapsTo F (boundaryNonTreeIndices G o ell h) cyclic := by
    intro e he
    have hnot := (Finset.mem_filter.mp he).2
    have hpos := connected_nonTree_excess_positive _
      (graphBall_connected (outsideGraph G (graphBallVertices G o ell)) (boundaryOuterEndpoint G _ e) h) hnot
    have hle := boundary_ball_excess_le_annulus_component G o ell R h hmargin e
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos.trans_le hle⟩
  have hcount := Finset.card_eq_sum_card_fiberwise
    (f := F) (s := boundaryNonTreeIndices G o ell h) (t := cyclic) hmaps
  have hsum := cyclic_attachment_sum_bound (graphBall G o R) (ballCutInner G o ell R)
    (graphBall_connected G o R) (ballCutInner_connected G o (show ell ≤ R by omega))
  have hsumBound : (∑ C ∈ cyclic, Nat.card (AmbientBallBoundaryFiber G o hR C)) ≤ ω := by
    have hcap := hbudget
    simp only [ambientBallBoundaryFiber_card, cyclic, Finset.sum_filter, graphBallExcess,
      graphExcess, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
      ← finsum_eq_sum_of_fintype] at hsum hcap ⊢
    exact hsum.trans hcap
  calc
    _ = ∑ C ∈ cyclic, ((boundaryNonTreeIndices G o ell h).filter (fun e => F e = C)).card := hcount
    _ ≤ ∑ C ∈ cyclic, Nat.card (AmbientBallBoundaryFiber G o hR C) := by
      apply Finset.sum_le_sum
      intro C _
      rw [ambientBoundaryFiber_card_filter G o hR C]
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
    _ ≤ ω := hsumBound

end LocalLaw
