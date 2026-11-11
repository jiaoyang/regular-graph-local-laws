import LocalLaw.TripleTreeTest

/-!
# Actual ambient tree neighborhoods of well-separated sampled edges

If a sampled endpoint's ambient R-ball meets T, a shortest walk to T meets
an outside boundary root within R. Thus an edge outside the marked boundary
hit set has its entire ambient two-root R-neighborhood outside T. Lifting
the short walks identifies it with a subgraph of the outside pair tree.
The cross-coordinate sample-separation test also excludes every other
resampling exterior triple from this actual ambient tree neighborhood.
-/

noncomputable section
set_option maxHeartbeats 1400000
namespace LocalLaw

local instance sampleTreeNeighborhoodDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*}

theorem walk_to_set_hits_boundary (G : SimpleGraph V) (T : Set V) {x t : V}
    (p : G.Walk x t) (hx : x ∉ T) (ht : t ∈ T) :
    ∃ e : BoundaryOrientedEdge G T, ∃ q : G.Walk x e.val.2, q.length ≤ p.length := by
  induction p with
  | nil => exact False.elim (hx ht)
  | @cons x y t hxy p ih =>
    by_cases hy : y ∈ T
    · exact ⟨⟨(y, x), hxy.symm, hy, hx⟩, SimpleGraph.Walk.nil, Nat.zero_le _⟩
    · obtain ⟨e, q, hq⟩ := ih hy ht
      exact ⟨e, q.cons hxy, by simpa only [SimpleGraph.Walk.length_cons] using Nat.succ_le_succ hq⟩

theorem walk_lift_induce_of_support (G : SimpleGraph V) (A : Set V) {x y : V}
    (p : G.Walk x y) (ha : x ∈ A) (hb : y ∈ A)
    (hsupport : ∀ v ∈ p.support, v ∈ A) :
    ∃ q : (G.induce A).Walk ⟨x, ha⟩ ⟨y, hb⟩, q.length = p.length := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons x u y hxu p ih =>
    have hu : u ∈ A := hsupport u (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons]; exact Or.inr p.start_mem_support)
    have htail : ∀ v ∈ p.support, v ∈ A := fun v hv =>
      hsupport v (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons]; exact Or.inr hv)
    obtain ⟨q, hq⟩ := ih hu hb htail
    have hadj : (G.induce A).Adj ⟨x, ha⟩ ⟨u, hu⟩ := hxu
    exact ⟨q.cons hadj, by simp only [SimpleGraph.Walk.length_cons, hq]⟩

/-- A short ambient ball contained in A retains its short distances after
inducing on A. The paths are lifted explicitly, not inferred from ambient
distance alone. -/
theorem ambient_ball_mem_induced (G : SimpleGraph V) (A : Set V) (x : V) (hx : x ∈ A)
    (R : ℕ) (hball : graphBallVertices G x R ⊆ A)
    (v : graphBallVertices G x R) :
    (G.induce A).edist ⟨x, hx⟩ ⟨v.val, hball v.property⟩ ≤ (R : ℕ∞) := by
  have hfinite := ne_top_of_le_ne_top (ENat.coe_ne_top R) v.property
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hfinite
  have hlen : p.length ≤ R := ENat.coe_le_coe.mp (hp.trans_le v.property)
  have hsupp : ∀ u ∈ p.support, u ∈ A := by
    intro u hu
    apply hball
    exact (G.edist_le (p.takeUntil u hu)).trans
      (ENat.coe_le_coe.mpr ((p.length_takeUntil_le hu).trans hlen))
  obtain ⟨q, hq⟩ := walk_lift_induce_of_support G A p hx (hball v.property) hsupp
  exact (SimpleGraph.edist_le q).trans (ENat.coe_le_coe.mpr (hq.trans_le hlen))

variable [Fintype V]

theorem ambient_ball_meeting_set_near_boundary (G : SimpleGraph V) (T : Set V)
    (R : ℕ) {x t : V} (hx : x ∉ T) (ht : t ∈ T) (hnear : G.edist x t ≤ (R : ℕ∞)) :
    x ∈ graphSetBall G (boundaryExteriorRoots G T) R := by
  have hfinite := ne_top_of_le_ne_top (ENat.coe_ne_top R) hnear
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hfinite
  have hlen : p.length ≤ R := ENat.coe_le_coe.mp (hp.trans_le hnear)
  obtain ⟨e, q, hq⟩ := walk_to_set_hits_boundary G T p hx ht
  refine ⟨e.val.2, Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩, ?_⟩
  exact (G.edist_le q.reverse).trans (by
    simpa only [SimpleGraph.Walk.length_reverse] using ENat.coe_le_coe.mpr (hq.trans hlen))

theorem sampled_ambient_pair_ball_avoids_interior (G : SimpleGraph V) (T : Set V)
    (R : ℕ) (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (hmark : α ∉ sampledBoundaryHitIndices G T R S) :
    ∀ v ∈ pairBallVertices G (S α).val.1 (S α).val.2 R, v ∉ T := by
  intro v hv hvT
  apply hmark
  apply (mem_endpointHitIndices G T _ S α).mpr
  rcases hv with hv | hv
  · exact Or.inl (Set.mem_toFinset.mpr (ambient_ball_meeting_set_near_boundary G T R
      (S α).property.2.1 hvT hv))
  · exact Or.inr (Set.mem_toFinset.mpr (ambient_ball_meeting_set_near_boundary G T R
      (S α).property.2.2 hvT hv))

/-- The actual ambient sampled pair neighborhood is a tree. The marked-hit
test is what rules out ambient shortcuts through T. -/
theorem sampled_ambient_pair_ball_isTree (G : SimpleGraph V) (T : Set V)
    (R : ℕ) (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (hmark : α ∉ sampledBoundaryHitIndices G T R S)
    (htree : α ∉ nonTreeSampledPairIndices G T R S) :
    (pairBallGraph G (S α).val.1 (S α).val.2 R).IsTree := by
  let b := sampledFirstOutsideVertex G T S α
  let c := sampledSecondOutsideVertex G T S α
  have hout := sampled_ambient_pair_ball_avoids_interior G T R S α hmark
  have hB : (pairBallGraph (outsideGraph G T) b c R).IsTree := by
    by_contra hn
    exact htree (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
  have hmem : ∀ v : pairBallVertices G (S α).val.1 (S α).val.2 R,
      (outsideGraph G T).edist b ⟨v.val, hout v.val v.property⟩ ≤ (R : ℕ∞) ∨
        (outsideGraph G T).edist c ⟨v.val, hout v.val v.property⟩ ≤ (R : ℕ∞) := by
    intro v
    rcases v.property with hv | hv
    · apply Or.inl
      exact ambient_ball_mem_induced G {v | v ∉ T} (S α).val.1 (S α).property.2.1 R
        (fun u hu => hout u (Or.inl hu)) ⟨v.val, hv⟩
    · apply Or.inr
      exact ambient_ball_mem_induced G {v | v ∉ T} (S α).val.2 (S α).property.2.2 R
        (fun u hu => hout u (Or.inr hu)) ⟨v.val, hv⟩
  let f : pairBallGraph G (S α).val.1 (S α).val.2 R →g pairBallGraph (outsideGraph G T) b c R :=
    { toFun := fun v => ⟨⟨v.val, hout v.val v.property⟩, hmem v⟩
      map_rel' := fun h => h }
  have hf : Function.Injective f := by
    intro v w h
    exact Subtype.ext (congrArg (fun z : pairBallVertices (outsideGraph G T) b c R => z.val.val) h)
  refine ⟨pairBall_connected_of_adj G (S α).property.1 R, ?_⟩
  intro v p hp
  exact hB.IsAcyclic (p.map f) (hp.map hf)

/-- Every other resampling exterior triple avoids this actual ambient tree
neighborhood. This derives the metric-to-geometry bridge from the deleted
graph separation test. -/
theorem sampled_ambient_pair_ball_avoids_other_triples (G : SimpleGraph V) (T : Set V)
    (R : ℕ) (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (hmark : α ∉ sampledBoundaryHitIndices G T R S)
    (hother : α ∉ sampledOtherTripleIndices G T R S) :
    ∀ β : BoundaryOrientedEdge G T, β ≠ α → ∀ y ∈ outsideTriple G T S β,
      y.val ∉ pairBallVertices G (S α).val.1 (S α).val.2 R := by
  intro β hβα y hy hW
  have hout := sampled_ambient_pair_ball_avoids_interior G T R S α hmark
  apply hother
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, β, hβα, y, hy, ?_⟩
  rcases hW with hb | hc
  · apply Or.inl
    exact ambient_ball_mem_induced G {v | v ∉ T} (S α).val.1 (S α).property.2.1 R
      (fun u hu => hout u (Or.inl hu)) ⟨y.val, hb⟩
  · apply Or.inr
    exact ambient_ball_mem_induced G {v | v ∉ T} (S α).val.2 (S α).property.2.2 R
      (fun u hu => hout u (Or.inr hu)) ⟨y.val, hc⟩

end LocalLaw
