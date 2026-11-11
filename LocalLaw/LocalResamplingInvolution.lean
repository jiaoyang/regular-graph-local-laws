import LocalLaw.LocalResamplingData
import LocalLaw.GraphMetricLocality

/-!
# Local-resampling orientation and boundary transport

For ordered quadruples the involutive update is
  (l,a,b,c) -> (l,c,b,a),
so the updated boundary edge is (l,c) and the updated sampled outside edge is
(b,a). Merely concatenating the printed oriented new edges as (l,c,a,b)
does not give the inverse switching. The undirected switched graph is the same,
but orientation of the sampled edge matters for graph-plus-data involutivity.

This module proves the dependent boundary-index transport, invariance of all
guarded I/J tests, and the full finite labelled graph-plus-data involution. A
uniform boundary labeling may be retained as auxiliary randomness. Preservation
of a dynamically chosen graph ball and the final weight construction are
separate modules. The guarded tree test convention is specified in
LocalResamplingData.
-/

namespace LocalLaw
variable {V : Type*}

namespace SwitchingQuad

@[simp] theorem exterior_inverse (q : SwitchingQuad V) : q.inverse.exterior = q.exterior := by
  ext x
  simp only [exterior, inverse, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- Exact boundary-edge update under one geometrically placed switching. The
other changed edges have both endpoints outside T, so they are not boundary
indices. -/
theorem boundary_adj_after (q : SwitchingQuad V) (G : SimpleGraph V) (T : Set V)
    (hroot : q.a ∈ T) (hext : Disjoint q.exterior T) {x y : V}
    (hx : x ∈ T) (hy : y ∉ T) :
    (q.apply G).Adj x y ↔
      (G.Adj x y ∧ (x, y) ≠ (q.a, q.b)) ∨ (x = q.a ∧ y = q.d) := by
  have hb : q.b ∉ T := fun h => Set.disjoint_left.mp hext (by simp [exterior]) h
  have hc : q.c ∉ T := fun h => Set.disjoint_left.mp hext (by simp [exterior]) h
  have hd : q.d ∉ T := fun h => Set.disjoint_left.mp hext (by simp [exterior]) h
  have hxb : x ≠ q.b := by aesop
  have hxc : x ≠ q.c := by aesop
  have hxd : x ≠ q.d := by aesop
  have hya : y ≠ q.a := by aesop
  have hxy : x ≠ y := by aesop
  simp only [apply, simpleSwitch, switchingRemoved, switchingAdded,
    SimpleGraph.sup_adj, SimpleGraph.sdiff_adj, SimpleGraph.edge_adj,
    hxb, hxc, hxd, hya, hxy, not_false_eq_true, and_true, and_false,
    false_and, or_false, false_or, Prod.mk.injEq]
  simp only [ne_eq, Prod.mk.injEq]
  tauto

end SwitchingQuad

noncomputable section
local instance involutionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Transport the boundary index under one valid boundary switching. -/
def boundarySwitchMap (G : SimpleGraph V) (T : Set V) (q : SwitchingQuad V)
    (hq : q.Admissible G) (hroot : q.a ∈ T) (hext : Disjoint q.exterior T)
    (α : BoundaryOrientedEdge G T) : BoundaryOrientedEdge (q.apply G) T :=
  if h : α.val = (q.a, q.b) then
    ⟨(q.a, q.d), (hq.adj_a q.d).mpr (Or.inr rfl), hroot,
      fun hd => Set.disjoint_left.mp hext (by simp [SwitchingQuad.exterior]) hd⟩
  else
    ⟨α.val, (q.boundary_adj_after G T hroot hext α.property.2.1 α.property.2.2).mpr
      (Or.inl ⟨α.property.1, h⟩), α.property.2⟩

@[simp] theorem boundarySwitchMap_val (G : SimpleGraph V) (T : Set V) (q : SwitchingQuad V)
    (hq : q.Admissible G) (hroot : q.a ∈ T) (hext : Disjoint q.exterior T)
    (α : BoundaryOrientedEdge G T) :
    (boundarySwitchMap G T q hq hroot hext α).val =
      if α.val = (q.a, q.b) then (q.a, q.d) else α.val := by
  unfold boundarySwitchMap
  split <;> simp_all

/-- The newly inserted boundary edge was absent from the original index type. -/
theorem boundaryIndex_ne_new (G : SimpleGraph V) (T : Set V) (q : SwitchingQuad V)
    (hq : q.Admissible G) (α : BoundaryOrientedEdge G T) : α.val ≠ (q.a, q.d) := by
  intro heq
  have hadj := α.property.1
  rw [heq] at hadj
  exact hq.new_ad hadj

/-- The removed boundary edge is absent from the switched index type. -/
theorem switchedBoundaryIndex_ne_old (G : SimpleGraph V) (T : Set V) (q : SwitchingQuad V)
    (hq : q.Admissible G) (β : BoundaryOrientedEdge (q.apply G) T) : β.val ≠ (q.a, q.b) := by
  intro heq
  have hadj := β.property.1
  rw [heq] at hadj
  exact hq.inverse_admissible.new_ad hadj

/-- The boundary-index map is injective: an inserted new index cannot collide
with any unchanged original index. -/
theorem boundarySwitchMap_injective (G : SimpleGraph V) (T : Set V) (q : SwitchingQuad V)
    (hq : q.Admissible G) (hroot : q.a ∈ T) (hext : Disjoint q.exterior T) :
    Function.Injective (boundarySwitchMap G T q hq hroot hext) := by
  intro α β heq
  have hv := congrArg Subtype.val heq
  simp only [boundarySwitchMap_val] at hv
  by_cases ha : α.val = (q.a, q.b)
  · by_cases hb : β.val = (q.a, q.b)
    · exact Subtype.ext (ha.trans hb.symm)
    · simp only [ha, hb, if_true, if_false] at hv
      exact False.elim (boundaryIndex_ne_new G T q hq β hv.symm)
  · by_cases hb : β.val = (q.a, q.b)
    · simp only [ha, hb, if_true, if_false] at hv
      exact False.elim (boundaryIndex_ne_new G T q hq α hv)
    · apply Subtype.ext
      simpa only [ha, hb, if_false] using hv

/-- Every switched boundary index is either the inserted edge or an unchanged
old boundary edge, giving an explicit preimage. -/
theorem boundarySwitchMap_surjective (G : SimpleGraph V) (T : Set V) (q : SwitchingQuad V)
    (hq : q.Admissible G) (hroot : q.a ∈ T) (hext : Disjoint q.exterior T) :
    Function.Surjective (boundarySwitchMap G T q hq hroot hext) := by
  intro β
  by_cases hb : β.val = (q.a, q.d)
  · let α : BoundaryOrientedEdge G T := ⟨(q.a, q.b), hq.old_ab, hroot,
      fun hT => Set.disjoint_left.mp hext (by simp [SwitchingQuad.exterior]) hT⟩
    refine ⟨α, Subtype.ext ?_⟩
    simp only [boundarySwitchMap_val, α, if_true]
    exact hb.symm
  · have hcases := (q.boundary_adj_after G T hroot hext β.property.2.1 β.property.2.2).mp β.property.1
    have hold : G.Adj β.val.1 β.val.2 := by
      rcases hcases with h | ⟨ha, hd⟩
      · exact h.1
      · exact False.elim (hb (Prod.ext ha hd))
    let α : BoundaryOrientedEdge G T := ⟨β.val, hold, β.property.2⟩
    refine ⟨α, Subtype.ext ?_⟩
    rw [boundarySwitchMap_val]
    have ha : α.val ≠ (q.a, q.b) := switchedBoundaryIndex_ne_old G T q hq β
    simp only [ha, if_false]
    rfl

/-- A genuine equivalence of the graph-dependent boundary index types. -/
def boundarySwitchEquiv (G : SimpleGraph V) (T : Set V) (q : SwitchingQuad V)
    (hq : q.Admissible G) (hroot : q.a ∈ T) (hext : Disjoint q.exterior T) :
    BoundaryOrientedEdge G T ≃ BoundaryOrientedEdge (q.apply G) T :=
  Equiv.ofBijective (boundarySwitchMap G T q hq hroot hext)
    ⟨boundarySwitchMap_injective G T q hq hroot hext,
      boundarySwitchMap_surjective G T q hq hroot hext⟩

/-- Shorthand for the concrete boundary equivalence at a selected index. -/
def elementaryBoundaryEquiv (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (hI : ResamplingTreeTest G T radius S α) (hJ : resamplingIsolation G T radius S α) :
    BoundaryOrientedEdge G T ≃ BoundaryOrientedEdge ((sampledSwitchingQuad G T S α).apply G) T :=
  boundarySwitchEquiv G T (sampledSwitchingQuad G T S α)
    (sampledSwitching_admissible G T radius S α hI hJ)
    (sampledSwitching_root_mem G T S α) (sampledSwitching_exterior_disjoint G T S α)

/-- The exterior vertices of every other sampled index lie outside the support
of an isolated switching. This also covers repeated interior leaf vertices. -/
theorem other_exterior_outside_isolated_support (G : SimpleGraph V) (T : Set V)
    (radius : ℕ) (S : LocalSamplingFiber G T) (α β : BoundaryOrientedEdge G T)
    (hJ : resamplingIsolation G T radius S α) (hβα : β ≠ α) {x : V}
    (hx : x ∈ (sampledSwitchingQuad G T S β).exterior) :
    x ∉ (sampledSwitchingQuad G T S α).support := by
  have hdis := isolation_exterior_disjoint G T radius S α β hJ hβα
  have hxT : x ∉ T := fun hT =>
    Set.disjoint_left.mp (sampledSwitching_exterior_disjoint G T S β) hx hT
  intro hsupport
  change x = α.val.1 ∨ x ∈ (sampledSwitchingQuad G T S α).exterior at hsupport
  rcases hsupport with rfl | hα
  · exact hxT α.property.2.1
  · exact Set.disjoint_left.mp hdis hα hx

/-- Updated outside sample, still indexed by the old boundary. Only the
chosen coordinate changes, from (b,c) to (b,a). -/
def updatedSampleOnOldBoundary (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (hI : ResamplingTreeTest G T radius S α) (hJ : resamplingIsolation G T radius S α)
    (β : BoundaryOrientedEdge G T) :
    OutsideOrientedEdge ((sampledSwitchingQuad G T S α).apply G) T :=
  if h : β = α then
    ⟨((S α).val.1, α.val.2),
      ((sampledSwitching_admissible G T radius S α hI hJ).adj_b (S α).val.1).mpr (Or.inr rfl) |>.symm,
      (S α).property.2.1, α.property.2.2⟩
  else
    ⟨(S β).val,
      ((sampledSwitchingQuad G T S α).adj_away G
        (other_exterior_outside_isolated_support G T radius S α β hJ h
          (by simp [sampledSwitchingQuad, SwitchingQuad.exterior]))).mpr (S β).property.1,
      (S β).property.2⟩

@[simp] theorem updatedSampleOnOldBoundary_val (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (hI : ResamplingTreeTest G T radius S α) (hJ : resamplingIsolation G T radius S α)
    (β : BoundaryOrientedEdge G T) :
    (updatedSampleOnOldBoundary G T radius S α hI hJ β).val =
      if β = α then ((S α).val.1, α.val.2) else (S β).val := by
  unfold updatedSampleOnOldBoundary
  split <;> simp_all

/-- The actual new sampling function, pushed to the new boundary-index type. -/
def elementaryResampledData (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (hI : ResamplingTreeTest G T radius S α) (hJ : resamplingIsolation G T radius S α) :
    LocalSamplingFiber ((sampledSwitchingQuad G T S α).apply G) T :=
  fun β => updatedSampleOnOldBoundary G T radius S α hI hJ
    ((boundarySwitchEquiv G T (sampledSwitchingQuad G T S α)
      (sampledSwitching_admissible G T radius S α hI hJ)
      (sampledSwitching_root_mem G T S α)
      (sampledSwitching_exterior_disjoint G T S α)).symm β)

/-- At mapped indices the new sample is precisely the explicit old-index update. -/
theorem elementaryResampledData_at_map (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (hI : ResamplingTreeTest G T radius S α) (hJ : resamplingIsolation G T radius S α)
    (β : BoundaryOrientedEdge G T) :
    elementaryResampledData G T radius S α hI hJ
      (boundarySwitchEquiv G T (sampledSwitchingQuad G T S α)
        (sampledSwitching_admissible G T radius S α hI hJ)
        (sampledSwitching_root_mem G T S α)
        (sampledSwitching_exterior_disjoint G T S α) β) =
      updatedSampleOnOldBoundary G T radius S α hI hJ β := by
  unfold elementaryResampledData
  rw [Equiv.symm_apply_apply]

/-- The transported quadruple is unchanged at every other index and equals
(l,c,b,a) at the selected index. This proves the orientation rule on actual
sampling data, not only on undirected graphs. -/
theorem elementaryResampledQuad_at_map (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (hI : ResamplingTreeTest G T radius S α) (hJ : resamplingIsolation G T radius S α)
    (β : BoundaryOrientedEdge G T) :
    sampledSwitchingQuad ((sampledSwitchingQuad G T S α).apply G) T
      (elementaryResampledData G T radius S α hI hJ)
      (elementaryBoundaryEquiv G T radius S α hI hJ β) =
      if β = α then (sampledSwitchingQuad G T S α).inverse else sampledSwitchingQuad G T S β := by
  let q := sampledSwitchingQuad G T S α
  let e := elementaryBoundaryEquiv G T radius S α hI hJ
  let D := elementaryResampledData G T radius S α hI hJ
  have hb : (e β).val = if β = α then (q.a, q.d) else β.val := by
    change (boundarySwitchMap G T q
      (sampledSwitching_admissible G T radius S α hI hJ)
      (sampledSwitching_root_mem G T S α)
      (sampledSwitching_exterior_disjoint G T S α) β).val = _
    rw [boundarySwitchMap_val]
    have hpair : (q.a, q.b) = α.val := rfl
    rw [hpair]
    by_cases h : β = α
    · simp [h]
    · have hv : β.val ≠ α.val := fun hv => h (Subtype.ext hv)
      simp [h, hv]
  have hs : (D (e β)).val = if β = α then ((S α).val.1, α.val.2) else (S β).val := by
    change (elementaryResampledData G T radius S α hI hJ
      (elementaryBoundaryEquiv G T radius S α hI hJ β)).val = _
    unfold elementaryBoundaryEquiv
    rw [elementaryResampledData_at_map, updatedSampleOnOldBoundary_val]
  change sampledSwitchingQuad (q.apply G) T D (e β) = _
  by_cases h : β = α
  · subst β
    simp only [if_pos rfl] at hb hs
    change SwitchingQuad.mk (e α).val.1 (e α).val.2 (D (e α)).val.1 (D (e α)).val.2 =
      (if α = α then q.inverse else sampledSwitchingQuad G T S α)
    rw [hb, hs]
    simp [q, SwitchingQuad.inverse, sampledSwitchingQuad]
  · simp only [h, if_false] at hb hs
    change SwitchingQuad.mk (e β).val.1 (e β).val.2 (D (e β)).val.1 (D (e β)).val.2 = _
    rw [hb, hs]
    simp only [h, if_false]
    rfl

/-- The unordered exterior triples are unchanged at all transported indices. -/
theorem elementaryResampledExterior_at_map (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (hI : ResamplingTreeTest G T radius S α) (hJ : resamplingIsolation G T radius S α)
    (β : BoundaryOrientedEdge G T) :
    (sampledSwitchingQuad ((sampledSwitchingQuad G T S α).apply G) T
      (elementaryResampledData G T radius S α hI hJ)
      (elementaryBoundaryEquiv G T radius S α hI hJ β)).exterior =
      (sampledSwitchingQuad G T S β).exterior := by
  rw [elementaryResampledQuad_at_map]
  split_ifs with h
  · subst β
    exact SwitchingQuad.exterior_inverse _
  · rfl

/-- The exterior triple as a set of vertices of G(T) is unchanged by transport. -/
theorem elementaryOutsideTriple_at_map (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (hI : ResamplingTreeTest G T radius S α) (hJ : resamplingIsolation G T radius S α)
    (β : BoundaryOrientedEdge G T) :
    outsideTriple ((sampledSwitchingQuad G T S α).apply G) T
      (elementaryResampledData G T radius S α hI hJ)
      (elementaryBoundaryEquiv G T radius S α hI hJ β) = outsideTriple G T S β := by
  ext v
  simp only [outsideTriple, Set.mem_setOf_eq]
  rw [elementaryResampledExterior_at_map]

/-- In the deleted graph, a boundary switching changes only edges internal to
its own exterior triple. The interior leaf is absent from this vertex type. -/
theorem outsideGraph_agree_away_selectedTriple (G : SimpleGraph V) (T : Set V)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    {x y : {v : V // v ∉ T}}
    (h : x ∉ outsideTriple G T S α ∨ y ∉ outsideTriple G T S α) :
    (outsideGraph ((sampledSwitchingQuad G T S α).apply G) T).Adj x y ↔
      (outsideGraph G T).Adj x y := by
  let q := sampledSwitchingQuad G T S α
  have hout : ∀ v : {v : V // v ∉ T}, v ∉ outsideTriple G T S α → v.val ∉ q.support := by
    intro v hv hsupport
    change v.val = α.val.1 ∨ v.val ∈ q.exterior at hsupport
    rcases hsupport with hroot | hext
    · exact v.property (hroot ▸ α.property.2.1)
    · exact hv hext
  change (q.apply G).Adj x.val y.val ↔ G.Adj x.val y.val
  rcases h with hx | hy
  · exact q.adj_away G (hout x hx)
  · rw [(q.apply G).adj_comm, G.adj_comm]
    exact q.adj_away G (hout y hy)

/-- One isolated switching preserves every exterior-triple neighborhood.
Its own triple uses internal-root rewiring; all other triples use the fact
that the changed edges are farther than the tested radius. -/
theorem elementaryTripleBall_preserved (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (hJ : resamplingIsolation G T radius S α) (β : BoundaryOrientedEdge G T) :
    graphSetBall (outsideGraph G T) (outsideTriple G T S β) radius =
      graphSetBall (outsideGraph ((sampledSwitchingQuad G T S α).apply G) T)
        (outsideTriple G T S β) radius := by
  by_cases hβα : β = α
  · subst β
    apply graphSetBall_eq_of_internal_changes
    intro x y hxy
    exact (outsideGraph_agree_away_selectedTriple G T S α hxy).symm
  · have hsep : graphSetsSeparated (outsideGraph G T)
        (outsideTriple G T S β) (outsideTriple G T S α) radius := by
      intro x hx y hy
      rw [SimpleGraph.edist_comm]
      exact hJ β hβα y hy x hx
    have hdis := (graphSetsSeparated_iff_disjoint_ball _ _ _ _).mp hsep
    apply graphSetBall_eq_of_incident_agreement
    intro x y hxy
    apply (outsideGraph_agree_away_selectedTriple G T S α ?_).symm
    rcases hxy with hx | hy
    · exact Or.inl (fun hroot => Set.disjoint_left.mp hdis hx hroot)
    · exact Or.inr (fun hroot => Set.disjoint_left.mp hdis hy hroot)

/-- Actual transported I-test neighborhoods have exactly the same vertices. -/
theorem elementaryNeighborhood_preserved (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (hI : ResamplingTreeTest G T radius S α) (hJ : resamplingIsolation G T radius S α)
    (β : BoundaryOrientedEdge G T) :
    outsideTripleNeighborhood ((sampledSwitchingQuad G T S α).apply G) T radius
      (elementaryResampledData G T radius S α hI hJ)
      (elementaryBoundaryEquiv G T radius S α hI hJ β) =
      outsideTripleNeighborhood G T radius S β := by
  change graphSetBall _ _ radius = graphSetBall _ _ radius
  rw [elementaryOutsideTriple_at_map]
  exact (elementaryTripleBall_preserved G T radius S α hJ β).symm

/-- Set-to-set distance isolation transfers through the actual data map. -/
theorem elementarySeparation_at_map (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (hI : ResamplingTreeTest G T radius S α) (hJ : resamplingIsolation G T radius S α)
    (β γ : BoundaryOrientedEdge G T) :
    graphSetsSeparated (outsideGraph ((sampledSwitchingQuad G T S α).apply G) T)
      (outsideTriple ((sampledSwitchingQuad G T S α).apply G) T
        (elementaryResampledData G T radius S α hI hJ)
        (elementaryBoundaryEquiv G T radius S α hI hJ β))
      (outsideTriple ((sampledSwitchingQuad G T S α).apply G) T
        (elementaryResampledData G T radius S α hI hJ)
        (elementaryBoundaryEquiv G T radius S α hI hJ γ)) radius ↔
      graphSetsSeparated (outsideGraph G T) (outsideTriple G T S β) (outsideTriple G T S γ) radius := by
  rw [elementaryOutsideTriple_at_map, elementaryOutsideTriple_at_map]
  rw [graphSetsSeparated_iff_disjoint_ball, graphSetsSeparated_iff_disjoint_ball,
    ← elementaryTripleBall_preserved G T radius S α hJ β]

/-- Every J indicator is invariant under one accepted elementary resampling.
This is proved for the graph-dependent boundary-index equivalence. -/
theorem elementaryIsolation_invariant (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (hI : ResamplingTreeTest G T radius S α) (hJ : resamplingIsolation G T radius S α)
    (β : BoundaryOrientedEdge G T) :
    resamplingIsolation ((sampledSwitchingQuad G T S α).apply G) T radius
      (elementaryResampledData G T radius S α hI hJ)
      (elementaryBoundaryEquiv G T radius S α hI hJ β) ↔ resamplingIsolation G T radius S β := by
  let e := elementaryBoundaryEquiv G T radius S α hI hJ
  constructor
  · intro hnew γ hγ
    have hne : e γ ≠ e β := fun heq => hγ (e.injective heq)
    exact (elementarySeparation_at_map G T radius S α hI hJ β γ).mp (hnew (e γ) hne)
  · intro hold γnew hγnew
    obtain ⟨γ, rfl⟩ := e.surjective γnew
    have hne : γ ≠ β := fun heq => hγnew (congrArg e heq)
    exact (elementarySeparation_at_map G T radius S α hI hJ β γ).mpr (hold γ hne)

def sampledSecondOutsideVertex (G : SimpleGraph V) (T : Set V) (S : LocalSamplingFiber G T)
    (α : BoundaryOrientedEdge G T) : {v : V // v ∉ T} :=
  ⟨(S α).val.2, (S α).property.2.2⟩

/-- Exact deleted-graph update: remove {b,c} and add {a,b}. -/
theorem elementaryOutsideGraph_update (G : SimpleGraph V) (T : Set V)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T) :
    outsideGraph ((sampledSwitchingQuad G T S α).apply G) T =
      (outsideGraph G T \ SimpleGraph.edge (sampledFirstOutsideVertex G T S α)
        (sampledSecondOutsideVertex G T S α)) ⊔
        SimpleGraph.edge (boundaryOutsideVertex G T α) (sampledFirstOutsideVertex G T S α) := by
  ext x y
  have hx : x.val ≠ α.val.1 := by
    intro heq
    exact x.property (heq ▸ α.property.2.1)
  have hy : y.val ≠ α.val.1 := by
    intro heq
    exact y.property (heq ▸ α.property.2.1)
  change (simpleSwitch G α.val.1 α.val.2 (S α).val.1 (S α).val.2).Adj x.val y.val ↔ _
  simp only [simpleSwitch, switchingRemoved, switchingAdded, SimpleGraph.sup_adj,
    SimpleGraph.sdiff_adj, SimpleGraph.edge_adj, outsideGraph, SimpleGraph.induce,
    boundaryOutsideVertex, sampledFirstOutsideVertex, sampledSecondOutsideVertex,
    Subtype.ext_iff]
  simp only [hx, hy, false_and, and_false, false_or, or_false, not_false_eq_true, and_true]
  simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype, ne_eq, Subtype.ext_iff]

/-- Adding the reverse tree-test edge after switching restores the same
augmented deleted graph used by the original tree test. -/
theorem elementaryAugmentedOutsideGraph_eq (G : SimpleGraph V) (T : Set V)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T) :
    outsideGraph ((sampledSwitchingQuad G T S α).apply G) T ⊔
        SimpleGraph.edge (sampledSecondOutsideVertex G T S α) (sampledFirstOutsideVertex G T S α) =
      outsideGraph G T ⊔ SimpleGraph.edge (boundaryOutsideVertex G T α)
        (sampledFirstOutsideVertex G T S α) := by
  rw [elementaryOutsideGraph_update, SimpleGraph.edge_comm (sampledSecondOutsideVertex G T S α)]
  have hold : SimpleGraph.edge (sampledFirstOutsideVertex G T S α)
      (sampledSecondOutsideVertex G T S α) ≤ outsideGraph G T :=
    sup_eq_left.mp ((outsideGraph G T).sup_edge_of_adj (S α).property.1)
  rw [sup_right_comm, sdiff_sup_cancel hold]

/-- The selected boundary outer vertex becomes the old sampled second endpoint. -/
theorem elementaryBoundaryOutside_selected (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (hI : ResamplingTreeTest G T radius S α) (hJ : resamplingIsolation G T radius S α) :
    boundaryOutsideVertex ((sampledSwitchingQuad G T S α).apply G) T
      (elementaryBoundaryEquiv G T radius S α hI hJ α) = sampledSecondOutsideVertex G T S α := by
  apply Subtype.ext
  have hq := congrArg SwitchingQuad.b (elementaryResampledQuad_at_map G T radius S α hI hJ α)
  simpa only [if_pos rfl] using hq

/-- The selected sampled first endpoint remains b under the involutive orientation. -/
theorem elementarySampledFirst_selected (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (hI : ResamplingTreeTest G T radius S α) (hJ : resamplingIsolation G T radius S α) :
    sampledFirstOutsideVertex ((sampledSwitchingQuad G T S α).apply G) T
      (elementaryResampledData G T radius S α hI hJ)
      (elementaryBoundaryEquiv G T radius S α hI hJ α) = sampledFirstOutsideVertex G T S α := by
  apply Subtype.ext
  have hq := congrArg SwitchingQuad.c (elementaryResampledQuad_at_map G T radius S α hI hJ α)
  simpa only [if_pos rfl] using hq

/-- The selected guarded I-test is valid after the elementary switching. Its
augmented graph and neighborhood are exactly the same as before. -/
theorem elementaryTreeTest_selected (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (hI : ResamplingTreeTest G T radius S α) (hJ : resamplingIsolation G T radius S α) :
    ResamplingTreeTest ((sampledSwitchingQuad G T S α).apply G) T radius
      (elementaryResampledData G T radius S α hI hJ)
      (elementaryBoundaryEquiv G T radius S α hI hJ α) := by
  constructor
  · rw [elementaryBoundaryOutside_selected, elementarySampledFirst_selected]
    intro heq
    have hv := congrArg Subtype.val heq
    exact (S α).property.1.ne hv.symm
  · rw [elementaryBoundaryOutside_selected, elementarySampledFirst_selected]
    exact (sampledSwitching_admissible G T radius S α hI hJ).inverse_admissible.new_bc
  · rw [elementaryBoundaryOutside_selected, elementarySampledFirst_selected,
      elementaryAugmentedOutsideGraph_eq, elementaryNeighborhood_preserved]
    exact hI.tree

/-- All deleted-graph edges incident to another triple's neighborhood are
unchanged by an isolated elementary switching. -/
theorem elementaryOtherNeighborhood_incident_agreement (G : SimpleGraph V) (T : Set V)
    (radius : ℕ) (S : LocalSamplingFiber G T) (α β : BoundaryOrientedEdge G T)
    (hJ : resamplingIsolation G T radius S α) (hβα : β ≠ α)
    (x y : {v : V // v ∉ T})
    (hxy : x ∈ outsideTripleNeighborhood G T radius S β ∨
      y ∈ outsideTripleNeighborhood G T radius S β) :
    (outsideGraph ((sampledSwitchingQuad G T S α).apply G) T).Adj x y ↔
      (outsideGraph G T).Adj x y := by
  have hsep : graphSetsSeparated (outsideGraph G T)
      (outsideTriple G T S β) (outsideTriple G T S α) radius := by
    intro u hu v hv
    rw [SimpleGraph.edist_comm]
    exact hJ β hβα v hv u hu
  have hdis := (graphSetsSeparated_iff_disjoint_ball _ _ _ _).mp hsep
  apply outsideGraph_agree_away_selectedTriple G T S α
  rcases hxy with hx | hy
  · exact Or.inl (fun hs => Set.disjoint_left.mp hdis hx hs)
  · exact Or.inr (fun hs => Set.disjoint_left.mp hdis hy hs)

theorem elementaryBoundaryOutside_other (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α β : BoundaryOrientedEdge G T)
    (hI : ResamplingTreeTest G T radius S α) (hJ : resamplingIsolation G T radius S α)
    (hβα : β ≠ α) :
    boundaryOutsideVertex ((sampledSwitchingQuad G T S α).apply G) T
      (elementaryBoundaryEquiv G T radius S α hI hJ β) = boundaryOutsideVertex G T β := by
  apply Subtype.ext
  have hq := congrArg SwitchingQuad.b (elementaryResampledQuad_at_map G T radius S α hI hJ β)
  simpa only [hβα, if_false] using hq

theorem elementarySampledFirst_other (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α β : BoundaryOrientedEdge G T)
    (hI : ResamplingTreeTest G T radius S α) (hJ : resamplingIsolation G T radius S α)
    (hβα : β ≠ α) :
    sampledFirstOutsideVertex ((sampledSwitchingQuad G T S α).apply G) T
      (elementaryResampledData G T radius S α hI hJ)
      (elementaryBoundaryEquiv G T radius S α hI hJ β) = sampledFirstOutsideVertex G T S β := by
  apply Subtype.ext
  have hq := congrArg SwitchingQuad.c (elementaryResampledQuad_at_map G T radius S α hI hJ β)
  simpa only [hβα, if_false] using hq

/-- Every other guarded I-test is unchanged, including indices whose I-test
or J-test originally failed. The changed edges do not meet its neighborhood. -/
theorem elementaryTreeTest_other (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α β : BoundaryOrientedEdge G T)
    (hI : ResamplingTreeTest G T radius S α) (hJ : resamplingIsolation G T radius S α)
    (hβα : β ≠ α) :
    ResamplingTreeTest ((sampledSwitchingQuad G T S α).apply G) T radius
      (elementaryResampledData G T radius S α hI hJ)
      (elementaryBoundaryEquiv G T radius S α hI hJ β) ↔ ResamplingTreeTest G T radius S β := by
  let H := outsideGraph G T
  let Hnew := outsideGraph ((sampledSwitchingQuad G T S α).apply G) T
  let N := outsideTripleNeighborhood G T radius S β
  let a := boundaryOutsideVertex G T β
  let b := sampledFirstOutsideVertex G T S β
  have haN : a ∈ N := by
    refine ⟨a, ?_, ?_⟩
    · simp [a, outsideTriple, sampledSwitchingQuad, boundaryOutsideVertex, SwitchingQuad.exterior]
    · simp only [SimpleGraph.edist_self]
      exact bot_le
  have habAdj : Hnew.Adj a b ↔ H.Adj a b :=
    elementaryOtherNeighborhood_incident_agreement G T radius S α β hJ hβα a b (Or.inl haN)
  have hinduced : (Hnew ⊔ SimpleGraph.edge a b).induce N = (H ⊔ SimpleGraph.edge a b).induce N := by
    ext x y
    change (Hnew.Adj x.val y.val ∨ (SimpleGraph.edge a b).Adj x.val y.val) ↔
      (H.Adj x.val y.val ∨ (SimpleGraph.edge a b).Adj x.val y.val)
    exact or_congr
      (elementaryOtherNeighborhood_incident_agreement G T radius S α β hJ hβα
        x.val y.val (Or.inl x.property)) Iff.rfl
  have hA := elementaryBoundaryOutside_other G T radius S α β hI hJ hβα
  have hB := elementarySampledFirst_other G T radius S α β hI hJ hβα
  have hN := elementaryNeighborhood_preserved G T radius S α hI hJ β
  constructor
  · intro ht
    constructor
    · simpa only [hA, hB] using ht.distinct
    · have hn : ¬Hnew.Adj a b := by simpa only [hA, hB] using ht.new_edge
      exact fun hh => hn (habAdj.mpr hh)
    · have hh := ht.tree
      rw [hA, hB, hN] at hh
      change ((Hnew ⊔ SimpleGraph.edge a b).induce N).IsTree at hh
      rw [hinduced] at hh
      exact hh
  · intro ht
    constructor
    · rw [hA, hB]
      exact ht.distinct
    · rw [hA, hB]
      exact fun hh => ht.new_edge (habAdj.mp hh)
    · rw [hA, hB, hN]
      change ((Hnew ⊔ SimpleGraph.edge a b).induce N).IsTree
      rw [hinduced]
      exact ht.tree

/-- Every actual guarded I indicator is invariant under one accepted switch. -/
theorem elementaryTreeTest_invariant (G : SimpleGraph V) (T : Set V) (radius : ℕ)
    (S : LocalSamplingFiber G T) (α : BoundaryOrientedEdge G T)
    (hI : ResamplingTreeTest G T radius S α) (hJ : resamplingIsolation G T radius S α)
    (β : BoundaryOrientedEdge G T) :
    ResamplingTreeTest ((sampledSwitchingQuad G T S α).apply G) T radius
      (elementaryResampledData G T radius S α hI hJ)
      (elementaryBoundaryEquiv G T radius S α hI hJ β) ↔ ResamplingTreeTest G T radius S β := by
  by_cases hβα : β = α
  · subst β
    exact ⟨fun _ => hI, fun _ => elementaryTreeTest_selected G T radius S α hI hJ⟩
  · exact elementaryTreeTest_other G T radius S α β hI hJ hβα

/-- A labeling of the actual graph-dependent boundary index type by a fixed
index type. This lets elementary operations be compared without changing
coordinate types; samples are still the actual boundary-indexed functions. -/
structure LabelledResamplingState (V : Type*) (T : Set V) (ι : Type*) where
  graph : SimpleGraph V
  boundary : ι ≃ BoundaryOrientedEdge graph T
  samples : LocalSamplingFiber graph T

namespace LabelledResamplingState
variable {T : Set V} {ι : Type*}

def quad (s : LabelledResamplingState V T ι) (i : ι) : SwitchingQuad V :=
  sampledSwitchingQuad s.graph T s.samples (s.boundary i)

def ITest (s : LabelledResamplingState V T ι) (radius : ℕ) (i : ι) : Prop :=
  ResamplingTreeTest s.graph T radius s.samples (s.boundary i)

def JTest (s : LabelledResamplingState V T ι) (radius : ℕ) (i : ι) : Prop :=
  resamplingIsolation s.graph T radius s.samples (s.boundary i)

/-- The graph and all labelled quadruples determine the complete labelled
sampling state, including the boundary equivalence and all sample coordinates. -/
theorem ext_graph_quad {s t : LabelledResamplingState V T ι}
    (hG : s.graph = t.graph) (hquad : ∀ i, s.quad i = t.quad i) : s = t := by
  cases s with
  | mk G e S =>
    cases t with
    | mk H f D =>
      dsimp only at hG
      subst H
      have hef : e = f := by
        apply Equiv.ext
        intro i
        apply Subtype.ext
        apply Prod.ext
        · exact congrArg SwitchingQuad.a (hquad i)
        · exact congrArg SwitchingQuad.b (hquad i)
      subst f
      have hSD : S = D := by
        funext α
        obtain ⟨i, rfl⟩ := e.surjective α
        apply Subtype.ext
        apply Prod.ext
        · exact congrArg SwitchingQuad.c (hquad i)
        · exact congrArg SwitchingQuad.d (hquad i)
      subst D
      rfl

/-- Perform the actual elementary operation at a valid labelled coordinate. -/
def perform (s : LabelledResamplingState V T ι) (radius : ℕ) (i : ι)
    (hI : s.ITest radius i) (hJ : s.JTest radius i) : LabelledResamplingState V T ι where
  graph := (s.quad i).apply s.graph
  boundary := s.boundary.trans (elementaryBoundaryEquiv s.graph T radius s.samples (s.boundary i) hI hJ)
  samples := elementaryResampledData s.graph T radius s.samples (s.boundary i) hI hJ

theorem perform_quad (s : LabelledResamplingState V T ι) (radius : ℕ) (i j : ι)
    (hI : s.ITest radius i) (hJ : s.JTest radius i) :
    (s.perform radius i hI hJ).quad j = if j = i then (s.quad i).inverse else s.quad j := by
  have hq := elementaryResampledQuad_at_map s.graph T radius s.samples (s.boundary i) hI hJ (s.boundary j)
  change (s.perform radius i hI hJ).quad j = _ at hq
  simpa only [s.boundary.apply_eq_iff_eq] using hq

theorem perform_ITest (s : LabelledResamplingState V T ι) (radius : ℕ) (i j : ι)
    (hI : s.ITest radius i) (hJ : s.JTest radius i) :
    (s.perform radius i hI hJ).ITest radius j ↔ s.ITest radius j :=
  elementaryTreeTest_invariant s.graph T radius s.samples (s.boundary i) hI hJ (s.boundary j)

theorem perform_JTest (s : LabelledResamplingState V T ι) (radius : ℕ) (i j : ι)
    (hI : s.ITest radius i) (hJ : s.JTest radius i) :
    (s.perform radius i hI hJ).JTest radius j ↔ s.JTest radius j :=
  elementaryIsolation_invariant s.graph T radius s.samples (s.boundary i) hI hJ (s.boundary j)

/-- The elementary graph-plus-labels-plus-samples operation is its own inverse.
Both second-stage selector certificates are derived from invariance above. -/
theorem perform_twice (s : LabelledResamplingState V T ι) (radius : ℕ) (i : ι)
    (hI : s.ITest radius i) (hJ : s.JTest radius i) :
    let t := s.perform radius i hI hJ
    t.perform radius i ((s.perform_ITest radius i i hI hJ).mpr hI)
      ((s.perform_JTest radius i i hI hJ).mpr hJ) = s := by
  dsimp only
  apply ext_graph_quad
  · change ((s.perform radius i hI hJ).quad i).apply ((s.quad i).apply s.graph) = s.graph
    rw [s.perform_quad radius i i hI hJ, if_pos rfl]
    exact (s.quad i).inverse_apply s.graph
      (sampledSwitching_admissible s.graph T radius s.samples (s.boundary i) hI hJ)
  · intro j
    rw [perform_quad, s.perform_quad radius i i hI hJ, s.perform_quad radius i j hI hJ]
    by_cases h : j = i
    · subst j
      simp only [ite_true, SwitchingQuad.inverse_inverse]
    · simp only [h, if_false]

/-- Isolation implies disjoint modified-edge footprints at distinct labels,
without requiring distinct interior leaves. -/
theorem quad_edge_disjoint (s : LabelledResamplingState V T ι) (radius : ℕ) (i j : ι)
    (hJ : s.JTest radius i) (hij : i ≠ j) : Disjoint (s.quad i).footprint (s.quad j).footprint := by
  apply SwitchingQuad.footprint_disjoint_of_boundary _ _ T
  · exact sampledSwitching_exterior_disjoint s.graph T s.samples (s.boundary i)
  · exact sampledSwitching_root_mem s.graph T s.samples (s.boundary j)
  · exact isolation_exterior_disjoint s.graph T radius s.samples (s.boundary i) (s.boundary j)
      hJ (fun heq => hij (s.boundary.injective heq).symm)

/-- Two distinct accepted elementary operations commute on the full actual
labelled sampling state, including its boundary equivalence and samples. -/
theorem perform_commute (s : LabelledResamplingState V T ι) (radius : ℕ) (i j : ι)
    (hij : i ≠ j) (hIi : s.ITest radius i) (hJi : s.JTest radius i)
    (hIj : s.ITest radius j) (hJj : s.JTest radius j) :
    (s.perform radius i hIi hJi).perform radius j
        ((s.perform_ITest radius i j hIi hJi).mpr hIj)
        ((s.perform_JTest radius i j hIi hJi).mpr hJj) =
      (s.perform radius j hIj hJj).perform radius i
        ((s.perform_ITest radius j i hIj hJj).mpr hIi)
        ((s.perform_JTest radius j i hIj hJj).mpr hJi) := by
  apply ext_graph_quad
  · change ((s.perform radius i hIi hJi).quad j).apply ((s.quad i).apply s.graph) =
      ((s.perform radius j hIj hJj).quad i).apply ((s.quad j).apply s.graph)
    rw [s.perform_quad radius i j hIi hJi, if_neg hij.symm,
      s.perform_quad radius j i hIj hJj, if_neg hij]
    exact (s.quad i).commute_of_edge_disjoint (s.quad j) s.graph (s.quad_edge_disjoint radius i j hJi hij)
  · intro k
    simp only [perform_quad]
    by_cases hki : k = i
    · subst k
      simp [hij, hij.symm]
    · by_cases hkj : k = j
      · subst k
        simp [hij, hij.symm]
      · simp [hki, hkj]

/-- Acceptance at a fixed label is exactly the conjunction of I and J. -/
def Eligible (s : LabelledResamplingState V T ι) (radius : ℕ) (i : ι) : Prop :=
  s.ITest radius i ∧ s.JTest radius i

/-- A total elementary involution: failed selectors leave the state unchanged. -/
def flip (s : LabelledResamplingState V T ι) (radius : ℕ) (i : ι) : LabelledResamplingState V T ι :=
  if h : s.Eligible radius i then s.perform radius i h.1 h.2 else s

theorem flip_eq_perform (s : LabelledResamplingState V T ι) (radius : ℕ) (i : ι)
    (h : s.Eligible radius i) : s.flip radius i = s.perform radius i h.1 h.2 := by
  simp only [flip, dif_pos h]

theorem flip_eq_self (s : LabelledResamplingState V T ι) (radius : ℕ) (i : ι)
    (h : ¬s.Eligible radius i) : s.flip radius i = s := by
  simp only [flip, dif_neg h]

/-- All acceptance tests, including failing ones, are invariant under a total
coordinate flip. No selector-invariance assumption remains in this theorem. -/
theorem flip_eligible (s : LabelledResamplingState V T ι) (radius : ℕ) (i j : ι) :
    (s.flip radius i).Eligible radius j ↔ s.Eligible radius j := by
  by_cases h : s.Eligible radius i
  · rw [s.flip_eq_perform radius i h]
    exact and_congr (s.perform_ITest radius i j h.1 h.2) (s.perform_JTest radius i j h.1 h.2)
  · rw [s.flip_eq_self radius i h]

theorem flip_twice (s : LabelledResamplingState V T ι) (radius : ℕ) (i : ι) :
    (s.flip radius i).flip radius i = s := by
  by_cases h : s.Eligible radius i
  · have hi : (s.perform radius i h.1 h.2).ITest radius i := (s.perform_ITest radius i i h.1 h.2).mpr h.1
    have hj : (s.perform radius i h.1 h.2).JTest radius i := (s.perform_JTest radius i i h.1 h.2).mpr h.2
    rw [s.flip_eq_perform radius i h, flip_eq_perform _ radius i ⟨hi, hj⟩]
    exact s.perform_twice radius i h.1 h.2
  · rw [s.flip_eq_self radius i h, s.flip_eq_self radius i h]

/-- Total coordinate flips commute, including coordinates which are rejected. -/
theorem flip_commute (s : LabelledResamplingState V T ι) (radius : ℕ) (i j : ι) :
    (s.flip radius i).flip radius j = (s.flip radius j).flip radius i := by
  by_cases hij : i = j
  · subst j
    rfl
  by_cases hi : s.Eligible radius i
  · by_cases hj : s.Eligible radius j
    · have hji : (s.perform radius i hi.1 hi.2).Eligible radius j :=
        ⟨(s.perform_ITest radius i j hi.1 hi.2).mpr hj.1, (s.perform_JTest radius i j hi.1 hi.2).mpr hj.2⟩
      have hij' : (s.perform radius j hj.1 hj.2).Eligible radius i :=
        ⟨(s.perform_ITest radius j i hj.1 hj.2).mpr hi.1, (s.perform_JTest radius j i hj.1 hj.2).mpr hi.2⟩
      rw [s.flip_eq_perform radius i hi, flip_eq_perform _ radius j hji,
        s.flip_eq_perform radius j hj, flip_eq_perform _ radius i hij']
      exact s.perform_commute radius i j hij hi.1 hi.2 hj.1 hj.2
    · have hj' : ¬(s.flip radius i).Eligible radius j := fun h => hj ((s.flip_eligible radius i j).mp h)
      rw [flip_eq_self _ radius j hj', s.flip_eq_self radius j hj]
  · have hi' : ¬(s.flip radius j).Eligible radius i := fun h => hi ((s.flip_eligible radius j i).mp h)
    rw [s.flip_eq_self radius i hi, flip_eq_self _ radius i hi']

/-- Execute a finite coordinate schedule using the actual selectors. -/
def flips (s : LabelledResamplingState V T ι) (radius : ℕ) : List ι → LabelledResamplingState V T ι
  | [] => s
  | i :: L => (s.flip radius i).flips radius L

/-- A coordinate flip commutes with an arbitrary finite schedule. -/
theorem flips_flip (s : LabelledResamplingState V T ι) (radius : ℕ) (i : ι) (L : List ι) :
    (s.flip radius i).flips radius L = (s.flips radius L).flip radius i := by
  induction L generalizing s with
  | nil => rfl
  | cons j L ih =>
      change ((s.flip radius i).flip radius j).flips radius L = ((s.flip radius j).flips radius L).flip radius i
      rw [s.flip_commute radius i j]
      exact ih (s.flip radius j)

/-- Any fixed finite schedule gives a genuine involution of graph, dependent
boundary labels, and sample data, because all total coordinate flips commute. -/
theorem flips_twice (s : LabelledResamplingState V T ι) (radius : ℕ) (L : List ι) :
    (s.flips radius L).flips radius L = s := by
  induction L generalizing s with
  | nil => rfl
  | cons i L ih =>
      change (((s.flip radius i).flips radius L).flip radius i).flips radius L = s
      rw [flips_flip, ih, s.flip_twice radius i]

/-- Every acceptance indicator is preserved by any finite schedule. -/
theorem flips_eligible (s : LabelledResamplingState V T ι) (radius : ℕ) (L : List ι) (j : ι) :
    (s.flips radius L).Eligible radius j ↔ s.Eligible radius j := by
  induction L generalizing s with
  | nil => rfl
  | cons i L ih => exact (ih (s.flip radius i)).trans (s.flip_eligible radius i j)

/-- The induced graph on T itself is unchanged by each elementary operation. -/
theorem perform_induce (s : LabelledResamplingState V T ι) (radius : ℕ) (i : ι)
    (hI : s.ITest radius i) (hJ : s.JTest radius i) :
    (s.perform radius i hI hJ).graph.induce T = s.graph.induce T := by
  ext x y
  have hnone : ¬(s.quad i).footprint.Adj x.val y.val := by
    intro hedge
    obtain hx | hy := (s.quad i).footprint_touches_exterior hedge
    · exact Set.disjoint_left.mp (sampledSwitching_exterior_disjoint s.graph T s.samples (s.boundary i)) hx x.property
    · exact Set.disjoint_left.mp (sampledSwitching_exterior_disjoint s.graph T s.samples (s.boundary i)) hy y.property
  exact (s.quad i).adj_outside_footprint s.graph hnone

theorem flip_induce (s : LabelledResamplingState V T ι) (radius : ℕ) (i : ι) :
    (s.flip radius i).graph.induce T = s.graph.induce T := by
  by_cases h : s.Eligible radius i
  · rw [s.flip_eq_perform radius i h]
    exact s.perform_induce radius i h.1 h.2
  · rw [s.flip_eq_self radius i h]

theorem flips_induce (s : LabelledResamplingState V T ι) (radius : ℕ) (L : List ι) :
    (s.flips radius L).graph.induce T = s.graph.induce T := by
  induction L generalizing s with
  | nil => rfl
  | cons i L ih => exact (ih (s.flip radius i)).trans (s.flip_induce radius i)

section FiniteVertices
variable [Fintype V]

theorem perform_degree (s : LabelledResamplingState V T ι) (radius : ℕ) (i : ι)
    (hI : s.ITest radius i) (hJ : s.JTest radius i) (v : V) :
    (s.perform radius i hI hJ).graph.degree v = s.graph.degree v :=
  (sampledSwitching_admissible s.graph T radius s.samples (s.boundary i) hI hJ).degree_eq v

theorem flip_degree (s : LabelledResamplingState V T ι) (radius : ℕ) (i : ι) (v : V) :
    (s.flip radius i).graph.degree v = s.graph.degree v := by
  by_cases h : s.Eligible radius i
  · rw [s.flip_eq_perform radius i h]
    exact s.perform_degree radius i h.1 h.2 v
  · rw [s.flip_eq_self radius i h]

theorem flips_degree (s : LabelledResamplingState V T ι) (radius : ℕ) (L : List ι) (v : V) :
    (s.flips radius L).graph.degree v = s.graph.degree v := by
  induction L generalizing s with
  | nil => rfl
  | cons i L ih => exact (ih (s.flip radius i)).trans (s.flip_degree radius i v)

end FiniteVertices

section FiniteLabels
variable [Fintype ι]

/-- Perform all coordinate flips once. Rejected coordinates remain unchanged;
all selector indicators are invariant throughout this finite schedule. -/
def fullResample (s : LabelledResamplingState V T ι) (radius : ℕ) : LabelledResamplingState V T ι :=
  s.flips radius (Finset.univ : Finset ι).toList

/-- The complete labelled local resampling is an involution. -/
theorem fullResample_twice (s : LabelledResamplingState V T ι) (radius : ℕ) :
    (s.fullResample radius).fullResample radius = s := s.flips_twice radius _

def fullResamplingPermutation (radius : ℕ) : Equiv.Perm (LabelledResamplingState V T ι) :=
  Function.Involutive.toPerm (fun s => s.fullResample radius) (fun s => s.fullResample_twice radius)

theorem fullResample_induce (s : LabelledResamplingState V T ι) (radius : ℕ) :
    (s.fullResample radius).graph.induce T = s.graph.induce T := s.flips_induce radius _

theorem fullResample_eligible (s : LabelledResamplingState V T ι) (radius : ℕ) (i : ι) :
    (s.fullResample radius).Eligible radius i ↔ s.Eligible radius i := s.flips_eligible radius _ i

variable [Fintype V]

theorem fullResample_degree (s : LabelledResamplingState V T ι) (radius : ℕ) (v : V) :
    (s.fullResample radius).graph.degree v = s.graph.degree v := s.flips_degree radius _ v

theorem fullResample_regular (s : LabelledResamplingState V T ι) (radius : ℕ) {d : ℕ}
    (hreg : s.graph.IsRegularOfDegree d) : (s.fullResample radius).graph.IsRegularOfDegree d := by
  intro v
  rw [s.fullResample_degree radius v]
  exact hreg.degree_eq v

end FiniteLabels

end LabelledResamplingState

end

end LocalLaw
