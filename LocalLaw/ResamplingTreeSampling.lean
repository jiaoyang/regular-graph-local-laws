import LocalLaw.ResamplingSamplingGeometry
import LocalLaw.LocalExcessGeometry

/-!
# Sampling tree neighborhoods of actual outside edges

The induced union of the radius-r balls around the two endpoints of an edge
is connected and lies inside the ambient radius-(r+1) ball around its first
endpoint. Thus an ambient tree at r+1 certifies the two-root tree at r.
The extra step is necessary: a cycle of length 2r+2 is a counterexample to
replacing r+1 by r. The resulting bad-pair tail is proved from endpoint counts.
-/

noncomputable section
namespace LocalLaw

local instance resamplingTreeSamplingDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {V : Type*}

/-- Deleting vertices can only increase extended graph distance. -/
theorem ambient_edist_le_induced_edist (G : SimpleGraph V) (A : Set V) (x y : A) :
    G.edist x.val y.val ≤ (G.induce A).edist x y := by
  by_cases htop : (G.induce A).edist x y = ⊤
  · simp only [htop, le_top]
  · obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top htop
    have h := G.edist_le (p.map (SimpleGraph.Embedding.induce A).toHom)
    simpa only [SimpleGraph.Walk.length_map, hp] using h

/-- The literal induced two-root neighborhood of an edge is connected. -/
theorem pairBall_connected_of_adj (G : SimpleGraph V) {i j : V} (hij : G.Adj i j) (r : ℕ) :
    (pairBallGraph G i j r).Connected := by
  let ii : pairBallVertices G i j r := ⟨i, Or.inl (by simp)⟩
  let jj : pairBallVertices G i j r := ⟨j, Or.inr (by simp)⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨ii, ?_⟩
  intro v
  by_cases hi : G.edist i v.val ≤ (r : ℕ∞)
  · let f : graphBall G i r →g pairBallGraph G i j r :=
      { toFun := fun a => ⟨a.val, Or.inl a.property⟩
        map_rel' := fun h => h }
    obtain ⟨p⟩ := (graphBall_connected G i r) ⟨i, by simp [graphBallVertices]⟩ ⟨v.val, hi⟩
    exact ⟨p.map f⟩
  · have hj : G.edist j v.val ≤ (r : ℕ∞) := v.property.resolve_left hi
    let f : graphBall G j r →g pairBallGraph G i j r :=
      { toFun := fun a => ⟨a.val, Or.inr a.property⟩
        map_rel' := fun h => h }
    obtain ⟨p⟩ := (graphBall_connected G j r) ⟨j, by simp [graphBallVertices]⟩ ⟨v.val, hj⟩
    have hedge : (pairBallGraph G i j r).Adj ii jj := hij
    exact hedge.reachable.trans ⟨p.map f⟩

/-- The actual outside two-root neighborhood is a tree when the ambient
first-endpoint ball at one larger radius is a tree. -/
theorem outside_pairBall_isTree_of_ambient (G : SimpleGraph V) (T : Set V)
    (e : OutsideOrientedEdge G T) (r : ℕ)
    (htree : (graphBall G e.val.1 (r + 1)).IsTree) :
    (pairBallGraph (outsideGraph G T)
      ⟨e.val.1, e.property.2.1⟩ ⟨e.val.2, e.property.2.2⟩ r).IsTree := by
  let b : {v : V // v ∉ T} := ⟨e.val.1, e.property.2.1⟩
  let c : {v : V // v ∉ T} := ⟨e.val.2, e.property.2.2⟩
  let H := pairBallGraph (outsideGraph G T) b c r
  have hbc : (outsideGraph G T).Adj b c := e.property.1
  have hsubset : ∀ x : pairBallVertices (outsideGraph G T) b c r,
      x.val.val ∈ graphBallVertices G e.val.1 (r + 1) := by
    intro x
    change G.edist e.val.1 x.val.val ≤ ((r + 1 : ℕ) : ℕ∞)
    rcases x.property with hx | hx
    · have hdist := (ambient_edist_le_induced_edist G {v | v ∉ T} b x.val).trans hx
      exact hdist.trans (ENat.coe_le_coe.mpr (Nat.le_succ r))
    · have hdist := (ambient_edist_le_induced_edist G {v | v ∉ T} c x.val).trans hx
      calc
        _ ≤ G.edist e.val.1 e.val.2 + G.edist e.val.2 x.val.val := G.edist_triangle
        _ ≤ 1 + (r : ℕ∞) := add_le_add
          (le_of_eq (SimpleGraph.edist_eq_one_iff_adj.mpr e.property.1)) hdist
        _ = ((r + 1 : ℕ) : ℕ∞) := by
          simp only [Nat.cast_add, Nat.cast_one]
          exact add_comm _ _
  let f : H →g graphBall G e.val.1 (r + 1) :=
    { toFun := fun x => ⟨x.val.val, hsubset x⟩
      map_rel' := fun h => h }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : graphBallVertices G e.val.1 (r + 1) => z.val) h
  refine ⟨pairBall_connected_of_adj (outsideGraph G T) hbc r, ?_⟩
  intro x p hp
  exact htree.IsAcyclic (p.map f) (hp.map hf)

variable [Fintype V]

/-- Coordinates whose actual outside edge has a non-tree two-root ball. -/
def nonTreeSampledPairIndices (G : SimpleGraph V) (T : Set V) (r : ℕ)
    (S : LocalSamplingFiber G T) : Finset (BoundaryOrientedEdge G T) :=
  Finset.univ.filter (fun α => ¬(pairBallGraph (outsideGraph G T)
    ⟨(S α).val.1, (S α).property.2.1⟩ ⟨(S α).val.2, (S α).property.2.2⟩ r).IsTree)

theorem nonTreeSampledPairIndices_subset_badCenters (G : SimpleGraph V) (T : Set V)
    (r : ℕ) (S : LocalSamplingFiber G T) :
    nonTreeSampledPairIndices G T r S ⊆ endpointHitIndices G T (nonTreeCenters G (r + 1)) S := by
  intro α hα
  apply (mem_endpointHitIndices G T _ S α).mpr
  apply Or.inl
  rw [nonTreeCenters_membership]
  intro ht
  exact (Finset.mem_filter.mp hα).2 (outside_pairBall_isTree_of_ambient G T (S α) r ht)

namespace RegularGraph
variable {N d : ℕ}

/-- The exact finite bad-two-root-tree sampling estimate. The single-center
exception count is at r+1, and that radius is visible in the hypotheses. -/
theorem localSampling_nonTree_pair_tail (g : RegularGraph N d) (T : Set (Fin N))
    (hN : 0 < N) (hd : 0 < d) (hT : 4 * Nat.card T ≤ N)
    (r b k : ℕ) (hbad : (nonTreeCenters g.graph (r + 1)).card ≤ b) :
    eventMass (localSamplingWeight g.graph T)
      (fun S => k ≤ (nonTreeSampledPairIndices g.graph T r S).card) ≤
      ((Nat.card (BoundaryOrientedEdge g.graph T) : ℝ) * (4 * (b : ℝ) / N)) ^ k := by
  apply (eventMass_mono (localSamplingWeight g.graph T) finiteUniformWeight_nonneg ?_).trans
    (g.localSampling_bad_center_tail T hN hd hT (r + 1) b k hbad)
  intro S hS
  exact hS.trans (Finset.card_le_card (nonTreeSampledPairIndices_subset_badCenters g.graph T r S))

end RegularGraph
end LocalLaw
