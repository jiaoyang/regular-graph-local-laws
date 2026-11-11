import LocalLaw.GraphBallCounting

/-!
# Sharp exponential base for finite graph-ball counts

The degree-d ball growth has exponential base d-1. Each noninitial layer has
one neighbor in the preceding layer, leaving at most d-1 forward choices.
This sharper base is needed at the logarithmic structural radius; the coarse
d+1 bound remains sufficient at a log-log resampling radius.
-/

open scoped BigOperators
noncomputable section

namespace LocalLaw

local instance sharpBallDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A predecessor on an actual shortest path, including disconnected graphs. -/
theorem edist_succ_parent {V : Type*} (G : SimpleGraph V) (o v : V) (n : ℕ)
    (hv : G.edist o v = (n + 1 : ℕ)) :
    ∃ u, G.Adj u v ∧ G.edist o u = (n : ℕ) := by
  obtain ⟨p, hp⟩ := G.exists_walk_of_edist_eq_coe hv
  have hreverse : p.reverse.length = n + 1 := by simpa only [SimpleGraph.Walk.length_reverse] using hp
  generalize hqeq : p.reverse = q at hreverse
  cases q with
  | nil => simp only [SimpleGraph.Walk.length_nil] at hreverse; omega
  | @cons v u o hvu q =>
      have hlen : q.length = n := by simp only [SimpleGraph.Walk.length_cons] at hreverse; omega
      have hle : G.edist o u ≤ (n : ℕ) := by
        have h := G.edist_le q.reverse
        simpa only [SimpleGraph.Walk.length_reverse, hlen] using h
      have hne : G.edist o u ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top n) hle
      have heq : ((G.edist o u).toNat : ℕ∞) = G.edist o u := ENat.coe_toNat hne
      have hmle : (G.edist o u).toNat ≤ n := by
        exact ENat.coe_le_coe.mp (heq ▸ hle)
      have htriangle : (n + 1 : ℕ∞) ≤ G.edist o u + 1 := by
        have h := G.edist_triangle (u := o) (v := u) (w := v)
        rw [hv, SimpleGraph.edist_eq_one_iff_adj.mpr hvu.symm] at h
        exact h
      rw [← heq, ← ENat.coe_one, ← Nat.cast_add] at htriangle
      have hmge : n + 1 ≤ (G.edist o u).toNat + 1 := ENat.coe_le_coe.mp htriangle
      have hm : (G.edist o u).toNat = n := by omega
      exact ⟨u, hvu.symm, heq.symm.trans (congrArg (fun x : ℕ => (x : ℕ∞)) hm)⟩

section Finite
variable {V : Type*} [Fintype V] [DecidableEq V]

def graphSphereFinset (G : SimpleGraph V) (o : V) (n : ℕ) : Finset V :=
  Finset.univ.filter (fun v => G.edist o v = (n : ℕ))

omit [DecidableEq V] in
@[simp] theorem mem_graphSphereFinset (G : SimpleGraph V) (o v : V) (n : ℕ) :
    v ∈ graphSphereFinset G o n ↔ G.edist o v = (n : ℕ) := by simp [graphSphereFinset]

omit [DecidableEq V] in
@[simp] theorem graphSphereFinset_zero (G : SimpleGraph V) (o : V) :
    graphSphereFinset G o 0 = {o} := by
  ext v
  simp only [mem_graphSphereFinset, Nat.cast_zero, Finset.mem_singleton]
  constructor
  · intro hv
    exact (SimpleGraph.edist_eq_zero_iff.mp hv).symm
  · intro hv
    subst v
    exact G.edist_self

omit [DecidableEq V] in
@[simp] theorem graphSphereFinset_one (G : SimpleGraph V) (o : V) :
    graphSphereFinset G o 1 = G.neighborFinset o := by ext v; simp

/-- Every vertex in a noninitial layer has a preceding-layer neighbor, which
is excluded from forward neighbors. -/
theorem sphere_forward_neighbor_bound (G : SimpleGraph V) (o : V) (d n : ℕ)
    (hdegree : ∀ v, G.degree v ≤ d) (u : V) (hu : u ∈ graphSphereFinset G o (n + 1)) :
    (G.neighborFinset u \ graphSphereFinset G o n).card ≤ d - 1 := by
  obtain ⟨p, hpu, hp⟩ := edist_succ_parent G o u n ((mem_graphSphereFinset G o u _).mp hu)
  have hpmem : p ∈ G.neighborFinset u := by simpa using hpu.symm
  have hpsphere : p ∈ graphSphereFinset G o n := (mem_graphSphereFinset G o p _).mpr hp
  have hsub : G.neighborFinset u \ graphSphereFinset G o n ⊆ (G.neighborFinset u).erase p := by
    intro v hv
    obtain ⟨hvG, hvold⟩ := Finset.mem_sdiff.mp hv
    exact Finset.mem_erase.mpr ⟨by intro he; subst v; exact hvold hpsphere, hvG⟩
  calc
    _ ≤ ((G.neighborFinset u).erase p).card := Finset.card_le_card hsub
    _ = G.degree u - 1 := by rw [Finset.card_erase_of_mem hpmem, SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ d - 1 := Nat.sub_le_sub_right (hdegree u) 1

/-- Actual adjacent-layer growth has base d-1. -/
theorem graphSphere_succ_card (G : SimpleGraph V) (o : V) (d n : ℕ)
    (hdegree : ∀ v, G.degree v ≤ d) :
    (graphSphereFinset G o (n + 2)).card ≤ (graphSphereFinset G o (n + 1)).card * (d - 1) := by
  have hsub : graphSphereFinset G o (n + 2) ⊆ (graphSphereFinset G o (n + 1)).biUnion
      (fun u => G.neighborFinset u \ graphSphereFinset G o n) := by
    intro v hv
    obtain ⟨u, huv, hu⟩ := edist_succ_parent G o v (n + 1)
      ((mem_graphSphereFinset G o v _).mp hv)
    apply Finset.mem_biUnion.mpr
    refine ⟨u, (mem_graphSphereFinset G o u _).mpr hu, Finset.mem_sdiff.mpr ⟨by simpa using huv, ?_⟩⟩
    intro hvn
    have hn := (mem_graphSphereFinset G o v _).mp hvn
    have hn' := (mem_graphSphereFinset G o v _).mp hv
    rw [hn] at hn'
    have hh : n = n + 2 := by exact_mod_cast hn'
    omega
  calc
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ u ∈ graphSphereFinset G o (n + 1),
        (G.neighborFinset u \ graphSphereFinset G o n).card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ graphSphereFinset G o (n + 1), (d - 1) :=
      Finset.sum_le_sum (fun u hu => sphere_forward_neighbor_bound G o d n hdegree u hu)
    _ = _ := by simp

theorem graphSphere_card_bound (G : SimpleGraph V) (o : V) (d n : ℕ)
    (hdegree : ∀ v, G.degree v ≤ d) :
    (graphSphereFinset G o (n + 1)).card ≤ d * (d - 1) ^ n := by
  induction n with
  | zero => simpa using hdegree o
  | succ n ih =>
      calc
        _ ≤ (graphSphereFinset G o (n + 1)).card * (d - 1) := graphSphere_succ_card G o d n hdegree
        _ ≤ (d * (d - 1) ^ n) * (d - 1) := Nat.mul_le_mul_right _ ih
        _ = _ := by rw [pow_succ]; ring

/-- Every finite-radius ball is covered by its previous ball and last sphere. -/
theorem graphBall_succ_sphere_subset (G : SimpleGraph V) (o : V) (r : ℕ) :
    (graphBallVertices G o (r + 1)).toFinset ⊆
      (graphBallVertices G o r).toFinset ∪ graphSphereFinset G o (r + 1) := by
  intro v hv
  have hle : G.edist o v ≤ (r + 1 : ℕ) := by simpa only [Set.mem_toFinset] using hv
  have hne : G.edist o v ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top (r + 1)) hle
  have heq := ENat.coe_toNat hne
  have hm : (G.edist o v).toNat ≤ r + 1 := ENat.coe_le_coe.mp (heq ▸ hle)
  by_cases hsmall : (G.edist o v).toNat ≤ r
  · apply Finset.mem_union.mpr; left
    apply Set.mem_toFinset.mpr
    change G.edist o v ≤ (r : ℕ)
    rw [← heq]
    exact_mod_cast hsmall
  · apply Finset.mem_union.mpr; right
    apply (mem_graphSphereFinset G o v _).mpr
    have hlast : (G.edist o v).toNat = r + 1 := by omega
    exact heq.symm.trans (congrArg (fun x : ℕ => (x : ℕ∞)) hlast)

theorem graphBall_card_geometric (G : SimpleGraph V) (o : V) (d r : ℕ)
    (hdegree : ∀ v, G.degree v ≤ d) :
    Nat.card (graphBallVertices G o r) ≤ 1 + d * ∑ j ∈ Finset.range r, (d - 1) ^ j := by
  have hfin : ((graphBallVertices G o r).toFinset).card ≤ 1 + d * ∑ j ∈ Finset.range r, (d - 1) ^ j := by
    induction r with
    | zero =>
      have heq : (graphBallVertices G o 0).toFinset = graphSphereFinset G o 0 := by
        ext v
        simp only [Set.mem_toFinset, graphBallVertices, Set.mem_setOf_eq,
          Nat.cast_zero, le_zero_iff, mem_graphSphereFinset]
        exact ⟨fun h => le_antisymm h bot_le, fun h => h.le⟩
      simp [heq]
    | succ r ih =>
      have hs := graphSphere_card_bound G o d r hdegree
      calc
        _ ≤ ((graphBallVertices G o r).toFinset ∪ graphSphereFinset G o (r + 1)).card :=
          Finset.card_le_card (graphBall_succ_sphere_subset G o r)
        _ ≤ ((graphBallVertices G o r).toFinset).card + (graphSphereFinset G o (r + 1)).card :=
          Finset.card_union_le _ _
        _ ≤ (1 + d * ∑ j ∈ Finset.range r, (d - 1) ^ j) + d * (d - 1) ^ r := Nat.add_le_add ih hs
        _ = _ := by rw [Finset.sum_range_succ]; ring
  simpa only [Set.toFinset_card, ← Nat.card_eq_fintype_card] using hfin

/-- Sharp-base ball growth, without any acyclicity assumption. -/
theorem graphBall_card_sharp (G : SimpleGraph V) (o : V) (d r : ℕ)
    (hd : 3 ≤ d) (hdegree : ∀ v, G.degree v ≤ d) :
    Nat.card (graphBallVertices G o r) ≤ (d + 1) * (d - 1) ^ r := by
  have hk : 2 ≤ d - 1 := by omega
  have hsum : (∑ j ∈ Finset.range r, (d - 1) ^ j) ≤ (d - 1) ^ r := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hm := Nat.mul_le_mul_left ((d - 1) ^ r) hk
      omega
  have hpow : 1 ≤ (d - 1) ^ r := Nat.one_le_pow r (d - 1) (by omega)
  have hh := graphBall_card_geometric G o d r hdegree
  nlinarith


/-- A union of balls has the same sharp base, with one factor for each root. -/
theorem graphSetBall_card_sharp (G : SimpleGraph V) (S : Set V) (d r : ℕ)
    (hd : 3 ≤ d) (hdegree : ∀ v, G.degree v ≤ d) :
    Nat.card (graphSetBall G S r) ≤ Nat.card S * ((d + 1) * (d - 1) ^ r) := by
  have heq : (graphSetBall G S r).toFinset = S.toFinset.biUnion
      (fun o => (graphBallVertices G o r).toFinset) := by
    ext v
    simp only [Set.mem_toFinset, Finset.mem_biUnion, graphSetBall, graphBallVertices,
      Set.mem_setOf_eq]
  have hcard : (graphSetBall G S r).toFinset.card ≤
      S.toFinset.card * ((d + 1) * (d - 1) ^ r) := by
    rw [heq]
    calc
      _ ≤ ∑ o ∈ S.toFinset, (graphBallVertices G o r).toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ _o ∈ S.toFinset, ((d + 1) * (d - 1) ^ r) := by
        apply Finset.sum_le_sum
        intro o _
        simpa only [Set.toFinset_card, ← Nat.card_eq_fintype_card] using graphBall_card_sharp G o d r hd hdegree
      _ = _ := by simp
  simpa only [Set.toFinset_card, ← Nat.card_eq_fintype_card] using hcard

end Finite

namespace RegularGraph
variable {N d : ℕ}

theorem ball_card_sharp (g : RegularGraph N d) (o : Fin N) (r : ℕ) (hd : 3 ≤ d) :
    Nat.card (graphBallVertices g.graph o r) ≤ (d + 1) * (d - 1) ^ r :=
  graphBall_card_sharp g.graph o d r hd (fun v => (g.regular v).le)

/-- The actual boundary-label count has the sharp exponential base as well. -/
theorem boundary_card_sharp (g : RegularGraph N d) (o : Fin N) (r : ℕ) (hd : 3 ≤ d) :
    Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o r)) ≤
      d * (d + 1) * (d - 1) ^ r := by
  have hcount := g.boundary_interior_count (graphBallVertices g.graph o r)
  calc
    _ ≤ d * Nat.card (graphBallVertices g.graph o r) := by omega
    _ ≤ d * ((d + 1) * (d - 1) ^ r) := Nat.mul_le_mul_left d (g.ball_card_sharp o r hd)
    _ = _ := by ring

end RegularGraph

end LocalLaw
