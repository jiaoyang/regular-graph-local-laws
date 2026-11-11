import LocalLaw.TreeReferenceKernel
import LocalLaw.CycleSpaceCounting

/-!
# Tree-path sphere counting for the bounded-excess core

A simple tree path meets a distance sphere in at most two vertices, proved
from unique parents. Actual shortest G walks split after their last off-tree
edge. Thus the concrete spanning-tree core has at most 2(2omega+2)(2omega+1)
vertices on each actual G-distance layer when excess(G)<=omega. Its complement
has no non-tree edges and is an actual induced forest. None of these geometric
conclusions is supplied as a hypothesis.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw

local instance coreLayerDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [DecidableEq V] {T : SimpleGraph V}

/-- Once an adjacent vertex is known to be the parent, every other neighbor
is one step farther from the root. -/
theorem tree_other_neighbor_distance (hT : T.IsTree) (root v parent w : V)
    (hp : T.Adj v parent) (hd : T.dist parent root + 1 = T.dist v root)
    (hw : T.Adj v w) (hne : w ≠ parent) :
    T.dist w root = T.dist v root + 1 := by
  have hv : v ≠ root := by
    intro heq
    subst v
    simp only [SimpleGraph.dist_self] at hd
    omega
  obtain ⟨p, hvp, hdp, hfar⟩ := forest_parent_distance hT.IsAcyclic root v (hT.isConnected.preconnected v root) hv
  have hparent : parent = p := by
    by_contra hnep
    have hh := hfar parent hp hnep
    omega
  exact hfar w hw (by simpa only [← hparent] using hne)

/-- Heights of adjacent tree vertices differ by exactly one. -/
theorem tree_adjacent_distance_step (hT : T.IsTree) (root u v : V) (huv : T.Adj u v) :
    T.dist u root + 1 = T.dist v root ∨ T.dist v root + 1 = T.dist u root := by
  by_cases hu : u = root
  · subst u
    left
    simp only [SimpleGraph.dist_self, zero_add]
    exact (SimpleGraph.dist_eq_one_iff_adj.mpr huv.symm).symm
  · obtain ⟨p, hup, hdp, hfar⟩ := forest_parent_distance hT.IsAcyclic root u (hT.isConnected.preconnected u root) hu
    by_cases hv : v = p
    · exact Or.inr (by simpa only [hv] using hdp)
    · exact Or.inl (hfar v huv hv).symm

/-- A simple path which avoids its initial parent moves strictly away from
the root. Both height minimality and height injectivity are derived. -/
theorem tree_path_away_height (hT : T.IsTree) (root : V) {u v : V}
    (p : T.Walk u v) (hp : p.IsPath) (parent : V) (hparent : T.Adj u parent)
    (hheight : T.dist parent root + 1 = T.dist u root) (havoid : parent ∉ p.support) :
    (∀ x ∈ p.support, T.dist u root ≤ T.dist x root) ∧
      Set.InjOn (fun x => T.dist x root) {x | x ∈ p.support} := by
  induction p generalizing parent with
  | nil =>
    constructor
    · intro x hx
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
      subst x
      exact le_rfl
    · intro x hx y hy _
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton, Set.mem_setOf_eq] at hx hy
      exact hx.trans hy.symm
  | @cons u v w huv p ih =>
    have hp' : p.IsPath := hp.of_cons
    have hno : u ∉ p.support := (List.nodup_cons.mp hp.support_nodup).1
    have hvparent : v ≠ parent := by
      intro heq
      apply havoid
      rw [SimpleGraph.Walk.support_cons, List.mem_cons]
      exact Or.inr (heq ▸ p.start_mem_support)
    have hstep := tree_other_neighbor_distance hT root u parent v hparent hheight huv hvparent
    have ht := ih hp' u huv.symm (by omega) hno
    constructor
    · intro x hx
      rcases (List.mem_cons.mp hx) with heq | hx
      · subst x; exact le_rfl
      · exact (by omega : T.dist u root ≤ T.dist v root).trans (ht.1 x hx)
    · intro x hx y hy heq
      change T.dist x root = T.dist y root at heq
      rcases (List.mem_cons.mp hx) with hxu | hx
      · subst x
        rcases (List.mem_cons.mp hy) with hyu | hy
        · exact hyu.symm
        · have hh := ht.1 y hy
          omega
      · rcases (List.mem_cons.mp hy) with hyu | hy
        · subst y
          have hh := ht.1 x hx
          omega
        · exact ht.2 hx hy heq

/-- If a path starts at a closest-to-root vertex of its support, root distance
is injective on that path. -/
theorem tree_path_min_height_injective (hT : T.IsTree) (root : V) {u v : V}
    (p : T.Walk u v) (hp : p.IsPath)
    (hmin : ∀ x ∈ p.support, T.dist u root ≤ T.dist x root) :
    Set.InjOn (fun x => T.dist x root) {x | x ∈ p.support} := by
  cases p with
  | nil =>
    intro x hx y hy _
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton, Set.mem_setOf_eq] at hx hy
    exact hx.trans hy.symm
  | @cons u v w huv p =>
    have hnear := hmin v (by simp [SimpleGraph.Walk.support_cons, p.start_mem_support])
    have hstep : T.dist u root + 1 = T.dist v root := by
      rcases tree_adjacent_distance_step hT root u v huv with h | h
      · exact h
      · omega
    have hno : u ∉ p.support := (List.nodup_cons.mp hp.support_nodup).1
    have ht := tree_path_away_height hT root p hp.of_cons u huv.symm hstep hno
    intro x hx y hy heq
    change T.dist x root = T.dist y root at heq
    rcases (List.mem_cons.mp hx) with hxu | hx
    · subst x
      rcases (List.mem_cons.mp hy) with hyu | hy
      · exact hyu.symm
      · have hh := ht.1 y hy
        omega
    · rcases (List.mem_cons.mp hy) with hyu | hy
      · subst y
        have hh := ht.1 x hx
        omega
      · exact ht.2 hx hy heq

/-- Actual vertices of a finite path lying on a specified tree sphere. -/
def treePathSphere (root : V) {u v : V} (p : T.Walk u v) (n : ℕ) : Finset V :=
  p.support.toFinset.filter (fun x => T.dist x root = n)

/-- A simple path in an actual tree meets every distance sphere in at most
two vertices. Splitting at a minimum-height vertex gives two injective halves. -/
theorem treePathSphere_card_le_two (hT : T.IsTree) (root : V) {u v : V}
    (p : T.Walk u v) (hp : p.IsPath) (n : ℕ) : (treePathSphere root p n).card ≤ 2 := by
  obtain ⟨w, hw, hmin⟩ := p.support.toFinset.exists_min_image (fun x => T.dist x root)
    ⟨u, List.mem_toFinset.mpr p.start_mem_support⟩
  have hw' : w ∈ p.support := List.mem_toFinset.mp hw
  let left := (p.takeUntil w hw').reverse
  let right := p.dropUntil w hw'
  have hl : Set.InjOn (fun x => T.dist x root) {x | x ∈ left.support} := by
    apply tree_path_min_height_injective hT root left (hp.takeUntil hw').reverse
    intro x hx
    apply hmin x
    apply List.mem_toFinset.mpr
    apply p.support_takeUntil_subset hw'
    simpa only [left, SimpleGraph.Walk.support_reverse, List.mem_reverse] using hx
  have hr : Set.InjOn (fun x => T.dist x root) {x | x ∈ right.support} := by
    apply tree_path_min_height_injective hT root right (hp.dropUntil hw')
    intro x hx
    exact hmin x (List.mem_toFinset.mpr (p.support_dropUntil_subset hw' hx))
  have hone : ∀ {s t : V} (q : T.Walk s t),
      Set.InjOn (fun x => T.dist x root) {x | x ∈ q.support} →
        (treePathSphere root q n).card ≤ 1 := by
    intro s t q hq
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨hx, hxheight⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy, hyheight⟩ := Finset.mem_filter.mp hy
    exact hq (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy) (hxheight.trans hyheight.symm)
  have hcover : treePathSphere root p n ⊆ treePathSphere root left n ∪ treePathSphere root right n := by
    intro x hx
    obtain ⟨hx, hheight⟩ := Finset.mem_filter.mp hx
    have hx' := List.mem_toFinset.mp hx
    rw [← p.take_spec hw', SimpleGraph.Walk.mem_support_append_iff] at hx'
    apply Finset.mem_union.mpr
    rcases hx' with hx' | hx'
    · left
      apply Finset.mem_filter.mpr
      exact ⟨List.mem_toFinset.mpr (by simpa only [left, SimpleGraph.Walk.support_reverse, List.mem_reverse] using hx'), hheight⟩
    · right
      exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hx', hheight⟩
  exact (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
    (by have hh := hone left hl; have hh' := hone right hr; omega))

/-- Finite unions of actual tree paths inherit the two-vertices-per-sphere
bound, without any disjointness requirement on those paths. -/
theorem treePathFamilySphere_card_bound {I : Type*} [Fintype I]
    (hT : T.IsTree) (root : V) (start finish : I → V)
    (paths : ∀ i, T.Walk (start i) (finish i)) (hp : ∀ i, (paths i).IsPath) (n : ℕ) :
    ((Finset.univ : Finset I).biUnion (fun i => treePathSphere root (paths i) n)).card ≤
      2 * Fintype.card I := by
  calc
    _ ≤ ∑ i : I, (treePathSphere root (paths i) n).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : I, 2 := Finset.sum_le_sum (fun i _ => treePathSphere_card_le_two hT root (paths i) (hp i) n)
    _ = _ := by simp; omega

/-- Multiple sphere centers and radii give the quadratic core-layer count
once a shortest-path decomposition supplies the actual center choices. -/
theorem treePathMultiSphere_card_bound {I J : Type*} [Fintype I] [Fintype J]
    (hT : T.IsTree) (roots : J → V) (radii : J → ℕ) (start finish : I → V)
    (paths : ∀ i, T.Walk (start i) (finish i)) (hp : ∀ i, (paths i).IsPath) :
    ((Finset.univ : Finset J).biUnion (fun j => (Finset.univ : Finset I).biUnion
      (fun i => treePathSphere (roots j) (paths i) (radii j)))).card ≤
        2 * Fintype.card I * Fintype.card J := by
  calc
    _ ≤ ∑ j : J, ((Finset.univ : Finset I).biUnion
        (fun i => treePathSphere (roots j) (paths i) (radii j))).card := Finset.card_biUnion_le
    _ ≤ ∑ _j : J, 2 * Fintype.card I := Finset.sum_le_sum
      (fun j _ => treePathFamilySphere_card_bound hT (roots j) start finish paths hp (radii j))
    _ = _ := by simp; ring

/-- Actual endpoints of edges outside the chosen spanning tree. -/
def OffTreeEndpoint (G T : SimpleGraph V) (v : V) : Prop :=
  ∃ w, G.Adj v w ∧ ¬ T.Adj v w

omit [DecidableEq V] in
/-- Every walk is either entirely in the subgraph or has an actual last
outside edge, followed by a walk wholly in the subgraph. -/
theorem walk_tree_suffix_or_last_offTree {G T : SimpleGraph V} (hTG : T ≤ G)
    {i x : V} (p : G.Walk i x) :
    (∃ q : T.Walk i x, p = q.map (SimpleGraph.Hom.ofLE hTG)) ∨
      ∃ b, OffTreeEndpoint G T b ∧ ∃ headWalk : G.Walk i b, ∃ tailWalk : T.Walk b x,
        p = headWalk.append (tailWalk.map (SimpleGraph.Hom.ofLE hTG)) := by
  induction p with
  | nil => exact Or.inl ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons i u x hiu p ih =>
    rcases ih with ⟨q, hq⟩ | ⟨b, hb, headWalk, tailWalk, hsplit⟩
    · by_cases hTree : T.Adj i u
      · left
        refine ⟨q.cons hTree, ?_⟩
        rw [hq]
        rfl
      · right
        refine ⟨u, ⟨i, hiu.symm, fun h => hTree h.symm⟩,
          SimpleGraph.Walk.cons hiu SimpleGraph.Walk.nil, q, ?_⟩
        rw [hq]
        rfl
    · right
      refine ⟨b, hb, headWalk.cons hiu, tailWalk, ?_⟩
      rw [hsplit]
      rfl

omit [DecidableEq V] in
/-- For an actual shortest G walk, the last outside-edge endpoint is a
sphere center with the exact additive G/T distance decomposition. -/
theorem shortest_tree_suffix_distance {G T : SimpleGraph V} (hTG : T ≤ G)
    (hT : T.IsTree) (i x : V) :
    ∃ b, (b = i ∨ OffTreeEndpoint G T b) ∧
      G.dist i x = G.dist i b + T.dist x b := by
  have hG := hT.isConnected.mono hTG
  obtain ⟨p, hlength⟩ := hG.exists_walk_length_eq_dist i x
  have hsplit : ∃ b, (b = i ∨ OffTreeEndpoint G T b) ∧
      ∃ headWalk : G.Walk i b, ∃ tailWalk : T.Walk b x,
        p = headWalk.append (tailWalk.map (SimpleGraph.Hom.ofLE hTG)) := by
    rcases walk_tree_suffix_or_last_offTree hTG p with ⟨q, hq⟩ | ⟨b, hb, headWalk, tailWalk, hs⟩
    · exact ⟨i, Or.inl rfl, SimpleGraph.Walk.nil, q, by simpa only [SimpleGraph.Walk.nil_append] using hq⟩
    · exact ⟨b, Or.inr hb, headWalk, tailWalk, hs⟩
  obtain ⟨b, hb, headWalk, tailWalk, heq⟩ := hsplit
  refine ⟨b, hb, ?_⟩
  have hlen : headWalk.length + tailWalk.length = G.dist i x := by
    rw [heq, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_map] at hlength
    exact hlength
  have hprefix := G.dist_le headWalk
  have hsuffix := T.dist_le tailWalk
  have htriangle : G.dist i x ≤ G.dist i b + G.dist b x := hG.dist_triangle
  have hanti : G.dist b x ≤ T.dist b x := (hT.isConnected.preconnected b x).dist_anti hTG
  have hcomm : T.dist b x = T.dist x b := T.dist_comm
  omega

section FiniteCore

variable [Fintype V]

/-- The actual endpoints of edges of G not in T, counted via actual darts. -/
def offTreeEndpointFinset (G T : SimpleGraph V) : Finset V :=
  (Finset.univ : Finset (G \ T).Dart).image (fun e => e.fst)

theorem mem_offTreeEndpointFinset (G T : SimpleGraph V) (v : V) :
    v ∈ offTreeEndpointFinset G T ↔ OffTreeEndpoint G T v := by
  simp only [offTreeEndpointFinset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e.snd, ((SimpleGraph.sdiff_adj G T e.fst e.snd).mp e.adj).1, ((SimpleGraph.sdiff_adj G T e.fst e.snd).mp e.adj).2⟩
  · rintro ⟨w, hG, hT⟩
    exact ⟨⟨(v, w), (SimpleGraph.sdiff_adj G T v w).mpr ⟨hG, hT⟩⟩, rfl⟩

theorem offTreeEndpointFinset_card_bound (G T : SimpleGraph V) (hTG : T ≤ G)
    (hT : T.IsTree) : (offTreeEndpointFinset G T).card ≤ 2 * graphExcess G := by
  have hG := hT.isConnected.mono hTG
  calc
    _ ≤ Fintype.card (G \ T).Dart := by
      exact Finset.card_image_le.trans_eq Finset.card_univ
    _ = 2 * Nat.card (G \ T).edgeSet := by
      have h := (G \ T).dart_card_eq_twice_card_edges
      simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using h
    _ = 2 * graphExcess G := by rw [off_tree_edge_count G T hG hTG hT]

/-- The unique actual simple path chosen in the spanning tree. -/
def spanningTreePath (hT : T.IsTree) (i j : V) : T.Walk i j :=
  Classical.choose (hT.isConnected.exists_isPath i j)

omit [DecidableEq V] [Fintype V] in
theorem spanningTreePath_isPath (hT : T.IsTree) (i j : V) :
    (spanningTreePath hT i j).IsPath := Classical.choose_spec (hT.isConnected.exists_isPath i j)

/-- The terminals are the two marked vertices and every non-tree endpoint. -/
def spanningCoreTerminals (G T : SimpleGraph V) (i j : V) : Finset V :=
  insert i (insert j (offTreeEndpointFinset G T))

/-- The concrete finite core is the union of tree paths to those terminals. -/
def spanningCore (G T : SimpleGraph V) (hT : T.IsTree) (i j : V) : Finset V :=
  (spanningCoreTerminals G T i j).biUnion (fun s => (spanningTreePath hT i s).support.toFinset)

/-- The actual ambient-G radial layer of the actual spanning-tree core. -/
def spanningCoreLayer (G T : SimpleGraph V) (hT : T.IsTree) (i j : V) (n : ℕ) : Finset V :=
  (spanningCore G T hT i j).filter (fun x => G.dist i x = n)

/-- The shortest-walk decomposition and actual tree path/sphere bound give
the core radial bound. Neither layer size nor a decomposition is assumed. -/
theorem spanningCoreLayer_card_bound (G T : SimpleGraph V) (hTG : T ≤ G)
    (hT : T.IsTree) (i j : V) (n ω : ℕ) (hω : graphExcess G ≤ ω) :
    (spanningCoreLayer G T hT i j n).card ≤ 2 * (2 * ω + 2) * (2 * ω + 1) := by
  let S := spanningCoreTerminals G T i j
  let B := insert i (offTreeEndpointFinset G T)
  let spheres := fun b : V => S.biUnion (fun s =>
    treePathSphere b (spanningTreePath hT i s) (n - G.dist i b))
  have hcover : spanningCoreLayer G T hT i j n ⊆ B.biUnion spheres := by
    intro x hx
    obtain ⟨hxcore, hxheight⟩ := Finset.mem_filter.mp hx
    obtain ⟨s, hs, hxs⟩ := Finset.mem_biUnion.mp hxcore
    obtain ⟨b, hb, hdist⟩ := shortest_tree_suffix_distance hTG hT i x
    have hbB : b ∈ B := by
      rcases hb with hb | hb
      · exact Finset.mem_insert.mpr (Or.inl hb)
      · exact Finset.mem_insert.mpr (Or.inr ((mem_offTreeEndpointFinset G T b).mpr hb))
    have hrad : T.dist x b = n - G.dist i b := by omega
    apply Finset.mem_biUnion.mpr
    refine ⟨b, hbB, Finset.mem_biUnion.mpr ⟨s, hs, ?_⟩⟩
    exact Finset.mem_filter.mpr ⟨hxs, hrad⟩
  have hone : ∀ b, (spheres b).card ≤ 2 * S.card := by
    intro b
    calc
      _ ≤ ∑ s ∈ S, (treePathSphere b (spanningTreePath hT i s) (n - G.dist i b)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _s ∈ S, 2 := Finset.sum_le_sum (fun s _ =>
        treePathSphere_card_le_two hT b (spanningTreePath hT i s) (spanningTreePath_isPath hT i s) _)
      _ = _ := by simp; omega
  have hS : S.card ≤ 2 * ω + 2 := by
    have he := (offTreeEndpointFinset_card_bound G T hTG hT).trans (Nat.mul_le_mul_left 2 hω)
    have h₁ := Finset.card_insert_le j (offTreeEndpointFinset G T)
    have h₂ := Finset.card_insert_le i (insert j (offTreeEndpointFinset G T))
    dsimp [S, spanningCoreTerminals]
    omega
  have hB : B.card ≤ 2 * ω + 1 := by
    have he := (offTreeEndpointFinset_card_bound G T hTG hT).trans (Nat.mul_le_mul_left 2 hω)
    have h₁ := Finset.card_insert_le i (offTreeEndpointFinset G T)
    dsimp [B]
    omega
  calc
    _ ≤ (B.biUnion spheres).card := Finset.card_le_card hcover
    _ ≤ ∑ b ∈ B, (spheres b).card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ B, 2 * S.card := Finset.sum_le_sum (fun b _ => hone b)
    _ = 2 * S.card * B.card := by simp; ring
    _ ≤ 2 * (2 * ω + 2) * (2 * ω + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hS) hB

/-- Every terminal really belongs to the constructed core. -/
theorem spanningCoreTerminals_subset (G T : SimpleGraph V) (hT : T.IsTree) (i j : V) :
    spanningCoreTerminals G T i j ⊆ spanningCore G T hT i j := by
  intro s hs
  apply Finset.mem_biUnion.mpr
  exact ⟨s, hs, List.mem_toFinset.mpr (spanningTreePath hT i s).end_mem_support⟩

/-- No non-tree edge can touch a vertex outside the constructed core. -/
theorem spanningCore_outside_adj (G T : SimpleGraph V) (hT : T.IsTree) (i j u v : V)
    (hu : u ∉ spanningCore G T hT i j) (huv : G.Adj u v) : T.Adj u v := by
  by_contra hn
  apply hu
  apply spanningCoreTerminals_subset G T hT i j
  apply Finset.mem_insert.mpr
  right
  apply Finset.mem_insert.mpr
  right
  exact (mem_offTreeEndpointFinset G T u).mpr ⟨v, huv, hn⟩

/-- The actual graph outside the core is exactly an induced forest of T. -/
theorem spanningCore_outside_graph_eq (G T : SimpleGraph V) (hTG : T ≤ G)
    (hT : T.IsTree) (i j : V) :
    G.induce {v | v ∉ spanningCore G T hT i j} =
      T.induce {v | v ∉ spanningCore G T hT i j} := by
  ext u v
  change G.Adj u.val v.val ↔ T.Adj u.val v.val
  exact ⟨spanningCore_outside_adj G T hT i j u.val v.val u.property, fun h => hTG h⟩

theorem spanningCore_outside_acyclic (G T : SimpleGraph V) (hTG : T ≤ G)
    (hT : T.IsTree) (i j : V) :
    (G.induce {v | v ∉ spanningCore G T hT i j}).IsAcyclic := by
  rw [spanningCore_outside_graph_eq G T hTG hT i j]
  exact graph_acyclic_induce T _ hT.IsAcyclic

/-- A finite connected G really has a spanning tree and the resulting core
with the proved quadratic-in-excess radial bound. -/
theorem connected_exists_core_layer_bound (G : SimpleGraph V) (hG : G.Connected)
    (i j : V) (ω : ℕ) (hω : graphExcess G ≤ ω) :
    ∃ T : SimpleGraph V, ∃ _hTG : T ≤ G, ∃ hT : T.IsTree, ∀ n,
      (spanningCoreLayer G T hT i j n).card ≤ 2 * (2 * ω + 2) * (2 * ω + 1) := by
  obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
  exact ⟨T, hTG, hT, fun n => spanningCoreLayer_card_bound G T hTG hT i j n ω hω⟩

end FiniteCore

end LocalLaw
