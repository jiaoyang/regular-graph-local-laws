import LocalLaw.LocalExcessGeometry
import LocalLaw.SharpBallCounting
import LocalLaw.CycleWalkEmbedding

/-!
# A short simple-cycle witness in a nonacyclic induced ball

A chosen parent of strictly smaller distance gives an actual spanning tree.
Its root paths have the prescribed distance lengths. Any edge outside this
tree closes a simple path of length at most twice the radius, producing a
cycle of length at most 2R+1 entirely in the original induced ball.
-/

noncomputable section
set_option maxHeartbeats 1200000

namespace LocalLaw

local instance ballCycleDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A finite rooted parent system with an exact natural height decrease. -/
structure HeightParentData (V : Type*) where
  root : V
  height : V → ℕ
  height_zero : ∀ v, height v = 0 ↔ v = root
  parent : {v : V // v ≠ root} → V
  parent_height : ∀ v, height (parent v) + 1 = height v.val

namespace HeightParentData

variable {V : Type*} (D : HeightParentData V)

def parentEdge (v : {v : V // v ≠ D.root}) : Sym2 V := s(v.val, D.parent v)

def tree : SimpleGraph V := SimpleGraph.fromEdgeSet (Set.range D.parentEdge)

theorem parent_ne (v : {v : V // v ≠ D.root}) : v.val ≠ D.parent v := by
  intro h
  have hh := D.parent_height v
  rw [← h] at hh
  omega

theorem parent_adj (v : {v : V // v ≠ D.root}) : D.tree.Adj v.val (D.parent v) := by
  exact (SimpleGraph.fromEdgeSet_adj (Set.range D.parentEdge)).mpr ⟨⟨v, rfl⟩, D.parent_ne v⟩

/-- The generated graph has a root walk whose length is exactly the height. -/
theorem walk_to_root (v : V) :
    ∃ p : D.tree.Walk v D.root, p.length = D.height v := by
  have haux : ∀ n : ℕ, ∀ w : V, D.height w = n →
      ∃ p : D.tree.Walk w D.root, p.length = D.height w := by
    intro n
    induction n with
    | zero =>
      intro w hw
      have hroot := (D.height_zero w).mp hw
      subst w
      exact ⟨SimpleGraph.Walk.nil, hw.symm⟩
    | succ n ih =>
      intro w hw
      have hwroot : w ≠ D.root := by
        intro h
        have hz := (D.height_zero w).mpr h
        omega
      let u := D.parent ⟨w, hwroot⟩
      have hu : D.height u = n := by
        have hp := D.parent_height ⟨w, hwroot⟩
        change D.height u + 1 = D.height w at hp
        omega
      obtain ⟨p, hp⟩ := ih u hu
      refine ⟨p.cons (D.parent_adj ⟨w, hwroot⟩), ?_⟩
      simp only [SimpleGraph.Walk.length_cons, hp]
      exact D.parent_height ⟨w, hwroot⟩
  exact haux (D.height v) v rfl

theorem tree_connected : D.tree.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨D.root, ?_⟩
  intro v
  obtain ⟨p, _⟩ := D.walk_to_root v
  exact p.reachable.symm

def parentEdgeToEdgeSet (v : {v : V // v ≠ D.root}) : D.tree.edgeSet :=
  ⟨D.parentEdge v, D.parent_adj v⟩

theorem parentEdgeToEdgeSet_surjective : Function.Surjective D.parentEdgeToEdgeSet := by
  rintro ⟨e, he⟩
  have hmem : e ∈ Set.range D.parentEdge := by
    change e ∈ (SimpleGraph.fromEdgeSet (Set.range D.parentEdge)).edgeSet at he
    rw [SimpleGraph.edgeSet_fromEdgeSet] at he
    exact he.1
  obtain ⟨v, hv⟩ := hmem
  exact ⟨v, Subtype.ext hv⟩

section Finite

variable [Fintype V]

theorem tree_edge_card_bound : Nat.card D.tree.edgeSet ≤ Nat.card {v : V // v ≠ D.root} :=
  Nat.card_le_card_of_surjective D.parentEdgeToEdgeSet D.parentEdgeToEdgeSet_surjective

theorem nonroot_card_add_one : Nat.card {v : V // v ≠ D.root} + 1 = Nat.card V := by
  have h := Fintype.card_subtype_compl (fun v : V => v = D.root)
  rw [Fintype.card_subtype_eq] at h
  have hp : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨D.root⟩
  simp only [← Nat.card_eq_fintype_card] at h hp
  change Nat.card {v : V // v ≠ D.root} = Nat.card V - 1 at h
  omega

/-- The chosen parent graph is a tree, proved by actual edge counting. -/
theorem tree_isTree : D.tree.IsTree := by
  apply (SimpleGraph.isTree_iff_connected_and_card).mpr
  refine ⟨D.tree_connected, ?_⟩
  have hupper := D.tree_edge_card_bound
  have hcard := D.nonroot_card_add_one
  have hlower := D.tree_connected.card_vert_le_card_edgeSet_add_one
  omega

omit [Fintype V] in
theorem tree_le (G : SimpleGraph V)
    (hparent : ∀ v : {v : V // v ≠ D.root}, G.Adj v.val (D.parent v)) : D.tree ≤ G := by
  intro x y hxy
  obtain ⟨⟨v, hv⟩, _⟩ := (SimpleGraph.fromEdgeSet_adj (Set.range D.parentEdge)).mp hxy
  change s(v.val, D.parent v) = s(x, y) at hv
  rcases Sym2.eq_iff.mp hv with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · simpa only [← hx, ← hy] using hparent v
  · simpa only [← hx, ← hy] using (hparent v).symm

/-- An edge outside the parent tree yields a cycle of the literal length
at most 2R+1. The resulting walk uses only vertices of the ambient graph. -/
theorem short_cycle_of_nonacyclic (G : SimpleGraph V) (hTG : D.tree ≤ G)
    (R : ℕ) (hheight : ∀ v, D.height v ≤ R) (hcycle : ¬G.IsAcyclic) :
    ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length ≤ 2 * R + 1 := by
  have hnot : ¬G ≤ D.tree := by
    intro hGT
    have heq : G = D.tree := le_antisymm hGT hTG
    exact hcycle (heq ▸ D.tree_isTree.IsAcyclic)
  have hex : ∃ a b, G.Adj a b ∧ ¬D.tree.Adj a b := by
    by_contra hnone
    apply hnot
    intro a b hab
    by_contra htab
    exact hnone ⟨a, b, hab, htab⟩
  obtain ⟨a, b, hab, htab⟩ := hex
  obtain ⟨pa, hpa⟩ := D.walk_to_root a
  obtain ⟨pb, hpb⟩ := D.walk_to_root b
  let p := pa.append pb.reverse
  let q := p.bypass
  let qG := q.mapLe hTG
  have hqpath : qG.IsPath := p.bypass_isPath.mapLe hTG
  have he_not : s(b, a) ∉ qG.edges := by
    intro he
    have heq : s(b, a) ∈ q.edges := by
      simpa only [qG, SimpleGraph.Walk.mapLe, SimpleGraph.Walk.edges_map,
        SimpleGraph.Hom.coe_ofLE, Sym2.map_id, List.map_id] using he
    exact htab (q.adj_of_mem_edges heq).symm
  have hqc : (qG.cons hab.symm).IsCycle :=
    (SimpleGraph.Walk.cons_isCycle_iff qG hab.symm).mpr ⟨hqpath, he_not⟩
  have hplen : p.length ≤ 2 * R := by
    simp only [p, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse, hpa, hpb]
    have ha := hheight a
    have hb := hheight b
    omega
  have hqlen : qG.length ≤ p.length := by
    simpa only [qG, SimpleGraph.Walk.length_map] using p.length_bypass_le
  refine ⟨b, qG.cons hab.symm, hqc, ?_⟩
  simp only [SimpleGraph.Walk.length_cons]
  omega

end Finite

end HeightParentData

section BallParents

variable {V : Type*}

def ballVertexHeight (G : SimpleGraph V) (o : V) (R : ℕ)
    (v : graphBallVertices G o R) : ℕ := (G.edist o v.val).toNat

theorem ballVertexHeight_coe (G : SimpleGraph V) (o : V) (R : ℕ)
    (v : graphBallVertices G o R) :
    (ballVertexHeight G o R v : ℕ∞) = G.edist o v.val := by
  exact ENat.coe_toNat (ne_top_of_le_ne_top (ENat.coe_ne_top R) v.property)

theorem ballVertexHeight_le (G : SimpleGraph V) (o : V) (R : ℕ)
    (v : graphBallVertices G o R) : ballVertexHeight G o R v ≤ R := by
  apply ENat.coe_le_coe.mp
  rw [ballVertexHeight_coe]
  exact v.property

theorem ballVertexHeight_zero (G : SimpleGraph V) (o : V) (R : ℕ)
    (v : graphBallVertices G o R) :
    ballVertexHeight G o R v = 0 ↔ v = ⟨o, center_mem_graphBall G o R⟩ := by
  constructor
  · intro hv
    have hdist : G.edist o v.val = 0 := by rw [← ballVertexHeight_coe G o R v, hv]; rfl
    exact Subtype.ext (SimpleGraph.edist_eq_zero_iff.mp hdist).symm
  · intro hv
    subst v
    simp only [ballVertexHeight, G.edist_self, ENat.toNat_zero]

/-- A nonroot ball vertex has an actual adjacent parent at distance one less. -/
theorem ball_vertex_parent_exists (G : SimpleGraph V) (o : V) (R : ℕ)
    (v : {v : graphBallVertices G o R // v ≠ ⟨o, center_mem_graphBall G o R⟩}) :
    ∃ u : graphBallVertices G o R, (graphBall G o R).Adj v.val u ∧
      ballVertexHeight G o R u + 1 = ballVertexHeight G o R v.val := by
  have hvpos : 0 < ballVertexHeight G o R v.val := by
    apply Nat.pos_of_ne_zero
    exact fun hzero => v.property ((ballVertexHeight_zero G o R v.val).mp hzero)
  let n := ballVertexHeight G o R v.val - 1
  have hsucc : n + 1 = ballVertexHeight G o R v.val := Nat.sub_add_cancel hvpos
  have hdist : G.edist o v.val.val = (n + 1 : ℕ) := by
    rw [hsucc]
    exact (ballVertexHeight_coe G o R v.val).symm
  obtain ⟨u, huv, hu⟩ := edist_succ_parent G o v.val.val n hdist
  have humem : u ∈ graphBallVertices G o R := by
    change G.edist o u ≤ (R : ℕ)
    rw [hu]
    exact ENat.coe_le_coe.mpr ((Nat.sub_le _ _).trans (ballVertexHeight_le G o R v.val))
  have huheight : ballVertexHeight G o R ⟨u, humem⟩ = n := by
    simp only [ballVertexHeight, hu, ENat.toNat_coe]
  exact ⟨⟨u, humem⟩, huv.symm, by rw [huheight]; exact hsucc⟩

/-- The actual shortest-distance parent system on the induced ball. -/
def ballHeightParentData (G : SimpleGraph V) (o : V) (R : ℕ) :
    HeightParentData (graphBallVertices G o R) where
  root := ⟨o, center_mem_graphBall G o R⟩
  height := ballVertexHeight G o R
  height_zero := ballVertexHeight_zero G o R
  parent v := Classical.choose (ball_vertex_parent_exists G o R v)
  parent_height v := (Classical.choose_spec (ball_vertex_parent_exists G o R v)).2

theorem ballHeightParentData_parent_adj (G : SimpleGraph V) (o : V) (R : ℕ)
    (v : {v : graphBallVertices G o R // v ≠ (ballHeightParentData G o R).root}) :
    (graphBall G o R).Adj v.val ((ballHeightParentData G o R).parent v) :=
  (Classical.choose_spec (ball_vertex_parent_exists G o R v)).1

end BallParents

section FiniteBall

variable {V : Type*} [Fintype V]

/-- Every nonacyclic induced radius-R ball contains a simple cycle of length
at most the literal 2R+1. Its entire vertex type is the original ball. -/
theorem nonacyclic_ball_short_cycle (G : SimpleGraph V) (o : V) (R : ℕ)
    (hcycle : ¬(graphBall G o R).IsAcyclic) :
    ∃ v : graphBallVertices G o R, ∃ p : (graphBall G o R).Walk v v,
      p.IsCycle ∧ p.length ≤ 2 * R + 1 := by
  let D := ballHeightParentData G o R
  have hle : D.tree ≤ graphBall G o R :=
    D.tree_le _ (ballHeightParentData_parent_adj G o R)
  exact D.short_cycle_of_nonacyclic _ hle R (ballVertexHeight_le G o R) hcycle

/-- Ambient-graph version, with explicit support containment and both length
bounds. No cycle witness or spanning-tree hypothesis is an input. -/
theorem nonacyclic_ball_ambient_short_cycle (G : SimpleGraph V) (o : V) (R : ℕ)
    (hcycle : ¬(graphBall G o R).IsAcyclic) :
    ∃ v ∈ graphBallVertices G o R, ∃ p : G.Walk v v,
      p.IsCycle ∧ 3 ≤ p.length ∧ p.length ≤ 2 * R + 1 ∧
        ∀ w ∈ p.support, w ∈ graphBallVertices G o R := by
  obtain ⟨v, p, hp, hlen⟩ := nonacyclic_ball_short_cycle G o R hcycle
  let f := SimpleGraph.Embedding.induce (G := G) (graphBallVertices G o R)
  let q := p.map f.toHom
  have hq : q.IsCycle := hp.map f.injective
  refine ⟨v.val, v.property, q, hq, hq.three_le_length, ?_, ?_⟩
  · simpa only [q, SimpleGraph.Walk.length_map] using hlen
  · intro w hw
    change w ∈ (p.map f.toHom).support at hw
    rw [SimpleGraph.Walk.support_map] at hw
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hw
    exact u.property

end FiniteBall

section LabelledBallWitness

variable {N : ℕ}

/-- An actual injective cycle pattern of length in [3,2R+1], entirely inside
the nonacyclic ball; in particular it has a vertex within distance R of o. -/
theorem nonacyclic_ball_cycle_pattern (G : SimpleGraph (Fin N)) (o : Fin N) (R : ℕ)
    (hcycle : ¬(graphBall G o R).IsAcyclic) :
    ∃ ell : ℕ, 3 ≤ ell ∧ ell ≤ 2 * R + 1 ∧
      ∃ f : Fin ell ↪ Fin N, cyclePattern f ≤ G ∧
        (∀ i, f i ∈ graphBallVertices G o R) ∧
          ∃ i, G.edist o (f i) ≤ (R : ℕ∞) := by
  obtain ⟨v, p, hp, hlen⟩ := nonacyclic_ball_short_cycle G o R hcycle
  obtain ⟨f, hf, hinside, i, hi⟩ :=
    induced_cycle_pattern_witness (graphBallVertices G o R) v p hp
  exact ⟨p.length, hp.three_le_length, hlen, f, hf, hinside, i, hinside i⟩

/-- Positive actual labelled-cycle count at some length in [3,2R+1]. -/
theorem nonacyclic_ball_labelledCycleCount_pos (G : SimpleGraph (Fin N))
    (o : Fin N) (R : ℕ) (hcycle : ¬(graphBall G o R).IsAcyclic) :
    ∃ ell : ℕ, 3 ≤ ell ∧ ell ≤ 2 * R + 1 ∧ 0 < labelledCycleCount ell G := by
  obtain ⟨v, p, hp, hlen⟩ := nonacyclic_ball_short_cycle G o R hcycle
  exact ⟨p.length, hp.three_le_length, hlen,
    labelledCycleCount_pos_of_induced_cycle (graphBallVertices G o R) v p hp⟩

/-- Balls are connected, so the paper's non-tree test supplies the same
actual short-cycle pattern witness. -/
theorem nonTree_ball_cycle_pattern (G : SimpleGraph (Fin N)) (o : Fin N) (R : ℕ)
    (hnotree : ¬(graphBall G o R).IsTree) :
    ∃ ell : ℕ, 3 ≤ ell ∧ ell ≤ 2 * R + 1 ∧
      ∃ f : Fin ell ↪ Fin N, cyclePattern f ≤ G ∧
        (∀ i, f i ∈ graphBallVertices G o R) ∧
          ∃ i, G.edist o (f i) ≤ (R : ℕ∞) := by
  apply nonacyclic_ball_cycle_pattern G o R
  exact fun hacyclic => hnotree ⟨graphBall_connected G o R, hacyclic⟩

theorem nonTreeCenter_labelledCycleCount_pos (G : SimpleGraph (Fin N))
    (o : Fin N) (R : ℕ) (ho : o ∈ nonTreeCenters G R) :
    ∃ ell : ℕ, 3 ≤ ell ∧ ell ≤ 2 * R + 1 ∧ 0 < labelledCycleCount ell G := by
  apply nonacyclic_ball_labelledCycleCount_pos G o R
  have hnotree := (nonTreeCenters_membership G R o).mp ho
  exact fun hacyclic => hnotree ⟨graphBall_connected G o R, hacyclic⟩

end LabelledBallWitness

end LocalLaw
