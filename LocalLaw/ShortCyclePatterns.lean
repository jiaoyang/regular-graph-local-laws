import LocalLaw.CycleSpaceCounting
import LocalLaw.CycleCounting
import LocalLaw.CycleArcGeometry
import LocalLaw.LocalExcessGeometry

/-!
# Distinct short-cycle edge patterns and local overlap

The finite objects here are actual edge graphs, with one chosen injective
cycle representation per graph. No orientation or starting-label multiplicity
is counted. Two-arc cycle geometry places every pattern through v inside B_R(v)
when its length is at most 2R+1. Restriction to that ball is injective and even,
so the actual cycle-space count bounds the number of patterns through v.
-/

noncomputable section
set_option maxHeartbeats 1600000

namespace LocalLaw

local instance shortCycleDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {N : ℕ}

/-- An actual injective cycle representation of the entire edge graph C. -/
structure ShortCycleRepresentation (C : SimpleGraph (Fin N)) (U : ℕ) where
  length : ℕ
  lower : 3 ≤ length
  upper : length ≤ U
  embedding : Fin length ↪ Fin N
  graph_eq : C = cyclePattern embedding

/-- Distinct edge graphs, rather than their labelled cycle representations. -/
def ShortCyclePattern (G : SimpleGraph (Fin N)) (U : ℕ) :=
  {C : SimpleGraph (Fin N) // C ≤ G ∧ Nonempty (ShortCycleRepresentation C U)}

instance shortCyclePatternFintype (G : SimpleGraph (Fin N)) (U : ℕ) :
    Fintype (ShortCyclePattern G U) := by
  unfold ShortCyclePattern
  infer_instance

theorem cyclePattern_support_eq_range {ell : ℕ} (hell : 3 ≤ ell)
    (f : Fin ell ↪ Fin N) : (cyclePattern f).support = Set.range f := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, hvw⟩ := ((cyclePattern f).mem_support).mp hv
    obtain ⟨i, j, _, hi, _⟩ := (SimpleGraph.map_adj f (SimpleGraph.cycleGraph ell) v w).mp hvw
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    have hpos : 0 < (SimpleGraph.cycleGraph ell).degree i := by
      rw [cycleGraph_degree ell hell i]
      decide
    obtain ⟨j, hij⟩ := ((SimpleGraph.cycleGraph ell).degree_pos_iff_exists_adj i).mp hpos
    exact ((cyclePattern f).mem_support).mpr ⟨f j, SimpleGraph.map_adj_apply.mpr hij⟩

theorem cyclePattern_all_even {ell : ℕ} (hell : 3 ≤ ell) (f : Fin ell ↪ Fin N) :
    ∀ v, Even ((cyclePattern f).degree v) := by
  intro v
  by_cases hv : v ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hv
    have htwo := cyclePattern_degree_image hell f i
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at htwo ⊢
    rw [htwo]
    decide
  · have hzero := cyclePattern_degree_outside f v hv
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hzero ⊢
    rw [hzero]
    exact Even.zero

namespace ShortCyclePattern

variable {G : SimpleGraph (Fin N)} {U : ℕ}

def graph (C : ShortCyclePattern G U) : SimpleGraph (Fin N) := C.val

theorem le_graph (C : ShortCyclePattern G U) : C.graph ≤ G := C.property.1

theorem graph_injective : Function.Injective (graph (G := G) (U := U)) := Subtype.val_injective

def ofCycle {ell : ℕ} (hell : 3 ≤ ell) (hupper : ell ≤ U)
    (f : Fin ell ↪ Fin N) (hsub : cyclePattern f ≤ G) : ShortCyclePattern G U :=
  ⟨cyclePattern f, hsub, ⟨⟨ell, hell, hupper, f, rfl⟩⟩⟩

/-- A single fixed representative is chosen for each actual edge pattern. -/
def representation (C : ShortCyclePattern G U) : ShortCycleRepresentation C.graph U :=
  Classical.choice C.property.2

def length (C : ShortCyclePattern G U) : ℕ := C.representation.length

def embedding (C : ShortCyclePattern G U) : Fin C.length ↪ Fin N := C.representation.embedding

theorem length_lower (C : ShortCyclePattern G U) : 3 ≤ C.length := C.representation.lower

theorem length_upper (C : ShortCyclePattern G U) : C.length ≤ U := C.representation.upper

theorem graph_eq (C : ShortCyclePattern G U) : C.graph = cyclePattern C.embedding :=
  C.representation.graph_eq

def support (C : ShortCyclePattern G U) : Finset (Fin N) := C.graph.support.toFinset

theorem mem_support_iff (C : ShortCyclePattern G U) (v : Fin N) :
    v ∈ C.support ↔ v ∈ C.graph.support := Set.mem_toFinset

theorem mem_support_degree (C : ShortCyclePattern G U) (v : Fin N) :
    v ∈ C.support ↔ 0 < C.graph.degree v := by
  rw [C.mem_support_iff, SimpleGraph.degree_pos_iff_mem_support]

theorem graph_support_eq_range (C : ShortCyclePattern G U) :
    C.graph.support = Set.range C.embedding := by
  rw [C.graph_eq]
  exact cyclePattern_support_eq_range C.length_lower C.embedding

theorem mem_support_embedding (C : ShortCyclePattern G U) (v : Fin N) :
    v ∈ C.support ↔ ∃ i, C.embedding i = v := by
  rw [C.mem_support_iff, C.graph_support_eq_range]
  rfl

theorem embedding_mem_support (C : ShortCyclePattern G U) (i : Fin C.length) :
    C.embedding i ∈ C.support := (C.mem_support_embedding _).mpr ⟨i, rfl⟩

theorem support_card_eq_length (C : ShortCyclePattern G U) : C.support.card = C.length := by
  have hrange : Nat.card (Set.range C.embedding) = C.length := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
      (Nat.card_congr (Equiv.ofInjective C.embedding C.embedding.injective)).symm
  simpa only [support, C.graph_support_eq_range, Set.toFinset_card,
    ← Nat.card_eq_fintype_card] using hrange

theorem support_card_le (C : ShortCyclePattern G U) : C.support.card ≤ U := by
  rw [C.support_card_eq_length]
  exact C.length_upper

theorem support_nonempty (C : ShortCyclePattern G U) : C.support.Nonempty := by
  apply Finset.card_pos.mp
  rw [C.support_card_eq_length]
  have h := C.length_lower
  omega

theorem edgeCount_eq_length (C : ShortCyclePattern G U) : graphEdgeCount C.graph = C.length := by
  rw [C.graph_eq]
  exact cyclePattern_edgeCount C.length_lower C.embedding

theorem all_even (C : ShortCyclePattern G U) : ∀ v, Even (C.graph.degree v) := by
  have h := cyclePattern_all_even C.length_lower C.embedding
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h ⊢
  rw [C.graph_eq]
  exact h

def cycleHom (C : ShortCyclePattern G U) : SimpleGraph.cycleGraph C.length →g G where
  toFun := C.embedding
  map_rel' := by
    intro i j hij
    apply C.le_graph
    rw [C.graph_eq]
    exact SimpleGraph.map_adj_apply.mpr hij

/-- The exact half-length arc bound places the entire cycle inside B_R(v). -/
theorem graph_support_subset_ball (C : ShortCyclePattern G U) (R : ℕ)
    (hU : U ≤ 2 * R + 1) (v : Fin N) (hv : v ∈ C.support) :
    C.graph.support ⊆ graphBallVertices G v R := by
  have hvimage : v ∈ Set.range C.embedding := by
    rw [← C.graph_support_eq_range]
    exact (C.mem_support_iff v).mp hv
  obtain ⟨i, hi⟩ := hvimage
  intro w hw
  rw [C.graph_support_eq_range] at hw
  obtain ⟨j, hj⟩ := hw
  have hball := cycle_hom_image_ball C.length R C.length_lower
    (C.length_upper.trans hU) C.cycleHom i j
  change C.embedding j ∈ graphBallVertices G (C.embedding i) R at hball
  simpa only [hi, hj] using hball

end ShortCyclePattern

/-- Restricting edge graphs supported in S is injective. -/
theorem graph_restriction_injective_on_support (S : Set (Fin N))
    (A B : SimpleGraph (Fin N)) (hA : A.support ⊆ S) (hB : B.support ⊆ S)
    (heq : A.induce S = B.induce S) : A = B := by
  ext x y
  by_cases hx : x ∈ S
  · by_cases hy : y ∈ S
    · exact (congrArg (fun H : SimpleGraph S => H.Adj ⟨x, hx⟩ ⟨y, hy⟩) heq).to_iff
    · have ha : ¬A.Adj x y := fun h => hy (hA ((A.mem_support).mpr ⟨x, h.symm⟩))
      have hb : ¬B.Adj x y := fun h => hy (hB ((B.mem_support).mpr ⟨x, h.symm⟩))
      exact iff_of_false ha hb
  · have ha : ¬A.Adj x y := fun h => hx (hA ((A.mem_support).mpr ⟨y, h⟩))
    have hb : ¬B.Adj x y := fun h => hx (hB ((B.mem_support).mpr ⟨y, h⟩))
    exact iff_of_false ha hb

/-- Short-cycle edge patterns containing a fixed actual ambient vertex. -/
def ShortCycleThrough (G : SimpleGraph (Fin N)) (U : ℕ) (v : Fin N) :=
  {C : ShortCyclePattern G U // v ∈ C.support}

instance shortCycleThroughFintype (G : SimpleGraph (Fin N)) (U : ℕ) (v : Fin N) :
    Fintype (ShortCycleThrough G U v) := by
  unfold ShortCycleThrough
  infer_instance

def shortCycleBallRestriction (G : SimpleGraph (Fin N)) (U R : ℕ)
    (hU : U ≤ 2 * R + 1) (v : Fin N) (C : ShortCycleThrough G U v) :
    EvenEdgeSubgraph (graphBall G v R) := by
  let S := graphBallVertices G v R
  have hs : C.val.graph.support ⊆ S := C.val.graph_support_subset_ball R hU v C.property
  refine ⟨C.val.graph.induce S, ?_, ?_⟩
  · intro x y hxy
    exact C.val.le_graph hxy
  · intro w
    have he := C.val.all_even w.val
    have hd := SimpleGraph.degree_induce_of_support_subset hs w
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at he hd ⊢
    rw [hd]
    exact he

theorem shortCycleBallRestriction_injective (G : SimpleGraph (Fin N)) (U R : ℕ)
    (hU : U ≤ 2 * R + 1) (v : Fin N) :
    Function.Injective (shortCycleBallRestriction G U R hU v) := by
  intro A B heq
  have hgraphs : A.val.graph.induce (graphBallVertices G v R) =
      B.val.graph.induce (graphBallVertices G v R) := congrArg Subtype.val heq
  have hab := graph_restriction_injective_on_support (graphBallVertices G v R)
    A.val.graph B.val.graph (A.val.graph_support_subset_ball R hU v A.property)
    (B.val.graph_support_subset_ball R hU v B.property) hgraphs
  apply Subtype.ext
  exact Subtype.ext hab

/-- Local cycle overlap is bounded by the actual even-subgraph count of B_R(v). -/
theorem shortCycleThrough_card_le (G : SimpleGraph (Fin N)) (U R ω : ℕ)
    (hU : U ≤ 2 * R + 1) (v : Fin N) (hbudget : graphBallExcess G v R ≤ ω) :
    Nat.card (ShortCycleThrough G U v) ≤ 2 ^ ω := by
  have hball : graphExcess (graphBall G v R) ≤ ω := by
    simpa only [graphBallExcess, graphExcess, SimpleGraph.edgeFinset_card,
      ← Nat.card_eq_fintype_card] using hbudget
  exact (Nat.card_le_card_of_injective (shortCycleBallRestriction G U R hU v)
    (shortCycleBallRestriction_injective G U R hU v)).trans
      (evenEdgeSubgraph_card_le_budget (graphBall G v R) (graphBall_connected G v R) ω hball)

theorem shortCycleThrough_card_le_uniform (G : SimpleGraph (Fin N)) (U R ω : ℕ)
    (hU : U ≤ 2 * R + 1) (hbudget : ∀ v, graphBallExcess G v R ≤ ω) :
    ∀ v, Nat.card (ShortCycleThrough G U v) ≤ 2 ^ ω :=
  fun v => shortCycleThrough_card_le G U R ω hU v (hbudget v)

end LocalLaw
