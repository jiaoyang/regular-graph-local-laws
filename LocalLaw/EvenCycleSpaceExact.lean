import LocalLaw.FundamentalCycleBasis

/-!
# The actual fundamental-cycle code is bijective

Finite symmetric differences assemble the single-edge fundamental codes.
Together with the previously proved injectivity, this proves the exact count
2^excess of even subgraphs. It also proves that if all single-code generators
avoid a vertex set, then every even edge subgraph avoids that set.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
namespace LocalLaw

local instance evenCycleSpaceExactDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V]

def emptyEvenSubgraph (G : SimpleGraph V) : EvenEdgeSubgraph G :=
  ⟨⊥, bot_le, fun v => by
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    simp⟩

def xorEvenSubgraph {G : SimpleGraph V} (A B : EvenEdgeSubgraph G) : EvenEdgeSubgraph G :=
  ⟨graphXor A.val B.val, fun _ _ h => h.elim (fun h => A.property.1 h.1)
    (fun h => B.property.1 h.1), graphXor_even A.val B.val A.property.2 B.property.2⟩

theorem evenSubgraphCode_empty (G T : SimpleGraph V) :
    evenSubgraphCode G T (emptyEvenSubgraph G) = ∅ := by
  ext e
  simp [evenSubgraphCode, emptyEvenSubgraph]

theorem evenSubgraphCode_xor (G T : SimpleGraph V) (A B : EvenEdgeSubgraph G) :
    evenSubgraphCode G T (xorEvenSubgraph A B) =
      (evenSubgraphCode G T A \ evenSubgraphCode G T B) ∪
        (evenSubgraphCode G T B \ evenSubgraphCode G T A) := by
  ext e
  simp only [evenSubgraphCode, xorEvenSubgraph, graphXor, Set.mem_setOf_eq,
    SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_sdiff, Set.mem_union, Set.mem_diff]

def assembleEvenCode (G T : SimpleGraph V) (gen : (G \ T).edgeSet → EvenEdgeSubgraph G) :
    List (G \ T).edgeSet → EvenEdgeSubgraph G
  | [] => emptyEvenSubgraph G
  | e :: L => xorEvenSubgraph (gen e) (assembleEvenCode G T gen L)

theorem assembleEvenCode_code (G T : SimpleGraph V)
    (gen : (G \ T).edgeSet → EvenEdgeSubgraph G)
    (hgen : ∀ e, evenSubgraphCode G T (gen e) = {e})
    (L : List (G \ T).edgeSet) (hL : L.Nodup) :
    evenSubgraphCode G T (assembleEvenCode G T gen L) = (L.toFinset : Set (G \ T).edgeSet) := by
  induction L with
  | nil => simpa only [assembleEvenCode, List.toFinset_nil, Finset.coe_empty] using evenSubgraphCode_empty G T
  | cons e L ih =>
      obtain ⟨he, htail⟩ := List.nodup_cons.mp hL
      change evenSubgraphCode G T (xorEvenSubgraph (gen e) (assembleEvenCode G T gen L)) = _
      rw [evenSubgraphCode_xor, hgen, ih htail]
      ext x
      by_cases hxe : x = e
      · subst x
        simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe,
          List.mem_toFinset, he, not_false_eq_true, and_true, eq_self_iff_true, true_and,
          List.toFinset_cons, Finset.mem_insert, true_or]
      · simp [hxe]

theorem evenSubgraphCode_surjective_of_generators (G T : SimpleGraph V)
    (gen : (G \ T).edgeSet → EvenEdgeSubgraph G)
    (hgen : ∀ e, evenSubgraphCode G T (gen e) = {e}) :
    Function.Surjective (evenSubgraphCode G T) := by
  intro S
  refine ⟨assembleEvenCode G T gen S.toFinset.toList, ?_⟩
  rw [assembleEvenCode_code G T gen hgen _ S.toFinset.nodup_toList]
  simp

/-- Fundamental single-code generators are constructed from actual paths
in the actual spanning tree, not assumed as a cycle-basis axiom. -/
theorem fundamental_even_generator_exists (G T : SimpleGraph V) (hTG : T ≤ G)
    (hT : T.IsTree) (e : (G \ T).edgeSet) :
    ∃ C : EvenEdgeSubgraph G, evenSubgraphCode G T C = {e} := by
  rcases e with ⟨z, hz⟩
  induction z using Sym2.inductionOn with
  | _ a b =>
      change G.Adj a b ∧ ¬ T.Adj a b at hz
      obtain ⟨p, hp⟩ := hT.isConnected.exists_isPath b a
      obtain ⟨C, _, _, _, hc⟩ := fundamental_even_cycle_of_path G T hTG hz.1 hz.2 p hp
      exact ⟨C, hc⟩

def chosenFundamentalGenerator (G T : SimpleGraph V) (hTG : T ≤ G) (hT : T.IsTree)
    (e : (G \ T).edgeSet) : EvenEdgeSubgraph G :=
  Classical.choose (fundamental_even_generator_exists G T hTG hT e)

theorem chosenFundamentalGenerator_code (G T : SimpleGraph V) (hTG : T ≤ G) (hT : T.IsTree)
    (e : (G \ T).edgeSet) :
    evenSubgraphCode G T (chosenFundamentalGenerator G T hTG hT e) = {e} :=
  Classical.choose_spec (fundamental_even_generator_exists G T hTG hT e)

theorem evenSubgraphCode_bijective (G T : SimpleGraph V) (hTG : T ≤ G) (hT : T.IsTree) :
    Function.Bijective (evenSubgraphCode G T) :=
  ⟨evenSubgraphCode_injective G T hT.IsAcyclic,
    evenSubgraphCode_surjective_of_generators G T (chosenFundamentalGenerator G T hTG hT)
      (chosenFundamentalGenerator_code G T hTG hT)⟩

/-- Exact finite cycle-space cardinality, including the empty graph. -/
theorem evenEdgeSubgraph_card_eq_excess (G : SimpleGraph V) (hG : G.Connected) :
    Nat.card (EvenEdgeSubgraph G) = 2 ^ graphExcess G := by
  obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
  have h := Nat.card_congr (Equiv.ofBijective (evenSubgraphCode G T)
    (evenSubgraphCode_bijective G T hTG hT))
  have hset : Nat.card (Set (G \ T).edgeSet) = 2 ^ Nat.card (G \ T).edgeSet := by
    rw [Nat.card_eq_fintype_card, Fintype.card_set, ← Nat.card_eq_fintype_card]
  rw [hset, off_tree_edge_count G T hG hTG hT] at h
  exact h

omit [Fintype V] in
theorem graphXor_avoids (A : Set V) (F K : SimpleGraph V)
    (hF : ∀ x ∈ A, x ∉ F.support) (hK : ∀ x ∈ A, x ∉ K.support) :
    ∀ x ∈ A, x ∉ (graphXor F K).support := by
  intro x hx hsupport
  obtain ⟨y, hy⟩ := ((graphXor F K).mem_support).mp hsupport
  rcases hy with hy | hy
  · exact hF x hx ((F.mem_support).mpr ⟨y, hy.1⟩)
  · exact hK x hx ((K.mem_support).mpr ⟨y, hy.1⟩)

theorem assembleEvenCode_avoids (G T : SimpleGraph V)
    (gen : (G \ T).edgeSet → EvenEdgeSubgraph G) (A : Set V)
    (hgen : ∀ e, ∀ x ∈ A, x ∉ (gen e).val.support) (L : List (G \ T).edgeSet) :
    ∀ x ∈ A, x ∉ (assembleEvenCode G T gen L).val.support := by
  induction L with
  | nil =>
      change ∀ x ∈ A, x ∉ (⊥ : SimpleGraph V).support
      intro x _ hx
      obtain ⟨y, hy⟩ := ((⊥ : SimpleGraph V).mem_support).mp hx
      exact hy
  | cons e L ih => exact graphXor_avoids A _ _ (hgen e) ih

/-- If the actual single-code cycles avoid A, all even subgraphs avoid A.
This is the finite linear-generation step used to transfer the cyclic part
of a switched small ball into the original graph. -/
theorem even_subgraphs_avoid_of_generators (G T : SimpleGraph V) (hT : T.IsAcyclic)
    (A : Set V) (gen : (G \ T).edgeSet → EvenEdgeSubgraph G)
    (hcode : ∀ e, evenSubgraphCode G T (gen e) = {e})
    (havoid : ∀ e, ∀ x ∈ A, x ∉ (gen e).val.support) (C : EvenEdgeSubgraph G) :
    ∀ x ∈ A, x ∉ C.val.support := by
  let L := (evenSubgraphCode G T C).toFinset.toList
  have hcodes : evenSubgraphCode G T (assembleEvenCode G T gen L) = evenSubgraphCode G T C := by
    rw [assembleEvenCode_code G T gen hcode _ (Finset.nodup_toList _)]
    simp [L]
  have heq := evenSubgraphCode_injective G T hT hcodes
  have h := assembleEvenCode_avoids G T gen A havoid L
  rwa [heq] at h

end LocalLaw
