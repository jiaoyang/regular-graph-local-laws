import LocalLaw.NonbacktrackingSequences
import LocalLaw.CyclePackingMomentBridge

/-!
# Universal short-cycle overlap from sharp path counting

A short cycle through a prescribed vertex is rotated so that vertex is its
first label. Its remaining adjacent injective sequence is counted by the
nonbacktracking path space. Thus the overlap bound requires only a degree
bound, including at a structural radius with a fixed additive offset.
-/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance universalCycleDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {N : ℕ}

/-- Translation of finite cycle labels preserves its edge graph. -/
theorem cycle_translation_adj (n : ℕ) (a i j : Fin (n + 3)) :
    (SimpleGraph.cycleGraph (n + 3)).Adj (a + i) (a + j) ↔
      (SimpleGraph.cycleGraph (n + 3)).Adj i j := by
  simp only [SimpleGraph.cycleGraph_adj, add_sub_add_left_eq_sub]

def cycleRotatedEmbedding {n : ℕ} (f : Fin (n + 3) ↪ Fin N) (a : Fin (n + 3)) :
    Fin (n + 3) ↪ Fin N := (Equiv.addLeft a).toEmbedding.trans f

/-- Rotation changes neither the actual pattern nor its support. -/
theorem cyclePattern_rotated {n : ℕ} (f : Fin (n + 3) ↪ Fin N) (a : Fin (n + 3)) :
    cyclePattern (cycleRotatedEmbedding f a) = cyclePattern f := by
  apply le_antisymm
  · apply (mappedPattern_le_iff _ _ _).mpr
    intro i j hij
    exact SimpleGraph.map_adj_apply.mpr ((cycle_translation_adj n a i j).mpr hij)
  · intro x y hxy
    obtain ⟨i, j, hij, rfl, rfl⟩ := (SimpleGraph.map_adj f _ x y).mp hxy
    have hσ : ∀ i : Fin (n + 3), a + (i - a) = i := by intro i; abel
    have hcyc : (SimpleGraph.cycleGraph (n + 3)).Adj (i - a) (j - a) := by
      apply (cycle_translation_adj n a _ _).mp
      simpa only [hσ] using hij
    exact (SimpleGraph.map_adj (cycleRotatedEmbedding f a) _ _ _).mpr
      ⟨i - a, j - a, hcyc, congrArg f (hσ i), congrArg f (hσ j)⟩

/-- A code needs only the adjacent injective sequence; retaining an extra
closing-edge condition would further reduce this finite space. -/
def RootedShortCycleCode (G : SimpleGraph (Fin N)) (U : ℕ) (v : Fin N) :=
  Σ n : Fin (U + 1), {_s : RootedSimpleSequence G v (n.val + 2) // n.val + 3 ≤ U}

instance rootedShortCycleCodeFintype (G : SimpleGraph (Fin N)) (U : ℕ) (v : Fin N) :
    Fintype (RootedShortCycleCode G U v) := by unfold RootedShortCycleCode; infer_instance

def rootedShortCycleCodeGraph {G : SimpleGraph (Fin N)} {U : ℕ} {v : Fin N}
    (s : RootedShortCycleCode G U v) : SimpleGraph (Fin N) := cyclePattern s.2.val.val

/-- Every actual distinct cycle through v has a root-first finite code. -/
theorem shortCycleThrough_code_exists (G : SimpleGraph (Fin N)) (U : ℕ) (v : Fin N)
    (C : ShortCycleThrough G U v) :
    ∃ s : RootedShortCycleCode G U v, rootedShortCycleCodeGraph s = C.val.graph := by
  obtain ⟨ell, hlower, hupper, f, hgraph⟩ := C.val.representation
  have hv : v ∈ (cyclePattern f).support := by
    rw [← hgraph]
    exact (C.val.mem_support_iff v).mp C.property
  rw [cyclePattern_support_eq_range hlower f] at hv
  obtain ⟨a, ha⟩ := hv
  obtain ⟨n, rfl⟩ : ∃ n, ell = n + 3 := ⟨ell - 3, by omega⟩
  let f' := cycleRotatedEmbedding f a
  have hf0 : f' 0 = v := by change f (a + 0) = v; simpa only [add_zero] using ha
  have hfgraph : cyclePattern f' = C.val.graph := (cyclePattern_rotated f a).trans hgraph.symm
  have hfadj : ∀ i : Fin (n + 2), G.Adj (f' i.castSucc) (f' i.succ) := by
    intro i
    apply C.val.le_graph
    rw [← hfgraph]
    apply SimpleGraph.map_adj_apply.mpr
    apply SimpleGraph.pathGraph_le_cycleGraph
    exact SimpleGraph.pathGraph_adj.mpr (Or.inl (by rfl))
  let s : RootedSimpleSequence G v (n + 2) := ⟨f', hf0, hfadj⟩
  refine ⟨⟨⟨n, by omega⟩, s, hupper⟩, ?_⟩
  exact hfgraph

def shortCycleThroughEncoding (G : SimpleGraph (Fin N)) (U : ℕ) (v : Fin N)
    (C : ShortCycleThrough G U v) : RootedShortCycleCode G U v :=
  Classical.choose (shortCycleThrough_code_exists G U v C)

theorem shortCycleThroughEncoding_injective (G : SimpleGraph (Fin N)) (U : ℕ) (v : Fin N) :
    Function.Injective (shortCycleThroughEncoding G U v) := by
  intro C D h
  apply Subtype.ext
  apply ShortCyclePattern.graph_injective
  have hc := Classical.choose_spec (shortCycleThrough_code_exists G U v C)
  have hd := Classical.choose_spec (shortCycleThrough_code_exists G U v D)
  change rootedShortCycleCodeGraph (shortCycleThroughEncoding G U v C) = C.val.graph at hc
  change rootedShortCycleCodeGraph (shortCycleThroughEncoding G U v D) = D.val.graph at hd
  rw [h] at hc
  exact hc.symm.trans hd

/-- Uniform sharp overlap at one vertex, with no ball-excess hypothesis. -/
theorem shortCycleThrough_card_universal (G : SimpleGraph (Fin N)) (U d : ℕ)
    (hd : 2 ≤ d) (hdeg : ∀ v, G.degree v ≤ d) (v : Fin N) :
    Nat.card (ShortCycleThrough G U v) ≤ (U + 1) * (d + 1) * (d - 1) ^ U := by
  have hcode : Nat.card (RootedShortCycleCode G U v) ≤ (U + 1) * ((d + 1) * (d - 1) ^ U) := by
    change Nat.card (Σ n : Fin (U + 1), {_s : RootedSimpleSequence G v (n.val + 2) // n.val + 3 ≤ U}) ≤ _
    rw [Nat.card_sigma]
    calc
      _ ≤ ∑ _n : Fin (U + 1), (d + 1) * (d - 1) ^ U := by
        apply Finset.sum_le_sum
        intro n _
        by_cases hn : n.val + 3 ≤ U
        · exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
            ((rootedSimpleSequence_card_bound G v d (n.val + 2) hd hdeg).trans
              (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega : 0 < d - 1) (by omega))))
        · letI : IsEmpty {_s : RootedSimpleSequence G v (n.val + 2) // n.val + 3 ≤ U} := ⟨fun s => hn s.property⟩
          simp
      _ = _ := by simp
  exact (Nat.card_le_card_of_injective _ (shortCycleThroughEncoding_injective G U v)).trans
    (hcode.trans_eq (by ring))

/-- A pattern conflicts with only a controlled number of other patterns. -/
theorem shortCycleOverlap_card_universal (G : SimpleGraph (Fin N)) (U d : ℕ)
    (hd : 2 ≤ d) (hdeg : ∀ v, G.degree v ≤ d) (A : ShortCyclePattern G U) :
    Nat.card {B : ShortCyclePattern G U // shortCycleOverlap A B} ≤
      U * ((U + 1) * (d + 1) * (d - 1) ^ U) := by
  let bad : Finset (ShortCyclePattern G U) := A.support.biUnion
    (fun v => Finset.univ.filter (fun B => v ∈ B.support))
  have heq : Finset.univ.filter (shortCycleOverlap A) = bad := by
    ext B
    simp only [bad, shortCycleOverlap, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Finset.not_disjoint_iff]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, heq]
  calc
    bad.card ≤ ∑ v ∈ A.support, (Finset.univ.filter (fun B : ShortCyclePattern G U => v ∈ B.support)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ A.support, (U + 1) * (d + 1) * (d - 1) ^ U := by
      apply Finset.sum_le_sum
      intro v _
      simpa only [ShortCycleThrough, Nat.card_eq_fintype_card, Fintype.card_subtype] using
        shortCycleThrough_card_universal G U d hd hdeg v
    _ = A.support.card * ((U + 1) * (d + 1) * (d - 1) ^ U) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ A.support_card_le

end
end LocalLaw
