import LocalLaw.BicyclicBallWitness
import LocalLaw.PathGraftGraph

/-!
# Canonical four-tail rooted tries

Four lengths and three graft labels encode a rooted tree built by successively
attaching fresh path tails. The labels range only over the previous vertices.
Two extra edges will join marked targets (1,2) and (3,4). The parameter space
has a fixed polynomial cardinality in the radius.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000

namespace LocalLaw

local instance fourPathDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The four fresh-tail lengths, each bounded by the original radius. -/
abbrev FourPathLengths (R : ℕ) := Fin 4 → Fin (R + 1)

def fourTailLength {R : ℕ} (lengths : FourPathLengths R) : ℕ → ℕ
  | 0 => (lengths 0).val
  | 1 => (lengths 1).val
  | 2 => (lengths 2).val
  | 3 => (lengths 3).val
  | _ + 4 => 0

def fourStageSize {R : ℕ} (lengths : FourPathLengths R) : ℕ → ℕ
  | 0 => 1
  | n + 1 => fourStageSize lengths n + fourTailLength lengths n

theorem fourTailLength_le {R : ℕ} (lengths : FourPathLengths R) (n : ℕ) :
    fourTailLength lengths n ≤ R := by
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> simp only [fourTailLength] <;> omega
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
    have hn : n = k + 4 := by omega
    clear hk
    subst n
    simp only [fourTailLength, Nat.zero_le]

theorem fourStageSize_positive {R : ℕ} (lengths : FourPathLengths R) (n : ℕ) :
    0 < fourStageSize lengths n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih => exact lt_of_lt_of_le ih (Nat.le_add_right _ _)

theorem fourStageSize_bound {R : ℕ} (lengths : FourPathLengths R) (n : ℕ) :
    fourStageSize lengths n ≤ 1 + n * R := by
  induction n with
  | zero => simp [fourStageSize]
  | succ n ih =>
    have ht := fourTailLength_le lengths n
    simp only [fourStageSize]
    nlinarith

theorem fourStageSize_mono {R : ℕ} (lengths : FourPathLengths R) :
    Monotone (fourStageSize lengths) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Nat.le_add_right _ _

/-- Each of the last three tails grafts at an already existing vertex.
The first tail has only the initial root as a possible graft vertex. -/
def FourPathGrafts {R : ℕ} (lengths : FourPathLengths R) :=
  (j : Fin 3) → Fin (fourStageSize lengths (j.val + 1))

instance fourPathGraftsFintype {R : ℕ} (lengths : FourPathLengths R) :
    Fintype (FourPathGrafts lengths) := by
  unfold FourPathGrafts
  infer_instance

def FourPathParameters (R : ℕ) := Σ lengths : FourPathLengths R, FourPathGrafts lengths

instance fourPathParametersFintype (R : ℕ) : Fintype (FourPathParameters R) := by
  unfold FourPathParameters
  infer_instance

theorem fourPathGrafts_card_bound {R : ℕ} (lengths : FourPathLengths R) :
    Fintype.card (FourPathGrafts lengths) ≤ (4 * R + 2) ^ 3 := by
  change Fintype.card ((j : Fin 3) → Fin (fourStageSize lengths (j.val + 1))) ≤ _
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  calc
    _ ≤ ∏ _j : Fin 3, (4 * R + 2) := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro j _
      have hs := fourStageSize_bound lengths (j.val + 1)
      have hj := j.isLt
      nlinarith
    _ = _ := by simp

/-- The actual dependent graft parameter type has polynomial cardinality. -/
theorem fourPathParameters_card_bound (R : ℕ) :
    Nat.card (FourPathParameters R) ≤ (R + 1) ^ 4 * (4 * R + 2) ^ 3 := by
  rw [Nat.card_eq_fintype_card]
  change Fintype.card (Σ lengths : FourPathLengths R, FourPathGrafts lengths) ≤ _
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _lengths : FourPathLengths R, (4 * R + 2) ^ 3 :=
      Finset.sum_le_sum (fun lengths _ => fourPathGrafts_card_bound lengths)
    _ = _ := by simp

/-- The first graft is the root; subsequent grafts use the three labels. -/
def fourStageGraft {R : ℕ} (P : FourPathParameters R) (i : Fin 4) :
    Fin (fourStageSize P.1 i.val) :=
  Fin.cases (motive := fun j : Fin 4 => Fin (fourStageSize P.1 j.val))
    ⟨0, Nat.zero_lt_one⟩ (fun j => P.2 j) i

theorem fourStageGraft_zero {R : ℕ} (P : FourPathParameters R) :
    fourStageGraft P 0 = (⟨0, Nat.zero_lt_one⟩ : Fin 1) := rfl

theorem fourStageGraft_succ {R : ℕ} (P : FourPathParameters R) (j : Fin 3) :
    fourStageGraft P j.succ = P.2 j := rfl

/-- Assemble the four sequential graft choices without changing their labels. -/
def fourPathParametersMk {R : ℕ} (l0 l1 l2 l3 : Fin (R + 1))
    (g1 : Fin (1 + l0.val)) (g2 : Fin ((1 + l0.val) + l1.val))
    (g3 : Fin (((1 + l0.val) + l1.val) + l2.val)) : FourPathParameters R := by
  refine ⟨![l0, l1, l2, l3], ?_⟩
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa [fourStageSize, fourTailLength] using g1
  · refine Fin.cases ?_ (fun j => ?_) j
    · simpa [fourStageSize, fourTailLength] using g2
    · refine Fin.cases ?_ (fun j => j.elim0) j
      simpa [fourStageSize, fourTailLength] using g3

@[simp] theorem fourPathParametersMk_length {R : ℕ} (l0 l1 l2 l3 : Fin (R + 1))
    (g1 : Fin (1 + l0.val)) (g2 : Fin ((1 + l0.val) + l1.val))
    (g3 : Fin (((1 + l0.val) + l1.val) + l2.val)) :
    (fourPathParametersMk l0 l1 l2 l3 g1 g2 g3).1 = ![l0, l1, l2, l3] := rfl

theorem fourStageSize_mk_four {R : ℕ} (l0 l1 l2 l3 : Fin (R + 1))
    (g1 : Fin (1 + l0.val)) (g2 : Fin ((1 + l0.val) + l1.val))
    (g3 : Fin (((1 + l0.val) + l1.val) + l2.val)) :
    fourStageSize (fourPathParametersMk l0 l1 l2 l3 g1 g2 g3).1 4 =
      (((1 + l0.val) + l1.val) + l2.val) + l3.val := by
  simp [fourStageSize, fourTailLength]

/-- The new endpoint and the old graft are the only possible new exceptions
to degree two after attaching a path. -/
def pathGraftSpecial {n : ℕ} (bad : Finset (Fin n)) (v : Fin n) (ell : ℕ) : Finset (Fin (n + ell)) :=
  ((insert v bad).map (Fin.castAddEmb ell)) ∪ {pathGraftEndpoint v ell}

theorem pathGraftSpecial_old_mem {n : ℕ} (bad : Finset (Fin n)) (v : Fin n) (ell : ℕ)
    (x : Fin n) (hx : x ∈ bad) : Fin.castAdd ell x ∈ pathGraftSpecial bad v ell :=
  Finset.mem_union_left _ (Finset.mem_map.mpr ⟨x, Finset.mem_insert_of_mem hx, rfl⟩)

theorem pathGraftSpecial_graft_mem {n : ℕ} (bad : Finset (Fin n)) (v : Fin n) (ell : ℕ) :
    Fin.castAdd ell v ∈ pathGraftSpecial bad v ell :=
  Finset.mem_union_left _ (Finset.mem_map.mpr ⟨v, Finset.mem_insert_self _ _, rfl⟩)

theorem pathGraftSpecial_endpoint_mem {n : ℕ} (bad : Finset (Fin n)) (v : Fin n) (ell : ℕ) :
    pathGraftEndpoint v ell ∈ pathGraftSpecial bad v ell := Finset.mem_union_right _ (Finset.mem_singleton_self _)

theorem pathGraftSpecial_card {n : ℕ} (bad : Finset (Fin n)) (v : Fin n) (ell : ℕ) :
    (pathGraftSpecial bad v ell).card ≤ bad.card + 2 := by
  have h := Finset.card_union_le ((insert v bad).map (Fin.castAddEmb ell)) {pathGraftEndpoint v ell}
  have hi := Finset.card_insert_le v bad
  simp only [Finset.card_map, Finset.card_singleton] at h
  exact h.trans (by omega)

theorem pathGraftSpecial_card_of_mem {n : ℕ} (bad : Finset (Fin n)) (v : Fin n) (ell : ℕ)
    (hv : v ∈ bad) : (pathGraftSpecial bad v ell).card ≤ bad.card + 1 := by
  have h := Finset.card_union_le ((insert v bad).map (Fin.castAddEmb ell)) {pathGraftEndpoint v ell}
  simpa only [pathGraftSpecial, Finset.card_map, Finset.card_singleton, Finset.insert_eq_of_mem hv] using h

theorem pathGraft_degree_two_off_special {n : ℕ} (G : SimpleGraph (Fin n))
    (bad : Finset (Fin n)) (v : Fin n) (ell : ℕ)
    (hdegree : ∀ x, x ∉ bad → G.degree x = 2) :
    ∀ x, x ∉ pathGraftSpecial bad v ell → (pathGraftGraph G v ell).degree x = 2 := by
  intro x
  refine Fin.addCases (fun i hi => ?_) (fun j hj => ?_) x
  · have hibad : i ∉ bad := fun h => hi (pathGraftSpecial_old_mem bad v ell i h)
    have hiv : i ≠ v := by
      intro h
      subst i
      exact hi (pathGraftSpecial_graft_mem bad v ell)
    have hold := hdegree i hibad
    have hnew := pathGraftGraph_degree_old_of_ne G v ell i hiv
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hold hnew ⊢
    exact hnew.trans hold
  · have hne : Fin.natAdd n j ≠ pathGraftEndpoint v ell := by
      intro h
      apply hj
      rw [h]
      exact pathGraftSpecial_endpoint_mem bad v ell
    have hnew := pathGraftGraph_degree_fresh_of_ne_endpoint G v ell j hne
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hnew ⊢
    exact hnew

/-- The canonical tree after n of the four fresh-tail grafts. -/
def fourTrieGraph {R : ℕ} (P : FourPathParameters R) :
    (n : ℕ) → n ≤ 4 → SimpleGraph (Fin (fourStageSize P.1 n))
  | 0, _ => ⊥
  | n + 1, hn => pathGraftGraph (fourTrieGraph P n (by omega))
      (fourStageGraft P ⟨n, by omega⟩) (fourTailLength P.1 n)

def fourTrieSpecial {R : ℕ} (P : FourPathParameters R) :
    (n : ℕ) → n ≤ 4 → Finset (Fin (fourStageSize P.1 n))
  | 0, _ => {⟨0, Nat.zero_lt_one⟩}
  | n + 1, hn => pathGraftSpecial (fourTrieSpecial P n (by omega))
      (fourStageGraft P ⟨n, by omega⟩) (fourTailLength P.1 n)

theorem fourTrieGraph_isTree {R : ℕ} (P : FourPathParameters R) (n : ℕ) (hn : n ≤ 4) :
    (fourTrieGraph P n hn).IsTree := by
  revert hn
  induction n with
  | zero =>
    intro hn
    have hconn : (⊥ : SimpleGraph (Fin 1)).Connected := by
      apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
      refine ⟨0, ?_⟩
      intro v
      have hv : v = 0 := Subsingleton.elim _ _
      subst v
      exact SimpleGraph.Reachable.rfl
    exact ⟨hconn, SimpleGraph.isAcyclic_bot⟩
  | succ n ih =>
    intro hn
    exact pathGraftGraph_isTree _ _ _ (ih (by omega))

theorem fourTrie_degree_two_off {R : ℕ} (P : FourPathParameters R) (n : ℕ) (hn : n ≤ 4) :
    ∀ x, x ∉ fourTrieSpecial P n hn → (fourTrieGraph P n hn).degree x = 2 := by
  revert hn
  induction n with
  | zero =>
    intro hn x hx
    have hmem : x ∈ fourTrieSpecial P 0 hn := by
      have hx0 : x = ⟨0, Nat.zero_lt_one⟩ := by
        apply Fin.ext
        change x.val = 0
        have hi : x.val < 1 := x.isLt
        omega
      simp only [fourTrieSpecial, Finset.mem_singleton, hx0]
    exact (hx hmem).elim
  | succ n ih =>
    intro hn
    exact pathGraft_degree_two_off_special _ _ _ _ (ih (by omega))

theorem fourTrieSpecial_card_step {R : ℕ} (P : FourPathParameters R) (n : ℕ) (hn : n < 4) :
    (fourTrieSpecial P (n + 1) (by omega)).card ≤ (fourTrieSpecial P n (by omega)).card + 2 :=
  pathGraftSpecial_card _ _ _

theorem fourTrieSpecial_card_four {R : ℕ} (P : FourPathParameters R) :
    (fourTrieSpecial P 4 le_rfl).card ≤ 8 := by
  have hg : fourStageGraft P 0 ∈ fourTrieSpecial P 0 (by omega) := by
    simp only [fourTrieSpecial, fourStageGraft_zero, Finset.mem_singleton]
  have h₁ := pathGraftSpecial_card_of_mem (fourTrieSpecial P 0 (by omega))
    (fourStageGraft P 0) (fourTailLength P.1 0) hg
  change (fourTrieSpecial P 1 (by omega)).card ≤ (fourTrieSpecial P 0 (by omega)).card + 1 at h₁
  have h₂ := fourTrieSpecial_card_step P 1 (by omega)
  have h₃ := fourTrieSpecial_card_step P 2 (by omega)
  have h₄ := fourTrieSpecial_card_step P 3 (by omega)
  change (fourTrieSpecial P 2 (by omega)).card ≤ (fourTrieSpecial P 1 (by omega)).card + 2 at h₂
  change (fourTrieSpecial P 3 (by omega)).card ≤ (fourTrieSpecial P 2 (by omega)).card + 2 at h₃
  change (fourTrieSpecial P 4 le_rfl).card ≤ (fourTrieSpecial P 3 (by omega)).card + 2 at h₄
  have hzero : (fourTrieSpecial P 0 (by omega)).card = 1 := Finset.card_singleton _
  omega

def fourStageEndpoint {R : ℕ} (P : FourPathParameters R) (i : Fin 4) :
    Fin (fourStageSize P.1 (i.val + 1)) :=
  pathGraftEndpoint (fourStageGraft P i) (fourTailLength P.1 i.val)

def fourMarkedTarget {R : ℕ} (P : FourPathParameters R) : Fin 4 → Fin (fourStageSize P.1 4) :=
  ![Fin.castAdd (fourTailLength P.1 3) (Fin.castAdd (fourTailLength P.1 2)
      (Fin.castAdd (fourTailLength P.1 1) (fourStageEndpoint P 0))),
    Fin.castAdd (fourTailLength P.1 3) (Fin.castAdd (fourTailLength P.1 2) (fourStageEndpoint P 1)),
    Fin.castAdd (fourTailLength P.1 3) (fourStageEndpoint P 2), fourStageEndpoint P 3]

theorem fourTrieSpecial_old_mem {R : ℕ} (P : FourPathParameters R) (n : ℕ) (hn : n < 4)
    (x : Fin (fourStageSize P.1 n)) (hx : x ∈ fourTrieSpecial P n (by omega)) :
    Fin.castAdd (fourTailLength P.1 n) x ∈ fourTrieSpecial P (n + 1) (by omega) :=
  pathGraftSpecial_old_mem _ _ _ _ hx

theorem fourStageEndpoint_mem {R : ℕ} (P : FourPathParameters R) (i : Fin 4) :
    fourStageEndpoint P i ∈ fourTrieSpecial P (i.val + 1) (by have h := i.isLt; omega) :=
  pathGraftSpecial_endpoint_mem _ _ _

theorem fourMarkedTarget_mem {R : ℕ} (P : FourPathParameters R) (i : Fin 4) :
    fourMarkedTarget P i ∈ fourTrieSpecial P 4 le_rfl := by
  fin_cases i
  · exact fourTrieSpecial_old_mem P 3 (by omega) _
      (fourTrieSpecial_old_mem P 2 (by omega) _
        (fourTrieSpecial_old_mem P 1 (by omega) _ (fourStageEndpoint_mem P 0)))
  · exact fourTrieSpecial_old_mem P 3 (by omega) _
      (fourTrieSpecial_old_mem P 2 (by omega) _ (fourStageEndpoint_mem P 1))
  · exact fourTrieSpecial_old_mem P 3 (by omega) _ (fourStageEndpoint_mem P 2)
  · exact fourStageEndpoint_mem P 3

/-- Add the two prescribed endpoint pairs to the canonical four-tail tree. -/
def fourPathBicyclicGraph {R : ℕ} (P : FourPathParameters R) : SimpleGraph (Fin (fourStageSize P.1 4)) :=
  (fourTrieGraph P 4 le_rfl ⊔ SimpleGraph.edge (fourMarkedTarget P 0) (fourMarkedTarget P 1)) ⊔
    SimpleGraph.edge (fourMarkedTarget P 2) (fourMarkedTarget P 3)

theorem fourPathBicyclicGraph_connected {R : ℕ} (P : FourPathParameters R) :
    (fourPathBicyclicGraph P).Connected :=
  (fourTrieGraph_isTree P 4 le_rfl).isConnected.mono (le_trans le_sup_left le_sup_left)

theorem fourPathBicyclicGraph_degree_two_off {R : ℕ} (P : FourPathParameters R) :
    ∀ x, x ∉ fourTrieSpecial P 4 le_rfl → (fourPathBicyclicGraph P).degree x = 2 := by
  intro x hx
  have hne : ∀ i : Fin 4, x ≠ fourMarkedTarget P i := by
    intro i h
    exact hx (h ▸ fourMarkedTarget_mem P i)
  have h₁ := degree_sup_new_edge_away (fourTrieGraph P 4 le_rfl)
    (fourMarkedTarget P 0) (fourMarkedTarget P 1) x (hne 0) (hne 1)
  have h₂ := degree_sup_new_edge_away (fourTrieGraph P 4 le_rfl ⊔
      SimpleGraph.edge (fourMarkedTarget P 0) (fourMarkedTarget P 1))
    (fourMarkedTarget P 2) (fourMarkedTarget P 3) x (hne 2) (hne 3)
  have ht := fourTrie_degree_two_off P 4 le_rfl x hx
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h₁ h₂ ht ⊢
  exact h₂.trans (h₁.trans ht)

end LocalLaw
