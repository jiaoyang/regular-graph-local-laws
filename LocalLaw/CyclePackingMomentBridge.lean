import LocalLaw.ShortCyclePatterns
import LocalLaw.PackingCounting
import LocalLaw.DisjointCycleMoments
import LocalLaw.BallCycleWitness
import LocalLaw.SharpBallCounting

/-!
# Distinct cycle packings are counted by the actual packed-cycle moment

Support overlap gives the conflict relation on distinct edge patterns.
Canonical cycle representations encode every separated tuple as one concrete
joint cycle embedding. Length fibers keep the encoding's vertex type fixed;
each component edge graph is recovered from its component embedding.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000

namespace LocalLaw

local instance cyclePackingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {N : ℕ}

def shortCycleOverlap {G : SimpleGraph (Fin N)} {U : ℕ}
    (A B : ShortCyclePattern G U) : Prop := ¬Disjoint A.support B.support

/-- A pattern conflicts only with patterns through one of its support vertices. -/
theorem shortCycleOverlap_card_bound (G : SimpleGraph (Fin N)) (U R ω : ℕ)
    (hU : U ≤ 2 * R + 1) (hbudget : ∀ v, graphBallExcess G v R ≤ ω)
    (A : ShortCyclePattern G U) :
    Nat.card {B : ShortCyclePattern G U // shortCycleOverlap A B} ≤ U * 2 ^ ω := by
  let bad : Finset (ShortCyclePattern G U) := A.support.biUnion
    (fun v => Finset.univ.filter (fun B => v ∈ B.support))
  have heq : Finset.univ.filter (shortCycleOverlap A) = bad := by
    ext B
    simp only [bad, shortCycleOverlap, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Finset.not_disjoint_iff]
  have hcard : ∀ v, (Finset.univ.filter (fun B : ShortCyclePattern G U => v ∈ B.support)).card ≤ 2 ^ ω := by
    intro v
    simpa only [ShortCycleThrough, Nat.card_eq_fintype_card, Fintype.card_subtype] using
      shortCycleThrough_card_le G U R ω hU v (hbudget v)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, heq]
  calc
    bad.card ≤ ∑ v ∈ A.support,
        (Finset.univ.filter (fun B : ShortCyclePattern G U => v ∈ B.support)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ A.support, 2 ^ ω := Finset.sum_le_sum (fun v _ => hcard v)
    _ = A.support.card * 2 ^ ω := by simp
    _ ≤ U * 2 ^ ω := Nat.mul_le_mul_right _ A.support_card_le

namespace ShortCyclePattern

variable {G : SimpleGraph (Fin N)} {U : ℕ}

/-- Transport the chosen embedding to an equal, externally fixed length. -/
def embeddingAt (C : ShortCyclePattern G U) (ell : ℕ) (h : C.length = ell) : Fin ell ↪ Fin N :=
  h ▸ C.embedding

theorem embeddingAt_pattern (C : ShortCyclePattern G U) (ell : ℕ) (h : C.length = ell) :
    cyclePattern (C.embeddingAt ell h) = C.graph := by
  cases h
  exact C.graph_eq.symm

theorem embeddingAt_mem_support (C : ShortCyclePattern G U) (ell : ℕ) (h : C.length = ell)
    (i : Fin ell) : C.embeddingAt ell h i ∈ C.support := by
  cases h
  exact C.embedding_mem_support i

end ShortCyclePattern

section PackingEncoding

variable (G : SimpleGraph (Fin N)) (U q : ℕ)

abbrev ShortCyclePacking := SeparatedTuple (shortCycleOverlap (G := G) (U := U)) q

def shortCycleTupleLengths (t : ShortCyclePacking G U q) : Fin q → Fin (U + 1) :=
  fun i => ⟨(t.val i).length, Nat.lt_succ_of_le (t.val i).length_upper⟩

def ShortCycleLengthFiber (lengths : Fin q → Fin (U + 1)) :=
  {t : ShortCyclePacking G U q // shortCycleTupleLengths G U q t = lengths}

instance shortCycleLengthFiberFintype (lengths : Fin q → Fin (U + 1)) :
    Fintype (ShortCycleLengthFiber G U q lengths) := by
  unfold ShortCycleLengthFiber
  infer_instance

theorem shortCyclePacking_disjoint (t : ShortCyclePacking G U q) (i j : Fin q)
    (hij : i ≠ j) : Disjoint (t.val i).support (t.val j).support := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact not_not.mp (t.property i j hlt)
  · exact (not_not.mp (t.property j i hgt)).symm

theorem lengthFiber_component_length (lengths : Fin q → Fin (U + 1))
    (t : ShortCycleLengthFiber G U q lengths) (i : Fin q) :
    (t.val.val i).length = (lengths i).val :=
  congrArg (fun f : Fin q → Fin (U + 1) => (f i).val) t.property

def lengthFiber_component (lengths : Fin q → Fin (U + 1))
    (t : ShortCycleLengthFiber G U q lengths) (i : Fin q) : Fin (lengths i).val ↪ Fin N :=
  (t.val.val i).embeddingAt _ (lengthFiber_component_length G U q lengths t i)

theorem lengthFiber_component_mem (lengths : Fin q → Fin (U + 1))
    (t : ShortCycleLengthFiber G U q lengths) (i : Fin q) (j : Fin (lengths i).val) :
    lengthFiber_component G U q lengths t i j ∈ (t.val.val i).support :=
  (t.val.val i).embeddingAt_mem_support _ (lengthFiber_component_length G U q lengths t i) j

theorem lengthFiber_component_pattern (lengths : Fin q → Fin (U + 1))
    (t : ShortCycleLengthFiber G U q lengths) (i : Fin q) :
    cyclePattern (lengthFiber_component G U q lengths t i) = (t.val.val i).graph :=
  (t.val.val i).embeddingAt_pattern _ (lengthFiber_component_length G U q lengths t i)

def lengthFiber_jointEmbedding (lengths : Fin q → Fin (U + 1))
    (t : ShortCycleLengthFiber G U q lengths) : (Σ i : Fin q, Fin (lengths i).val) ↪ Fin N where
  toFun p := lengthFiber_component G U q lengths t p.1 p.2
  inj' := by
    rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    change lengthFiber_component G U q lengths t i x =
      lengthFiber_component G U q lengths t j y at hxy
    by_cases hij : i = j
    · subst j
      have h := (lengthFiber_component G U q lengths t i).injective hxy
      cases h
      rfl
    · have hd := shortCyclePacking_disjoint G U q t.val i j hij
      have hx := lengthFiber_component_mem G U q lengths t i x
      have hy := lengthFiber_component_mem G U q lengths t j y
      rw [← hxy] at hy
      exact (Finset.disjoint_left.mp hd hx hy).elim

theorem lengthFiber_joint_preserves (lengths : Fin q → Fin (U + 1))
    (t : ShortCycleLengthFiber G U q lengths) :
    ∀ a b, (cycleFamilyGraph (fun i => (lengths i).val)).Adj a b →
      G.Adj (lengthFiber_jointEmbedding G U q lengths t a)
        (lengthFiber_jointEmbedding G U q lengths t b) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ ⟨hij, hxy⟩
  cases hij
  have hsub : cyclePattern (lengthFiber_component G U q lengths t i) ≤ G := by
    rw [lengthFiber_component_pattern]
    exact (t.val.val i).le_graph
  exact hsub (SimpleGraph.map_adj_apply.mpr hxy)

def lengthFiber_finiteEmbedding (lengths : Fin q → Fin (U + 1))
    (t : ShortCycleLengthFiber G U q lengths) :
    Fin (Fintype.card (Σ i : Fin q, Fin (lengths i).val)) ↪ Fin N :=
  (Fintype.equivFin (Σ i : Fin q, Fin (lengths i).val)).symm.toEmbedding.trans
    (lengthFiber_jointEmbedding G U q lengths t)

theorem lengthFiber_finite_preserves (lengths : Fin q → Fin (U + 1))
    (t : ShortCycleLengthFiber G U q lengths) :
    (finiteCycleFamilyPattern (fun i => (lengths i).val)).map
      (lengthFiber_finiteEmbedding G U q lengths t) ≤ G := by
  apply (mappedPattern_le_iff _ _ _).mpr
  intro x y hxy
  let E := Fintype.equivFin (Σ i : Fin q, Fin (lengths i).val)
  obtain ⟨a, b, hab, ha, hb⟩ :=
    (SimpleGraph.map_adj E.toEmbedding (cycleFamilyGraph (fun i => (lengths i).val)) x y).mp hxy
  have h := lengthFiber_joint_preserves G U q lengths t a b hab
  have hEa : E.symm x = a := by rw [← ha]; exact E.symm_apply_apply a
  have hEb : E.symm y = b := by rw [← hb]; exact E.symm_apply_apply b
  change G.Adj (lengthFiber_jointEmbedding G U q lengths t (E.symm x))
    (lengthFiber_jointEmbedding G U q lengths t (E.symm y))
  rw [hEa, hEb]
  exact h

theorem lengthFiber_finite_apply (lengths : Fin q → Fin (U + 1))
    (t : ShortCycleLengthFiber G U q lengths) (a : Σ i : Fin q, Fin (lengths i).val) :
    lengthFiber_finiteEmbedding G U q lengths t
      (Fintype.equivFin (Σ i : Fin q, Fin (lengths i).val) a) =
        lengthFiber_jointEmbedding G U q lengths t a := by
  simp only [lengthFiber_finiteEmbedding, Function.Embedding.trans_apply,
    Equiv.toEmbedding_apply, Equiv.symm_apply_apply]

def lengthFiber_encoding (lengths : Fin q → Fin (U + 1))
    (t : ShortCycleLengthFiber G U q lengths) :
    {f : Fin (Fintype.card (Σ i : Fin q, Fin (lengths i).val)) ↪ Fin N //
      (finiteCycleFamilyPattern (fun i => (lengths i).val)).map f ≤ G} :=
  ⟨lengthFiber_finiteEmbedding G U q lengths t, lengthFiber_finite_preserves G U q lengths t⟩

/-- The encoded component embedding recovers its entire edge pattern. -/
theorem lengthFiber_encoding_injective (lengths : Fin q → Fin (U + 1)) :
    Function.Injective (lengthFiber_encoding G U q lengths) := by
  intro A B heq
  have hfinite : lengthFiber_finiteEmbedding G U q lengths A =
      lengthFiber_finiteEmbedding G U q lengths B := congrArg Subtype.val heq
  have hcomponents : ∀ i, lengthFiber_component G U q lengths A i =
      lengthFiber_component G U q lengths B i := by
    intro i
    apply Function.Embedding.ext
    intro j
    have h := congrArg (fun f : Fin (Fintype.card (Σ i : Fin q, Fin (lengths i).val)) ↪ Fin N =>
      f (Fintype.equivFin (Σ i : Fin q, Fin (lengths i).val) ⟨i, j⟩)) hfinite
    simpa only [lengthFiber_finite_apply] using h
  apply Subtype.ext
  apply Subtype.ext
  funext i
  apply ShortCyclePattern.graph_injective
  calc
    (A.val.val i).graph = cyclePattern (lengthFiber_component G U q lengths A i) :=
      (lengthFiber_component_pattern G U q lengths A i).symm
    _ = cyclePattern (lengthFiber_component G U q lengths B i) :=
      congrArg cyclePattern (hcomponents i)
    _ = (B.val.val i).graph := lengthFiber_component_pattern G U q lengths B i

theorem shortCycleLengthFiber_card_le (lengths : Fin q → Fin (U + 1)) :
    Nat.card (ShortCycleLengthFiber G U q lengths) ≤
      if ∀ i, 3 ≤ (lengths i).val then
        labelledPatternCount (finiteCycleFamilyPattern (fun i => (lengths i).val)) G else 0 := by
  by_cases hvalid : ∀ i, 3 ≤ (lengths i).val
  · rw [if_pos hvalid]
    have hcard := Nat.card_le_card_of_injective (lengthFiber_encoding G U q lengths)
      (lengthFiber_encoding_injective G U q lengths)
    have htarget : Nat.card {f : Fin (Fintype.card (Σ i : Fin q, Fin (lengths i).val)) ↪ Fin N //
        (finiteCycleFamilyPattern (fun i => (lengths i).val)).map f ≤ G} =
          labelledPatternCount (finiteCycleFamilyPattern (fun i => (lengths i).val)) G := by
      simp only [labelledPatternCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact hcard.trans_eq htarget
  · rw [if_neg hvalid]
    letI : IsEmpty (ShortCycleLengthFiber G U q lengths) := ⟨fun t => hvalid (by
      intro i
      have hi := (t.val.val i).length_lower
      rw [lengthFiber_component_length G U q lengths t i] at hi
      exact hi)⟩
    simp

/-- Every actual separated pattern tuple contributes a distinct joint labelled
cycle embedding to the actual packed-cycle observable. -/
theorem shortCyclePacking_card_le_moment :
    Nat.card (ShortCyclePacking G U q) ≤ RegularGraph.packedCycleMoment q U G := by
  have hpartition : Nat.card (ShortCyclePacking G U q) =
      ∑ lengths : Fin q → Fin (U + 1), Nat.card (ShortCycleLengthFiber G U q lengths) := by
    calc
      _ = Nat.card (Σ lengths : Fin q → Fin (U + 1), ShortCycleLengthFiber G U q lengths) :=
        (Nat.card_congr (Equiv.sigmaFiberEquiv (shortCycleTupleLengths G U q))).symm
      _ = _ := Nat.card_sigma
  rw [hpartition]
  unfold RegularGraph.packedCycleMoment
  exact Finset.sum_le_sum (fun lengths _ => shortCycleLengthFiber_card_le G U q lengths)

end PackingEncoding

theorem packedCycleMoment_lower (G : SimpleGraph (Fin N)) (U R ω q : ℕ)
    (hU : U ≤ 2 * R + 1) (hbudget : ∀ v, graphBallExcess G v R ≤ ω) :
    (Nat.card (ShortCyclePattern G U) - q * (U * 2 ^ ω)) ^ q ≤
      RegularGraph.packedCycleMoment q U G := by
  have hsep := separatedTuple_card_lower (shortCycleOverlap (G := G) (U := U))
    (U * 2 ^ ω) q (shortCycleOverlap_card_bound G U R ω hU hbudget)
  have hsep' : (Nat.card (ShortCyclePattern G U) - q * (U * 2 ^ ω)) ^ q ≤
      Nat.card (ShortCyclePacking G U q) := by
    simpa only [← Nat.card_eq_fintype_card] using hsep
  exact hsep'.trans (shortCyclePacking_card_le_moment G U q)

theorem packedCycleMoment_lower_half (G : SimpleGraph (Fin N)) (U R ω q : ℕ)
    (hU : U ≤ 2 * R + 1) (hbudget : ∀ v, graphBallExcess G v R ≤ ω)
    (hsize : 2 * q * (U * 2 ^ ω) ≤ Nat.card (ShortCyclePattern G U)) :
    ((Nat.card (ShortCyclePattern G U) : ℝ) / 2) ^ q ≤
      (RegularGraph.packedCycleMoment q U G : ℝ) := by
  have hsep := separatedTuple_card_half (shortCycleOverlap (G := G) (U := U))
    (U * 2 ^ ω) q (shortCycleOverlap_card_bound G U R ω hU hbudget)
    (by simpa only [Nat.card_eq_fintype_card] using hsize)
  have hsep' : ((Nat.card (ShortCyclePattern G U) : ℝ) / 2) ^ q ≤
      (Nat.card (ShortCyclePacking G U q) : ℝ) := by
    simpa only [← Nat.card_eq_fintype_card] using hsep
  apply hsep'.trans
  exact_mod_cast shortCyclePacking_card_le_moment G U q

/-- Cover bad centers by radius-R neighborhoods of the supports of distinct
short-cycle edge patterns. No labelled orientation multiplicity appears. -/
theorem nonTreeCenters_card_le_shortPatterns (G : SimpleGraph (Fin N)) (d R U : ℕ)
    (hd : 3 ≤ d) (hdegree : ∀ v, G.degree v ≤ d) (hU : 2 * R + 1 ≤ U) :
    (nonTreeCenters G R).card ≤ Nat.card (ShortCyclePattern G U) * U *
      ((d + 1) * (d - 1) ^ R) := by
  let neighborhood : ShortCyclePattern G U → Finset (Fin N) :=
    fun C => (graphSetBall G (C.support : Set (Fin N)) R).toFinset
  have hcover : nonTreeCenters G R ⊆ Finset.univ.biUnion neighborhood := by
    intro o ho
    have hnotree := (nonTreeCenters_membership G R o).mp ho
    obtain ⟨ell, hell, hlen, f, hf, _, i, hi⟩ := nonTree_ball_cycle_pattern G o R hnotree
    let C : ShortCyclePattern G U := ShortCyclePattern.ofCycle hell (hlen.trans hU) f hf
    have hfi : f i ∈ C.support := by
      apply (C.mem_support_iff _).mpr
      change f i ∈ (cyclePattern f).support
      rw [cyclePattern_support_eq_range hell f]
      exact ⟨i, rfl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨C, Finset.mem_univ _, ?_⟩
    change o ∈ (graphSetBall G (C.support : Set (Fin N)) R).toFinset
    apply Set.mem_toFinset.mpr
    refine ⟨f i, hfi, ?_⟩
    rw [G.edist_comm]
    exact hi
  have hcard : ∀ C : ShortCyclePattern G U,
      (neighborhood C).card ≤ U * ((d + 1) * (d - 1) ^ R) := by
    intro C
    have hs := graphSetBall_card_sharp G (C.support : Set (Fin N)) d R hd hdegree
    have hroot : Nat.card (C.support : Set (Fin N)) = C.support.card := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_of_subtype C.support (by intro v; rfl)
    rw [hroot] at hs
    have hsmall := hs.trans (Nat.mul_le_mul_right _ C.support_card_le)
    simpa only [neighborhood, Set.toFinset_card, ← Nat.card_eq_fintype_card] using hsmall
  calc
    _ ≤ (Finset.univ.biUnion neighborhood).card := Finset.card_le_card hcover
    _ ≤ ∑ C : ShortCyclePattern G U, (neighborhood C).card := Finset.card_biUnion_le
    _ ≤ ∑ _C : ShortCyclePattern G U, U * ((d + 1) * (d - 1) ^ R) :=
      Finset.sum_le_sum (fun C _ => hcard C)
    _ = _ := by simp [Nat.card_eq_fintype_card, Nat.mul_assoc]

namespace RegularGraph

variable {d : ℕ}

theorem badCenters_card_le_pattern_count (g : RegularGraph N d) (R : ℕ) (hd : 3 ≤ d) :
    (nonTreeCenters g.graph R).card ≤ Nat.card (ShortCyclePattern g.graph (2 * R + 1)) *
      ((d + 1) * (2 * R + 1) * (d - 1) ^ R) := by
  have h := nonTreeCenters_card_le_shortPatterns g.graph d R (2 * R + 1) hd
    (fun v => (g.regular v).le) le_rfl
  simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

/-- The explicit numerical numerator dominates both the packing threshold
and the normalization of the actual packed-cycle expectation. -/
theorem cyclePacking_cover_factor_bounds (d R : ℕ) (hd : 3 ≤ d) :
    let U := 2 * R + 1
    let A := (d + 1) * U * (d - 1) ^ R
    let B := 2 * (d + 1) * (2 * R + 2) ^ 2 * (d - 1) ^ (3 * R + 1)
    0 < A ∧ 2 * U * A ≤ B ∧ 2 * A * (U + 1) * (d - 1) ^ U ≤ B := by
  let U := 2 * R + 1
  let k := d - 1
  let A := (d + 1) * U * k ^ R
  let B := 2 * (d + 1) * (2 * R + 2) ^ 2 * k ^ (3 * R + 1)
  change 0 < A ∧ 2 * U * A ≤ B ∧ 2 * A * (U + 1) * k ^ U ≤ B
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hA : 0 < A := by dsimp [A, U]; positivity
  have hB : B = 2 * (d + 1) * (U + 1) ^ 2 * k ^ (R + U) := by
    dsimp [B, U]
    rw [show 3 * R + 1 = R + (2 * R + 1) by omega]
  have hpoly : U * (U + 1) ≤ (U + 1) ^ 2 := by nlinarith
  have hinflation : 2 * A * (U + 1) * k ^ U ≤ B := by
    calc
      _ = (2 * (d + 1) * k ^ (R + U)) * (U * (U + 1)) := by
        dsimp [A]
        rw [pow_add]
        ring
      _ ≤ (2 * (d + 1) * k ^ (R + U)) * (U + 1) ^ 2 :=
        Nat.mul_le_mul_left _ hpoly
      _ = B := by rw [hB]; ring
  have hU : U ≤ (U + 1) * k ^ U := by
    have hp := Nat.mul_le_mul_left (U + 1) (Nat.one_le_pow U k hk)
    nlinarith
  refine ⟨hA, ?_, hinflation⟩
  calc
    _ = 2 * A * U := by ring
    _ ≤ 2 * A * ((U + 1) * k ^ U) := Nat.mul_le_mul_left _ hU
    _ = 2 * A * (U + 1) * k ^ U := by ring
    _ ≤ B := hinflation

/-- Finite actual strong tail on the bounded-excess event. The high moment
comes from joint disjoint-cycle embeddings; no independence is assumed. -/
theorem strong_badCenters_tail_bound (R ω q K : ℕ) (hd : 3 ≤ d) (hq : 1 ≤ q)
    (hK : q * (2 * R + 1) ≤ K) (hN : 0 < N)
    (hbudget : 2 * K * patternSwitchSlack d K ≤ N * d) (t : ℝ) (ht : 0 < t)
    (hthreshold : ((q * 2 ^ ω *
      (2 * (d + 1) * (2 * R + 2) ^ 2 * (d - 1) ^ (3 * R + 1)) : ℕ) : ℝ) ≤ t) :
    eventMass (weight (N := N) (d := d)) (fun g =>
      (∀ v, graphBallExcess g.graph v R ≤ ω) ∧
        t < ((nonTreeCenters g.graph R).card : ℝ)) ≤
      2 * ((((2 * (d + 1) * (2 * R + 2) ^ 2 * (d - 1) ^ (3 * R + 1) : ℕ) : ℝ) / t) ^ q) := by
  let U := 2 * R + 1
  let k := d - 1
  let A := (d + 1) * U * k ^ R
  let B := 2 * (d + 1) * (2 * R + 2) ^ 2 * k ^ (3 * R + 1)
  let E : ℝ := ((U + 1 : ℕ) : ℝ) * ((d - 1 : ℕ) : ℝ) ^ U
  let T : ℝ := (t / (2 * (A : ℝ))) ^ q
  have hb := cyclePacking_cover_factor_bounds d R hd
  change 0 < A ∧ 2 * U * A ≤ B ∧ 2 * A * (U + 1) * k ^ U ≤ B at hb
  have hAp : (0 : ℝ) < A := Nat.cast_pos.mpr hb.1
  have hTp : 0 < T := by dsimp [T]; positivity
  have hKpos : 1 ≤ K := by
    have hp : 0 < q * U := Nat.mul_pos (by omega) (by dsimp [U]; omega)
    exact hp.trans_le hK
  change ((q * 2 ^ ω * B : ℕ) : ℝ) ≤ t at hthreshold
  have hsmall : 2 * q * (U * 2 ^ ω) * A ≤ q * 2 ^ ω * B := by
    calc
      _ = (q * 2 ^ ω) * (2 * U * A) := by ring
      _ ≤ (q * 2 ^ ω) * B := Nat.mul_le_mul_left _ hb.2.1
      _ = _ := rfl
  have hsmallR : ((2 * q * (U * 2 ^ ω) : ℕ) : ℝ) * (A : ℝ) ≤ t := by
    have hs : ((2 * q * (U * 2 ^ ω) * A : ℕ) : ℝ) ≤ ((q * 2 ^ ω * B : ℕ) : ℝ) := by
      exact_mod_cast hsmall
    simpa only [Nat.cast_mul] using hs.trans hthreshold
  have hevent : ∀ g : RegularGraph N d,
      (∀ v, graphBallExcess g.graph v R ≤ ω) ∧
        t < ((nonTreeCenters g.graph R).card : ℝ) →
          T ≤ (packedCycleMoment q U g.graph : ℝ) := by
    intro g hg
    let S := Nat.card (ShortCyclePattern g.graph U)
    have hcover := g.badCenters_card_le_pattern_count R hd
    change (nonTreeCenters g.graph R).card ≤ S * A at hcover
    have hcoverR : ((nonTreeCenters g.graph R).card : ℝ) ≤ (S : ℝ) * (A : ℝ) := by
      exact_mod_cast hcover
    have hsizeR : ((2 * q * (U * 2 ^ ω) : ℕ) : ℝ) ≤ (S : ℝ) := by
      nlinarith [hg.2]
    have hsize : 2 * q * (U * 2 ^ ω) ≤ S := by exact_mod_cast hsizeR
    have hmoment := packedCycleMoment_lower_half g.graph U R ω q le_rfl hg.1 hsize
    have hSa : t ≤ (S : ℝ) * (A : ℝ) := hg.2.le.trans hcoverR
    have hbase : t / (2 * (A : ℝ)) ≤ (S : ℝ) / 2 := by
      calc
        _ ≤ ((S : ℝ) * (A : ℝ)) / (2 * (A : ℝ)) :=
          div_le_div_of_nonneg_right hSa (by positivity)
        _ = (S : ℝ) / 2 := by field_simp; ring
    exact (pow_le_pow_left₀ (by positivity) hbase q).trans hmoment
  have hmass := (eventMass_mono weight weight_nonnegative hevent).trans
    (packedCycleMoment_tail q U K hK hKpos hN (by omega) hbudget T hTp)
  apply hmass.trans
  change 2 * E ^ q / T ≤ 2 * ((B : ℝ) / t) ^ q
  have hinflation : 2 * (A : ℝ) * E ≤ (B : ℝ) := by
    have hn : ((2 * A * (U + 1) * k ^ U : ℕ) : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast hb.2.2
    simpa only [E, k, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, mul_assoc] using hn
  have hratio : E / (t / (2 * (A : ℝ))) = (2 * (A : ℝ) * E) / t := by
    field_simp
    ring
  dsimp only [T]
  rw [mul_div_assoc, ← div_pow, hratio]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply pow_le_pow_left₀ (by positivity)
  exact div_le_div_of_nonneg_right hinflation ht.le

end RegularGraph

end LocalLaw
