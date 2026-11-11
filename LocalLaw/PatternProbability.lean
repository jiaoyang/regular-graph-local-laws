import LocalLaw.PatternSwitchingProbability

/-!
# Sparse-pattern probabilities with falling-degree factors

An actual edge-deletion induction iterates the simple-switching mass recurrence.
The numerator retains the descending factorial of every required vertex degree,
including its automatic zero when a required degree exceeds d.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

namespace LocalLaw

local instance patternProbabilityDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Uniform finite weights have event mass at most one, also on an empty type. -/
theorem finiteUniform_eventMass_le_one {Ω : Type*} [Fintype Ω] (P : Ω → Prop) :
    eventMass (finiteUniformWeight Ω) P ≤ 1 := by
  classical
  rcases isEmpty_or_nonempty Ω with hempty | hnonempty
  · letI := hempty
    simp [eventMass]
  · letI := hnonempty
    calc
      _ ≤ ∑ ω : Ω, finiteUniformWeight Ω ω := by
        unfold eventMass
        apply Finset.sum_le_sum
        intro ω _
        split_ifs
        · exact le_rfl
        · exact finiteUniformWeight_nonneg ω
      _ = 1 := finiteUniformWeight_total

section EdgeInduction

variable {V : Type*} [Fintype V]

theorem graphEdgeCount_sup_new_edge (S : SimpleGraph V) (a b : V)
    (hab : a ≠ b) (hnew : ¬S.Adj a b) :
    graphEdgeCount (S ⊔ SimpleGraph.edge a b) = graphEdgeCount S + 1 := by
  have h := S.card_edgeFinset_sup_edge hnew hab
  simpa only [graphEdgeCount, SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card] using h

/-- Induction by adding a genuinely new edge; all finite simple graphs are covered. -/
theorem finite_graph_edge_induction (P : SimpleGraph V → Prop) (hbot : P ⊥)
    (hstep : ∀ (H : SimpleGraph V) (a b : V), a ≠ b → ¬H.Adj a b → P H →
      P (H ⊔ SimpleGraph.edge a b)) (S : SimpleGraph V) : P S := by
  have haux : ∀ n : ℕ, ∀ H : SimpleGraph V, graphEdgeCount H = n → P H := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro H hcard
      by_cases hH : H = ⊥
      · simpa only [hH] using hbot
      have hex : ∃ a b, H.Adj a b := by
        by_contra hnone
        apply hH
        ext a b
        simp only [SimpleGraph.bot_adj, iff_false]
        exact fun hab => hnone ⟨a, b, hab⟩
      obtain ⟨a, b, hab⟩ := hex
      let J := H \ SimpleGraph.edge a b
      have hnew : ¬J.Adj a b := by
        change ¬(H.Adj a b ∧ ¬(SimpleGraph.edge a b).Adj a b)
        have hedge : (SimpleGraph.edge a b).Adj a b :=
          (SimpleGraph.edge_adj a b a b).mpr ⟨Or.inl ⟨rfl, rfl⟩, hab.ne⟩
        tauto
      have hreconstruct : J ⊔ SimpleGraph.edge a b = H := by
        exact sdiff_sup_cancel (sup_eq_left.mp (H.sup_edge_of_adj hab))
      have hcount : graphEdgeCount J + 1 = n := by
        rw [← graphEdgeCount_sup_new_edge J a b hab.ne hnew, hreconstruct, hcard]
      have hsmall : graphEdgeCount J < n := by omega
      have hJ := ih (graphEdgeCount J) hsmall J rfl
      rw [← hreconstruct]
      exact hstep J a b hab.ne hnew hJ
  exact haux (graphEdgeCount S) S rfl

theorem neighborFinset_sup_new_edge_left (S : SimpleGraph V) (a b : V) (hab : a ≠ b) :
    (S ⊔ SimpleGraph.edge a b).neighborFinset a = insert b (S.neighborFinset a) := by
  ext v
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
    SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  have hloop : ¬S.Adj a a := S.loopless a
  aesop

theorem degree_sup_new_edge_left (S : SimpleGraph V) (a b : V)
    (hab : a ≠ b) (hnew : ¬S.Adj a b) :
    (S ⊔ SimpleGraph.edge a b).degree a = S.degree a + 1 := by
  change ((S ⊔ SimpleGraph.edge a b).neighborFinset a).card = _
  rw [neighborFinset_sup_new_edge_left S a b hab,
    Finset.card_insert_of_not_mem (by simpa only [SimpleGraph.mem_neighborFinset] using hnew)]
  rfl

theorem degree_sup_new_edge_right (S : SimpleGraph V) (a b : V)
    (hab : a ≠ b) (hnew : ¬S.Adj a b) :
    (S ⊔ SimpleGraph.edge a b).degree b = S.degree b + 1 := by
  have h := degree_sup_new_edge_left S b a hab.symm (fun h => hnew h.symm)
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at h ⊢
  simpa only [SimpleGraph.edge_comm a b] using h

theorem degree_sup_new_edge_away (S : SimpleGraph V) (a b v : V)
    (hva : v ≠ a) (hvb : v ≠ b) :
    (S ⊔ SimpleGraph.edge a b).degree v = S.degree v := by
  have hrow : (S ⊔ SimpleGraph.edge a b).neighborFinset v = S.neighborFinset v := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.sup_adj, SimpleGraph.edge_adj,
      hva, hvb, false_and, or_false]
  change ((S ⊔ SimpleGraph.edge a b).neighborFinset v).card = (S.neighborFinset v).card
  rw [hrow]

/-- Natural descending-factorial product, to keep all numerator algebra exact. -/
def patternDegreeProduct (d : ℕ) (S : SimpleGraph V) : ℕ :=
  ∏ v : V, d.descFactorial (S.degree v)

theorem patternDegreeProduct_bot (d : ℕ) :
    patternDegreeProduct d (⊥ : SimpleGraph V) = 1 := by
  have hcard : ∀ v : V, Nat.card ((⊥ : SimpleGraph V).neighborSet v) = 0 := by
    intro v
    change Nat.card (∅ : Set V) = 0
    simp
  unfold patternDegreeProduct
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    hcard, Nat.descFactorial_zero, Finset.prod_const_one]

theorem patternDegreeProduct_sup_new_edge (d : ℕ) (S : SimpleGraph V) (a b : V)
    (hab : a ≠ b) (hnew : ¬S.Adj a b) :
    patternDegreeProduct d (S ⊔ SimpleGraph.edge a b) =
      ((d - S.degree a) * (d - S.degree b)) * patternDegreeProduct d S := by
  have hpoint : ∀ v : V,
      d.descFactorial ((S ⊔ SimpleGraph.edge a b).degree v) =
        ((if v = a then d - S.degree a else 1) *
          (if v = b then d - S.degree b else 1)) * d.descFactorial (S.degree v) := by
    intro v
    by_cases hva : v = a
    · subst v
      rw [degree_sup_new_edge_left S a b hab hnew, Nat.descFactorial_succ]
      simp [hab]
    by_cases hvb : v = b
    · subst v
      rw [degree_sup_new_edge_right S a b hab hnew, Nat.descFactorial_succ]
      simp [hab.symm]
    rw [degree_sup_new_edge_away S a b v hva hvb]
    simp only [if_neg hva, if_neg hvb, one_mul]
  unfold patternDegreeProduct
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    at hpoint ⊢
  simp_rw [hpoint]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp

end EdgeInduction

namespace RegularGraph

variable {N degree : ℕ}

/-- Sparse-pattern probability with every falling-degree factor retained.
The single positive denominator budget works for every intermediate subpattern. -/
theorem pattern_probability_bound (S : SimpleGraph (Fin N)) (K L : ℕ)
    (hK : graphEdgeCount S ≤ K) (hL : 0 < L)
    (hbudget : L ≤ N * degree - patternSwitchSlack degree K) :
    eventMass (weight (N := N) (d := degree)) (fun g => S ≤ g.graph) ≤
      (patternDegreeProduct degree S : ℝ) / (L : ℝ) ^ graphEdgeCount S := by
  revert hK
  refine finite_graph_edge_induction
    (fun H : SimpleGraph (Fin N) => graphEdgeCount H ≤ K →
      eventMass (weight (N := N) (d := degree)) (fun g => H ≤ g.graph) ≤
        (patternDegreeProduct degree H : ℝ) / (L : ℝ) ^ graphEdgeCount H) ?_ ?_ S
  · intro _
    have hzero : graphEdgeCount (⊥ : SimpleGraph (Fin N)) = 0 := by simp [graphEdgeCount]
    simp only [bot_le, patternDegreeProduct_bot, hzero, Nat.cast_one, pow_zero, div_one]
    change eventMass (finiteUniformWeight (RegularGraph N degree)) (fun _ => True) ≤ 1
    exact finiteUniform_eventMass_le_one _
  · intro H a b hab hnew hIH hcap
    have hcount := graphEdgeCount_sup_new_edge H a b hab hnew
    have hHcap : graphEdgeCount H ≤ K := by omega
    have hslack : patternSwitchSlack degree (graphEdgeCount H) ≤
        patternSwitchSlack degree K := by
      unfold patternSwitchSlack
      omega
    have hbudgetH : L ≤ N * degree - patternSwitchSlack degree (graphEdgeCount H) :=
      hbudget.trans (Nat.sub_le_sub_left hslack (N * degree))
    have hext := pattern_extension_eventMass_bound H a b hab hnew L hL hbudgetH
    have hprod : (patternDegreeProduct degree (H ⊔ SimpleGraph.edge a b) : ℝ) =
        (((degree - H.degree a : ℕ) : ℝ) * ((degree - H.degree b : ℕ) : ℝ)) *
          (patternDegreeProduct degree H : ℝ) := by
      exact_mod_cast patternDegreeProduct_sup_new_edge degree H a b hab hnew
    calc
      _ ≤ (((degree - H.degree a : ℕ) : ℝ) * ((degree - H.degree b : ℕ) : ℝ) /
          (L : ℝ)) * eventMass (weight (N := N) (d := degree)) (fun g => H ≤ g.graph) := hext
      _ ≤ (((degree - H.degree a : ℕ) : ℝ) * ((degree - H.degree b : ℕ) : ℝ) /
          (L : ℝ)) * ((patternDegreeProduct degree H : ℝ) /
            (L : ℝ) ^ graphEdgeCount H) :=
        mul_le_mul_of_nonneg_left (hIH hHcap) (by positivity)
      _ = _ := by
        rw [hcount, hprod, pow_succ]
        rw [div_mul_div_comm, mul_comm (L : ℝ) ((L : ℝ) ^ graphEdgeCount H)]

/-- Equivalent real-product form of the sparse-pattern bound. -/
theorem pattern_probability_falling_degrees (S : SimpleGraph (Fin N)) (K L : ℕ)
    (hK : graphEdgeCount S ≤ K) (hL : 0 < L)
    (hbudget : L ≤ N * degree - patternSwitchSlack degree K) :
    eventMass (weight (N := N) (d := degree)) (fun g => S ≤ g.graph) ≤
      (∏ v : Fin N, (degree.descFactorial (S.degree v) : ℝ)) /
        (L : ℝ) ^ graphEdgeCount S := by
  simpa only [patternDegreeProduct, Nat.cast_prod] using
    pattern_probability_bound S K L hK hL hbudget

/-- Overfull required degrees give zero mass automatically in the product bound. -/
theorem pattern_probability_zero_of_degree (S : SimpleGraph (Fin N)) (K L : ℕ)
    (hK : graphEdgeCount S ≤ K) (hL : 0 < L)
    (hbudget : L ≤ N * degree - patternSwitchSlack degree K)
    (v : Fin N) (hover : degree < S.degree v) :
    eventMass (weight (N := N) (d := degree)) (fun g => S ≤ g.graph) = 0 := by
  have hzero : patternDegreeProduct degree S = 0 := by
    unfold patternDegreeProduct
    exact Finset.prod_eq_zero (Finset.mem_univ v) (Nat.descFactorial_of_lt hover)
  have hbound := pattern_probability_bound S K L hK hL hbudget
  rw [hzero, Nat.cast_zero, zero_div] at hbound
  apply le_antisymm hbound
  unfold eventMass
  apply Finset.sum_nonneg
  intro g _
  split_ifs
  · exact g.weight_nonnegative
  · exact le_rfl

end RegularGraph

end LocalLaw
