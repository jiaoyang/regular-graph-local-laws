import LocalLaw.NonbacktrackingCounting

/-!
# Simple vertex sequences are counted by nonbacktracking paths

An injective adjacent vertex sequence extends the exact finite dependent path
space. Reading its vertices recovers the original sequence, so the encoding
is injective and the sharp degree-minus-one count applies.
-/

namespace LocalLaw
noncomputable section
local instance nbSequenceDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type} [Fintype V]

/-- Read all vertices, including the current endpoint, of a continuation. -/
def nonbacktrackingTailVertex (G : SimpleGraph V) (a b : V) :
    (n : ℕ) → NonbacktrackingTail G a b n → Fin (n + 1) → V
  | 0, _ => fun _ => b
  | n + 1, t => Fin.cases b (fun j => nonbacktrackingTailVertex G b t.1.val n t.2 j)

/-- Read all vertices of a rooted nonbacktracking path. -/
def nonbacktrackingPathVertex (G : SimpleGraph V) (root : V) :
    (n : ℕ) → NonbacktrackingPath G root n → Fin (n + 1) → V
  | 0, _ => fun _ => root
  | n + 1, p => Fin.cases root (fun j => nonbacktrackingTailVertex G root p.1.val n p.2 j)

omit [Fintype V] in
/-- An adjacent injective sequence avoiding the preceding endpoint is an
actual nonbacktracking continuation with exactly those vertices. -/
theorem nonbacktrackingTail_of_sequence (G : SimpleGraph V) (n : ℕ)
    (a b : V) (f : Fin (n + 1) ↪ V) (hzero : f 0 = b)
    (hprev : a ∉ Set.range f)
    (hadj : ∀ i : Fin n, G.Adj (f i.castSucc) (f i.succ)) :
    ∃ t : NonbacktrackingTail G a b n, nonbacktrackingTailVertex G a b n t = f := by
  induction n generalizing a b with
  | zero =>
    refine ⟨(), ?_⟩
    funext i
    have hi : i = 0 := Fin.ext (by have hh := i.is_lt; omega)
    subst i
    exact hzero.symm
  | succ n ih =>
    let f' : Fin (n + 1) ↪ V :=
      { toFun := fun i => f i.succ
        inj' := fun _ _ h => Fin.succ_injective _ (f.injective h) }
    have hprev' : b ∉ Set.range f' := by
      rintro ⟨i, hi⟩
      have heq : f i.succ = f 0 := hi.trans hzero.symm
      have hidx := f.injective heq
      have hv := congrArg Fin.val hidx
      simp only [Fin.val_succ, Fin.val_zero] at hv
      omega
    have hadj' : ∀ i : Fin n, G.Adj (f' i.castSucc) (f' i.succ) := by
      intro i
      have hh := hadj i.succ
      convert hh using 1
    have hfirst : G.Adj b (f' 0) := by
      have hh := hadj (0 : Fin (n + 1))
      change G.Adj (f 0) (f' 0) at hh
      rw [hzero] at hh
      exact hh
    have hne : f' 0 ≠ a := fun h => hprev ⟨(0 : Fin (n + 1)).succ, h⟩
    obtain ⟨t, ht⟩ := ih b (f' 0) f' rfl hprev' hadj'
    refine ⟨⟨⟨f' 0, hfirst, hne⟩, t⟩, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hzero.symm
    · exact congrFun ht j

/-- Rooted adjacent injective sequences of exactly n edges. -/
def RootedSimpleSequence (G : SimpleGraph V) (root : V) (n : ℕ) :=
  {f : Fin (n + 1) ↪ V // f 0 = root ∧ ∀ i : Fin n, G.Adj (f i.castSucc) (f i.succ)}

instance rootedSimpleSequenceFintype (G : SimpleGraph V) (root : V) (n : ℕ) :
    Fintype (RootedSimpleSequence G root n) := by unfold RootedSimpleSequence; infer_instance

omit [Fintype V] in
theorem nonbacktrackingPath_of_sequence (G : SimpleGraph V) (root : V) (n : ℕ)
    (s : RootedSimpleSequence G root n) :
    ∃ p : NonbacktrackingPath G root n, nonbacktrackingPathVertex G root n p = s.val := by
  cases n with
  | zero =>
    refine ⟨(), ?_⟩
    funext i
    have hi : i = 0 := Fin.ext (by have hh := i.is_lt; omega)
    subst i
    exact s.property.1.symm
  | succ n =>
    let f' : Fin (n + 1) ↪ V :=
      { toFun := fun i => s.val i.succ
        inj' := fun _ _ h => Fin.succ_injective _ (s.val.injective h) }
    have hprev : root ∉ Set.range f' := by
      rintro ⟨i, hi⟩
      have hidx := s.val.injective (hi.trans s.property.1.symm)
      have hv := congrArg Fin.val hidx
      simp only [Fin.val_succ, Fin.val_zero] at hv
      omega
    have hadj : ∀ i : Fin n, G.Adj (f' i.castSucc) (f' i.succ) := by
      intro i
      have hh := s.property.2 i.succ
      convert hh using 1
    have hfirst : G.Adj root (f' 0) := by
      have hh := s.property.2 (0 : Fin (n + 1))
      change G.Adj (s.val 0) (f' 0) at hh
      rw [s.property.1] at hh
      exact hh
    obtain ⟨t, ht⟩ := nonbacktrackingTail_of_sequence G n root (f' 0) f' rfl hprev hadj
    refine ⟨⟨⟨f' 0, hfirst⟩, t⟩, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact s.property.1.symm
    · exact congrFun ht j

def rootedSequenceEncoding (G : SimpleGraph V) (root : V) (n : ℕ)
    (s : RootedSimpleSequence G root n) : NonbacktrackingPath G root n :=
  Classical.choose (nonbacktrackingPath_of_sequence G root n s)

omit [Fintype V] in
theorem rootedSequenceEncoding_injective (G : SimpleGraph V) (root : V) (n : ℕ) :
    Function.Injective (rootedSequenceEncoding G root n) := by
  intro s t h
  apply Subtype.ext
  apply Function.Embedding.ext
  intro i
  have hs := congrFun (Classical.choose_spec (nonbacktrackingPath_of_sequence G root n s)) i
  have ht := congrFun (Classical.choose_spec (nonbacktrackingPath_of_sequence G root n t)) i
  change nonbacktrackingPathVertex G root n (rootedSequenceEncoding G root n s) i = s.val i at hs
  change nonbacktrackingPathVertex G root n (rootedSequenceEncoding G root n t) i = t.val i at ht
  rw [h] at hs
  exact hs.symm.trans ht

/-- Sharp rooted simple-sequence count, without an acyclicity or excess input. -/
theorem rootedSimpleSequence_card_bound (G : SimpleGraph V) (root : V) (d n : ℕ)
    (hd : 2 ≤ d) (hdeg : ∀ v, G.degree v ≤ d) :
    Nat.card (RootedSimpleSequence G root n) ≤ (d + 1) * (d - 1) ^ n :=
  (Nat.card_le_card_of_injective _ (rootedSequenceEncoding_injective G root n)).trans
    (nonbacktrackingPath_card_bound G d n hd hdeg root)

end
end LocalLaw
