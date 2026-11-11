import LocalLaw.SharpBallCounting

/-!
# Finite nonbacktracking path counts at the sharp degree-minus-one rate

After the first edge, the preceding vertex is an actual forbidden neighbor.
The finite dependent path space therefore has at most (d-1)^n continuations;
no acyclicity or local excess assumption is needed.
-/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance nbCountingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type} [Fintype V]

/-- A nonbacktracking continuation after an oriented edge a→b. -/
def NonbacktrackingTail (G : SimpleGraph V) (a b : V) : ℕ → Type
  | 0 => Unit
  | n + 1 => Σ w : {w : V // G.Adj b w ∧ w ≠ a}, NonbacktrackingTail G b w.val n

instance nonbacktrackingTailFintype (G : SimpleGraph V) (a b : V) :
    (n : ℕ) → Fintype (NonbacktrackingTail G a b n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => by
    unfold NonbacktrackingTail
    letI := fun w : {w : V // G.Adj b w ∧ w ≠ a} => nonbacktrackingTailFintype G b w.val n
    infer_instance

/-- The actual preceding endpoint removes one available neighbor. -/
theorem nonbacktracking_next_card (G : SimpleGraph V) (a b : V) (hab : G.Adj a b) :
    Nat.card {w : V // G.Adj b w ∧ w ≠ a} + 1 = Nat.card (G.neighborSet b) := by
  classical
  let E : {w : V // G.Adj b w ∧ w ≠ a} ≃ {w : G.neighborSet b // w.val ≠ a} :=
    { toFun := fun w => ⟨⟨w.val, w.property.1⟩, w.property.2⟩
      invFun := fun w => ⟨w.val.val, w.val.property, w.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr E]
  have ha : a ∈ G.neighborSet b := hab.symm
  let a' : G.neighborSet b := ⟨a, ha⟩
  have heq : {w : G.neighborSet b // w.val ≠ a} = {w : G.neighborSet b // w ≠ a'} := by
    congr 1
    funext w
    apply propext
    constructor
    · intro h heq; exact h (congrArg Subtype.val heq)
    · intro h heq; exact h (Subtype.ext heq)
  rw [heq]
  have h := Fintype.card_subtype_compl (fun w : G.neighborSet b => w = a')
  rw [Fintype.card_subtype_eq] at h
  have hpos : 0 < Fintype.card (G.neighborSet b) := Fintype.card_pos_iff.mpr ⟨a'⟩
  simp only [← Nat.card_eq_fintype_card] at h hpos
  change Nat.card {w : G.neighborSet b // w ≠ a'} = Nat.card (G.neighborSet b) - 1 at h
  omega

/-- Each successive continuation has at most d-1 choices. -/
theorem nonbacktrackingTail_card_bound (G : SimpleGraph V) (d : ℕ) (hd : 1 ≤ d)
    (hdeg : ∀ v, G.degree v ≤ d) (n : ℕ) (a b : V) (hab : G.Adj a b) :
    Nat.card (NonbacktrackingTail G a b n) ≤ (d - 1) ^ n := by
  induction n generalizing a b with
  | zero => simp [NonbacktrackingTail]
  | succ n ih =>
    change Nat.card (Σ w : {w : V // G.Adj b w ∧ w ≠ a}, NonbacktrackingTail G b w.val n) ≤ _
    rw [Nat.card_sigma]
    have hc := nonbacktracking_next_card G a b hab
    have hb := hdeg b
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hb
    have hnext : Nat.card {w : V // G.Adj b w ∧ w ≠ a} ≤ d - 1 := by omega
    calc
      _ ≤ ∑ _w : {w : V // G.Adj b w ∧ w ≠ a}, (d - 1) ^ n :=
        Finset.sum_le_sum (fun w _ => ih b w.val w.property.1)
      _ = Nat.card {w : V // G.Adj b w ∧ w ≠ a} * (d - 1) ^ n := by
        simp [Nat.card_eq_fintype_card]
      _ ≤ (d - 1) * (d - 1) ^ n := Nat.mul_le_mul_right _ hnext
      _ = _ := by rw [pow_succ]; exact Nat.mul_comm _ _

/-- Rooted path space, separating the first unrestricted neighbor choice. -/
def NonbacktrackingPath (G : SimpleGraph V) (root : V) : ℕ → Type
  | 0 => Unit
  | n + 1 => Σ w : G.neighborSet root, NonbacktrackingTail G root w.val n

instance nonbacktrackingPathFintype (G : SimpleGraph V) (root : V) :
    (n : ℕ) → Fintype (NonbacktrackingPath G root n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => by unfold NonbacktrackingPath; infer_instance

theorem nonbacktrackingPath_card_bound (G : SimpleGraph V) (d n : ℕ) (hd : 2 ≤ d)
    (hdeg : ∀ v, G.degree v ≤ d) (root : V) :
    Nat.card (NonbacktrackingPath G root n) ≤ (d + 1) * (d - 1) ^ n := by
  cases n with
  | zero => simp [NonbacktrackingPath]
  | succ n =>
    change Nat.card (Σ w : G.neighborSet root, NonbacktrackingTail G root w.val n) ≤ _
    rw [Nat.card_sigma]
    have hroot := hdeg root
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hroot
    calc
      _ ≤ ∑ _w : G.neighborSet root, (d - 1) ^ n :=
        Finset.sum_le_sum (fun w _ => nonbacktrackingTail_card_bound G d (by omega) hdeg n root w.val w.property)
      _ = Nat.card (G.neighborSet root) * (d - 1) ^ n := by simp [Nat.card_eq_fintype_card]
      _ ≤ (d + 1) * (d - 1) ^ (n + 1) := by
        have hp : (d - 1) ^ n ≤ (d - 1) ^ (n + 1) :=
          Nat.pow_le_pow_right (by omega : 0 < d - 1) (by omega)
        exact Nat.mul_le_mul (by omega) hp

end
end LocalLaw
