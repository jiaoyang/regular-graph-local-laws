import LocalLaw.Abstract

/-!
# Finite greedy packing counts

If each object conflicts with at most D objects, many ordered q-tuples avoid
all conflicts. The actual prefix/last-coordinate equivalence and excluded
choice union bound prove a lower count; no packing-size claim is assumed.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance packingCountDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {I : Type*} [Fintype I]

/-- Increasing index order is enough; a symmetric overlap relation is a
special case. Reflexive conflicts automatically enforce distinct objects. -/
def SeparatedTuple (R : I → I → Prop) (n : ℕ) :=
  {f : Fin n → I // ∀ i j, i < j → ¬ R (f i) (f j)}

instance separatedTupleFintype (R : I → I → Prop) (n : ℕ) : Fintype (SeparatedTuple R n) := by
  unfold SeparatedTuple
  infer_instance

def AllowedAfter {n : ℕ} (R : I → I → Prop) (f : SeparatedTuple R n) :=
  {x : I // ∀ i, ¬ R (f.val i) x}

instance allowedAfterFintype {n : ℕ} (R : I → I → Prop) (f : SeparatedTuple R n) :
    Fintype (AllowedAfter R f) := by unfold AllowedAfter; infer_instance

def separatedTupleZeroEquiv (R : I → I → Prop) : SeparatedTuple R 0 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨Fin.elim0, fun i => i.elim0⟩
  left_inv f := by apply Subtype.ext; funext i; exact i.elim0
  right_inv x := by cases x; rfl

/-- Appending the last element is a genuine equivalence of finite tuple data. -/
def separatedTupleSuccEquiv (R : I → I → Prop) (n : ℕ) :
    SeparatedTuple R (n + 1) ≃ Σ f : SeparatedTuple R n, AllowedAfter R f where
  toFun f := ⟨⟨fun i => f.val i.castSucc, fun i j hij => f.property _ _ hij⟩,
    ⟨f.val (Fin.last n), fun i => f.property _ _ (Fin.castSucc_lt_last i)⟩⟩
  invFun p := ⟨Fin.snoc p.1.val p.2.val, by
    intro i j hij
    by_cases hi : i.val = n
    · have hj := j.isLt
      change i.val < j.val at hij
      omega
    · let ip : Fin n := ⟨i.val, by have hh := i.isLt; omega⟩
      have heqi : i = ip.castSucc := Fin.ext rfl
      rw [heqi, Fin.snoc_castSucc]
      by_cases hj : j.val = n
      · have heqj : j = Fin.last n := Fin.ext hj
        rw [heqj, Fin.snoc_last]
        exact p.2.property ip
      · let jp : Fin n := ⟨j.val, by have hh := j.isLt; omega⟩
        have heqj : j = jp.castSucc := Fin.ext rfl
        rw [heqj, Fin.snoc_castSucc]
        exact p.1.property ip jp hij⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp
  right_inv p := by
    rcases p with ⟨f, x⟩
    apply Sigma.ext
    · apply Subtype.ext
      funext i
      change Fin.snoc (α := fun _ => I) f.val x.val i.castSucc = f.val i
      exact Fin.snoc_castSucc _ _ _
    · apply (Subtype.heq_iff_coe_eq (fun y => by simp [AllowedAfter])).mpr
      change Fin.snoc (α := fun _ => I) f.val x.val (Fin.last n) = x.val
      exact Fin.snoc_last (α := fun _ => I) x.val f.val

/-- The union of all previous conflict sets removes at most nD choices. -/
theorem allowedAfter_card_lower (R : I → I → Prop) (D n : ℕ)
    (hD : ∀ x, Nat.card {y : I // R x y} ≤ D) (f : SeparatedTuple R n) :
    Fintype.card I - n * D ≤ Nat.card (AllowedAfter R f) := by
  classical
  let bad : Finset I := Finset.univ.biUnion (fun i : Fin n => Finset.univ.filter (R (f.val i)))
  have hbad : bad.card ≤ n * D := by
    calc
      bad.card ≤ ∑ i : Fin n, (Finset.univ.filter (R (f.val i))).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin n, D := Finset.sum_le_sum (fun i _ => by
        simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hD (f.val i))
      _ = n * D := by simp
  have heq : (Finset.univ.filter (fun x => ∀ i : Fin n, ¬ R (f.val i) x)) = Finset.univ \ bad := by
    ext x
    simp [bad]
  have hcard : Nat.card (AllowedAfter R f) = Fintype.card I - bad.card := by
    rw [Nat.card_eq_fintype_card]
    change Fintype.card {x : I // ∀ i : Fin n, ¬ R (f.val i) x} = _
    rw [Fintype.card_subtype, heq, Finset.card_sdiff (Finset.subset_univ bad), Finset.card_univ]
  rw [hcard]
  exact Nat.sub_le_sub_left hbad _

/-- The fixed-q loss bound is propagated through every prefix length. -/
theorem separatedTuple_card_lower (R : I → I → Prop) (D q : ℕ)
    (hD : ∀ x, Nat.card {y : I // R x y} ≤ D) :
    (Fintype.card I - q * D) ^ q ≤ Nat.card (SeparatedTuple R q) := by
  have hprefix : ∀ n ≤ q, (Fintype.card I - q * D) ^ n ≤ Nat.card (SeparatedTuple R n) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [pow_zero, Nat.card_congr (separatedTupleZeroEquiv R)]
      simp
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hall : ∀ f : SeparatedTuple R n, Fintype.card I - q * D ≤ Nat.card (AllowedAfter R f) := by
        intro f
        exact (Nat.sub_le_sub_left (Nat.mul_le_mul_right D (by omega : n ≤ q)) _).trans
          (allowedAfter_card_lower R D n hD f)
      calc
        _ = (Fintype.card I - q * D) ^ n * (Fintype.card I - q * D) := pow_succ _ _
        _ ≤ Nat.card (SeparatedTuple R n) * (Fintype.card I - q * D) := Nat.mul_le_mul_right _ hprev
        _ = ∑ _f : SeparatedTuple R n, (Fintype.card I - q * D) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id, Nat.card_eq_fintype_card]
        _ ≤ ∑ f : SeparatedTuple R n, Nat.card (AllowedAfter R f) := Finset.sum_le_sum (fun f _ => hall f)
        _ = Nat.card (Σ f : SeparatedTuple R n, AllowedAfter R f) := (Nat.card_sigma).symm
        _ = Nat.card (SeparatedTuple R (n + 1)) := (Nat.card_congr (separatedTupleSuccEquiv R n)).symm
  exact hprefix q le_rfl

/-- If the union loss is at most half the objects, at least (M/2)^q ordered
compatible choices remain. -/
theorem separatedTuple_card_half (R : I → I → Prop) (D q : ℕ)
    (hD : ∀ x, Nat.card {y : I // R x y} ≤ D) (hbudget : 2 * q * D ≤ Fintype.card I) :
    ((Fintype.card I : ℝ) / 2) ^ q ≤ (Nat.card (SeparatedTuple R q) : ℝ) := by
  have hle : q * D ≤ Fintype.card I := by nlinarith
  have hmin : (Fintype.card I : ℝ) / 2 ≤ ((Fintype.card I - q * D : ℕ) : ℝ) := by
    rw [Nat.cast_sub hle]
    have hh : 2 * (q : ℝ) * (D : ℝ) ≤ (Fintype.card I : ℝ) := by exact_mod_cast hbudget
    push_cast
    linarith
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ (Fintype.card I : ℝ) / 2 by positivity) hmin q
  apply hp.trans
  exact_mod_cast separatedTuple_card_lower R D q hD

end LocalLaw
