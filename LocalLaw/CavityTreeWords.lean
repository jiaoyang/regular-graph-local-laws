import LocalLaw.DirichletGraftGraph

/-! # Canonical finite cavity trees are actual truncations of the word tree -/

noncomputable section
namespace LocalLaw
local instance cavityTreeWordsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def wordTreeAdj {A : Type*} (x y : List A) : Prop := ∃ a,x=y++[a] ∨ y=x++[a]

theorem wordTreeAdj_symm {A : Type*} {x y : List A} : wordTreeAdj x y → wordTreeAdj y x :=
  fun ⟨a,h⟩ => ⟨a,h.symm⟩

theorem wordTreeAdj_irrefl {A : Type*} (x : List A) : ¬wordTreeAdj x x := by
  rintro ⟨a,h|h⟩ <;> have hh := congrArg List.length h <;> simp at hh

theorem wordTreeAdj_nil_iff {A : Type*} (w : List A) : wordTreeAdj [] w ↔ ∃ a,w=[a] := by
  constructor
  · rintro ⟨a,h|h⟩
    · have hh := congrArg List.length h
      simp at hh
    · exact ⟨a,by simpa only [List.nil_append] using h⟩
  · rintro ⟨a,rfl⟩
    exact ⟨a,Or.inr rfl⟩

theorem wordTreeAdj_cons_iff {A : Type*} (a b : A) (x y : List A) :
    wordTreeAdj (a::x) (b::y) ↔ a=b ∧ wordTreeAdj x y := by
  constructor
  · rintro ⟨c,h|h⟩
    · have hh := List.cons.inj (show a::x=b::(y++[c]) from h)
      exact ⟨hh.1,⟨c,Or.inl hh.2⟩⟩
    · have hh := List.cons.inj (show b::y=a::(x++[c]) from h)
      exact ⟨hh.1.symm,⟨c,Or.inr hh.2⟩⟩
  · rintro ⟨rfl,c,h|h⟩
    · exact ⟨c,Or.inl (by simpa only [List.cons_append] using congrArg (List.cons a) h)⟩
    · exact ⟨c,Or.inr (by simpa only [List.cons_append] using congrArg (List.cons a) h)⟩

def wordTreeGraph (k : ℕ) : SimpleGraph (List (Fin k)) where
  Adj := wordTreeAdj
  symm := fun _ _ => wordTreeAdj_symm
  loopless := wordTreeAdj_irrefl

def cavityTreeWord (k : ℕ) : (n : ℕ) → CavityTreeIndex k n → List (Fin k)
  | 0,_ => []
  | _n+1,Sum.inl _ => []
  | n+1,Sum.inr p => p.2::cavityTreeWord k n p.1

@[simp] theorem cavityTreeWord_root (k n : ℕ) : cavityTreeWord k n (cavityTreeRoot k n)=[] := by
  cases n <;> rfl

theorem cavityTreeWord_length (k n : ℕ) (x : CavityTreeIndex k n) : (cavityTreeWord k n x).length≤n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    cases x with
    | inl x => exact Nat.zero_le _
    | inr p => exact Nat.succ_le_succ (ih p.1)

theorem cavityTreeWord_injective (k n : ℕ) : Function.Injective (cavityTreeWord k n) := by
  induction n with
  | zero =>
    change Function.Injective (fun _ : Unit => ([] : List (Fin k)))
    exact fun _ _ _ => Subsingleton.elim _ _
  | succ n ih =>
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subsingleton.elim x y)
      | inr q => exact False.elim (List.cons_ne_nil _ _ h.symm)
    | inr p =>
      cases y with
      | inl y => exact False.elim (List.cons_ne_nil _ _ h)
      | inr q =>
        have hh := List.cons.inj h
        exact congrArg Sum.inr (Prod.ext (ih hh.2) hh.1)

theorem cavityTreeWord_eq_nil_iff (k n : ℕ) (x : CavityTreeIndex k n) :
    cavityTreeWord k n x=[] ↔ x=cavityTreeRoot k n := by
  rw [←cavityTreeWord_root k n]
  exact (cavityTreeWord_injective k n).eq_iff

theorem cavityTreeWord_surjective (k n : ℕ) (w : List (Fin k)) (hw : w.length≤n) :
    ∃ x : CavityTreeIndex k n,cavityTreeWord k n x=w := by
  induction n generalizing w with
  | zero =>
    have hz : w=[] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    exact ⟨(),hz.symm⟩
  | succ n ih =>
    cases w with
    | nil => exact ⟨Sum.inl (),rfl⟩
    | cons a w =>
      obtain ⟨x,hx⟩ := ih w (Nat.le_of_succ_le_succ hw)
      exact ⟨Sum.inr (x,a),congrArg (List.cons a) hx⟩

def cavityTreeWordEquiv (k n : ℕ) : CavityTreeIndex k n ≃ {w : List (Fin k) // w.length≤n} :=
  Equiv.ofBijective (fun x => ⟨cavityTreeWord k n x,cavityTreeWord_length k n x⟩)
    ⟨fun _ _ h => cavityTreeWord_injective k n (congrArg Subtype.val h),by
      intro w
      obtain ⟨x,hx⟩ := cavityTreeWord_surjective k n w.val w.property
      exact ⟨x,Subtype.ext hx⟩⟩

theorem cavityTreeWord_adj_iff (k n : ℕ) (x y : CavityTreeIndex k n) :
    (cavityTreeGraph k n).Adj x y ↔ wordTreeAdj (cavityTreeWord k n x) (cavityTreeWord k n y) := by
  induction n with
  | zero =>
    cases x
    cases y
    simp [cavityTreeGraph,cavityTreeWord,wordTreeAdj_irrefl]
  | succ n ih =>
    cases x with
    | inl x =>
      cases y with
      | inl y => simp [cavityTreeGraph,cavityTreeWord,wordTreeAdj_irrefl]
      | inr q =>
        simp only [cavityTreeGraph,cavityTreeWord,wordTreeAdj_nil_iff,List.cons.injEq]
        constructor
        · intro h
          exact ⟨q.2,rfl,by rw [h,cavityTreeWord_root]⟩
        · rintro ⟨a,_,h⟩
          exact (cavityTreeWord_eq_nil_iff k n q.1).mp h
    | inr p =>
      cases y with
      | inl y =>
        have hh := ih (cavityTreeRoot k n) p.1
        constructor
        · intro h
          apply wordTreeAdj_symm
          apply (wordTreeAdj_nil_iff _).mpr
          exact ⟨p.2,by simp only [cavityTreeWord]; rw [h,cavityTreeWord_root]⟩
        · intro h
          have hn := (wordTreeAdj_nil_iff _).mp (wordTreeAdj_symm h)
          obtain ⟨a,ha⟩ := hn
          exact (cavityTreeWord_eq_nil_iff k n p.1).mp (List.cons.inj ha).2
      | inr q =>
        simp only [cavityTreeGraph,cavityTreeWord,wordTreeAdj_cons_iff]
        exact and_congr Iff.rfl (ih p.1 q.1)

def cavityTreeWordIso (k n : ℕ) : cavityTreeGraph k n ≃g (wordTreeGraph k).induce {w | w.length≤n} where
  toEquiv := cavityTreeWordEquiv k n
  map_rel_iff' := by
    intro x y
    exact (cavityTreeWord_adj_iff k n x y).symm

end LocalLaw
