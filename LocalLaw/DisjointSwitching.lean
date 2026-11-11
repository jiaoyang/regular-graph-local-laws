import LocalLaw.SimpleSwitching

/-!
# Disjoint families of simple switchings

For a fixed family with disjoint four-vertex supports, switchings commute,
remain admissible, preserve every degree, and are undone by the reversed family
of inverse quadruples. This does not prove invariance of the paper's I/J
admissibility selector under the full local resampling.
-/

namespace LocalLaw

/-- The oriented data for one switching. -/
structure SwitchingQuad (V : Type*) where
  a : V
  b : V
  c : V
  d : V

namespace SwitchingQuad
variable {V : Type*}

def support (q : SwitchingQuad V) : Set V := {q.a, q.b, q.c, q.d}

def apply (q : SwitchingQuad V) (G : SimpleGraph V) : SimpleGraph V :=
  simpleSwitch G q.a q.b q.c q.d

def Admissible (q : SwitchingQuad V) (G : SimpleGraph V) : Prop :=
  SimpleSwitchingAdmissible G q.a q.b q.c q.d

def inverse (q : SwitchingQuad V) : SwitchingQuad V := ⟨q.a, q.d, q.c, q.b⟩

@[simp] theorem inverse_inverse (q : SwitchingQuad V) : q.inverse.inverse = q := by
  cases q
  rfl

@[simp] theorem support_inverse (q : SwitchingQuad V) : q.inverse.support = q.support := by
  ext x
  simp only [support, inverse, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem removed_left_mem (q : SwitchingQuad V) {x y : V}
    (h : (switchingRemoved q.a q.b q.c q.d).Adj x y) : x ∈ q.support := by
  simp only [switchingRemoved, SimpleGraph.sup_adj, SimpleGraph.edge_adj] at h
  simp only [support, Set.mem_insert_iff, Set.mem_singleton_iff]
  aesop

theorem added_left_mem (q : SwitchingQuad V) {x y : V}
    (h : (switchingAdded q.a q.b q.c q.d).Adj x y) : x ∈ q.support := by
  simp only [switchingAdded, SimpleGraph.sup_adj, SimpleGraph.edge_adj] at h
  simp only [support, Set.mem_insert_iff, Set.mem_singleton_iff]
  aesop

/-- A switching has no effect on adjacency rows outside its support. -/
theorem adj_away (q : SwitchingQuad V) (G : SimpleGraph V) {x y : V}
    (hx : x ∉ q.support) : (q.apply G).Adj x y ↔ G.Adj x y := by
  have hr : ¬(switchingRemoved q.a q.b q.c q.d).Adj x y := fun h => hx (q.removed_left_mem h)
  have ha : ¬(switchingAdded q.a q.b q.c q.d).Adj x y := fun h => hx (q.added_left_mem h)
  simp only [apply, simpleSwitch, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj, hr, ha,
    not_false_eq_true, and_true, or_false]

/-- Disjoint supports make the inserted edges disjoint from the other
switching's removed edges. -/
theorem added_disjoint_removed (p q : SwitchingQuad V)
    (h : Disjoint p.support q.support) :
    Disjoint (switchingAdded p.a p.b p.c p.d) (switchingRemoved q.a q.b q.c q.d) := by
  apply disjoint_iff_inf_le.mpr
  intro x y hxy
  exact False.elim ((Set.disjoint_left.mp h) (p.added_left_mem hxy.1) (q.removed_left_mem hxy.2))

/-- The graph-lattice calculation behind disjoint switching commutation. -/
private theorem replacement_commute (G R S A B : SimpleGraph V)
    (hAS : Disjoint A S) (hBR : Disjoint B R) :
    ((G \ R) ⊔ A) \ S ⊔ B = ((G \ S) ⊔ B) \ R ⊔ A := by
  rw [sup_sdiff_distrib, hAS.sdiff_eq_left, sup_sdiff_distrib, hBR.sdiff_eq_left,
    sdiff_sdiff, sdiff_sdiff]
  rw [sup_comm R S]
  ac_rfl

/-- Operations with disjoint vertex supports commute, even before requiring
that either switching is admissible. -/
theorem commute (p q : SwitchingQuad V) (G : SimpleGraph V)
    (h : Disjoint p.support q.support) : q.apply (p.apply G) = p.apply (q.apply G) := by
  exact replacement_commute G _ _ _ _ (p.added_disjoint_removed q h)
    (q.added_disjoint_removed p h.symm)

/-- One switching preserves the other switching's admissibility when their
supports are disjoint. -/
theorem admissible_after_disjoint (p q : SwitchingQuad V) (G : SimpleGraph V)
    (h : Disjoint p.support q.support) (hq : q.Admissible G) : q.Admissible (p.apply G) := by
  have hout : ∀ x ∈ q.support, x ∉ p.support := by
    intro x hx hp
    exact Set.disjoint_left.mp h hp hx
  have ha := p.adj_away G (hout q.a (by simp [support])) (y := q.b)
  have hc := p.adj_away G (hout q.c (by simp [support])) (y := q.d)
  have had := p.adj_away G (hout q.a (by simp [support])) (y := q.d)
  have hbc := p.adj_away G (hout q.b (by simp [support])) (y := q.c)
  exact ⟨hq.ab_ne, hq.ac_ne, hq.ad_ne, hq.bc_ne, hq.bd_ne, hq.cd_ne,
    ha.mpr hq.old_ab, hc.mpr hq.old_cd, fun hh => hq.new_ad (had.mp hh),
    fun hh => hq.new_bc (hbc.mp hh)⟩

theorem inverse_admissible (q : SwitchingQuad V) (G : SimpleGraph V)
    (hq : q.Admissible G) : q.inverse.Admissible (q.apply G) := hq.inverse_admissible

theorem inverse_apply (q : SwitchingQuad V) (G : SimpleGraph V)
    (hq : q.Admissible G) : q.inverse.apply (q.apply G) = G := hq.switch_inverse

end SwitchingQuad

/-- Apply a list of switchings in its listed order. -/
def applySwitches {V : Type*} : List (SwitchingQuad V) → SimpleGraph V → SimpleGraph V
  | [], G => G
  | q :: qs, G => applySwitches qs (q.apply G)

/-- Undo a list by reversing its order and inverting each quadruple. -/
def inverseSwitches {V : Type*} (L : List (SwitchingQuad V)) : List (SwitchingQuad V) :=
  L.reverse.map SwitchingQuad.inverse

@[simp] theorem applySwitches_nil {V : Type*} (G : SimpleGraph V) : applySwitches [] G = G := rfl

@[simp] theorem applySwitches_cons {V : Type*} (q : SwitchingQuad V)
    (qs : List (SwitchingQuad V)) (G : SimpleGraph V) :
    applySwitches (q :: qs) G = applySwitches qs (q.apply G) := rfl

theorem applySwitches_append {V : Type*} (L K : List (SwitchingQuad V)) (G : SimpleGraph V) :
    applySwitches (L ++ K) G = applySwitches K (applySwitches L G) := by
  induction L generalizing G with
  | nil => rfl
  | cons q qs ih => simpa only [List.cons_append, applySwitches_cons] using ih (q.apply G)

@[simp] theorem inverseSwitches_cons {V : Type*} (q : SwitchingQuad V)
    (qs : List (SwitchingQuad V)) :
    inverseSwitches (q :: qs) = inverseSwitches qs ++ [q.inverse] := by
  simp [inverseSwitches]

@[simp] theorem inverseSwitches_inverse {V : Type*} (L : List (SwitchingQuad V)) :
    inverseSwitches (inverseSwitches L) = L := by
  simp [inverseSwitches, List.map_reverse, List.map_map, Function.comp_def]

/-- Pairwise disjoint vertex supports of the family. -/
def DisjointSwitchingSupports {V : Type*} (L : List (SwitchingQuad V)) : Prop :=
  L.Pairwise (fun p q => Disjoint p.support q.support)

/-- Simultaneous admissibility means admissibility in the original graph. -/
def SwitchingFamilyAdmissible {V : Type*} (L : List (SwitchingQuad V)) (G : SimpleGraph V) : Prop :=
  ∀ q ∈ L, q.Admissible G

/-- After the first switch, all remaining disjoint switches are still admissible. -/
theorem tail_switches_admissible {V : Type*} (q : SwitchingQuad V)
    (qs : List (SwitchingQuad V)) (G : SimpleGraph V)
    (hdis : DisjointSwitchingSupports (q :: qs)) (ha : SwitchingFamilyAdmissible (q :: qs) G) :
    SwitchingFamilyAdmissible qs (q.apply G) := by
  intro p hp
  have hd : Disjoint q.support p.support := (List.pairwise_cons.mp hdis).1 p hp
  exact q.admissible_after_disjoint p G hd (ha p (List.mem_cons_of_mem _ hp))

/-- A disjoint admissible family is restored by its reverse inverse family. -/
theorem applySwitches_inverse_restore {V : Type*} (L : List (SwitchingQuad V))
    (G : SimpleGraph V) (hdis : DisjointSwitchingSupports L) (ha : SwitchingFamilyAdmissible L G) :
    applySwitches (inverseSwitches L) (applySwitches L G) = G := by
  induction L generalizing G with
  | nil => rfl
  | cons q qs ih =>
      have htail := tail_switches_admissible q qs G hdis ha
      have hd := (List.pairwise_cons.mp hdis).2
      rw [inverseSwitches_cons, applySwitches_append]
      simp only [applySwitches_cons, applySwitches_nil]
      rw [ih (q.apply G) hd htail]
      exact q.inverse_apply G (ha q (List.mem_cons_self))

/-- The switched graph is independent of how a disjoint family is enumerated.
Admissibility is not needed for order independence itself. -/
theorem applySwitches_perm {V : Type*} {L K : List (SwitchingQuad V)} (hp : L.Perm K)
    (hdis : DisjointSwitchingSupports L) (G : SimpleGraph V) :
    applySwitches L G = applySwitches K G := by
  revert hdis
  induction hp generalizing G with
  | nil => intro _; rfl
  | @cons q L K hperm ih =>
      intro hdis
      exact ih (q.apply G) (List.pairwise_cons.mp hdis).2
  | swap p q L =>
      intro hdis
      have hqd : Disjoint q.support p.support :=
        (List.pairwise_cons.mp hdis).1 p (by simp)
      simp only [applySwitches_cons]
      rw [q.commute p G hqd]
  | @trans L K M h₁ h₂ ih₁ ih₂ =>
      intro hdis
      have hdisK : DisjointSwitchingSupports K :=
        (h₁.pairwise_iff (fun {_ _} h => h.symm)).mp hdis
      exact (ih₁ G hdis).trans (ih₂ G hdisK)

/-- Disjointness of supports is unchanged by reversing and inverting a family. -/
theorem inverseSwitches_disjoint {V : Type*} (L : List (SwitchingQuad V))
    (hdis : DisjointSwitchingSupports L) : DisjointSwitchingSupports (inverseSwitches L) := by
  unfold DisjointSwitchingSupports inverseSwitches
  rw [List.pairwise_map, List.pairwise_reverse]
  simp only [SwitchingQuad.support_inverse]
  exact List.Pairwise.imp (fun {_ _} h => h.symm) hdis

/-- An admissible switching stays admissible after any family disjoint from it.
The other switches do not need to be admissible for this locality statement. -/
theorem admissible_after_switches {V : Type*} (q : SwitchingQuad V)
    (L : List (SwitchingQuad V)) (G : SimpleGraph V) (ha : q.Admissible G)
    (hd : ∀ p ∈ L, Disjoint p.support q.support) : q.Admissible (applySwitches L G) := by
  induction L generalizing G with
  | nil => exact ha
  | cons p ps ih =>
      apply ih (p.apply G)
      · exact p.admissible_after_disjoint q G (hd p List.mem_cons_self) ha
      · exact fun r hr => hd r (List.mem_cons_of_mem _ hr)

/-- Every inverse switch is admissible in the final graph. Thus the inverse
family is valid data as well as algebraically undoing the graph operation. -/
theorem inverseSwitches_admissible {V : Type*} (L : List (SwitchingQuad V))
    (G : SimpleGraph V) (hdis : DisjointSwitchingSupports L) (ha : SwitchingFamilyAdmissible L G) :
    SwitchingFamilyAdmissible (inverseSwitches L) (applySwitches L G) := by
  induction L generalizing G with
  | nil =>
      intro q hq
      simp [inverseSwitches] at hq
  | cons q qs ih =>
      have htail := tail_switches_admissible q qs G hdis ha
      have hd := (List.pairwise_cons.mp hdis).2
      intro p hp
      simp only [inverseSwitches_cons, List.mem_append, List.mem_singleton] at hp
      rcases hp with hptail | rfl
      · exact ih (q.apply G) hd htail p hptail
      · apply admissible_after_switches q.inverse qs (q.apply G)
        · exact q.inverse_admissible G (ha q List.mem_cons_self)
        · intro p hp
          rw [SwitchingQuad.support_inverse]
          exact ((List.pairwise_cons.mp hdis).1 p hp).symm

/-- The actual enlarged state: graph together with a fixed admissible family
having disjoint supports. This is not the paper's complete I/J-selected state. -/
def DisjointSwitchingState (V : Type*) :=
  {s : SimpleGraph V × List (SwitchingQuad V) //
    DisjointSwitchingSupports s.2 ∧ SwitchingFamilyAdmissible s.2 s.1}

/-- Switch the graph and reverse the oriented data; validity is proved. -/
def reverseSwitchingState {V : Type*} (s : DisjointSwitchingState V) :
    DisjointSwitchingState V :=
  ⟨(applySwitches s.val.2 s.val.1, inverseSwitches s.val.2),
    inverseSwitches_disjoint s.val.2 s.property.1,
    inverseSwitches_admissible s.val.2 s.val.1 s.property.1 s.property.2⟩

/-- A genuine involution of graph-plus-data states for disjoint families. -/
theorem reverseSwitchingState_involutive {V : Type*} :
    Function.Involutive (@reverseSwitchingState V) := by
  intro s
  apply Subtype.ext
  apply Prod.ext
  · exact applySwitches_inverse_restore s.val.2 s.val.1 s.property.1 s.property.2
  · exact inverseSwitches_inverse s.val.2

/-- The disjoint-family graph-plus-data involution as a permutation. -/
def disjointSwitchingPermutation (V : Type*) : Equiv.Perm (DisjointSwitchingState V) :=
  Function.Involutive.toPerm reverseSwitchingState reverseSwitchingState_involutive

section Degrees
variable {V : Type*} [Fintype V]
noncomputable local instance familySwitchingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Every degree is preserved by a finite disjoint admissible switching family. -/
theorem applySwitches_degree (L : List (SwitchingQuad V)) (G : SimpleGraph V)
    (hdis : DisjointSwitchingSupports L) (ha : SwitchingFamilyAdmissible L G) (x : V) :
    (applySwitches L G).degree x = G.degree x := by
  induction L generalizing G with
  | nil => rfl
  | cons q qs ih =>
      have htail := tail_switches_admissible q qs G hdis ha
      have hd := (List.pairwise_cons.mp hdis).2
      rw [applySwitches_cons, ih (q.apply G) hd htail]
      exact (ha q List.mem_cons_self).degree_eq x

theorem applySwitches_regular (L : List (SwitchingQuad V)) (G : SimpleGraph V)
    (hdis : DisjointSwitchingSupports L) (ha : SwitchingFamilyAdmissible L G) {d : ℕ}
    (hG : G.IsRegularOfDegree d) : (applySwitches L G).IsRegularOfDegree d := by
  intro x
  rw [applySwitches_degree L G hdis ha x]
  exact hG.degree_eq x

end Degrees

end LocalLaw
