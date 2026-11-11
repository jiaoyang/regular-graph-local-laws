import LocalLaw.DisjointSwitching

/-!
# Edge-disjoint boundary switchings

The boundary switchings in the paper may share an interior leaf. Disjoint
four-vertex supports are therefore unnecessarily restrictive. Disjoint modified
edge footprints suffice for commutation, persistence of admissibility, degree
preservation, and inversion. Exterior triple isolation implies this weaker
condition even when the interior leaf vertices are repeated.

The full paper I/J selector and its invariance are not supplied by this module.
-/

namespace LocalLaw

namespace SwitchingQuad
variable {V : Type*}

/-- All edges changed by a switching, both removed and added. -/
def footprint (q : SwitchingQuad V) : SimpleGraph V :=
  switchingRemoved q.a q.b q.c q.d ⊔ switchingAdded q.a q.b q.c q.d

/-- The three exterior vertices for boundary data (l,a,b,c). -/
def exterior (q : SwitchingQuad V) : Set V := {q.b, q.c, q.d}

@[simp] theorem footprint_inverse (q : SwitchingQuad V) : q.inverse.footprint = q.footprint := by
  unfold footprint inverse switchingRemoved switchingAdded
  dsimp only
  rw [SimpleGraph.edge_comm q.c q.b, SimpleGraph.edge_comm q.d q.c]
  ac_rfl

/-- An edge outside the modified footprint keeps exactly its old adjacency. -/
theorem adj_outside_footprint (q : SwitchingQuad V) (G : SimpleGraph V) {x y : V}
    (h : ¬q.footprint.Adj x y) : (q.apply G).Adj x y ↔ G.Adj x y := by
  have hr : ¬(switchingRemoved q.a q.b q.c q.d).Adj x y := fun hr => h (Or.inl hr)
  have ha : ¬(switchingAdded q.a q.b q.c q.d).Adj x y := fun ha => h (Or.inr ha)
  simp only [apply, simpleSwitch, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj,
    hr, ha, not_false_eq_true, and_true, or_false]

/-- Edges of another disjoint footprint retain their original adjacency. -/
theorem adj_on_disjoint_footprint (p q : SwitchingQuad V) (G : SimpleGraph V)
    (hd : Disjoint p.footprint q.footprint) {x y : V} (hq : q.footprint.Adj x y) :
    (p.apply G).Adj x y ↔ G.Adj x y := by
  apply p.adj_outside_footprint G
  intro hp
  exact (hd.le_bot ⟨hp, hq⟩ : False)

/-- Edge-disjoint modified footprints are enough for switching commutation. -/
theorem commute_of_edge_disjoint (p q : SwitchingQuad V) (G : SimpleGraph V)
    (hd : Disjoint p.footprint q.footprint) : q.apply (p.apply G) = p.apply (q.apply G) := by
  have hAS : Disjoint (switchingAdded p.a p.b p.c p.d)
      (switchingRemoved q.a q.b q.c q.d) := hd.mono le_sup_right le_sup_left
  have hBR : Disjoint (switchingAdded q.a q.b q.c q.d)
      (switchingRemoved p.a p.b p.c p.d) := hd.symm.mono le_sup_right le_sup_left
  unfold apply simpleSwitch
  rw [sup_sdiff_distrib, hAS.sdiff_eq_left, sup_sdiff_distrib, hBR.sdiff_eq_left,
    sdiff_sdiff, sdiff_sdiff]
  rw [sup_comm (switchingRemoved p.a p.b p.c p.d) (switchingRemoved q.a q.b q.c q.d)]
  ac_rfl

/-- Edge-disjoint modifications preserve every original admissibility test
concerning the other switching's old and new edges. -/
theorem admissible_after_edge_disjoint (p q : SwitchingQuad V) (G : SimpleGraph V)
    (hd : Disjoint p.footprint q.footprint) (hq : q.Admissible G) : q.Admissible (p.apply G) := by
  have hab : q.footprint.Adj q.a q.b := by
    simp [footprint, switchingRemoved, switchingAdded, SimpleGraph.sup_adj,
      SimpleGraph.edge_adj, hq.ab_ne]
  have hcd : q.footprint.Adj q.c q.d := by
    simp [footprint, switchingRemoved, switchingAdded, SimpleGraph.sup_adj,
      SimpleGraph.edge_adj, hq.cd_ne]
  have had : q.footprint.Adj q.a q.d := by
    simp [footprint, switchingRemoved, switchingAdded, SimpleGraph.sup_adj,
      SimpleGraph.edge_adj, hq.ad_ne]
  have hbc : q.footprint.Adj q.b q.c := by
    simp [footprint, switchingRemoved, switchingAdded, SimpleGraph.sup_adj,
      SimpleGraph.edge_adj, hq.bc_ne]
  exact ⟨hq.ab_ne, hq.ac_ne, hq.ad_ne, hq.bc_ne, hq.bd_ne, hq.cd_ne,
    (p.adj_on_disjoint_footprint q G hd hab).mpr hq.old_ab,
    (p.adj_on_disjoint_footprint q G hd hcd).mpr hq.old_cd,
    fun hh => hq.new_ad ((p.adj_on_disjoint_footprint q G hd had).mp hh),
    fun hh => hq.new_bc ((p.adj_on_disjoint_footprint q G hd hbc).mp hh)⟩

theorem footprint_left_mem_support (q : SwitchingQuad V) {x y : V}
    (h : q.footprint.Adj x y) : x ∈ q.support := by
  rcases h with hr | ha
  · exact q.removed_left_mem hr
  · exact q.added_left_mem ha

/-- Every modified edge touches at least one exterior vertex. -/
theorem footprint_touches_exterior (q : SwitchingQuad V) {x y : V}
    (h : q.footprint.Adj x y) : x ∈ q.exterior ∨ y ∈ q.exterior := by
  simp only [footprint, switchingRemoved, switchingAdded, SimpleGraph.sup_adj,
    SimpleGraph.edge_adj] at h
  simp only [exterior, Set.mem_insert_iff, Set.mem_singleton_iff]
  aesop

/-- Exterior triples isolated from each other force disjoint edge footprints,
even if the interior leaf vertices agree. Only the interior/exterior placement
needed in the proof is assumed; no inequality between the two leaves is used. -/
theorem footprint_disjoint_of_boundary (p q : SwitchingQuad V) (T : Set V)
    (hpExt : Disjoint p.exterior T) (hqRoot : q.a ∈ T)
    (hExt : Disjoint p.exterior q.exterior) : Disjoint p.footprint q.footprint := by
  apply disjoint_iff_inf_le.mpr
  intro x y hxy
  obtain hx | hy := p.footprint_touches_exterior hxy.1
  · have hq := q.footprint_left_mem_support hxy.2
    change x = q.a ∨ x ∈ q.exterior at hq
    rcases hq with rfl | hqx
    · exact False.elim ((Set.disjoint_left.mp hpExt) hx hqRoot)
    · exact False.elim ((Set.disjoint_left.mp hExt) hx hqx)
  · have hq := q.footprint_left_mem_support hxy.2.symm
    change y = q.a ∨ y ∈ q.exterior at hq
    rcases hq with rfl | hqy
    · exact False.elim ((Set.disjoint_left.mp hpExt) hy hqRoot)
    · exact False.elim ((Set.disjoint_left.mp hExt) hy hqy)

end SwitchingQuad

/-- Pairwise disjoint modified-edge footprints; interior vertices may repeat. -/
def EdgeDisjointSwitchingFootprints {V : Type*} (L : List (SwitchingQuad V)) : Prop :=
  L.Pairwise (fun p q => Disjoint p.footprint q.footprint)

/-- The paper's isolated exterior triples imply the correct finite-family
edge-disjointness condition without requiring distinct interior leaves. -/
theorem boundary_family_edge_disjoint {V : Type*} (L : List (SwitchingQuad V)) (T : Set V)
    (hroot : ∀ q ∈ L, q.a ∈ T) (hext : ∀ q ∈ L, Disjoint q.exterior T)
    (htriples : L.Pairwise (fun p q => Disjoint p.exterior q.exterior)) :
    EdgeDisjointSwitchingFootprints L := by
  induction L with
  | nil => exact List.Pairwise.nil
  | cons p ps ih =>
      apply List.pairwise_cons.mpr
      constructor
      · intro q hq
        exact p.footprint_disjoint_of_boundary q T (hext p List.mem_cons_self)
          (hroot q (List.mem_cons_of_mem _ hq)) ((List.pairwise_cons.mp htriples).1 q hq)
      · exact ih (fun q hq => hroot q (List.mem_cons_of_mem _ hq))
          (fun q hq => hext q (List.mem_cons_of_mem _ hq)) (List.pairwise_cons.mp htriples).2

/-- After the first switch, all remaining disjoint switches are still admissible. -/
theorem edge_tail_switches_admissible {V : Type*} (q : SwitchingQuad V)
    (qs : List (SwitchingQuad V)) (G : SimpleGraph V)
    (hdis : EdgeDisjointSwitchingFootprints (q :: qs)) (ha : SwitchingFamilyAdmissible (q :: qs) G) :
    SwitchingFamilyAdmissible qs (q.apply G) := by
  intro p hp
  have hd : Disjoint q.footprint p.footprint := (List.pairwise_cons.mp hdis).1 p hp
  exact q.admissible_after_edge_disjoint p G hd (ha p (List.mem_cons_of_mem _ hp))

/-- A disjoint admissible family is restored by its reverse inverse family. -/
theorem edge_applySwitches_inverse_restore {V : Type*} (L : List (SwitchingQuad V))
    (G : SimpleGraph V) (hdis : EdgeDisjointSwitchingFootprints L) (ha : SwitchingFamilyAdmissible L G) :
    applySwitches (inverseSwitches L) (applySwitches L G) = G := by
  induction L generalizing G with
  | nil => rfl
  | cons q qs ih =>
      have htail := edge_tail_switches_admissible q qs G hdis ha
      have hd := (List.pairwise_cons.mp hdis).2
      rw [inverseSwitches_cons, applySwitches_append]
      simp only [applySwitches_cons, applySwitches_nil]
      rw [ih (q.apply G) hd htail]
      exact q.inverse_apply G (ha q (List.mem_cons_self))

/-- The switched graph is independent of how a disjoint family is enumerated.
Admissibility is not needed for order independence itself. -/
theorem edge_applySwitches_perm {V : Type*} {L K : List (SwitchingQuad V)} (hp : L.Perm K)
    (hdis : EdgeDisjointSwitchingFootprints L) (G : SimpleGraph V) :
    applySwitches L G = applySwitches K G := by
  revert hdis
  induction hp generalizing G with
  | nil => intro _; rfl
  | @cons q L K hperm ih =>
      intro hdis
      exact ih (q.apply G) (List.pairwise_cons.mp hdis).2
  | swap p q L =>
      intro hdis
      have hqd : Disjoint q.footprint p.footprint :=
        (List.pairwise_cons.mp hdis).1 p (by simp)
      simp only [applySwitches_cons]
      rw [q.commute_of_edge_disjoint p G hqd]
  | @trans L K M h₁ h₂ ih₁ ih₂ =>
      intro hdis
      have hdisK : EdgeDisjointSwitchingFootprints K :=
        (h₁.pairwise_iff (fun {_ _} h => h.symm)).mp hdis
      exact (ih₁ G hdis).trans (ih₂ G hdisK)

/-- Disjointness of footprints is unchanged by reversing and inverting a family. -/
theorem edge_inverseSwitches_disjoint {V : Type*} (L : List (SwitchingQuad V))
    (hdis : EdgeDisjointSwitchingFootprints L) : EdgeDisjointSwitchingFootprints (inverseSwitches L) := by
  unfold EdgeDisjointSwitchingFootprints inverseSwitches
  rw [List.pairwise_map, List.pairwise_reverse]
  simp only [SwitchingQuad.footprint_inverse]
  exact List.Pairwise.imp (fun {_ _} h => h.symm) hdis

/-- An admissible switching stays admissible after any family disjoint from it.
The other switches do not need to be admissible for this locality statement. -/
theorem edge_admissible_after_switches {V : Type*} (q : SwitchingQuad V)
    (L : List (SwitchingQuad V)) (G : SimpleGraph V) (ha : q.Admissible G)
    (hd : ∀ p ∈ L, Disjoint p.footprint q.footprint) : q.Admissible (applySwitches L G) := by
  induction L generalizing G with
  | nil => exact ha
  | cons p ps ih =>
      apply ih (p.apply G)
      · exact p.admissible_after_edge_disjoint q G (hd p List.mem_cons_self) ha
      · exact fun r hr => hd r (List.mem_cons_of_mem _ hr)

/-- Every inverse switch is admissible in the final graph. Thus the inverse
family is valid data as well as algebraically undoing the graph operation. -/
theorem edge_inverseSwitches_admissible {V : Type*} (L : List (SwitchingQuad V))
    (G : SimpleGraph V) (hdis : EdgeDisjointSwitchingFootprints L) (ha : SwitchingFamilyAdmissible L G) :
    SwitchingFamilyAdmissible (inverseSwitches L) (applySwitches L G) := by
  induction L generalizing G with
  | nil =>
      intro q hq
      simp [inverseSwitches] at hq
  | cons q qs ih =>
      have htail := edge_tail_switches_admissible q qs G hdis ha
      have hd := (List.pairwise_cons.mp hdis).2
      intro p hp
      simp only [inverseSwitches_cons, List.mem_append, List.mem_singleton] at hp
      rcases hp with hptail | rfl
      · exact ih (q.apply G) hd htail p hptail
      · apply edge_admissible_after_switches q.inverse qs (q.apply G)
        · exact q.inverse_admissible G (ha q List.mem_cons_self)
        · intro p hp
          rw [SwitchingQuad.footprint_inverse]
          exact ((List.pairwise_cons.mp hdis).1 p hp).symm

/-- The actual enlarged state: graph together with a fixed admissible family
having disjoint footprints. This is not the paper's complete I/J-selected state. -/
def EdgeDisjointSwitchingState (V : Type*) :=
  {s : SimpleGraph V × List (SwitchingQuad V) //
    EdgeDisjointSwitchingFootprints s.2 ∧ SwitchingFamilyAdmissible s.2 s.1}

/-- Switch the graph and reverse the oriented data; validity is proved. -/
def reverseEdgeSwitchingState {V : Type*} (s : EdgeDisjointSwitchingState V) :
    EdgeDisjointSwitchingState V :=
  ⟨(applySwitches s.val.2 s.val.1, inverseSwitches s.val.2),
    edge_inverseSwitches_disjoint s.val.2 s.property.1,
    edge_inverseSwitches_admissible s.val.2 s.val.1 s.property.1 s.property.2⟩

/-- A genuine involution of graph-plus-data states for disjoint families. -/
theorem reverseEdgeSwitchingState_involutive {V : Type*} :
    Function.Involutive (@reverseEdgeSwitchingState V) := by
  intro s
  apply Subtype.ext
  apply Prod.ext
  · exact edge_applySwitches_inverse_restore s.val.2 s.val.1 s.property.1 s.property.2
  · exact inverseSwitches_inverse s.val.2

/-- The disjoint-family graph-plus-data involution as a permutation. -/
def edgeDisjointSwitchingPermutation (V : Type*) : Equiv.Perm (EdgeDisjointSwitchingState V) :=
  Function.Involutive.toPerm reverseEdgeSwitchingState reverseEdgeSwitchingState_involutive

section Degrees
variable {V : Type*} [Fintype V]
noncomputable local instance edgeFamilySwitchingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Every degree is preserved by a finite disjoint admissible switching family. -/
theorem edge_applySwitches_degree (L : List (SwitchingQuad V)) (G : SimpleGraph V)
    (hdis : EdgeDisjointSwitchingFootprints L) (ha : SwitchingFamilyAdmissible L G) (x : V) :
    (applySwitches L G).degree x = G.degree x := by
  induction L generalizing G with
  | nil => rfl
  | cons q qs ih =>
      have htail := edge_tail_switches_admissible q qs G hdis ha
      have hd := (List.pairwise_cons.mp hdis).2
      rw [applySwitches_cons, ih (q.apply G) hd htail]
      exact (ha q List.mem_cons_self).degree_eq x

theorem edge_applySwitches_regular (L : List (SwitchingQuad V)) (G : SimpleGraph V)
    (hdis : EdgeDisjointSwitchingFootprints L) (ha : SwitchingFamilyAdmissible L G) {d : ℕ}
    (hG : G.IsRegularOfDegree d) : (applySwitches L G).IsRegularOfDegree d := by
  intro x
  rw [edge_applySwitches_degree L G hdis ha x]
  exact hG.degree_eq x

end Degrees


end LocalLaw
