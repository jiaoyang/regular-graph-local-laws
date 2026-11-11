import Mathlib

/-!
# Simple edge switchings

Definition 3.1 of Huang--Yau: replace the disjoint edges {a,b},{c,d} by
{a,d},{b,c}. Construction uses the simple-graph lattice, so symmetry and absence
of loops are built in. Admissibility additionally ensures that two existing
edges are removed and two genuinely new edges are inserted.
-/

namespace LocalLaw

variable {V : Type*}

/-- Edges removed by the oriented switching (a,b),(c,d). -/
def switchingRemoved (a b c d : V) : SimpleGraph V :=
  SimpleGraph.edge a b ⊔ SimpleGraph.edge c d

/-- Edges inserted by the oriented switching (a,b),(c,d). -/
def switchingAdded (a b c d : V) : SimpleGraph V :=
  SimpleGraph.edge a d ⊔ SimpleGraph.edge b c

/-- The standard simple switching is always a simple graph. -/
def simpleSwitch (G : SimpleGraph V) (a b c d : V) : SimpleGraph V :=
  (G \ switchingRemoved a b c d) ⊔ switchingAdded a b c d

/-- Four distinct endpoints, old edges present, and new edges absent. -/
structure SimpleSwitchingAdmissible (G : SimpleGraph V) (a b c d : V) : Prop where
  ab_ne : a ≠ b
  ac_ne : a ≠ c
  ad_ne : a ≠ d
  bc_ne : b ≠ c
  bd_ne : b ≠ d
  cd_ne : c ≠ d
  old_ab : G.Adj a b
  old_cd : G.Adj c d
  new_ad : ¬G.Adj a d
  new_bc : ¬G.Adj b c

namespace SimpleSwitchingAdmissible

variable {G : SimpleGraph V} {a b c d : V}

theorem removed_le (h : SimpleSwitchingAdmissible G a b c d) :
    switchingRemoved a b c d ≤ G := by
  apply sup_le
  · exact sup_eq_left.mp (G.sup_edge_of_adj h.old_ab)
  · exact sup_eq_left.mp (G.sup_edge_of_adj h.old_cd)

theorem added_disjoint (h : SimpleSwitchingAdmissible G a b c d) :
    Disjoint G (switchingAdded a b c d) := by
  exact disjoint_sup_right.mpr
    ⟨(G.disjoint_edge).mpr h.new_ad, (G.disjoint_edge).mpr h.new_bc⟩

/-- The exact new adjacency row at endpoint a. -/
theorem adj_a (h : SimpleSwitchingAdmissible G a b c d) (y : V) :
    (simpleSwitch G a b c d).Adj a y ↔ (G.Adj a y ∧ y ≠ b) ∨ y = d := by
  simp only [simpleSwitch, switchingRemoved, switchingAdded, SimpleGraph.sup_adj,
    SimpleGraph.sdiff_adj, SimpleGraph.edge_adj]
  have hne : G.Adj a y → a ≠ y := fun hadj => hadj.ne
  rcases h with ⟨hab, hac, had, hbc, hbd, hcd, _, _, _, _⟩
  aesop

/-- The exact new adjacency row at endpoint b. -/
theorem adj_b (h : SimpleSwitchingAdmissible G a b c d) (y : V) :
    (simpleSwitch G a b c d).Adj b y ↔ (G.Adj b y ∧ y ≠ a) ∨ y = c := by
  simp only [simpleSwitch, switchingRemoved, switchingAdded, SimpleGraph.sup_adj,
    SimpleGraph.sdiff_adj, SimpleGraph.edge_adj]
  have hne : G.Adj b y → b ≠ y := fun hadj => hadj.ne
  rcases h with ⟨hab, hac, had, hbc, hbd, hcd, _, _, _, _⟩
  aesop

/-- The exact new adjacency row at endpoint c. -/
theorem adj_c (h : SimpleSwitchingAdmissible G a b c d) (y : V) :
    (simpleSwitch G a b c d).Adj c y ↔ (G.Adj c y ∧ y ≠ d) ∨ y = b := by
  simp only [simpleSwitch, switchingRemoved, switchingAdded, SimpleGraph.sup_adj,
    SimpleGraph.sdiff_adj, SimpleGraph.edge_adj]
  have hne : G.Adj c y → c ≠ y := fun hadj => hadj.ne
  rcases h with ⟨hab, hac, had, hbc, hbd, hcd, _, _, _, _⟩
  aesop

/-- The exact new adjacency row at endpoint d. -/
theorem adj_d (h : SimpleSwitchingAdmissible G a b c d) (y : V) :
    (simpleSwitch G a b c d).Adj d y ↔ (G.Adj d y ∧ y ≠ c) ∨ y = a := by
  simp only [simpleSwitch, switchingRemoved, switchingAdded, SimpleGraph.sup_adj,
    SimpleGraph.sdiff_adj, SimpleGraph.edge_adj]
  have hne : G.Adj d y → d ≠ y := fun hadj => hadj.ne
  rcases h with ⟨hab, hac, had, hbc, hbd, hcd, _, _, _, _⟩
  aesop

/-- Adjacency away from the four endpoints is unchanged. -/
theorem adj_away (_h : SimpleSwitchingAdmissible G a b c d) (x y : V)
    (ha : x ≠ a) (hb : x ≠ b) (hc : x ≠ c) (hd : x ≠ d) :
    (simpleSwitch G a b c d).Adj x y ↔ G.Adj x y := by
  simp [simpleSwitch, switchingRemoved, switchingAdded, SimpleGraph.sup_adj,
    SimpleGraph.sdiff_adj, SimpleGraph.edge_adj, ha, hb, hc, hd]

/-- Replacing old by new and then new by old recovers the original graph. -/
theorem switch_inverse (h : SimpleSwitchingAdmissible G a b c d) :
    simpleSwitch (simpleSwitch G a b c d) a d c b = G := by
  have hr : switchingRemoved a d c b = switchingAdded a b c d := by
    unfold switchingRemoved switchingAdded
    rw [SimpleGraph.edge_comm c b]
  have ha : switchingAdded a d c b = switchingRemoved a b c d := by
    unfold switchingRemoved switchingAdded
    rw [SimpleGraph.edge_comm d c]
  have hd : Disjoint (G \ switchingRemoved a b c d) (switchingAdded a b c d) :=
    h.added_disjoint.mono_left sdiff_le
  rw [simpleSwitch, hr, ha, simpleSwitch, sup_sdiff_distrib,
    sdiff_self, sup_bot_eq, hd.sdiff_eq_left, sdiff_sup_cancel h.removed_le]

/-- The reversed oriented switching is admissible in the switched graph. -/
theorem inverse_admissible (h : SimpleSwitchingAdmissible G a b c d) :
    SimpleSwitchingAdmissible (simpleSwitch G a b c d) a d c b := by
  refine ⟨h.ad_ne, h.ac_ne, h.ab_ne, h.cd_ne.symm, h.bd_ne.symm, h.bc_ne.symm,
    ?_, ?_, ?_, ?_⟩
  · exact (h.adj_a d).mpr (Or.inr rfl)
  · exact (h.adj_c b).mpr (Or.inr rfl)
  · rw [h.adj_a b]
    simp [h.bd_ne]
  · rw [h.adj_d c]
    simp [h.ac_ne.symm]

section Finite

variable [Fintype V]

noncomputable local instance switchingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Switching replaces exactly one neighbor at endpoint a. -/
theorem neighborFinset_a (h : SimpleSwitchingAdmissible G a b c d) :
    (simpleSwitch G a b c d).neighborFinset a = insert d ((G.neighborFinset a).erase b) := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset, h.adj_a, Finset.mem_insert,
    Finset.mem_erase]
  tauto

theorem neighborFinset_b (h : SimpleSwitchingAdmissible G a b c d) :
    (simpleSwitch G a b c d).neighborFinset b = insert c ((G.neighborFinset b).erase a) := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset, h.adj_b, Finset.mem_insert,
    Finset.mem_erase]
  tauto

theorem neighborFinset_c (h : SimpleSwitchingAdmissible G a b c d) :
    (simpleSwitch G a b c d).neighborFinset c = insert b ((G.neighborFinset c).erase d) := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset, h.adj_c, Finset.mem_insert,
    Finset.mem_erase]
  tauto

theorem neighborFinset_d (h : SimpleSwitchingAdmissible G a b c d) :
    (simpleSwitch G a b c d).neighborFinset d = insert a ((G.neighborFinset d).erase c) := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset, h.adj_d, Finset.mem_insert,
    Finset.mem_erase]
  tauto

theorem neighborFinset_away (h : SimpleSwitchingAdmissible G a b c d) (x : V)
    (ha : x ≠ a) (hb : x ≠ b) (hc : x ≠ c) (hd : x ≠ d) :
    (simpleSwitch G a b c d).neighborFinset x = G.neighborFinset x := by
  ext y
  simpa only [SimpleGraph.mem_neighborFinset] using h.adj_away x y ha hb hc hd

omit [Fintype V] in
private theorem card_insert_erase_neighbor (s : Finset V) (old new : V)
    (hold : old ∈ s) (hnew : new ∉ s) :
    (insert new (s.erase old)).card = s.card := by
  have hn : new ∉ s.erase old := fun h => hnew (Finset.mem_of_mem_erase h)
  rw [Finset.card_insert_of_not_mem hn, Finset.card_erase_of_mem hold]
  have hpos : 0 < s.card := Finset.card_pos.mpr ⟨old, hold⟩
  omega

/-- Every vertex has exactly the same degree after an admissible switching. -/
theorem degree_eq (h : SimpleSwitchingAdmissible G a b c d) (x : V) :
    (simpleSwitch G a b c d).degree x = G.degree x := by
  by_cases ha : x = a
  · subst x
    change ((simpleSwitch G a b c d).neighborFinset a).card = (G.neighborFinset a).card
    rw [h.neighborFinset_a]
    apply card_insert_erase_neighbor
    · exact (G.mem_neighborFinset a b).mpr h.old_ab
    · exact fun hn => h.new_ad ((G.mem_neighborFinset a d).mp hn)
  by_cases hb : x = b
  · subst x
    change ((simpleSwitch G a b c d).neighborFinset b).card = (G.neighborFinset b).card
    rw [h.neighborFinset_b]
    apply card_insert_erase_neighbor
    · exact (G.mem_neighborFinset b a).mpr h.old_ab.symm
    · exact fun hn => h.new_bc ((G.mem_neighborFinset b c).mp hn)
  by_cases hc : x = c
  · subst x
    change ((simpleSwitch G a b c d).neighborFinset c).card = (G.neighborFinset c).card
    rw [h.neighborFinset_c]
    apply card_insert_erase_neighbor
    · exact (G.mem_neighborFinset c d).mpr h.old_cd
    · exact fun hn => h.new_bc ((G.mem_neighborFinset c b).mp hn).symm
  by_cases hd : x = d
  · subst x
    change ((simpleSwitch G a b c d).neighborFinset d).card = (G.neighborFinset d).card
    rw [h.neighborFinset_d]
    apply card_insert_erase_neighbor
    · exact (G.mem_neighborFinset d c).mpr h.old_cd.symm
    · exact fun hn => h.new_ad ((G.mem_neighborFinset d a).mp hn).symm
  change ((simpleSwitch G a b c d).neighborFinset x).card = (G.neighborFinset x).card
  rw [h.neighborFinset_away x ha hb hc hd]

/-- A standard switching preserves d-regularity. -/
theorem regular (h : SimpleSwitchingAdmissible G a b c d) {degree : ℕ}
    (hG : G.IsRegularOfDegree degree) : (simpleSwitch G a b c d).IsRegularOfDegree degree := by
  intro x
  rw [h.degree_eq x]
  exact hG.degree_eq x

end Finite

end SimpleSwitchingAdmissible

end LocalLaw
