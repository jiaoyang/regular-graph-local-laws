import SpectralConsequences.AllCoreTreeExtension

/-! A fixed ambient vertex type for varying tree extensions. Unused degree
slots are isolated vertices, so no component containing a core vertex changes.
-/
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2400000
namespace SpectralConsequences
open LocalLaw
local instance paddedExtensionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

abbrev PaddedVertex (V : Type) (d : ℕ) := V ⊕ (List (Fin (d-1)) × (V × Fin d))
namespace AllCoreGraph
variable {V : Type} [DecidableEq V] {d : ℕ}

def missing (g : AllCoreGraph V d) (v : V) := d-g.deficit v-g.graph.degree v
omit [DecidableEq V] in
theorem missing_le (g : AllCoreGraph V d) (v : V) : g.missing v≤d :=
  (Nat.sub_le _ _).trans (Nat.sub_le _ _)

def slotEmbedding (g : AllCoreGraph V d) (v : V) : Fin (g.missing v) ↪ Fin d where
  toFun i := ⟨i.val,i.isLt.trans_le (g.missing_le v)⟩
  inj' _ _ h := Fin.ext (congrArg (fun k : Fin d => k.val) h)

def slotFinset (g : AllCoreGraph V d) (v : V) : Finset (Fin d) :=
  Finset.univ.map (g.slotEmbedding v)

omit [DecidableEq V] in
theorem mem_slotFinset (g : AllCoreGraph V d) (v : V) (i : Fin d) :
    i∈g.slotFinset v ↔ i.val<g.missing v := by
  simp only [slotFinset,Finset.mem_map,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨j,rfl⟩
    exact j.isLt
  · intro h
    exact ⟨⟨i.val,h⟩,Fin.ext rfl⟩

def active (g : AllCoreGraph V d) (s : V × Fin d) : Prop := s.2.val<g.missing s.1

def padded (g : AllCoreGraph V d) : SimpleGraph (PaddedVertex V d) where
  Adj x y := match x,y with
    | Sum.inl v,Sum.inl w => g.graph.Adj v w
    | Sum.inl v,Sum.inr p => p.1=[] ∧ p.2.1=v ∧ g.active p.2
    | Sum.inr p,Sum.inl v => p.1=[] ∧ p.2.1=v ∧ g.active p.2
    | Sum.inr p,Sum.inr q => p.2=q.2 ∧ g.active p.2 ∧ wordTreeAdj p.1 q.1
  symm := by
    intro x y
    cases x <;> cases y
    · exact fun h => g.graph.symm h
    · exact id
    · exact id
    · rintro ⟨h,ha,hw⟩
      exact ⟨h.symm,h ▸ ha,wordTreeAdj_symm hw⟩
  loopless := by
    intro x
    cases x with
    | inl v => exact g.graph.loopless v
    | inr p => exact fun h => wordTreeAdj_irrefl p.1 h.2.2

def paddedParent (_g : AllCoreGraph V d) (w : List (Fin (d-1))) (s : V × Fin d) :
    PaddedVertex V d := if w=[] then Sum.inl s.1 else Sum.inr (w.dropLast,s)

def paddedNeighbors (g : AllCoreGraph V d) : PaddedVertex V d → Finset (PaddedVertex V d)
  | Sum.inl v => (g.graph.neighborFinset v).image Sum.inl ∪
      (g.slotFinset v).image (fun k => Sum.inr ([],(v,k)))
  | Sum.inr p => if g.active p.2 then
      (Finset.univ : Finset (Fin (d-1))).image (fun a => Sum.inr (p.1++[a],p.2)) ∪
        {g.paddedParent p.1 p.2} else ∅

theorem padded_adj_iff_neighbors (g : AllCoreGraph V d) (x y : PaddedVertex V d) :
    g.padded.Adj x y ↔ y∈g.paddedNeighbors x := by
  cases x with
  | inl v =>
    cases y with
    | inl w => simp [padded,paddedNeighbors,SimpleGraph.mem_neighborFinset]
    | inr p =>
      rcases p with ⟨w,u,k⟩
      by_cases h : u=v
      · subst u
        simp [padded,paddedNeighbors,mem_slotFinset,active,and_comm]
      · simp [padded,paddedNeighbors,mem_slotFinset,active,h,Ne.symm h]
  | inr p =>
    rcases p with ⟨w,s⟩
    by_cases hs : g.active s
    · cases y with
      | inl v =>
        by_cases hw : w=[] <;> simp [padded,paddedNeighbors,paddedParent,hs,hw,eq_comm]
      | inr q =>
        rcases q with ⟨y,t⟩
        by_cases hw : w=[]
        · subst w
          simp [padded,paddedNeighbors,paddedParent,hs,wordTreeAdj_nil_iff,
            Prod.mk.injEq,eq_comm,and_comm]
        · by_cases hst : s=t
          · subst t
            simp [padded,paddedNeighbors,paddedParent,hs,hw,
              wordTreeAdj_parent_iff,eq_comm,or_comm]
          · simp [padded,paddedNeighbors,paddedParent,hs,hw,hst,Ne.symm hst]
    · cases y with
      | inl v => simp [padded,paddedNeighbors,hs]
      | inr q => simp [padded,paddedNeighbors,hs]

instance paddedLocallyFinite (g : AllCoreGraph V d) : g.padded.LocallyFinite := fun x => by
  exact ((g.paddedNeighbors x).finite_toSet.subset
    (fun y hy => (g.padded_adj_iff_neighbors x y).mp hy)).fintype

theorem padded_neighborFinset (g : AllCoreGraph V d) (x : PaddedVertex V d) :
    g.padded.neighborFinset x=g.paddedNeighbors x := by
  ext y
  exact (SimpleGraph.mem_neighborFinset _ _ _).trans (g.padded_adj_iff_neighbors x y)

theorem padded_degree_le (g : AllCoreGraph V d) (hd : 1≤d) (x : PaddedVertex V d) :
    g.padded.degree x≤d := by
  change (g.padded.neighborFinset x).card≤d
  rw [g.padded_neighborFinset]
  cases x with
  | inl v =>
    apply (Finset.card_union_le _ _).trans
    have h₁ := Finset.card_image_le (s:=g.graph.neighborFinset v)
      (f:=fun w : V => (Sum.inl w:PaddedVertex V d))
    have h₂ := Finset.card_image_le (s:=g.slotFinset v)
      (f:=fun k => (Sum.inr ([],(v,k)):PaddedVertex V d))
    have hc : (g.slotFinset v).card=g.missing v := by simp [slotFinset]
    rw [hc] at h₂
    apply (Nat.add_le_add h₁ h₂).trans
    change g.graph.degree v+(d-g.deficit v-g.graph.degree v)≤d
    have hh := g.degree_deficit_le v
    omega
  | inr p =>
    by_cases hs : g.active p.2
    · simp only [paddedNeighbors,if_pos hs]
      apply (Finset.card_union_le _ _).trans
      have hh := Finset.card_image_le (s:=(Finset.univ : Finset (Fin (d-1))))
        (f:=fun a : Fin (d-1) => (Sum.inr (p.1++[a],p.2):PaddedVertex V d))
      simp only [Finset.card_univ,Fintype.card_fin,Finset.card_singleton] at hh ⊢
      omega
    · simp [paddedNeighbors,hs]

end AllCoreGraph
end SpectralConsequences
