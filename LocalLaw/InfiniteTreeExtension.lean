import LocalLaw.CavityTreeWords
import LocalLaw.BoundedGraphOperator

/-! # The actual infinite tree extension of a finite deficient graph

Every missing degree slot receives one disjoint infinite word tree. The
literal graph is locally finite and its degree is bounded by d, supplying
the actual bounded self-adjoint ell2 operator of the previous module.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance infiniteTreeExtensionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem wordTreeAdj_parent_iff {A : Type*} (x y : List A) :
    wordTreeAdj x y ↔ (x≠[] ∧ y=x.dropLast) ∨ ∃ a,y=x++[a] := by
  constructor
  · rintro ⟨a,h|h⟩
    · apply Or.inl
      constructor
      · rw [h]
        simp
      · rw [h]
        simp
    · exact Or.inr ⟨a,h⟩
  · rintro (⟨hx,rfl⟩|⟨a,h⟩)
    · exact ⟨x.getLast hx,Or.inl (List.dropLast_append_getLast hx).symm⟩
    · exact ⟨a,Or.inr h⟩

namespace DeficientGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

abbrev TreeExtensionVertex (g : DeficientGraph V d) := V ⊕ (List (Fin (d-1)) × g.treeExtensionSlots)

def treeExtension (g : DeficientGraph V d) : SimpleGraph g.TreeExtensionVertex where
  Adj x y := match x,y with
    | Sum.inl v,Sum.inl w => g.graph.Adj v w
    | Sum.inl v,Sum.inr p => p.1=[] ∧ p.2.1=v
    | Sum.inr p,Sum.inl v => p.1=[] ∧ p.2.1=v
    | Sum.inr p,Sum.inr q => p.2=q.2 ∧ wordTreeAdj p.1 q.1
  symm := by
    intro x y
    cases x with
    | inl v =>
      cases y with
      | inl w => exact fun h => g.graph.symm h
      | inr p => exact id
    | inr p =>
      cases y with
      | inl v => exact id
      | inr q => exact fun h => ⟨h.1.symm,wordTreeAdj_symm h.2⟩
  loopless := by
    intro x
    cases x with
    | inl v => exact g.graph.loopless v
    | inr p => exact fun h => wordTreeAdj_irrefl p.1 h.2

def treeExtensionParent (g : DeficientGraph V d) (w : List (Fin (d-1))) (s : g.treeExtensionSlots) :
    g.TreeExtensionVertex := if w=[] then Sum.inl s.1 else Sum.inr (w.dropLast,s)

def treeExtensionNeighbors (g : DeficientGraph V d) : g.TreeExtensionVertex → Finset g.TreeExtensionVertex
  | Sum.inl v => (g.graph.neighborFinset v).image Sum.inl ∪
      (Finset.univ.filter (fun s : g.treeExtensionSlots => s.1=v)).image (fun s => Sum.inr ([],s))
  | Sum.inr p => (Finset.univ : Finset (Fin (d-1))).image (fun a => Sum.inr (p.1++[a],p.2)) ∪
      {g.treeExtensionParent p.1 p.2}

theorem treeExtension_adj_iff_mem_neighbors (g : DeficientGraph V d) (x y : g.TreeExtensionVertex) :
    g.treeExtension.Adj x y ↔ y∈g.treeExtensionNeighbors x := by
  cases x with
  | inl v =>
    cases y with
    | inl w => simp [treeExtension,treeExtensionNeighbors,SimpleGraph.mem_neighborFinset]
    | inr p =>
      rcases p with ⟨w,s⟩
      simp [treeExtension,treeExtensionNeighbors,Prod.mk.injEq,eq_comm,and_comm]
  | inr p =>
    rcases p with ⟨w,s⟩
    cases y with
    | inl v =>
      by_cases hw : w=[] <;> simp [treeExtension,treeExtensionNeighbors,treeExtensionParent,hw,eq_comm]
    | inr q =>
      rcases q with ⟨y,t⟩
      by_cases hw : w=[]
      · subst w
        simp [treeExtension,treeExtensionNeighbors,treeExtensionParent,wordTreeAdj_nil_iff,
          Prod.mk.injEq,eq_comm,and_comm]
      · simp only [treeExtension,treeExtensionNeighbors,Finset.mem_union,Finset.mem_image,
          Finset.mem_univ,true_and,Finset.mem_singleton,treeExtensionParent,if_neg hw,Sum.inr.injEq,
          Prod.mk.injEq,wordTreeAdj_parent_iff,hw,true_and]
        simp only [if_false,Sum.inr.injEq,Prod.mk.injEq]
        constructor
        · rintro ⟨hst,hy|⟨a,hy⟩⟩
          · exact Or.inr ⟨hy.2,hst.symm⟩
          · exact Or.inl ⟨a,hy.symm,hst⟩
        · rintro (⟨a,hy,hst⟩|⟨hy,hst⟩)
          · exact ⟨hst,Or.inr ⟨a,hy.symm⟩⟩
          · exact ⟨hst.symm,Or.inl ⟨hw,hy⟩⟩

instance treeExtensionLocallyFinite (g : DeficientGraph V d) : g.treeExtension.LocallyFinite := fun x => by
  have hf : {y | g.treeExtension.Adj x y}.Finite := (g.treeExtensionNeighbors x).finite_toSet.subset
    (fun y hy => (g.treeExtension_adj_iff_mem_neighbors x y).mp hy)
  exact hf.fintype

theorem treeExtension_neighborFinset (g : DeficientGraph V d) (x : g.TreeExtensionVertex) :
    g.treeExtension.neighborFinset x=g.treeExtensionNeighbors x := by
  ext y
  exact (SimpleGraph.mem_neighborFinset _ _ _).trans (g.treeExtension_adj_iff_mem_neighbors x y)

def treeExtensionSlotFiberEquiv (g : DeficientGraph V d) (v : V) :
    {s : g.treeExtensionSlots // s.1=v} ≃ Fin (d-g.deficit v-g.graph.degree v) where
  toFun := fun ⟨⟨w,i⟩,h⟩ => by cases h; exact i
  invFun i := ⟨⟨v,i⟩,rfl⟩
  left_inv := by rintro ⟨⟨w,i⟩,h⟩; cases h; rfl
  right_inv _ := rfl

theorem treeExtensionSlots_fiber_card (g : DeficientGraph V d) (v : V) :
    (Finset.univ.filter (fun s : g.treeExtensionSlots => s.1=v)).card=d-g.deficit v-g.graph.degree v := by
  have h := Fintype.card_congr (g.treeExtensionSlotFiberEquiv v)
  simpa only [Fintype.card_subtype,Fintype.card_fin] using h

theorem treeExtension_degree_le (g : DeficientGraph V d) (hd : 1≤d) (x : g.TreeExtensionVertex) :
    g.treeExtension.degree x≤d := by
  change (g.treeExtension.neighborFinset x).card≤d
  rw [g.treeExtension_neighborFinset]
  cases x with
  | inl v =>
    apply (Finset.card_union_le _ _).trans
    change _≤d
    have h₁ := Finset.card_image_le (s:=g.graph.neighborFinset v) (f:=fun w : V => (Sum.inl w:g.TreeExtensionVertex))
    have h₂ := Finset.card_image_le (s:=Finset.univ.filter (fun s : g.treeExtensionSlots => s.1=v))
      (f:=fun s : g.treeExtensionSlots => (Sum.inr ([],s):g.TreeExtensionVertex))
    rw [g.treeExtensionSlots_fiber_card] at h₂
    have hh := g.degree_deficit_le v
    have hsum : (g.graph.neighborFinset v).card+(d-g.deficit v-g.graph.degree v)≤d := by
      change g.graph.degree v+(d-g.deficit v-g.graph.degree v)≤d
      omega
    exact (Nat.add_le_add h₁ h₂).trans hsum
  | inr p =>
    apply (Finset.card_union_le _ _).trans
    have hh := Finset.card_image_le (s:=(Finset.univ : Finset (Fin (d-1))))
      (f:=fun a : Fin (d-1) => (Sum.inr (p.1++[a],p.2):g.TreeExtensionVertex))
    simp only [Finset.card_univ,Fintype.card_fin,Finset.card_singleton] at hh ⊢
    omega

end DeficientGraph
end LocalLaw
