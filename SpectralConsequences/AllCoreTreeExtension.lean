import LocalLaw.InfiniteTreeExtension
import LocalLaw.TreeExtensionResolvent

/-! Literal tree extensions with a possibly infinite deficient core.
The finite-degree condition is an actual neighbor-cardinality condition.
No reference estimate is included in these definitions. -/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2400000
namespace SpectralConsequences
open LocalLaw
local instance allCoreDecidable (p : Prop) : Decidable p := Classical.propDecidable p

structure AllCoreGraph (V : Type) (d : ℕ) where
  graph : SimpleGraph V
  locallyFinite : graph.LocallyFinite
  deficit : V → ℕ
  degree_deficit_le : ∀ v, graph.degree v + deficit v ≤ d

attribute [instance] AllCoreGraph.locallyFinite

namespace AllCoreGraph
variable {V : Type} [DecidableEq V] {d : ℕ}

abbrev Slots (g : AllCoreGraph V d) := Σ v : V, Fin (d-g.deficit v-g.graph.degree v)
abbrev Vertex (g : AllCoreGraph V d) := V ⊕ (List (Fin (d-1)) × g.Slots)

def extension (g : AllCoreGraph V d) : SimpleGraph g.Vertex where
  Adj x y := match x,y with
    | Sum.inl v,Sum.inl w => g.graph.Adj v w
    | Sum.inl v,Sum.inr p => p.1=[] ∧ p.2.1=v
    | Sum.inr p,Sum.inl v => p.1=[] ∧ p.2.1=v
    | Sum.inr p,Sum.inr q => p.2=q.2 ∧ wordTreeAdj p.1 q.1
  symm := by
    intro x y
    cases x <;> cases y
    · exact fun h => g.graph.symm h
    · exact id
    · exact id
    · exact fun h => ⟨h.1.symm,wordTreeAdj_symm h.2⟩
  loopless := by
    intro x
    cases x with
    | inl v => exact g.graph.loopless v
    | inr p => exact fun h => wordTreeAdj_irrefl p.1 h.2

def parent (g : AllCoreGraph V d) (w : List (Fin (d-1))) (s : g.Slots) : g.Vertex :=
  if w=[] then Sum.inl s.1 else Sum.inr (w.dropLast,s)

def neighbors (g : AllCoreGraph V d) : g.Vertex → Finset g.Vertex
  | Sum.inl v => (g.graph.neighborFinset v).image Sum.inl ∪
      (Finset.univ : Finset (Fin (d-g.deficit v-g.graph.degree v))).image
        (fun i => Sum.inr ([],⟨v,i⟩))
  | Sum.inr p => (Finset.univ : Finset (Fin (d-1))).image
      (fun a => Sum.inr (p.1++[a],p.2)) ∪ {g.parent p.1 p.2}

theorem adj_iff_mem_neighbors (g : AllCoreGraph V d) (x y : g.Vertex) :
    g.extension.Adj x y ↔ y∈g.neighbors x := by
  cases x with
  | inl v =>
    cases y with
    | inl w => simp [extension,neighbors,SimpleGraph.mem_neighborFinset]
    | inr p =>
      rcases p with ⟨w,⟨u,i⟩⟩
      by_cases h : u=v
      · subst u
        simp [extension,neighbors]
      · simp [extension,neighbors,h,Ne.symm h]
  | inr p =>
    rcases p with ⟨w,s⟩
    cases y with
    | inl v =>
      by_cases hw : w=[] <;> simp [extension,neighbors,parent,hw,eq_comm]
    | inr q =>
      rcases q with ⟨y,t⟩
      by_cases hw : w=[]
      · subst w
        simp [extension,neighbors,parent,wordTreeAdj_nil_iff,Prod.mk.injEq,eq_comm,and_comm]
      · simp only [extension,neighbors,Finset.mem_union,Finset.mem_image,
          Finset.mem_univ,true_and,Finset.mem_singleton,parent,if_neg hw,Sum.inr.injEq,
          Prod.mk.injEq,wordTreeAdj_parent_iff,hw,true_and]
        simp only [if_false,Sum.inr.injEq,Prod.mk.injEq]
        constructor
        · rintro ⟨hst,hy|⟨a,hy⟩⟩
          · exact Or.inr ⟨hy.2,hst.symm⟩
          · exact Or.inl ⟨a,hy.symm,hst⟩
        · rintro (⟨a,hy,hst⟩|⟨hy,hst⟩)
          · exact ⟨hst,Or.inr ⟨a,hy.symm⟩⟩
          · exact ⟨hst.symm,Or.inl ⟨hw,hy⟩⟩

instance extensionLocallyFinite (g : AllCoreGraph V d) : g.extension.LocallyFinite := fun x => by
  have hf : {y | g.extension.Adj x y}.Finite := (g.neighbors x).finite_toSet.subset
    (fun y hy => (g.adj_iff_mem_neighbors x y).mp hy)
  exact hf.fintype

theorem neighborFinset (g : AllCoreGraph V d) (x : g.Vertex) :
    g.extension.neighborFinset x=g.neighbors x := by
  ext y
  exact (SimpleGraph.mem_neighborFinset _ _ _).trans (g.adj_iff_mem_neighbors x y)

theorem extension_degree_le (g : AllCoreGraph V d) (hd : 1≤d) (x : g.Vertex) :
    g.extension.degree x≤d := by
  change (g.extension.neighborFinset x).card≤d
  rw [g.neighborFinset]
  cases x with
  | inl v =>
    apply (Finset.card_union_le _ _).trans
    have h₁ := Finset.card_image_le (s:=g.graph.neighborFinset v)
      (f:=fun w : V => (Sum.inl w:g.Vertex))
    have h₂ := Finset.card_image_le
      (s:=(Finset.univ : Finset (Fin (d-g.deficit v-g.graph.degree v))))
      (f:=fun i => (Sum.inr ([],⟨v,i⟩):g.Vertex))
    simp only [Finset.card_univ,Fintype.card_fin] at h₂
    have hh := g.degree_deficit_le v
    apply (Nat.add_le_add h₁ h₂).trans
    change g.graph.degree v+(d-g.deficit v-g.graph.degree v)≤d
    omega
  | inr p =>
    apply (Finset.card_union_le _ _).trans
    have hh := Finset.card_image_le (s:=(Finset.univ : Finset (Fin (d-1))))
      (f:=fun a : Fin (d-1) => (Sum.inr (p.1++[a],p.2):g.Vertex))
    simp only [Finset.card_univ,Fintype.card_fin,Finset.card_singleton] at hh ⊢
    omega

def green (g : AllCoreGraph V d) (hd : 1≤d) (z : ℂ) (i j : V) : ℂ :=
  g.extension.infiniteGreen d (g.extension_degree_le hd) z (Sum.inl i) (Sum.inl j)

end AllCoreGraph
end SpectralConsequences
