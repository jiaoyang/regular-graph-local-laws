import LocalLaw.InfiniteTreeExtension

/-! # Exact finite graft graph truncations of the actual infinite extension -/

noncomputable section
namespace LocalLaw
local instance treeExtensionTruncationsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

def dirichletGraftEmbedding (g : DeficientGraph V d) (n : ℕ) :
    (V ⊕ (CavityTreeIndex (d-1) n × g.treeExtensionSlots)) ↪ g.TreeExtensionVertex where
  toFun := fun x => match x with
    | Sum.inl v => Sum.inl v
    | Sum.inr p => Sum.inr (cavityTreeWord (d-1) n p.1,p.2)
  inj' := by
    intro x y h
    cases x with
    | inl v =>
      cases y with
      | inl w => exact congrArg Sum.inl (Sum.inl.inj h)
      | inr q => exact False.elim (Sum.noConfusion h)
    | inr p =>
      cases y with
      | inl w => exact False.elim (Sum.noConfusion h)
      | inr q =>
        have hh := Prod.mk.inj (Sum.inr.inj h)
        exact congrArg Sum.inr (Prod.ext (cavityTreeWord_injective (d-1) n hh.1) hh.2)

omit [DecidableEq V] in
@[simp] theorem dirichletGraftEmbedding_core (g : DeficientGraph V d) (n : ℕ) (v : V) :
    g.dirichletGraftEmbedding n (Sum.inl v)=Sum.inl v := rfl

omit [DecidableEq V] in
theorem dirichletGraftEmbedding_adj_iff (g : DeficientGraph V d) (n : ℕ)
    (x y : V ⊕ (CavityTreeIndex (d-1) n × g.treeExtensionSlots)) :
    g.treeExtension.Adj (g.dirichletGraftEmbedding n x) (g.dirichletGraftEmbedding n y)↔
      (g.dirichletGraftGraph n).Adj x y := by
  cases x with
  | inl v =>
    cases y with
    | inl w => rfl
    | inr p =>
      simp only [dirichletGraftEmbedding,Function.Embedding.coeFn_mk,treeExtension,dirichletGraftGraph,
        cavityTreeWord_eq_nil_iff]
  | inr p =>
    cases y with
    | inl w =>
      simp only [dirichletGraftEmbedding,Function.Embedding.coeFn_mk,treeExtension,dirichletGraftGraph,
        cavityTreeWord_eq_nil_iff]
    | inr q =>
      exact and_congr Iff.rfl (cavityTreeWord_adj_iff (d-1) n p.1 q.1).symm

def treeExtensionTruncation (g : DeficientGraph V d) (n : ℕ) : Finset g.TreeExtensionVertex :=
  Finset.univ.map (g.dirichletGraftEmbedding n)

omit [DecidableEq V] in
theorem treeExtensionTruncation_core (g : DeficientGraph V d) (n : ℕ) (v : V) :
    Sum.inl v∈g.treeExtensionTruncation n :=
  Finset.mem_map.mpr ⟨Sum.inl v,Finset.mem_univ _,rfl⟩

omit [DecidableEq V] in
theorem treeExtensionTruncation_tail_iff (g : DeficientGraph V d) (n : ℕ)
    (w : List (Fin (d-1))) (s : g.treeExtensionSlots) :
    Sum.inr (w,s)∈g.treeExtensionTruncation n ↔ w.length≤n := by
  constructor
  · rintro h
    obtain ⟨x,_,hx⟩ := Finset.mem_map.mp h
    cases x with
    | inl v => exact False.elim (Sum.noConfusion hx)
    | inr p =>
      have hh := Prod.mk.inj (Sum.inr.inj hx)
      rw [←hh.1]
      exact cavityTreeWord_length (d-1) n p.1
  · intro hw
    obtain ⟨x,hx⟩ := cavityTreeWord_surjective (d-1) n w hw
    exact Finset.mem_map.mpr ⟨Sum.inr (x,s),Finset.mem_univ _,congrArg (fun w => Sum.inr (w,s)) hx⟩

omit [DecidableEq V] in
theorem treeExtensionTruncation_monotone (g : DeficientGraph V d) : Monotone g.treeExtensionTruncation := by
  intro n m hnm x hx
  cases x with
  | inl v => exact g.treeExtensionTruncation_core m v
  | inr p =>
    exact (g.treeExtensionTruncation_tail_iff m p.1 p.2).mpr
      (((g.treeExtensionTruncation_tail_iff n p.1 p.2).mp hx).trans hnm)

omit [DecidableEq V] in
theorem treeExtensionTruncation_cover (g : DeficientGraph V d) (x : g.TreeExtensionVertex) :
    ∃ n,x∈g.treeExtensionTruncation n := by
  cases x with
  | inl v => exact ⟨0,g.treeExtensionTruncation_core 0 v⟩
  | inr p => exact ⟨p.1.length,(g.treeExtensionTruncation_tail_iff _ p.1 p.2).mpr le_rfl⟩

def treeExtensionTruncationEquiv (g : DeficientGraph V d) (n : ℕ) :
    (V ⊕ (CavityTreeIndex (d-1) n × g.treeExtensionSlots)) ≃ g.treeExtensionTruncation n :=
  Equiv.ofBijective (fun x => ⟨g.dirichletGraftEmbedding n x,Finset.mem_map.mpr ⟨x,Finset.mem_univ _,rfl⟩⟩)
    ⟨fun _ _ h => (g.dirichletGraftEmbedding n).injective (congrArg Subtype.val h),by
      intro x
      obtain ⟨v,_,hv⟩ := Finset.mem_map.mp x.property
      exact ⟨v,Subtype.ext hv⟩⟩

def treeExtensionTruncationIso (g : DeficientGraph V d) (n : ℕ) :
    g.dirichletGraftGraph n ≃g g.treeExtension.induce (g.treeExtensionTruncation n : Set g.TreeExtensionVertex) where
  toEquiv := g.treeExtensionTruncationEquiv n
  map_rel_iff' := by
    intro x y
    exact g.dirichletGraftEmbedding_adj_iff n x y

end DeficientGraph
end LocalLaw
