import LocalLaw.DeficientBudgetIso

/-! # Lowering inherited deficits preserves the finite reference class

The extra class with a positive deficit becomes a base-class graph if every
remaining deficit vanishes. The actual matrix change is the corresponding
negative diagonal physical boundary self-energy.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance deficitReductionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) deficitReductionMemDecidable {W : Type*}
    (G : SimpleGraph W) (C : G.ConnectedComponent) : DecidablePred (fun x => x∈C.supp) :=
  fun _ => Classical.propDecidable _
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

def lowerDeficit (g : DeficientGraph V d) (ρ : V→ℕ) (_hρ : ∀ v,ρ v≤g.deficit v) : DeficientGraph V d where
  graph := g.graph
  deficit := fun v => g.deficit v-ρ v
  degree_deficit_le v := (Nat.add_le_add_left (Nat.sub_le _ _) _).trans (g.degree_deficit_le v)

omit [DecidableEq V] in
theorem finiteReferenceBudget_mono_deficit (g h : DeficientGraph V d)
    (hgraph : h.graph=g.graph) (hδ : ∀ v,h.deficit v≤g.deficit v)
    (hb : g.FiniteReferenceBudget) : h.FiniteReferenceBudget := by
  have hsum : (∑ v,h.deficit v)≤∑ v,g.deficit v := Finset.sum_le_sum (fun v _ => hδ v)
  have hcomplex : (∑ v,h.deficit v)+graphExcess h.graph≤(∑ v,g.deficit v)+graphExcess g.graph := by
    rw [hgraph]
    exact Nat.add_le_add_right hsum _
  rcases hb with hb|⟨hb,v,hv⟩
  · exact Or.inl (hcomplex.trans hb)
  · by_cases hp : ∃ w,0<h.deficit w
    · exact Or.inr ⟨hcomplex.trans hb,hp⟩
    · have hz : ∀ w,h.deficit w=0 := by
        intro w
        by_contra hw
        exact hp ⟨w,Nat.pos_of_ne_zero hw⟩
      have hpos : 1≤∑ w,g.deficit w := Nat.succ_le_of_lt
        (hv.trans_le (Finset.single_le_sum (fun w _ => Nat.zero_le (g.deficit w)) (Finset.mem_univ v)))
      left
      simp only [hz,Finset.sum_const_zero,Nat.zero_add]
      rw [hgraph]
      omega

omit [DecidableEq V] in
theorem lowerDeficit_finiteReferenceBudget (g : DeficientGraph V d) (ρ : V→ℕ)
    (hρ : ∀ v,ρ v≤g.deficit v) (hb : g.FiniteReferenceBudget) :
    (g.lowerDeficit ρ hρ).FiniteReferenceBudget :=
  g.finiteReferenceBudget_mono_deficit (g.lowerDeficit ρ hρ) rfl (fun v => Nat.sub_le (g.deficit v) (ρ v)) hb

omit [DecidableEq V] in
theorem lowerDeficit_componentFiniteReferenceBudget (g : DeficientGraph V d) (ρ : V→ℕ)
    (hρ : ∀ v,ρ v≤g.deficit v) (hb : g.ComponentFiniteReferenceBudget) :
    (g.lowerDeficit ρ hρ).ComponentFiniteReferenceBudget := by
  intro C
  exact (g.restrict C.supp).finiteReferenceBudget_mono_deficit
    ((g.lowerDeficit ρ hρ).restrict C.supp) rfl (fun v => Nat.sub_le _ _) (hb C)

omit [DecidableEq V] in
theorem lowerDeficit_componentReferenceBudget (g : DeficientGraph V d) (ρ : V→ℕ)
    (hρ : ∀ v,ρ v≤g.deficit v) (hb : g.ComponentReferenceBudget) :
    (g.lowerDeficit ρ hρ).ComponentReferenceBudget := by
  intro C
  exact (Nat.add_le_add_right (Finset.sum_le_sum (fun v _ => Nat.sub_le (g.deficit v.val) (ρ v.val))) _).trans (hb C)

omit [DecidableEq V] in
theorem lowerDeficit_boundaryCoefficient (g : DeficientGraph V d) (ρ : V→ℕ)
    (hρ : ∀ v,ρ v≤g.deficit v) (v : V) :
    (g.lowerDeficit ρ hρ).boundaryCoefficient v=g.boundaryCoefficient v+(ρ v:ℝ)/((d:ℝ)-1) := by
  change ((d:ℝ)-((g.deficit v-ρ v:ℕ):ℝ)-(g.graph.degree v:ℝ))/((d:ℝ)-1)=_
  rw [Nat.cast_sub (hρ v)]
  dsimp only [boundaryCoefficient]
  ring

theorem lowerDeficit_extensionMatrix (g : DeficientGraph V d) (ρ : V→ℕ)
    (hρ : ∀ v,ρ v≤g.deficit v) (q z : ℂ) :
    (g.lowerDeficit ρ hρ).extensionMatrix q z=g.extensionMatrix q z-
      q • Matrix.diagonal (fun v => ((ρ v:ℝ)/((d:ℝ)-1):ℂ)) := by
  have hD : (g.lowerDeficit ρ hρ).boundaryDiagonal=g.boundaryDiagonal+
      Matrix.diagonal (fun v => ((ρ v:ℝ)/((d:ℝ)-1):ℂ)) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp only [boundaryDiagonal,Matrix.diagonal_apply_eq,Matrix.add_apply,
        g.lowerDeficit_boundaryCoefficient,Complex.ofReal_add]
      push_cast
      ring
    · simp [boundaryDiagonal,Matrix.diagonal_apply,hij]
  change spectralMatrix g.H z-q • (g.lowerDeficit ρ hρ).boundaryDiagonal=
    (spectralMatrix g.H z-q • g.boundaryDiagonal)-_
  rw [hD,smul_add]
  abel

def restoreOneDeficit (g : DeficientGraph V d) (A : Set V)
    (hA : ∀ v∈A,0<g.deficit v) : DeficientGraph V d :=
  g.lowerDeficit (fun v => if v∈A then 1 else 0) (by
    intro v
    dsimp only
    split_ifs with hv
    · exact Nat.succ_le_of_lt (hA v hv)
    · exact Nat.zero_le _)

omit [DecidableEq V] in
theorem restoreOneDeficit_componentFiniteReferenceBudget (g : DeficientGraph V d) (A : Set V)
    (hA : ∀ v∈A,0<g.deficit v) (hb : g.ComponentFiniteReferenceBudget) :
    (g.restoreOneDeficit A hA).ComponentFiniteReferenceBudget :=
  g.lowerDeficit_componentFiniteReferenceBudget _ _ hb

theorem restoreOneDeficit_extensionMatrix (g : DeficientGraph V d) (A : Set V)
    (hA : ∀ v∈A,0<g.deficit v) (q z : ℂ) :
    (g.restoreOneDeficit A hA).extensionMatrix q z=g.extensionMatrix q z-
      q • Matrix.diagonal (fun v => if v∈A then ((1/((d:ℝ)-1):ℝ):ℂ) else 0) := by
  rw [restoreOneDeficit,g.lowerDeficit_extensionMatrix]
  congr 2
  ext i j
  by_cases hij : i=j
  · subst j
    by_cases hi : i∈A <;> simp [hi]
  · simp [Matrix.diagonal_apply,hij]

end DeficientGraph
end LocalLaw
