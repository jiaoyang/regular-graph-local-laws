import LocalLaw.GraphExcessSurgery
import LocalLaw.ComponentFiniteLocalization

/-!
# Actual tree attachments preserve excess and spend inherited deficit

Each tree branch has exactly one cut edge to the connected old core.
The exact finite Euler cut identity proves preservation of excess. Restoring
one old lost-degree unit for each attachment then improves the finite class;
in particular any attached core moves from the extra class into the base one.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance treeAttachmentBudgetDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) treeAttachmentCoreMemDecidable {V : Type*} (S : Set V) :
    DecidablePred (fun v => v ∈ S) := fun _ => Classical.propDecidable _
variable {V : Type} [Fintype V] [DecidableEq V]


namespace DeficientGraph
variable {d : ℕ}

omit [DecidableEq V] in
/-- Pointwise inherited deficit restoration gives its exact total mass. -/
theorem deficit_mass_core_restoration (g : DeficientGraph V d) (S : Set V)
    (core : DeficientGraph S d) (restored : S → ℕ)
    (hout : ∀ v, v ∉ S → g.deficit v = 0)
    (hcore : ∀ v : S, g.deficit v.val + restored v = core.deficit v) :
    (∑ v, g.deficit v) + (∑ v : S, restored v) = ∑ v, core.deficit v := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun v => v ∈ S) g.deficit
  have hzero : (∑ v : {v : V // v ∉ S}, g.deficit v.val) = 0 :=
    Finset.sum_eq_zero (fun v _ => hout v.val v.property)
  rw [hzero, add_zero] at hsplit
  calc
    _ = (∑ v : S, g.deficit v.val) + (∑ v : S, restored v) := by rw [hsplit]
    _ = ∑ v : S, (g.deficit v.val + restored v) := (Finset.sum_add_distrib ..).symm
    _ = _ := Finset.sum_congr rfl (fun v _ => hcore v)

omit [DecidableEq V] in
/-- Restoring at least one unit turns the actual extra finite budget into a
base finite budget. Every excess and deficit identity is derived here. -/
theorem tree_attachment_base_reference_budget (g : DeficientGraph V d) (S : Set V)
    (core : DeficientGraph S d) (hgraph : core.graph = g.graph.induce S)
    (hG : g.graph.Connected) (hS : (g.graph.induce S).Connected)
    (htree : ∀ c : CutComponent g.graph S, (cutComponentGraph g.graph S c).IsTree)
    (hattach : ∀ c : CutComponent g.graph S, cutMultiplicity g.graph S c = 1)
    (restored : S → ℕ) (hout : ∀ v, v ∉ S → g.deficit v = 0)
    (hcore : ∀ v : S, g.deficit v.val + restored v = core.deficit v)
    (hpositive : 1 ≤ ∑ v : S, restored v)
    (hbudget : core.FiniteReferenceBudget) :
    (∑ v, g.deficit v) + graphExcess g.graph ≤ finiteOmega d := by
  have hsum := g.deficit_mass_core_restoration S core restored hout hcore
  have hex := graphExcess_eq_core_of_tree_attachments g.graph S hG hS htree (fun c => (hattach c).le)
  rw [← hgraph] at hex
  have hbound : (∑ v, core.deficit v) + graphExcess core.graph ≤ finiteOmega d + 1 := by
    rcases hbudget with hbase | hextra
    · exact hbase.trans (Nat.le_succ _)
    · exact hextra.1
  rw [hex]
  omega

omit [DecidableEq V] in
/-- Zero restoration retains the old base/extra class exactly; positive
restoration improves it to the base class. -/
theorem tree_attachment_finiteReferenceBudget (g : DeficientGraph V d) (S : Set V)
    (core : DeficientGraph S d) (hgraph : core.graph = g.graph.induce S)
    (hG : g.graph.Connected) (hS : (g.graph.induce S).Connected)
    (htree : ∀ c : CutComponent g.graph S, (cutComponentGraph g.graph S c).IsTree)
    (hattach : ∀ c : CutComponent g.graph S, cutMultiplicity g.graph S c = 1)
    (restored : S → ℕ) (hout : ∀ v, v ∉ S → g.deficit v = 0)
    (hcore : ∀ v : S, g.deficit v.val + restored v = core.deficit v)
    (hbudget : core.FiniteReferenceBudget) : g.FiniteReferenceBudget := by
  by_cases hpositive : 1 ≤ ∑ v : S, restored v
  · exact Or.inl (g.tree_attachment_base_reference_budget S core hgraph hG hS htree hattach
      restored hout hcore hpositive hbudget)
  have hrestored : (∑ v : S, restored v) = 0 := by omega
  have hsum := g.deficit_mass_core_restoration S core restored hout hcore
  have hex := graphExcess_eq_core_of_tree_attachments g.graph S hG hS htree (fun c => (hattach c).le)
  rw [← hgraph] at hex
  rcases hbudget with hbase | hextra
  · apply Or.inl
    rw [hex]
    omega
  · apply Or.inr
    constructor
    · rw [hex]
      omega
    · obtain ⟨v, hv⟩ := hextra.2
      have hvzero : restored v = 0 := by
        have hh := Finset.single_le_sum (fun u (_ : u ∈ Finset.univ) => Nat.zero_le (restored u))
          (Finset.mem_univ v)
        omega
      have hh := hcore v
      exact ⟨v.val, by omega⟩

end DeficientGraph
end LocalLaw
