import LocalLaw.ComponentFiniteLocalization
import LocalLaw.DeficientGraphIso
import LocalLaw.GraphExcessSurgery

/-!
# Source reference budgets under actual deficient-graph isomorphism

The actual vertex/edge/component equivalences preserve graph excess and the
transported deficit sum. Component restrictions are identified explicitly,
so both the base and extended componentwise reference classes transport.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance deficientBudgetIsoDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) canonicalDeficientBudgetIsoMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

def graphIsoComponentVertexEquiv (e : H ≃g G) (c : H.ConnectedComponent) :
    c.supp ≃ (e.connectedComponentEquiv c).supp where
  toFun v := ⟨e v.val, congrArg e.connectedComponentEquiv v.property⟩
  invFun v := ⟨e.symm v.val, by
    have hh := congrArg e.connectedComponentEquiv.symm v.property
    simpa only [Equiv.symm_apply_apply] using hh⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v.val)
  right_inv v := Subtype.ext (e.apply_symm_apply v.val)

def graphIsoComponentIso (e : H ≃g G) (c : H.ConnectedComponent) :
    H.induce c.supp ≃g G.induce (e.connectedComponentEquiv c).supp where
  toEquiv := graphIsoComponentVertexEquiv e c
  map_rel_iff' := by intro i j; exact e.map_rel_iff'

namespace DeficientGraph
variable [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] {d : ℕ}

omit [DecidableEq V] [DecidableEq W] in
theorem complexity_iso (g : DeficientGraph V d) (h : DeficientGraph W d)
    (e : h.graph ≃g g.graph) (hdeficit : ∀ v, h.deficit v = g.deficit (e v)) :
    (∑ v, h.deficit v) + graphExcess h.graph = (∑ v, g.deficit v) + graphExcess g.graph := by
  have hsum : (∑ v, h.deficit v) = ∑ v, g.deficit v :=
    Fintype.sum_equiv e.toEquiv _ _ hdeficit
  rw [hsum, graphExcess_iso e]

end DeficientGraph

namespace DeficientGraph
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] {d : ℕ}

omit [DecidableEq V] [DecidableEq W] in
theorem finiteReferenceBudget_of_iso (g : DeficientGraph V d) (h : DeficientGraph W d)
    (e : h.graph ≃g g.graph) (hdeficit : ∀ v, h.deficit v = g.deficit (e v))
    (hbudget : g.FiniteReferenceBudget) : h.FiniteReferenceBudget := by
  have hc := g.complexity_iso h e hdeficit
  rcases hbudget with hb | ⟨hb, v, hv⟩
  · exact Or.inl (hc.le.trans hb)
  · right
    refine ⟨hc.le.trans hb, e.symm v, ?_⟩
    rw [hdeficit, e.apply_symm_apply]
    exact hv

omit [DecidableEq V] [DecidableEq W] in
theorem componentReferenceBudget_of_iso (g : DeficientGraph V d) (h : DeficientGraph W d)
    (e : h.graph ≃g g.graph) (hdeficit : ∀ v, h.deficit v = g.deficit (e v))
    (hbudget : g.ComponentReferenceBudget) : h.ComponentReferenceBudget := by
  intro c
  let c' := e.connectedComponentEquiv c
  let φ := graphIsoComponentIso e c
  have hc := (g.restrict c'.supp).complexity_iso (h.restrict c.supp) φ (fun v => hdeficit v.val)
  exact hc.le.trans (hbudget c')

omit [DecidableEq V] [DecidableEq W] in
theorem componentFiniteReferenceBudget_of_iso (g : DeficientGraph V d) (h : DeficientGraph W d)
    (e : h.graph ≃g g.graph) (hdeficit : ∀ v, h.deficit v = g.deficit (e v))
    (hbudget : g.ComponentFiniteReferenceBudget) : h.ComponentFiniteReferenceBudget := by
  intro c
  let c' := e.connectedComponentEquiv c
  let φ := graphIsoComponentIso e c
  exact (g.restrict c'.supp).finiteReferenceBudget_of_iso (h.restrict c.supp) φ
    (fun v => hdeficit v.val) (hbudget c')

end DeficientGraph
end LocalLaw
