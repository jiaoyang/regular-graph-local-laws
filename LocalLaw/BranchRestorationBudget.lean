import LocalLaw.BranchLabelFibers
import LocalLaw.TreeAttachmentBudget
import LocalLaw.ComponentRestrictionBudget
import LocalLaw.DetachedEndpointModel

/-! # Derive the post-switch finite class from actual tree attachments

The hypotheses are the old finite class, literal branch trees, and the
pointwise restoration of inherited deficit. Both the post component class
and the improved base class at every restored attachment are proved.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 3000000
namespace LocalLaw
local instance branchRestorationBudgetDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) branchRestorationComponentMemDecidable {A : Type*}
    (G : SimpleGraph A) (c : G.ConnectedComponent) : DecidablePred (fun a => a ∈ c.supp) :=
  fun _ => Classical.propDecidable _

namespace BranchAttachmentData
variable {V : Type} [Fintype V] [DecidableEq V] {I : Type*} {d : ℕ}
variable (old post : DeficientGraph V d) (D : BranchAttachmentData V I old.graph post.graph)

omit [DecidableEq V] in
theorem centralFiber_restoration_budgets
    (hcore : post.graph.induce D.core = old.graph.induce D.core)
    (hB : ∀ i, (post.graph.induce (D.B i)).IsTree)
    (hC : ∀ i, (post.graph.induce (D.C i)).IsTree)
    (hold : old.ComponentFiniteReferenceBudget) (restored : V → ℕ)
    (hrestore : ∀ v ∈ D.core, post.deficit v + restored v = old.deficit v)
    (hzero : ∀ i v, v ∈ D.B i → post.deficit v = 0)
    (c : (old.graph.induce D.core).ConnectedComponent) :
    (post.restrict (D.centralFiber c)).FiniteReferenceBudget ∧
      (∀ i, D.centralLabel i = c → 1 ≤ restored (D.attach i) →
        (∑ v, (post.restrict (D.centralFiber c)).deficit v) +
          graphExcess (post.restrict (D.centralFiber c)).graph ≤ finiteOmega d) := by
  let F := D.centralFiber c
  let S := D.centralFiberCore c
  let g := post.restrict F
  let core := (old.restrict F).restrict S
  have hG : g.graph.Connected := D.centralFiber_connected hcore hB hC c
  have hS : (g.graph.induce S).Connected := D.centralFiberCore_connected hcore c
  have hgraph : core.graph = g.graph.induce S := by
    ext x y
    exact Iff.of_eq (congrArg (fun G => G.Adj (⟨x.val.val, x.property⟩ : D.core)
      (⟨y.val.val, y.property⟩ : D.core)) hcore.symm)
  have hOldConn : ((old.restrict F).graph.induce S).Connected := by
    change core.graph.Connected
    rw [hgraph]
    exact hS
  have hbudget : core.FiniteReferenceBudget :=
    (old.restrict F).connected_restrict_finiteReferenceBudget S hOldConn
      (old.restrict_componentFiniteReferenceBudget F hold)
  have hcut := D.centralFiber_tree_cut_components hB c
  let r : S → ℕ := fun v => restored v.val.val
  have hout : ∀ v, v ∉ S → g.deficit v = 0 := by
    intro v hv
    rcases D.cover v.val hv with ⟨i, hi | hi⟩
    · exact hzero i v.val hi
    · have hh := (D.vertexLabel_C i v.val hi).symm.trans v.property
      exact Sum.noConfusion hh
  have hr : ∀ v : S, g.deficit v.val + r v = core.deficit v :=
    fun v => hrestore v.val.val v.property
  constructor
  · exact g.tree_attachment_finiteReferenceBudget S core hgraph hG hS hcut.1 hcut.2 r hout hr hbudget
  · intro i hi hp
    let j : {i : I // D.centralLabel i = c} := ⟨i, hi⟩
    let v : S := ⟨D.centralFiberPort c j, D.attach_mem i⟩
    have hsingle : r v ≤ ∑ u : S, r u :=
      Finset.single_le_sum (fun u (_ : u ∈ Finset.univ) => Nat.zero_le (r u)) (Finset.mem_univ v)
    have hpos : 1 ≤ ∑ u : S, r u := hp.trans hsingle
    exact g.tree_attachment_base_reference_budget S core hgraph hG hS hcut.1 hcut.2 r hout hr hpos hbudget

theorem detachedFiber_base_budget (hω : 1 ≤ finiteOmega d)
    (hC : ∀ i, (post.graph.induce (D.C i)).IsTree)
    (hδ : ∀ i v, v ∈ D.C i → post.deficit v = if v = D.tip i then 1 else 0) (i : I) :
    (∑ v, (post.restrict (D.C i)).deficit v) + graphExcess (post.restrict (D.C i)).graph ≤ finiteOmega d := by
  let root : D.C i := ⟨D.tip i, D.tip_mem i⟩
  have hmass : (∑ v, (post.restrict (D.C i)).deficit v) = 1 := by
    rw [Finset.sum_eq_single root]
    · have h := hδ i (D.tip i) (D.tip_mem i)
      simpa only [if_pos rfl] using h
    · intro v _ hv
      have hne : v.val ≠ D.tip i := fun h => hv (Subtype.ext h)
      exact (hδ i v.val v.property).trans (if_neg hne)
    · exact fun h => False.elim (h (Finset.mem_univ root))
  have hex : graphExcess (post.restrict (D.C i)).graph = 0 :=
    tree_graphExcess_zero _ (hC i)
  rw [hmass, hex, add_zero]
  exact hω

theorem componentFiniteReferenceBudget_of_restoration
    (hcore : post.graph.induce D.core = old.graph.induce D.core)
    (hB : ∀ i, (post.graph.induce (D.B i)).IsTree)
    (hC : ∀ i, (post.graph.induce (D.C i)).IsTree)
    (hold : old.ComponentFiniteReferenceBudget) (restored : V → ℕ)
    (hrestore : ∀ v ∈ D.core, post.deficit v + restored v = old.deficit v)
    (hzero : ∀ i v, v ∈ D.B i → post.deficit v = 0)
    (hδ : ∀ i v, v ∈ D.C i → post.deficit v = if v = D.tip i then 1 else 0)
    (hω : 1 ≤ finiteOmega d) : post.ComponentFiniteReferenceBudget := by
  have hcell (l : (old.graph.induce D.core).ConnectedComponent ⊕ I) :
      (post.restrict (D.labelFiber l)).FiniteReferenceBudget := by
    rcases l with c | i
    · exact (D.centralFiber_restoration_budgets old post hcore hB hC hold restored hrestore hzero c).1
    · rw [D.labelFiber_inr_eq_C]
      exact Or.inl (D.detachedFiber_base_budget old post hω hC hδ i)
  intro c
  let a : c.supp := Classical.choice c.connected_induce_supp.nonempty
  let l := D.vertexLabel a.val
  let F := D.labelFiber l
  have hmem (v : c.supp) : v.val ∈ F :=
    D.vertexLabel_eq_of_reachable (SimpleGraph.ConnectedComponent.exact (v.property.trans a.property.symm))
  let f : c.supp → F := fun v => ⟨v.val, hmem v⟩
  have hf : Function.Injective f := fun _ _ h => Subtype.ext (congrArg (fun v : F => v.val) h)
  let S := Set.range f
  letI : Fintype S := @Subtype.fintype F (fun v => v ∈ S) (fun _ => Classical.propDecidable _) inferInstance
  let e : (post.graph.induce c.supp) ≃g (post.restrict F).graph.induce S :=
    { toEquiv := Equiv.ofInjective f hf
      map_rel_iff' := Iff.rfl }
  have hS : ((post.restrict F).graph.induce S).Connected := e.connected_iff.mp c.connected_induce_supp
  have hF : (post.restrict F).graph.Connected :=
    D.labelFiber_connected hcore hB hC l ⟨⟨a.val, rfl⟩⟩
  have hb := (post.restrict F).restrict_finiteReferenceBudget S hF hS (hcell l)
  exact ((post.restrict F).restrict S).finiteReferenceBudget_of_iso (post.restrict c.supp) e
    (fun _ => rfl) hb

omit [DecidableEq V] in
theorem labelFiber_eq_component
    (hcore : post.graph.induce D.core = old.graph.induce D.core)
    (hB : ∀ i, (post.graph.induce (D.B i)).IsTree)
    (hC : ∀ i, (post.graph.induce (D.C i)).IsTree)
    (l : (old.graph.induce D.core).ConnectedComponent ⊕ I) (v : V) (hv : D.vertexLabel v = l) :
    D.labelFiber l = (post.graph.connectedComponentMk v).supp := by
  ext w
  constructor
  · intro hw
    exact (SimpleGraph.ConnectedComponent.sound
      ((D.reachable_iff_vertexLabel_eq (D.core_edge_persists hcore)
        (fun i => (hB i).isConnected.preconnected) (fun i => (hC i).isConnected.preconnected) v w).mpr
          (hv.trans hw.symm))).symm
  · intro hw
    exact (D.vertexLabel_eq_of_reachable (SimpleGraph.ConnectedComponent.exact hw.symm)).symm.trans hv

omit [DecidableEq V] in
theorem base_component_reference_budget
    (hcore : post.graph.induce D.core = old.graph.induce D.core)
    (hB : ∀ i, (post.graph.induce (D.B i)).IsTree)
    (hC : ∀ i, (post.graph.induce (D.C i)).IsTree)
    (hold : old.ComponentFiniteReferenceBudget) (restored : V → ℕ)
    (hrestore : ∀ v ∈ D.core, post.deficit v + restored v = old.deficit v)
    (hzero : ∀ i v, v ∈ D.B i → post.deficit v = 0)
    (i : I) (hpositive : 1 ≤ restored (D.attach i)) :
    let c := post.graph.connectedComponentMk (D.base i)
    (∑ v, (post.restrict c.supp).deficit v) + graphExcess (post.restrict c.supp).graph ≤ finiteOmega d := by
  dsimp only
  let F := D.centralFiber (D.centralLabel i)
  let c := post.graph.connectedComponentMk (D.base i)
  have hF : F = c.supp := D.labelFiber_eq_component old post hcore hB hC (Sum.inl (D.centralLabel i))
    (D.base i) (D.vertexLabel_B i _ (D.base_mem i))
  have hb := (D.centralFiber_restoration_budgets old post hcore hB hC hold restored hrestore hzero
    (D.centralLabel i)).2 i rfl hpositive
  let e : (post.restrict c.supp).graph ≃g (post.restrict F).graph := induceSetIso post.graph _ _ hF.symm
  have he := (post.restrict F).complexity_iso (post.restrict c.supp) e (fun _ => rfl)
  exact he.le.trans hb

end BranchAttachmentData
end LocalLaw
