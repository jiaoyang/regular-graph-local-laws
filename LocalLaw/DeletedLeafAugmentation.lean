import LocalLaw.MultiLeafAugmentation
import LocalLaw.ComponentRestrictionBudget

/-! # Actual lost-neighbor leaf model for a physical deletion

There is one new leaf for every literal removed-to-retained edge. Distinct
lost neighbors remain distinctly labelled. The retained deficit becomes the
original inherited deficit exactly; all new leaves have deficit zero.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance deletedLeafAugmentationDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type*} [Fintype V]

def DeletedLeafIndex (G:SimpleGraph V)(T:Set V) :=
  Σ v:(Tᶜ:Set V),{t:T //G.Adj t.val v.val}

instance deletedLeafIndexFintype (G:SimpleGraph V)(T:Set V) : Fintype (DeletedLeafIndex G T) :=
  inferInstanceAs (Fintype (Σv:(Tᶜ:Set V),{t:T //G.Adj t.val v.val}))

def deletedLeafMate (G:SimpleGraph V)(T:Set V) : DeletedLeafIndex G T→(Tᶜ:Set V) := Sigma.fst

def deletedLeafFiberEquiv (G:SimpleGraph V)(T:Set V)(v:(Tᶜ:Set V)) :
    {l:DeletedLeafIndex G T //deletedLeafMate G T l=v}≃{t:T //G.Adj t.val v.val} where
  toFun l:=l.property ▸ l.val.2
  invFun t:=⟨⟨v,t⟩,rfl⟩
  left_inv:=by
    rintro ⟨⟨w,t⟩,h⟩
    change w=v at h
    cases h
    rfl
  right_inv _:=rfl

omit [Fintype V] in
theorem deletedLeafMultiplicity (G:SimpleGraph V)(T:Set V)(v:(Tᶜ:Set V)) :
    multiLeafMultiplicity (deletedLeafMate G T) v=Nat.card {t:T //G.Adj t.val v.val} :=
  Nat.card_congr (deletedLeafFiberEquiv G T v)

def deletedLeafSwapEquiv (G:SimpleGraph V)(T:Set V) :
    DeletedLeafIndex G T≃Σt:T,{v:(Tᶜ:Set V) //G.Adj t.val v.val} where
  toFun l:=⟨l.2.val,⟨l.1,l.2.property⟩⟩
  invFun l:=⟨l.2.val,⟨l.1,l.2.property⟩⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem deletedLeafIndex_card_bound (G:SimpleGraph V)(T:Set V)(d:ℕ)
    (hdegree:∀v,G.degree v≤d) : Nat.card (DeletedLeafIndex G T)≤Nat.card T*d := by
  rw [Nat.card_congr (deletedLeafSwapEquiv G T),Nat.card_sigma]
  calc
    _≤∑t:T,d:=by
      apply Finset.sum_le_sum
      intro t _
      have hh:=Nat.card_le_card_of_injective
        (fun v:{v:(Tᶜ:Set V) //G.Adj t.val v.val}=>
          (⟨v.val.val,v.property⟩:G.neighborSet t.val))
        (by
          intro v w h
          have hv:v.val.val=w.val.val:=congrArg (fun x:G.neighborSet t.val=>x.val) h
          exact Subtype.ext (Subtype.ext hv))
      have hd:=hdegree t.val
      simp only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] at hd
      exact hh.trans hd
    _=Nat.card T*d:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id]

namespace DeficientGraph
variable {d:ℕ}

def deletedLeafModel (g:DeficientGraph V d)(hd:1≤d)(T:Set V) :
    DeficientGraph ((Tᶜ:Set V)⊕DeletedLeafIndex g.graph T) d :=
  (g.delete T).attachLeaves hd (deletedLeafMate g.graph T) (by
    intro v
    rw [deletedLeafMultiplicity,g.delete_deficit_eq_removed_neighbors]
    omega)

theorem deletedLeafModel_deficit_old (g:DeficientGraph V d)(hd:1≤d)(T:Set V)(v:(Tᶜ:Set V)) :
    (g.deletedLeafModel hd T).deficit (.inl v)=g.deficit v.val := by
  change (g.delete T).deficit v-multiLeafMultiplicity (deletedLeafMate g.graph T) v=g.deficit v.val
  rw [deletedLeafMultiplicity,g.delete_deficit_eq_removed_neighbors]
  omega

theorem deletedLeafModel_deficit_leaf (g:DeficientGraph V d)(hd:1≤d)(T:Set V)
    (l:DeletedLeafIndex g.graph T) : (g.deletedLeafModel hd T).deficit (.inr l)=0 := rfl

theorem deletedLeafModel_degree_old (g:DeficientGraph V d)(hd:1≤d)(T:Set V)(v:(Tᶜ:Set V)) :
    (g.deletedLeafModel hd T).graph.degree (.inl v)=g.graph.degree v.val := by
  have ha:=(g.delete T).attachLeaves_degree_deficit hd (deletedLeafMate g.graph T)
    (show ∀v,multiLeafMultiplicity (deletedLeafMate g.graph T) v≤(g.delete T).deficit v by
      intro v;rw [deletedLeafMultiplicity,g.delete_deficit_eq_removed_neighbors];omega) v
  change (g.deletedLeafModel hd T).graph.degree (.inl v)+
    (g.deletedLeafModel hd T).deficit (.inl v)=(g.delete T).graph.degree v+(g.delete T).deficit v at ha
  rw [g.deletedLeafModel_deficit_old,g.delete_deficit] at ha
  have hle:=induced_degree_le g.graph Tᶜ v
  change (g.deletedLeafModel hd T).graph.degree (.inl v)+g.deficit v.val=
    (g.graph.induce Tᶜ).degree v+(g.deficit v.val+
      (g.graph.degree v.val-(g.graph.induce Tᶜ).degree v)) at ha
  simp only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] at ha hle ⊢
  omega

theorem deletedLeafModel_deficit_sum (g:DeficientGraph V d)(hd:1≤d)(T:Set V) :
    (∑a,(g.deletedLeafModel hd T).deficit a)=∑v:(Tᶜ:Set V),g.deficit v.val := by
  rw [Fintype.sum_sum_type]
  simp only [g.deletedLeafModel_deficit_old,g.deletedLeafModel_deficit_leaf,
    Finset.sum_const_zero,add_zero]

theorem deletedLeafModel_extensionMatrix_principal (g:DeficientGraph V d)(hd:1≤d)
    (T:Set V)(q z:ℂ) :
    ((g.deletedLeafModel hd T).extensionMatrix q z).submatrix Sum.inl Sum.inl=
      (g.delete T).extensionMatrix q z :=
  by
    have hh:=(g.delete T).attachLeaves_extensionMatrix_principal hd (deletedLeafMate g.graph T)
      (show ∀v,multiLeafMultiplicity (deletedLeafMate g.graph T) v≤(g.delete T).deficit v by
        intro v;rw [deletedLeafMultiplicity,g.delete_deficit_eq_removed_neighbors];omega) q z
    ext i j
    have he:=congrArg (fun M:Matrix (Tᶜ:Set V) (Tᶜ:Set V) ℂ=>M i j) hh
    by_cases hij:i=j
    · subst j
      simpa only [extensionMatrix,boundaryMatrix,spectralMatrix,Matrix.submatrix_apply,
        Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,
        Sum.inl.injEq,if_pos rfl,boundaryDiagonal,Matrix.diagonal_apply] using he
    · simpa only [extensionMatrix,boundaryMatrix,spectralMatrix,Matrix.submatrix_apply,
        Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,
        Sum.inl.injEq,if_neg hij,boundaryDiagonal,Matrix.diagonal_apply] using he

theorem deletedLeafModel_edist_old (g:DeficientGraph V d)(hd:1≤d)(T:Set V)(u v:(Tᶜ:Set V)) :
    (g.deletedLeafModel hd T).graph.edist (.inl u) (.inl v)=(g.delete T).graph.edist u v :=
  multiLeafGraph_edist_old _ _ u v

theorem deletedLeafModel_excess (g:DeficientGraph V d)(hd:1≤d)(T:Set V) :
    graphExcess (g.deletedLeafModel hd T).graph=graphExcess (g.delete T).graph :=
  multiLeafGraph_excess _ _

end DeficientGraph
end LocalLaw
