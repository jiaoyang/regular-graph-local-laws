import LocalLaw.MultiLeafAugmentation

/-! # Keeping every leaf slot makes restriction commute with completion

The lifted set keeps precisely the core vertices in S and every leaf whose
mate is in S. Its retained core precision is exactly the precision of the
original correctly deficient restriction, with no omitted-slot charge.
-/

noncomputable section
set_option maxHeartbeats 1600000
namespace LocalLaw
local instance multiLeafRestrictionDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V L:Type*}

def multiLeafLiftMate (mate:L→V)(S:Set V) : {l:L //mate l∈S}→S :=fun l=>⟨mate l.val,l.property⟩

def multiLeafLiftCore (mate:L→V)(S:Set V):S↪multiLeafLift mate S where
  toFun v:=⟨.inl v.val,v.property⟩
  inj':=by intro a b h;exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))

def multiLeafLiftGraphIso (G:SimpleGraph V)(mate:L→V)(S:Set V) :
    multiLeafGraph (G.induce S) (multiLeafLiftMate mate S)≃g
      (multiLeafGraph G mate).induce (multiLeafLift mate S) where
  toFun a:=match a with
    | .inl v=>⟨.inl v.val,v.property⟩
    | .inr l=>⟨.inr l.val,l.property⟩
  invFun a:=match h:a.val with
    | .inl v=>.inl ⟨v,show Sum.inl v∈multiLeafLift mate S from h ▸ a.property⟩
    | .inr l=>.inr ⟨l,show Sum.inr l∈multiLeafLift mate S from h ▸ a.property⟩
  left_inv a:=by cases a <;> rfl
  right_inv a:=by rcases a with ⟨a,ha⟩;cases a <;> rfl
  map_rel_iff':=by
    intro a b
    cases a with
    | inl a=>
      cases b with
      | inl b=>rfl
      | inr b=>
        change a.val=mate b.val ↔ a=⟨mate b.val,b.property⟩
        exact ⟨fun h=>Subtype.ext h,fun h=>congrArg Subtype.val h⟩
    | inr a=>
      cases b with
      | inl b=>
        change b.val=mate a.val ↔ b=⟨mate a.val,a.property⟩
        exact ⟨fun h=>Subtype.ext h,fun h=>congrArg Subtype.val h⟩
      | inr b=>rfl

def multiLeafLiftFiberEquiv (mate:L→V)(S:Set V)(v:S) :
    {l:{l:L //mate l∈S} //multiLeafLiftMate mate S l=v}≃{l:L //mate l=v.val} where
  toFun l:=⟨l.val.val,congrArg Subtype.val l.property⟩
  invFun l:=⟨⟨l.val,l.property.symm ▸ v.property⟩,Subtype.ext l.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

section Finite
variable [Fintype V] [Fintype L]

omit [Fintype V] [Fintype L] in
theorem multiLeafLiftMultiplicity (mate:L→V)(S:Set V)(v:S) :
    multiLeafMultiplicity (multiLeafLiftMate mate S) v=multiLeafMultiplicity mate v.val :=
  Nat.card_congr (multiLeafLiftFiberEquiv mate S v)

theorem multiLeafLift_degree_core (G:SimpleGraph V)(mate:L→V)(S:Set V)(v:S) :
    ((multiLeafGraph G mate).induce (multiLeafLift mate S)).degree
      (multiLeafLiftCore mate S v)=(G.induce S).degree v+multiLeafMultiplicity mate v.val := by
  let e:=multiLeafLiftGraphIso G mate S
  have hh:=Nat.card_congr (e.mapNeighborSet (.inl v))
  have hd:=multiLeafGraph_degree_old (G.induce S) (multiLeafLiftMate mate S) v
  rw [multiLeafLiftMultiplicity] at hd
  simp only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] at hh hd ⊢
  exact hh.symm.trans hd

namespace DeficientGraph
variable {d:ℕ}

theorem attachLeaves_lift_boundaryCoefficient (g:DeficientGraph V d)(hd:1≤d)(mate:L→V)
    (hrestore:∀v,multiLeafMultiplicity mate v≤g.deficit v)(S:Set V)(v:S) :
    ((g.attachLeaves hd mate hrestore).restrict (multiLeafLift mate S)).boundaryCoefficient
      (multiLeafLiftCore mate S v)=(g.restrict S).boundaryCoefficient v := by
  have hdeg:=multiLeafLift_degree_core g.graph mate S v
  have hrest:=hrestore v.val
  have htotal :
      ((g.attachLeaves hd mate hrestore).restrict (multiLeafLift mate S)).deficit
          (multiLeafLiftCore mate S v)+
        ((g.attachLeaves hd mate hrestore).restrict (multiLeafLift mate S)).graph.degree
          (multiLeafLiftCore mate S v)=
        (g.restrict S).deficit v+(g.restrict S).graph.degree v := by
    change (g.deficit v.val-multiLeafMultiplicity mate v.val)+
      ((multiLeafGraph g.graph mate).induce (multiLeafLift mate S)).degree
        (multiLeafLiftCore mate S v)=g.deficit v.val+(g.graph.induce S).degree v
    rw [hdeg]
    omega
  have hreal :
      (((g.attachLeaves hd mate hrestore).restrict (multiLeafLift mate S)).deficit
          (multiLeafLiftCore mate S v):ℝ)+
        (((g.attachLeaves hd mate hrestore).restrict (multiLeafLift mate S)).graph.degree
          (multiLeafLiftCore mate S v):ℝ)=
        ((g.restrict S).deficit v:ℝ)+((g.restrict S).graph.degree v:ℝ):=by exact_mod_cast htotal
  unfold boundaryCoefficient
  congr 1
  linarith

theorem attachLeaves_lift_extensionMatrix_core (g:DeficientGraph V d)(hd:1≤d)(mate:L→V)
    (hrestore:∀v,multiLeafMultiplicity mate v≤g.deficit v)(S:Set V)(q z:ℂ) :
    (((g.attachLeaves hd mate hrestore).restrict (multiLeafLift mate S)).extensionMatrix q z).submatrix
      (multiLeafLiftCore mate S) (multiLeafLiftCore mate S)=(g.restrict S).extensionMatrix q z := by
  ext i j
  simp only [extensionMatrix,boundaryMatrix,spectralMatrix,H,boundaryDiagonal,
    Matrix.submatrix_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.diagonal_apply,(multiLeafLiftCore mate S).injective.eq_iff]
  rw [g.attachLeaves_lift_boundaryCoefficient hd mate hrestore S i]
  simp only [normalizedAdjacency,Matrix.smul_apply,smul_eq_mul,SimpleGraph.adjMatrix_apply,
    restrict,attachLeaves,multiLeafLiftCore,multiLeafGraph]
  rfl

end DeficientGraph
end Finite
end LocalLaw
