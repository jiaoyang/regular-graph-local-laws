import LocalLaw.DeletedLeafAugmentation

/-! # The actual lost-neighbor leaf model immerses into the original graph

Every fake leaf maps to its literal removed neighbor. The map need not be
globally injective, since one removed vertex can have several incident
slots. It is injective on each neighbor set: every actual lost edge occurs
exactly once, and removed vertices are disjoint from retained vertices.
-/

noncomputable section
namespace LocalLaw
local instance deletedLeafMapDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type*}[Fintype V]

def deletedLeafOriginalVertex (G:SimpleGraph V)(T:Set V) :
    ((Tᶜ:Set V)⊕DeletedLeafIndex G T)→V :=
  Sum.elim Subtype.val (fun l=>l.2.val.val)

def deletedLeafOriginalHom (G:SimpleGraph V)(T:Set V) :
    multiLeafGraph (G.induce Tᶜ) (deletedLeafMate G T)→g G where
  toFun:=deletedLeafOriginalVertex G T
  map_rel':=by
    intro a b hab
    cases a with
    | inl a=>
      cases b with
      | inl b=>exact hab
      | inr b=>
        change a=b.1 at hab
        subst a
        exact b.2.property.symm
    | inr a=>
      cases b with
      | inl b=>
        change b=a.1 at hab
        subst b
        exact a.2.property
      | inr b=>exact False.elim hab

omit [Fintype V] in
theorem deletedLeafOriginal_locally_injective (G:SimpleGraph V)(T:Set V)
    (x a b:((Tᶜ:Set V)⊕DeletedLeafIndex G T))
    (ha:(multiLeafGraph (G.induce Tᶜ) (deletedLeafMate G T)).Adj x a)
    (hb:(multiLeafGraph (G.induce Tᶜ) (deletedLeafMate G T)).Adj x b)
    (he:deletedLeafOriginalVertex G T a=deletedLeafOriginalVertex G T b) : a=b := by
  cases x with
  | inl x=>
    cases a with
    | inl a=>
      cases b with
      | inl b=>exact congrArg Sum.inl (Subtype.ext he)
      | inr b=>
        apply False.elim
        apply a.property
        change a.val=b.2.val.val at he
        rw [he]
        exact b.2.val.property
    | inr a=>
      cases b with
      | inl b=>
        apply False.elim
        apply b.property
        change a.2.val.val=b.val at he
        rw [←he]
        exact a.2.val.property
      | inr b=>
        rcases a with ⟨va,ta⟩
        rcases b with ⟨vb,tb⟩
        change x=va at ha
        change x=vb at hb
        subst va
        subst vb
        have ht:ta=tb:=Subtype.ext (Subtype.ext he)
        subst tb
        rfl
  | inr x=>
    cases a with
    | inl a=>
      cases b with
      | inl b=>
        change a=x.1 at ha
        change b=x.1 at hb
        exact congrArg Sum.inl (ha.trans hb.symm)
      | inr b=>exact False.elim hb
    | inr a=>exact False.elim ha

end LocalLaw
