import LocalLaw.AttachedLeafSubfamilyRows

/-! # Fixed entry caps after a genuine scalar leaf-complement deletion -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance attachedLeafSubfamilyEntryCapDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V L J:Type}[Fintype V][Fintype L][Fintype J]{d:ℕ}

theorem attachLeaves_subfamily_entry_cap (g:DeficientGraph V d)(hd:3≤d)(mate:L→V)
    (hr:∀v,multiLeafMultiplicity mate v≤g.deficit v)(e:J↪L)(q z p:ℂ)
    (hz:0<z.im)(hq:0≤q.im)(hp:p≠0)(σ W C:ℝ)(hσ:0≤σ)(hC:0≤C)
    (herror:∀l k:LeafFamilyComplement e,
      ‖(g.attachLeaves (by omega) mate hr).extensionGreen q z (.inr l.val) (.inr k.val)-
        (if l=k then p else 0)‖≤σ)
    (hsmall:(Fintype.card (LeafFamilyComplement e):ℝ)*‖p⁻¹‖*σ≤1/2)
    (hrows:∀x:V⊕L,∑l:L,‖(g.attachLeaves (by omega) mate hr).extensionGreen q z x (.inr l)‖≤W)
    (hcap:∀x y:V⊕L,‖(g.attachLeaves (by omega) mate hr).extensionGreen q z x y‖≤C) :
    let kept:=g.attachLeaves (by omega) (mate∘e)
      (fun v=>(subfamily_leaf_multiplicity_le mate e v).trans (hr v))
    ∀i j:V⊕J,‖kept.extensionGreen q z i j‖≤C+2*W*‖p⁻¹‖*C := by
  dsimp only
  let H:=g.attachLeaves (by omega) mate hr
  let M:=g.leafSubfamilyMatrix hd mate hr e q z
  let f:=leafBlockPartition (V:=V) e
  have hi (a b:(V⊕J)⊕LeafFamilyComplement e):M⁻¹ a b=H.extensionGreen q z (f a) (f b):=
    congrArg (fun P=>P a b) (g.leafSubfamilyMatrix_inverse hd mate hr e q z)
  have hu:=g.leafSubfamilyMatrix_units hd mate hr e q z hz hq
  have he:∀l k:LeafFamilyComplement e,‖M⁻¹ (.inr l) (.inr k)-(if l=k then p else 0)‖≤σ:=by
    intro l k
    simpa only [hi,f,leafBlockPartition_removed] using herror l k
  have hcross:∀i:V⊕J,∑l:LeafFamilyComplement e,‖M⁻¹ (.inl i) (.inr l)‖≤W:=by
    intro i
    simpa only [hi,f,leafBlockPartition_removed] using
      (finite_norm_sum_embedding_le (Function.Embedding.subtype (fun l:L=>l∉Set.range e))
        (fun l=>H.extensionGreen q z (f (.inl i)) (.inr l))).trans (hrows _)
  intro i j
  have hb:∀x:V⊕J,∑_k:Unit,‖M⁻¹ (.inl x) (.inl j)‖≤C:=by
    intro x
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_unique,nsmul_eq_mul,Nat.cast_one,one_mul,hi] using hcap (f (.inl x)) (f (.inl j))
  have hrm:∀l:LeafFamilyComplement e,∑_k:Unit,‖M⁻¹ (.inr l) (.inl j)‖≤C:=by
    intro l
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_unique,nsmul_eq_mul,Nat.cast_one,one_mul,hi] using hcap (f (.inr l)) (f (.inl j))
  have hh:=core_inverse_scalar_leaf_remaining_rows M hu.1 hu.2 (fun _:Unit=>j) p hp σ C W C hσ hC he hsmall hb hcross hrm i
  rw [g.leafSubfamilyMatrix_core hd mate hr e q z] at hh
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_unique,nsmul_eq_mul,Nat.cast_one,one_mul] using hh

end DeficientGraph
end LocalLaw
