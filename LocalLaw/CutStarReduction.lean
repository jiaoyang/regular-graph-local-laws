import LocalLaw.FullCutPrecision
import LocalLaw.MatchedStarReduction
import LocalLaw.RestrictionDeletionIdentity

/-! # Genuine finite-core reduction across a completely captured inner set -/

noncomputable section
namespace LocalLaw
local instance cutStarReductionDecidable (p:Prop):Decidable p:=Classical.propDecidable p
local instance (priority := 2000) cutStarReductionRangeDecidable {L W:Type}(a:L↪W) :
    DecidablePred (fun v:W=>v∈Set.range a):=fun _=>Classical.propDecidable _
variable {V:Type}

theorem cutInner_range_iff (T S:Set V)(hTS:T⊆S)(v:S) :
    v∈Set.range (cutInnerEmbedding T S hTS) ↔ v.val∈T := by
  constructor
  · rintro ⟨t,ht⟩
    exact congrArg Subtype.val ht ▸ t.property
  · intro hv
    exact ⟨⟨v.val,hv⟩,Subtype.ext rfl⟩

def cutCoreEmbedding (T S I:Set V)(hTS:T⊆S)(hIS:I⊆S)(hIT:∀v∈I,v∉T) :
    I↪((Set.range (cutInnerEmbedding T S hTS))ᶜ:Set S) where
  toFun i:=⟨⟨i.val,hIS i.property⟩,fun h=>hIT i.val i.property ((cutInner_range_iff T S hTS _).mp h)⟩
  inj':=by
    intro i j h
    exact Subtype.ext (congrArg (fun v:((Set.range (cutInnerEmbedding T S hTS))ᶜ:Set S)=>v.val.val) h)

namespace DeficientGraph
variable [Fintype V] [DecidableEq V] {d:ℕ}

theorem captured_cut_star_inverse_difference (g:DeficientGraph V d)(hd:3≤d)
    (T S₀ S₁ I:Set V)(hc₀:graphSetBall g.graph T 1⊆S₀)(hc₁:graphSetBall g.graph T 1⊆S₁)
    (hI₀:I⊆S₀)(hI₁:I⊆S₁)(hIT:∀v∈I,v∉T)
    (hcut:∀t∈T,∀v,g.graph.Adj t v→v∉T→v∈I)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im) :
    let hT₀:=cut_neighborhood_captures_inner g.graph T S₀ hc₀
    let hT₁:=cut_neighborhood_captures_inner g.graph T S₁ hc₁
    let a:=cutInnerEmbedding T S₀ hT₀
    let b:=cutInnerEmbedding T S₁ hT₁
    let e:=cutCoreEmbedding T S₀ I hT₀ hI₀ hIT
    let f:=cutCoreEmbedding T S₁ I hT₁ hI₁ hIT
    let E:=embeddedStarEmbedding a e
    let F:=embeddedStarEmbedding b f
    let R:=(((g.restrict S₀).delete (Set.range a)).extensionGreen q z).submatrix e e
    let P:=(((g.restrict S₁).delete (Set.range b)).extensionGreen q z).submatrix f f
    let GM:=((g.restrict S₀).extensionGreen q z).submatrix E E
    let GN:=((g.restrict S₁).extensionGreen q z).submatrix F F
    IsUnit R ∧ IsUnit P ∧
      GM-GN=(GM.submatrix id Sum.inl*R⁻¹)*(R-P)*(P⁻¹*GN.submatrix Sum.inl id) := by
  dsimp only
  let hT₀:=cut_neighborhood_captures_inner g.graph T S₀ hc₀
  let hT₁:=cut_neighborhood_captures_inner g.graph T S₁ hc₁
  let a:=cutInnerEmbedding T S₀ hT₀
  let b:=cutInnerEmbedding T S₁ hT₁
  let e:=cutCoreEmbedding T S₀ I hT₀ hI₀ hIT
  let f:=cutCoreEmbedding T S₁ I hT₁ hI₁ hIT
  have hng:∀v t,(g.restrict S₀).graph.Adj v.val (a t)→v∈Set.range e:=by
    intro v t hadj
    have hout:v.val.val∉T:=fun ht=>v.property ((cutInner_range_iff T S₀ hT₀ v.val).mpr ht)
    have hi:v.val.val∈I:=hcut t.val t.property v.val.val hadj.symm hout
    exact ⟨⟨v.val.val,hi⟩,Subtype.ext (Subtype.ext rfl)⟩
  have hnh:∀v t,(g.restrict S₁).graph.Adj v.val (b t)→v∈Set.range f:=by
    intro v t hadj
    have hout:v.val.val∉T:=fun ht=>v.property ((cutInner_range_iff T S₁ hT₁ v.val).mpr ht)
    have hi:v.val.val∈I:=hcut t.val t.property v.val.val hadj.symm hout
    exact ⟨⟨v.val.val,hi⟩,Subtype.ext (Subtype.ext rfl)⟩
  let ei:I↪V:=⟨Subtype.val,Subtype.val_injective⟩
  have hp:=g.two_restrictions_captured_cut_precision_blocks T S₀ S₁ hc₀ hc₁ ei
    (fun i=>hI₀ i.property) (fun i=>hI₁ i.property) q z
  exact (g.restrict S₀).matched_star_inverse_difference (g.restrict S₁) hd a b e f hng hnh q z hz hq
    (fun i j=>congrArg (fun M:Matrix T T ℂ=>M i j) hp.1)
    (fun i j=>congrArg (fun M:Matrix I T ℂ=>M i j) hp.2.1)

theorem captured_cut_star_core_Green (g:DeficientGraph V d)(T S I:Set V)
    (hTS:T⊆S)(hIS:I⊆S)(hIT:∀v∈I,v∉T)(q z:ℂ) :
    let a:=cutInnerEmbedding T S hTS
    let e:=cutCoreEmbedding T S I hTS hIS hIT
    let φ:=restrictionDeletionGraphIso g.graph S T (Set.range a) (cutInner_range_iff T S hTS)
    ((((g.restrict S).delete (Set.range a)).extensionGreen q z).submatrix e e)=
      (((g.delete T).restrict {v:(Tᶜ:Set V)|v.val∈S}).extensionGreen q z).submatrix
        (fun i=>φ (e i)) (fun i=>φ (e i)) := by
  dsimp only
  rw [←g.restriction_delete_extensionGreen S T (Set.range (cutInnerEmbedding T S hTS))
    (cutInner_range_iff T S hTS) hTS q z]
  rfl

end DeficientGraph
end LocalLaw
