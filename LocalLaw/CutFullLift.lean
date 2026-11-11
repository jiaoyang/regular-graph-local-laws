import LocalLaw.CutStarHarmonicRows
import LocalLaw.FiniteStarUniformBound
import LocalLaw.FiniteStarTargets

/-! # Actual full inner-set lifting with true harmonic masses

The exterior vertex sets may differ. Radius-one inner capture supplies
matching precision rows and genuine units; the two literal exterior inverse
blocks supply the core error. No inner cardinality factor is introduced.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance cutFullLiftDecidable (p:Prop):Decidable p:=Classical.propDecidable p
local instance (priority := 2000) cutFullLiftRangeDecidable {L W:Type}(a:L↪W) :
    DecidablePred (fun v:W=>v∈Set.range a):=fun _=>Classical.propDecidable _
variable {V:Type}

def cutExteriorEmbedding (T S I:Set V)(hIS:I⊆S)(hIT:∀v∈I,v∉T) :
    I↪{v:(Tᶜ:Set V)|v.val∈S} where
  toFun i:=⟨⟨i.val,hIT i.val i.property⟩,hIS i.property⟩
  inj':=by
    intro i j h
    exact Subtype.ext (congrArg (fun v:{v:(Tᶜ:Set V)|v.val∈S}=>v.val.val) h)

theorem cutStarTarget_value (T S I:Set V)(hTS:T⊆S)(hIS:I⊆S)(hIT:∀v∈I,v∉T)
    (v:V)(hcover:v∈I∨v∈T) :
    (embeddedStarEmbedding (cutInnerEmbedding T S hTS) (cutCoreEmbedding T S I hTS hIS hIT)
      (starTargetIndex I T v hcover)).val=v := by
  unfold starTargetIndex
  split <;> rfl

namespace DeficientGraph
variable [Fintype V] [DecidableEq V] {d:ℕ}

theorem captured_cut_full_error (g:DeficientGraph V d)(hd:3≤d)
    (T S₀ S₁ I:Set V)(hc₀:graphSetBall g.graph T 1⊆S₀)(hc₁:graphSetBall g.graph T 1⊆S₁)
    (hI₀:I⊆S₀)(hI₁:I⊆S₁)(hIT:∀v∈I,v∉T)
    (hcut:∀t∈T,∀v,g.graph.Adj t v→v∉T→v∈I)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(δ B₀ B₁:ℝ)(hδ:0≤δ)(hB₀:0≤B₀)(hB₁:0≤B₁) :
    let hT₀:=cut_neighborhood_captures_inner g.graph T S₀ hc₀
    let hT₁:=cut_neighborhood_captures_inner g.graph T S₁ hc₁
    let a:=cutInnerEmbedding T S₀ hT₀
    let b:=cutInnerEmbedding T S₁ hT₁
    let e:=cutCoreEmbedding T S₀ I hT₀ hI₀ hIT
    let f:=cutCoreEmbedding T S₁ I hT₁ hI₁ hIT
    let E:=embeddedStarEmbedding a e
    let F:=embeddedStarEmbedding b f
    let e₀:=cutExteriorEmbedding T S₀ I hI₀ hIT
    let e₁:=cutExteriorEmbedding T S₁ I hI₁ hIT
    (∀i j:I,‖((g.delete T).restrict {v:(Tᶜ:Set V)|v.val∈S₀}).extensionGreen q z (e₀ i) (e₀ j)-
      ((g.delete T).restrict {v:(Tᶜ:Set V)|v.val∈S₁}).extensionGreen q z (e₁ i) (e₁ j)‖≤δ)→
    ∀x y:I⊕T,
    (∑t:T,‖(g.restrict S₀).extensionGreen q z (E x) (a t)‖)≤B₀→
    (∑t:T,‖(g.restrict S₁).extensionGreen q z (F y) (b t)‖)≤B₁→
    ‖(g.restrict S₀).extensionGreen q z (E x) (E y)-
      (g.restrict S₁).extensionGreen q z (F x) (F y)‖≤δ*(1+(d:ℝ)*B₀)*(1+(d:ℝ)*B₁) := by
  dsimp only
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
  intro herror x y hrow₀ hrow₁
  have hreduce:=g.captured_cut_star_inverse_difference hd T S₀ S₁ I hc₀ hc₁ hI₀ hI₁ hIT hcut q z hz hq
  have hR:=g.captured_cut_star_core_Green T S₀ I hT₀ hI₀ hIT q z
  have hP:=g.captured_cut_star_core_Green T S₁ I hT₁ hI₁ hIT q z
  have he:∀i j:I,‖(R-P) i j‖≤δ:=by
    intro i j
    change ‖(R-P) i j‖≤δ
    have hr:=congrArg (fun M:Matrix I I ℂ=>M i j) hR
    have hp:=congrArg (fun M:Matrix I I ℂ=>M i j) hP
    change R i j=_ at hr
    change P i j=_ at hp
    rw [Matrix.sub_apply,hr,hp]
    exact herror i j
  have hleft:=(g.cut_star_harmonic_l1 hd T S₀ I hT₀ hI₀ hIT hcut q z hz hq B₀ hB₀ x hrow₀).1
  have hright:=(g.cut_star_harmonic_l1 hd T S₁ I hT₁ hI₁ hIT hcut q z hz hq B₁ hB₁ y hrow₁).2
  exact finite_star_uniform_error GM GN R P hreduce.2.2 x y δ (1+(d:ℝ)*B₀) (1+(d:ℝ)*B₁)
    hδ (by positivity) (by positivity) he hleft hright

end DeficientGraph
end LocalLaw
