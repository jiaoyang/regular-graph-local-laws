import LocalLaw.SourceFullExteriorComparisonFamily
import LocalLaw.FullNearLiftBudget
import LocalLaw.FullInnerTargetRows
import LocalLaw.CutFullLift
import LocalLaw.NearCutStarGeometry

/-! # The full quarter-close comparison follows from the proved exterior bound

This assembly derives all actual inner precision, inverse, harmonic and
logarithmic inputs. Its exterior contract is instantiated separately by
the deterministic sampled-star comparison.
-/

open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance sourceFullNearComparisonDecidable (p:Prop):Decidable p:=Classical.propDecidable p
local instance (priority := 2000) sourceFullNearComparisonRangeDecidable {L W:Type}(a:L↪W):
    DecidablePred (fun v:W=>v∈Set.range a):=fun _=>Classical.propDecidable _
namespace RegularGraph

theorem source_full_near_comparison_of_exterior (a b d:ℕ)(c β B C1:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hC1:1≤C1)
    (hExterior:SourceFullExteriorComparisonFamily a b d c β B C1) :
    ∃D:ℝ,1≤D ∧ ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z q:ℂ),
      0<z.im→‖z‖≤B→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→0≤q.im→
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z)→
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d)→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y:Fin N),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      let new:=g.labelledResampledGraph T labels samples selector
      let S:=s.fullTwoTargetVertices selector r x y
      let xl:=twoBallLeft g.graph (filledExteriorVertices T (s.endpointModelVertices selector r)) x y r
      let yl:=twoBallRight g.graph (filledExteriorVertices T (s.endpointModelVertices selector r)) x y r
      quarterCutClose (s.fullResample selector).graph T r x y→
      ‖(new.deficient.restrict S).extensionGreen q z xl yl-new.P r z q x y‖≤D/Real.log (N:ℝ) := by
  obtain ⟨K,hK,hExt⟩:=hExterior
  let M:=sourceFullAugmentedRowConstant d β
  let H:=1+(d:ℝ)*M
  let Count:ℝ:=(d:ℝ)*((d:ℝ)+1)
  have hM:0≤M:=sourceFullAugmentedRowConstant_nonnegative d β hd
  have hH:0≤H:=by dsimp only [H];positivity
  have hCount:0≤Count:=by dsimp only [Count];positivity
  refine ⟨K*H^2+1,by nlinarith [mul_nonneg hK (sq_nonneg H)],?_⟩
  filter_upwards [hExt,eventually_source_full_inner_target_rows a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_full_near_lift_budget a b d β Count K H ha hb hd hβ hCount hK hH,
    eventually_source_quarter_cut_dichotomy a d β (by omega) hd hβ,
    eventually_actual_selected_counts a d ha hd,eventually_log_ge_nat 1,eventually_ge_atTop 1]
    with N hExtN hRows hBudget hQuarter hCounts hLog hN
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let new:=g.labelledResampledGraph T labels samples selector
  let Γ:=(s.fullResample selector).graph
  let S₀:=s.fullTwoTargetVertices selector r x y
  let S₁:=pairBallVertices Γ x y r
  let I:=finiteStarCoreSet Γ T x y
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let ρ:=physicalTransfer d z
  let mass:ℝ:=Nat.card (BoundaryOrientedEdge g.graph T)
  let loss:=quarterCutLoss ell r
  let δ:=K*L*ε+K*(mass+1)*L^4*ρ^(2*(r-loss))
  let Binner:=M*L^(2*a-2)
  intro hClose
  have hQuart:=hQuarter g o z labels samples selector x y
  have hr:1≤r:=by have hh:=hQuart.1;dsimp only [r,ell] at *;omega
  have hLoss:loss≤r/2:=hQuart.2.1
  have hNear:graphSetBall Γ T 1⊆S₁ ∧ ∀v∈graphSetBall Γ T 1∪{x,y},
      Γ.edist x v≤(loss:ℕ∞) ∨ Γ.edist y v≤(loss:ℕ∞):=by
    rcases hQuart.2.2 with hn|hf
    · exact hn.2
    · obtain ⟨t,ht,hx|hy⟩:=hClose
      · exact False.elim (not_lt_of_ge hx (hf.2.2 t ht).1)
      · exact False.elim (not_lt_of_ge hy (hf.2.2 t ht).2)
  let geom:=s.full_pair_near_cut_star_geometry selector r x y loss hNear.1 hNear.2
  have hc₀:graphSetBall new.deficient.graph T 1⊆S₀:=s.fullTwoTarget_captures_cut_neighborhood selector r hr x y
  have hc₁:graphSetBall new.deficient.graph T 1⊆S₁:=hNear.1
  let hT₀:=cut_neighborhood_captures_inner new.deficient.graph T S₀ hc₀
  let hT₁:=cut_neighborhood_captures_inner new.deficient.graph T S₁ hc₁
  let hI₀:=geom.core_in_local.trans geom.local_in_common
  let hI₁:=geom.core_in_local
  let aT:=cutInnerEmbedding T S₀ hT₀
  let bT:=cutInnerEmbedding T S₁ hT₁
  let eI:=cutCoreEmbedding T S₀ I hT₀ hI₀ geom.core_outside
  let fI:=cutCoreEmbedding T S₁ I hT₁ hI₁ geom.core_outside
  let E:=embeddedStarEmbedding aT eI
  let F:=embeddedStarEmbedding bT fI
  let tx:=starTargetIndex I T x geom.left_target
  let ty:=starTargetIndex I T y geom.right_target
  let e₀:=cutExteriorEmbedding T S₀ I hI₀ geom.core_outside
  let e₁:=cutExteriorEmbedding T S₁ I hI₁ geom.core_outside
  have hL0:0≤L:=by dsimp only [L];linarith
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hδ:0≤δ:=by
    exact add_nonneg (mul_nonneg (mul_nonneg hK hL0) hε)
      (mul_nonneg (mul_nonneg (mul_nonneg hK (by dsimp only [mass];positivity)) (pow_nonneg hL0 4))
        (pow_nonneg (physicalTransfer_pos d hd z).le _))
  have hBinner:0≤Binner:=mul_nonneg hM (pow_nonneg hL0 _)
  have hOutside:∀i j:I,
      ‖((new.deficient.delete T).restrict {v:(Tᶜ:Set (Fin N))|v.val∈S₀}).extensionGreen q z (e₀ i) (e₀ j)-
        ((new.deficient.delete T).restrict {v:(Tᶜ:Set (Fin N))|v.val∈S₁}).extensionGreen q z (e₁ i) (e₁ j)‖≤δ:=by
    intro i j
    have hh:=hExtN g o z q hz hzB hfloor hq hprior hballs labels samples x y loss hLoss
      (e₁ i) (e₁ j) (geom.near i.val i.property) (geom.near j.val j.property)
    have he (i:I):s.fullPairOutsideEmbedding selector r x y (e₁ i)=e₀ i:=rfl
    simpa only [he] using hh
  have hrow₀:(∑t:T,‖(new.deficient.restrict S₀).extensionGreen q z (E tx) (aT t)‖)≤Binner:=
    hRows g o z q hz hzB hfloor hq hprior hballs labels samples x y S₀ (Set.Subset.refl _) hT₀ (E tx)
  have hrow₁:(∑t:T,‖(new.deficient.restrict S₁).extensionGreen q z (F ty) (bT t)‖)≤Binner:=
    hRows g o z q hz hzB hfloor hq hprior hballs labels samples x y S₁ geom.local_in_common hT₁ (F ty)
  have hfull:=new.deficient.captured_cut_full_error hd T S₀ S₁ I hc₀ hc₁ hI₀ hI₁ geom.core_outside
    geom.cut_neighbors q z hz hq δ Binner Binner hδ hBinner hBinner hOutside tx ty hrow₀ hrow₁
  have hfactor:1+(d:ℝ)*Binner≤H*L^(2*a-2):=by
    have hp:1≤L^(2*a-2):=one_le_pow₀ hLog
    dsimp only [Binner,H]
    nlinarith only [hp]
  have hfactor0:0≤1+(d:ℝ)*Binner:=by positivity
  have hscaled:δ*(1+(d:ℝ)*Binner)*(1+(d:ℝ)*Binner)≤δ*(H*L^(2*a-2))^2:=by
    have hh:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hfactor0 hfactor 2) hδ
    nlinarith only [hh]
  have hmass:mass≤Count*L^(2*a):=by
    have hh:mass≤Count*L^(2*a-4):=(hCounts g o z).2
    exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hLog (by omega)) hCount)
  have hbudget:=hBudget z hz hfloor loss hLoss mass (Nat.cast_nonneg _) hmass
  have hfinal:=hfull.trans (hscaled.trans hbudget)
  let xl:S₀:=twoBallLeft g.graph (filledExteriorVertices T (s.endpointModelVertices selector r)) x y r
  let yl:S₀:=twoBallRight g.graph (filledExteriorVertices T (s.endpointModelVertices selector r)) x y r
  let pl:S₁:=pairBallLeft new.graph x y r
  let pr:S₁:=pairBallRight new.graph x y r
  have hEx:E tx=xl:=Subtype.ext (cutStarTarget_value T S₀ I hT₀ hI₀ geom.core_outside x geom.left_target)
  have hEy:E ty=yl:=Subtype.ext (cutStarTarget_value T S₀ I hT₀ hI₀ geom.core_outside y geom.right_target)
  have hFx:F tx=pl:=Subtype.ext (cutStarTarget_value T S₁ I hT₁ hI₁ geom.core_outside x geom.left_target)
  have hFy:F ty=pr:=Subtype.ext (cutStarTarget_value T S₁ I hT₁ hI₁ geom.core_outside y geom.right_target)
  rw [hEx,hEy,hFx,hFy] at hfinal
  rw [←new.deficient_P r z q x y]
  exact hfinal

end RegularGraph
end LocalLaw
