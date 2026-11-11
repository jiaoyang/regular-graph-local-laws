import LocalLaw.SourceFullExteriorComparisonFamily
import LocalLaw.FullNearLiftBudget
import LocalLaw.SelectedDepthCounting

/-! The exterior comparison at the two original outside targets has size O(1/log N). -/
open Filter
noncomputable section
namespace LocalLaw
local instance sourceFullFarExteriorDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

def FullExteriorComparedAt (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector r:ℕ)(z q:ℂ)(x y:Fin N)(hx:x∉T)(hy:y∉T)(δ:ℝ):Prop:=
  let s:=g.admissibleState T labels samples
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
  let S:=s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r)
  let xl:S:=⟨⟨x,hx⟩,Or.inl (center_mem_graphBall _ _ _)⟩
  let yl:S:=⟨⟨y,hy⟩,Or.inr (center_mem_graphBall _ _ _)⟩
  let e:=s.fullPairOutsideEmbedding selector r x y
  ‖(new.restrict (s.fullSliceOutside (s.fullTwoTargetVertices selector r x y))).extensionGreen q z (e xl) (e yl)-
    (new.restrict S).extensionGreen q z xl yl‖≤δ

theorem source_full_far_exterior_comparison_of_exterior (a b d:ℕ)(c β B C1:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hβ:0<β)
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
      ∀(hx:x∉T)(hy:y∉T),
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      g.FullExteriorComparedAt T labels samples selector r z q x y hx hy (D/Real.log (N:ℝ)) := by
  obtain ⟨K,hK,hExt⟩:=hExterior
  let Count:ℝ:=(d:ℝ)*((d:ℝ)+1)
  have hCount:0≤Count:=by dsimp only [Count];positivity
  refine ⟨K+1,by linarith,?_⟩
  filter_upwards [hExt,
    eventually_full_near_lift_budget a b d β Count K 1 ha hb hd hβ hCount hK (by norm_num),
    eventually_actual_selected_counts a d ha hd,eventually_log_ge_nat 1,eventually_ge_atTop 1]
    with N hExtN hBudget hCounts hLog hN
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  intro hx hy
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let Γ:=(s.fullResample selector).graph
  let S:=s.fullSliceOutside (pairBallVertices Γ x y r)
  let xl:S:=⟨⟨x,hx⟩,Or.inl (center_mem_graphBall _ _ _)⟩
  let yl:S:=⟨⟨y,hy⟩,Or.inr (center_mem_graphBall _ _ _)⟩
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let ρ:=physicalTransfer d z
  let mass:ℝ:=Nat.card (BoundaryOrientedEdge g.graph T)
  let δ:=K*L*ε+K*(mass+1)*L^4*ρ^(2*r)
  have hL0:0≤L:=by dsimp only [L];linarith
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hδ:0≤δ:=by
    exact add_nonneg (mul_nonneg (mul_nonneg hK hL0) hε)
      (mul_nonneg (mul_nonneg (mul_nonneg hK (by dsimp only [mass];positivity)) (pow_nonneg hL0 4))
        (pow_nonneg (physicalTransfer_pos d hd z).le _))
  have hmass:mass≤Count*L^(2*a):=by
    have hh:mass≤Count*L^(2*a-4):=(hCounts g o z).2
    exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hLog (by omega)) hCount)
  have hbudget:=hBudget z hz hfloor 0 (Nat.zero_le _) mass (Nat.cast_nonneg _) hmass
  have hfactor:1≤(1*L^(2*a-2))^2:=one_le_pow₀ (by simpa only [one_mul] using one_le_pow₀ hLog (n:=2*a-2))
  have hbound:δ≤(K+1)/L:=by
    calc
      _≤δ*(1*L^(2*a-2))^2:=by nlinarith only [mul_le_mul_of_nonneg_left hfactor hδ]
      _≤(K+1)/L:=by simpa only [Nat.sub_zero,one_pow,mul_one] using hbudget
  have hleft:Γ.edist x xl.val.val≤((0:ℕ):ℕ∞) ∨ Γ.edist y xl.val.val≤((0:ℕ):ℕ∞):=by
    left;change Γ.edist x x≤0;simp
  have hright:Γ.edist x yl.val.val≤((0:ℕ):ℕ∞) ∨ Γ.edist y yl.val.val≤((0:ℕ):ℕ∞):=by
    right;change Γ.edist y y≤0;simp
  have hh:=hExtN g o z q hz hzB hfloor hq hprior hballs labels samples x y 0 (Nat.zero_le _) xl yl hleft hright
  exact hh.trans hbound

end RegularGraph
end LocalLaw
