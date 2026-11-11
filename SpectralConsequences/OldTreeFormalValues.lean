import SpectralConsequences.OldSampleFormalValues
import SpectralConsequences.RegularBallRecursion
import LocalLaw.OffsetStructuralEvent

/-! Formal q-dependent values at an arbitrary old tree center, without a
sampling or acceptance hypothesis. -/
open Filter
noncomputable section
set_option maxHeartbeats 2400000
namespace SpectralConsequences
open LocalLaw
local instance oldTreeFormalDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem graphBall_tree_of_edist_le {V:Type} (G:SimpleGraph V) (o v:V)
    (k r R:ℕ) (hv:G.edist o v≤(k:ℕ∞)) (hmargin:k+r≤R)
    (htree:(graphBall G o R).IsTree) : (graphBall G v r).IsTree := by
  let f : graphBall G v r →g graphBall G o R :=
    { toFun:=fun x=>⟨x.val,(G.edist_triangle (u:=o) (v:=v) (w:=x.val)).trans
        ((add_le_add hv x.property).trans (by exact_mod_cast hmargin))⟩
      map_rel':=fun h=>h }
  refine ⟨graphBall_connected G v r,?_⟩
  intro a p hp
  exact htree.IsAcyclic (p.map f) (hp.map (fun _ _ h=>Subtype.ext
    (congrArg (fun x:graphBallVertices G o R=>x.val) h)))

def oldTreeFormalConstant (d:ℕ) (β B:ℝ):ℝ :=
  |treePatchWeakConstant d B (sourceObservationLogCap d β)|+1

namespace RegularGraph

theorem eventually_old_tree_formal_values (a b d:ℕ) (c β B:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hβ:0<β) (hβc:β≤c/32) :
    ∀ᶠ N:ℕ in atTop, ∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z →
      (graphBall g.graph o (logarithmicRadius (c/4) d N)).IsTree →
      let q:=g.Q z
      let p:=rationalTreeReference (d-1) q
      let δ:=oldTreeFormalConstant d β B*Real.log (N:ℝ)*
        graphPaperError a d N (logarithmicRadius β d N) z
      (‖g.G z o o-p‖≤δ) ∧
      (∀v:g.graph.neighborSet o, ‖g.G z v.val v.val-p‖≤δ ∧
        ‖g.G z o v.val-p*(-q*treeEdgeWeight d)‖≤δ ∧
        ‖g.G z v.val o-p*(-q*treeEdgeWeight d)‖≤δ) ∧
      (‖regularRootValue d (actualCavityDepth a d N z-1) q z-p‖≤δ) := by
  let A:=sourceObservationLogCap d β
  have hA:0≤A:=sourceObservationLogCap_nonnegative d hd β hβ.le
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_sourceObservationBounds a b d c β B 1 ha hb hd hc hβ hβc (by norm_num),
    eventually_source_formal_kernel_bounds a b d c β B 1 A ha hb hd hc hβ hβc (by norm_num) hA,
    eventually_source_formal_kernel_inverse_bound a b d c β B 1 ha hb hd hc hβ hβc (by norm_num),
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    eventually_resampling_radius_margin a d 3 6 β hd hβ,hdepth]
    with N hnum hformal hinverse hmargin hroom hdepth
  intro g o z hz hzB hfloor badCount hsource htree
  dsimp only
  let r:=effectiveModelRadius a d N β
  let R:=logarithmicRadius (c/4) d N
  let ell:=actualCavityDepth a d N z-1
  let q:=g.Q z
  let p:=rationalTreeReference (d-1) q
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let K:=treePatchWeakConstant d B A
  have num:=hnum z hz hfloor
  have hprior:‖q-semicircleRoot z‖≤1*scalarScale (spectralScale z) ε:=by
    simpa only [one_mul] using hsource.2.1
  have hf:=hformal z q hz hzB hfloor hprior
  have hi:=hinverse z q hz hzB hfloor hprior
  have hp:p*(q⁻¹-q/((d:ℂ)-1))=1:=by
    have hrel:p⁻¹=q⁻¹-q/((d:ℂ)-1):=by
      rw [hf.2.2.2.1,treeEdgeWeight_sq d hd]
      simp only [mul_one_div]
    rw [←hrel]
    exact mul_inv_cancel₀ hf.2.1
  have hqpow:∀n≤4*r+1,‖q‖^n≤2:=by
    intro n hn
    have hh:(n:ℝ)≤((4*r+1:ℕ):ℝ)+1:=by exact_mod_cast Nat.le_succ_of_le hn
    exact hf.2.2.2.2 n (hh.trans num.pair_log)
  have hclass:4*r+1≤R:=by dsimp only [r,R];omega
  have hrR:r+1≤R:=by omega
  have hellr:ell≤r:=by
    have hh:=(actualCavityDepth_radius_bounds a d N z hdepth).2
    dsimp only [ell,r,effectiveModelRadius,modelRadiusLoss]
    omega
  have hell:1≤ell:=by
    have hh:=(nonresonantDepth_bounds (semicircleRoot z) (baselineCavityDepth a d N)).1
    have hh':2≤baselineCavityDepth a d N:=by unfold baselineCavityDepth;omega
    dsimp only [ell,actualCavityDepth];omega
  have hbudget (x y:Fin N):(g.deficient.restrict (pairBallVertices g.graph x y r)).ComponentFiniteReferenceBudget:=
    (g.pairModel_componentReferenceBudget x y r R hclass hsource.1.1).to_componentFinite
  have hD (x y:Fin N):∀u v:pairBallVertices g.graph x y r,
      ((g.deficient.restrict (pairBallVertices g.graph x y r)).graph).dist u v≤4*r+1:=
    pairBall_distance_bound g.graph x y r
  have hzero (x:Fin N)(n:ℕ):∀w∈graphBallVertices g.deficient.graph x n,g.deficient.deficit w=0:=by
    intros;rfl
  have herr:ε≤L*ε:=le_mul_of_one_le_left num.error_nonnegative num.log_one
  have hmul:0≤L*ε:=mul_nonneg (by linarith [num.log_one]) num.error_nonnegative
  have hK:K≤|K|:=le_abs_self K
  have hdiag (v:Fin N)(hv:g.graph.edist o v≤(1:ℕ∞)):
      ‖g.G z v v-p‖≤(|K|+1)*L*ε:=by
    let S:=pairBallVertices g.graph v v r
    let u:S:=pairBallLeft g.graph v v r
    have ht:=(graphBall_tree_of_edist_le g.graph o v 1 r R hv (by omega) htree)
    have hh:=g.deficient.restrict_tree_diagonal_weak_residual hd S (hbudget _ _) u r (4*r+1)
      ht (hzero _ _) q p z hf.1 hp hz (g.Q_im_nonnegative z hz) B 1 ε L A hzB num hprior
      (hD _ _) num.pair_log hf.2.2.1 hi.2 hqpow
    have happ:‖g.G z v v-g.P r z q v v‖≤ε:=hsource.2.2 v v
    have hmodel:g.P r z q v v=(g.deficient.restrict S).extensionGreen q z u u:=
      (g.deficient_P r z q v v).symm
    rw [hmodel] at happ
    have hh':=(norm_sub_le_norm_sub_add_norm_sub (g.G z v v) _ p).trans (add_le_add happ hh)
    norm_num only [one_pow,one_mul,mul_one] at hh'
    have hk:=mul_le_mul_of_nonneg_right hK hmul
    nlinarith only [hh',herr,hk]
  refine ⟨?_,?_,?_⟩
  · simpa only [oldTreeFormalConstant,K] using hdiag o (by simp)
  · intro v
    have hdv:=hdiag v.val (SimpleGraph.edist_eq_one_iff_adj.mpr v.property).le
    let S:=pairBallVertices g.graph o v.val r
    let u:S:=pairBallLeft g.graph o v.val r
    let u':S:=pairBallRight g.graph o v.val r
    have ht:=graphBall_tree_mono g.graph o hrR htree
    have hh:=g.deficient.restrict_tree_adjacent_weak_residual hd S (hbudget _ _) u u' v.property
      r (4*r+1) ht (hzero _ _) q p z hf.1 hp hz (g.Q_im_nonnegative z hz)
      B 1 ε L A hzB num hprior (hD _ _) num.pair_log hf.2.2.1 hi.2 hqpow
    have happ:‖g.G z o v.val-g.P r z q o v.val‖≤ε:=hsource.2.2 o v.val
    have hmodel:g.P r z q o v.val=(g.deficient.restrict S).extensionGreen q z u u':=
      (g.deficient_P r z q o v.val).symm
    rw [hmodel] at happ
    have hh':=(norm_sub_le_norm_sub_add_norm_sub (g.G z o v.val) _ (p*(-q*treeEdgeWeight d))).trans
      (add_le_add happ hh)
    norm_num only [one_pow,one_mul,mul_one] at hh'
    have hk:=mul_le_mul_of_nonneg_right hK hmul
    have hforward:‖g.G z o v.val-p*(-q*treeEdgeWeight d)‖≤(|K|+1)*L*ε:=by
      nlinarith only [hh',herr,hk]
    have hsymm:(g.G z).IsSymm:=by
      have hh:=g.deficient.extensionGreen_isSymm (0:ℂ) z
      simpa only [LocalLaw.RegularGraph.G,LocalLaw.RegularGraph.H,DeficientGraph.extensionGreen,
        DeficientGraph.H,boundaryGreen,boundaryMatrix,zero_smul,sub_zero,green] using hh
    refine ⟨?_,?_,?_⟩
    · simpa only [oldTreeFormalConstant,K] using hdv
    · simpa only [oldTreeFormalConstant,K] using hforward
    · rw [hsymm.apply o v.val]
      simpa only [oldTreeFormalConstant,K] using hforward
  · let T:=graphBallVertices g.graph o ell
    let root:=cavityBallRoot g.graph o ell
    have ht:=(graphBall_tree_mono g.graph o (hellr.trans (by omega)) htree)
    have hb:(g.deficient.restrict T).ComponentFiniteReferenceBudget:=
      ((g.deficient.restrict T).connected_zero_component_budget ht.isConnected (fun _=>rfl)
        (by change graphExcess (graphBall g.graph o ell)≤_;rw [tree_graphExcess_zero _ ht];exact Nat.zero_le _)).to_componentFinite
    have hDT:∀u v:T,(g.deficient.restrict T).graph.dist u v≤4*r+1:=by
      intro u v
      exact (graphBall_distance_le_twice_radius g.graph o ell u v).trans (by omega)
    have hh:=g.deficient.restrict_tree_diagonal_weak_residual hd T hb root r (4*r+1)
      (graphBall_tree_mono g.graph o (by omega:r≤R) htree) (hzero _ _) q p z hf.1 hp hz
      (g.Q_im_nonnegative z hz) B 1 ε L A hzB num hprior hDT num.pair_log hf.2.2.1 hi.2 hqpow
    rw [full_ball_extension_diagonal g hd o ell hell ht q z hz (g.Q_im_nonnegative z hz)] at hh
    norm_num only [one_pow,one_mul,mul_one] at hh
    have hk:=mul_le_mul_of_nonneg_right hK hmul
    change ‖_‖≤(|K|+1)*L*ε
    nlinarith only [hh,hk,hmul]

end RegularGraph
end SpectralConsequences
