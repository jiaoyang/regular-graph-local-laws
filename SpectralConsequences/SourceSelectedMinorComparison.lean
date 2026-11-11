import SpectralConsequences.SelectedCommonTransport

/-! # The source (7.5) selected-minor replacement, uniform over samples

The switched outside tip kernel is compared to the ORIGINAL full-graph minor
which removes only the chosen one or two sampled first vertices. No event on
the switched graph is needed. The cost is quadratic in the source prime error.
-/
open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
namespace SpectralConsequences
open LocalLaw
local instance sourceSelectedMinorComparisonDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def sourceSelectedMinorConstant (d:ℕ) (B C1:ℝ):ℝ:=
  1+|2*sourcePartialFirstInverseCap d B*(sourceEndpointErrorConstant d C1)^2|+
    |oldMinorRetainedConstant d B*(1+4*oldMinorPivotConstant d B*oldMinorEntryConstant d)^2|

theorem eventually_source_selected_minor_comparison (a b d:ℕ) (c β B C1:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hβ:0<β) (hβc:β≤c/32)
    (hB:0≤B) (hC1:1≤C1):
    ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→‖z‖≤B→∀Cq badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let s:=g.admissibleState T labels samples
      let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
      ∀(Q:Set (s.AdmissibleSampleIndex selector)),Nat.card Q≤2→
      ∀i j,i∈Q→j∈Q→
      ‖new.G z (s.admissibleSecondVertex selector i) (s.admissibleSecondVertex selector j)-
        oldOwnSampleMinorEntry g.H T (s.selectedFirstEmbedding selector) (s.admissibleSecondVertex selector)
          (selected_first_ne_second s selector) Q z i j‖≤
        sourceSelectedMinorConstant d B C1*
          ((Nat.card (BoundaryOrientedEdge g.graph T)+Nat.card T:ℕ):ℝ)*
          (g.sourcePrime a (logarithmicRadius β d N) z)^2 := by
  filter_upwards [eventually_switched_tip_common_comparison a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_old_minor_common_comparison a b d c β B C1 ha hb hd hc hβ hβc hB (by linarith),
    eventually_log_ge_nat 1,eventually_ge_atTop 1] with N hnew hold hL hN
  intro g o z hz hfloor hzB Cq badCount hsource hplus ι _ labels samples
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let s:=g.admissibleState T labels samples
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
  let common:=(g.deficient.delete T).delete (s.selectedFirstSet selector)
  let μ:ℝ:=Nat.card (BoundaryOrientedEdge g.graph T)
  let n:ℝ:=((Nat.card (BoundaryOrientedEdge g.graph T)+Nat.card T:ℕ):ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let εp:=g.sourcePrime a (logarithmicRadius β d N) z
  let K0:=oldMinorRetainedConstant d B*(1+4*oldMinorPivotConstant d B*oldMinorEntryConstant d)^2
  let K1:=2*sourcePartialFirstInverseCap d B*(sourceEndpointErrorConstant d C1)^2
  have hε:0≤ε:=graphPaperError_nonnegative a d N _ z hN hz.le
  have hεp:0≤εp:=by dsimp only[εp,RegularGraph.sourcePrime,inflatedPrime];positivity
  have hεle:ε≤εp:=by
    have hh:=mul_le_mul_of_nonneg_right (show 1≤Real.log (N:ℝ)^3 from one_le_pow₀ hL) hε
    simpa only[εp,RegularGraph.sourcePrime,inflatedPrime,one_mul] using hh
  have hK0:0≤K0:=by dsimp only[K0,oldMinorRetainedConstant];positivity
  have hμn:μ≤n:=by
    dsimp only[μ,n]
    simp only[Nat.cast_add]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hK1:K1≤sourceSelectedMinorConstant d B C1-K0:=by
    dsimp only[sourceSelectedMinorConstant,K0,K1]
    linarith [le_abs_self (2*sourcePartialFirstInverseCap d B*(sourceEndpointErrorConstant d C1)^2),
      le_abs_self (oldMinorRetainedConstant d B*(1+4*oldMinorPivotConstant d B*oldMinorEntryConstant d)^2)]
  have hK1nonneg:0≤K1:=by
    have hh:=finiteExtraReferenceConstant_ge_one d hd
    dsimp only[K1,sourcePartialFirstInverseCap]
    positivity
  intro Q hcard i j hi hj
  have hn:=hnew g o z hz hfloor hzB Cq badCount hplus hsource.1.1 labels samples i j
  have ho:=hold g o z hz hfloor hzB Cq badCount hsource hplus labels samples Q hcard i j hi hj
  rw [oldCommonSampleEntry_eq_outside_common g T labels samples selector z i j] at ho
  let v:=oldOwnSampleMinorEntry g.H T (s.selectedFirstEmbedding selector) (s.admissibleSecondVertex selector)
    (selected_first_ne_second s selector) Q z i j
  have hnewbound:‖new.G z (s.admissibleSecondVertex selector i) (s.admissibleSecondVertex selector j)-
      common.G z (selectedTipOutsideFirsts s selector i) (selectedTipOutsideFirsts s selector j)‖≤μ*K1*εp^2:=by
    convert hn using 1
    dsimp only[μ,K1,εp]
    ring
  have holdbound:‖v-common.G z (selectedTipOutsideFirsts s selector i) (selectedTipOutsideFirsts s selector j)‖≤n*K0*εp^2:=by
    apply ho.trans
    have hh:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε hεle 2) (show 0≤n*K0 by positivity)
    convert hh using 1
    dsimp only[n,K0]
    ring
  have ht:=norm_sub_le_norm_sub_add_norm_sub
    (new.G z (s.admissibleSecondVertex selector i) (s.admissibleSecondVertex selector j))
    (common.G z (selectedTipOutsideFirsts s selector i) (selectedTipOutsideFirsts s selector j)) v
  have hrev : ‖common.G z (selectedTipOutsideFirsts s selector i) (selectedTipOutsideFirsts s selector j)-v‖≤n*K0*εp^2 := by
    calc
      _ = ‖v-common.G z (selectedTipOutsideFirsts s selector i) (selectedTipOutsideFirsts s selector j)‖ := norm_sub_rev _ _
      _ ≤ _ := holdbound
  apply (ht.trans (add_le_add hnewbound hrev)).trans
  calc
    _ ≤ n*K1*εp^2+n*K0*εp^2:=by gcongr
    _ = n*(K1+K0)*εp^2:=by ring
    _ ≤ n*sourceSelectedMinorConstant d B C1*εp^2:=by gcongr;linarith only[hK1]
    _ = _:=by ring

end SpectralConsequences
