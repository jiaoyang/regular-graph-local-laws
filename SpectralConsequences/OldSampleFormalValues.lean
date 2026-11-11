import LocalLaw.FullSampleTreeValues
import LocalLaw.FullSampleSeparation
import LocalLaw.PairModelReferenceBounds
import LocalLaw.PairModelFarZero
import LocalLaw.SourceFormalKernelInverse
import LocalLaw.SourceFormalEdgeBounds
import LocalLaw.IndependentRadiusEvents

/-! # Actual old sampled-edge entries at the formal q-dependent tree values

The original weak event gives the physical-to-pair-model error. Eligibility
supplies genuine full-graph tree balls. The finite tree-patch theorem then
identifies the q-dependent diagonal and adjacent values with O(log N epsilon)
error. No physical sampled-entry approximation is an input.
-/
open Filter
noncomputable section
set_option maxHeartbeats 2200000
namespace SpectralConsequences
open LocalLaw
local instance oldSampleFormalDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def oldSampleFormalConstant (d:ℕ) (β B:ℝ) : ℝ :=
  treePatchWeakConstant d B (sourceObservationLogCap d β)+1

namespace RegularGraph

theorem eventually_old_sample_formal_values (a b d:ℕ) (c β B:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hβ:0<β) (hβc:β≤c/32) :
    ∀ᶠ N:ℕ in atTop, ∀ (g:LocalLaw.RegularGraph N d) (o:Fin N) (z:ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z →
      ∀ {ι:Type} [Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let s:=g.admissibleState T labels samples
      let q:=g.Q z
      let p:=rationalTreeReference (d-1) q
      let δ:=oldSampleFormalConstant d β B*Real.log (N:ℝ)*
        graphPaperError a d N (logarithmicRadius β d N) z
      (∀ (i:s.AdmissibleSampleIndex selector) (v:(Tᶜ:Set (Fin N))),
        v∈s.admissiblePairRoots selector i → ‖g.G z v.val v.val-p‖≤δ) ∧
      (∀ i:s.AdmissibleSampleIndex selector,
        ‖g.G z (s.admissibleSampleVertex selector i).val (s.admissibleSecondVertex selector i).val-
          p*(-q*treeEdgeWeight d)‖≤δ) ∧
      (∀ (i j:s.AdmissibleSampleIndex selector),i≠j → ∀ (v w:(Tᶜ:Set (Fin N))),
        v∈s.admissiblePairRoots selector i → w∈s.admissiblePairRoots selector j →
          ‖g.G z v.val w.val‖≤graphPaperError a d N (logarithmicRadius β d N) z) := by
  let A:=sourceObservationLogCap d β
  have hA:0≤A:=sourceObservationLogCap_nonnegative d hd β hβ.le
  filter_upwards [eventually_sourceObservationBounds a b d c β B 1 ha hb hd hc hβ hβc (by norm_num),
    eventually_source_formal_kernel_bounds a b d c β B 1 A ha hb hd hc hβ hβc (by norm_num) hA,
    eventually_source_formal_kernel_inverse_bound a b d c β B 1 ha hb hd hc hβ hβc (by norm_num),
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc]
    with N hnum hformal hinverse hmargin
  intro g o z hz hzB hfloor badCount hsource ι _ labels samples
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let R:=logarithmicRadius (c/4) d N
  let s:=g.admissibleState T labels samples
  let q:=g.Q z
  let p:=rationalTreeReference (d-1) q
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let K:=treePatchWeakConstant d B A
  have happrox : ∀ x y, ‖g.G z x y-g.P r z q x y‖≤ε := hsource.2.2
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
  have hsep:2*r+2≤selector:=by dsimp only [r,selector];omega
  have hclass:4*r+1≤R:=by dsimp only [r,R];omega
  have hbudget (x y:Fin N):(g.deficient.restrict (pairBallVertices g.graph x y r)).ComponentFiniteReferenceBudget:=
    (g.pairModel_componentReferenceBudget x y r R hclass hsource.1.1).to_componentFinite
  have hD (x y:Fin N):∀u v:pairBallVertices g.graph x y r,
      ((g.deficient.restrict (pairBallVertices g.graph x y r)).graph).dist u v≤4*r+1:=
    pairBall_distance_bound g.graph x y r
  have herr:ε≤L*ε:=by
    exact le_mul_of_one_le_left num.error_nonnegative num.log_one
  have hdiag (i:s.AdmissibleSampleIndex selector) (v:(Tᶜ:Set (Fin N)))
      (hv:v∈s.admissiblePairRoots selector i):
      ‖g.G z v.val v.val-p‖≤(K+1)*L*ε:=by
    let S:=pairBallVertices g.graph v.val v.val r
    let u:S:=pairBallLeft g.graph v.val v.val r
    have htree:=g.full_sample_diagonal_weak_value hd T labels samples selector r (by omega) i v hv
      S (hbudget _ _) u rfl (4*r+1) q p z hf.1 hp hz (g.Q_im_nonnegative z hz)
      B 1 ε L A hzB num hprior (hD _ _) num.pair_log hf.2.2.1 hi.2 hqpow
    have happ:=happrox v.val v.val
    have hmodel:g.P r z q v.val v.val=(g.deficient.restrict S).extensionGreen q z u u:=by
      exact (g.deficient_P r z q v.val v.val).symm
    rw [hmodel] at happ
    have hh:=(norm_sub_le_norm_sub_add_norm_sub (g.G z v.val v.val)
      ((g.deficient.restrict S).extensionGreen q z u u) p).trans (add_le_add happ htree)
    norm_num only [one_pow,one_mul,mul_one] at hh
    dsimp only [K] at *
    nlinarith only [hh,herr]
  constructor
  · intro i v hv
    simpa only [oldSampleFormalConstant,K] using hdiag i v hv
  constructor
  · intro i
    let v:=s.admissibleSampleVertex selector i
    let w:=s.admissibleSecondVertex selector i
    let S:=pairBallVertices g.graph v.val w.val r
    let u:S:=pairBallLeft g.graph v.val w.val r
    let u':S:=pairBallRight g.graph v.val w.val r
    have htree:=g.full_sample_adjacent_weak_value hd T labels samples selector r (by omega) i
      S (hbudget _ _) u u' rfl rfl (4*r+1) q p z hf.1 hp hz (g.Q_im_nonnegative z hz)
      B 1 ε L A hzB num hprior (hD _ _) num.pair_log hf.2.2.1 hi.2 hqpow
    have happ:=happrox v.val w.val
    have hmodel:g.P r z q v.val w.val=(g.deficient.restrict S).extensionGreen q z u u':=by
      exact (g.deficient_P r z q v.val w.val).symm
    rw [hmodel] at happ
    have hh:=(norm_sub_le_norm_sub_add_norm_sub (g.G z v.val w.val)
      ((g.deficient.restrict S).extensionGreen q z u u') (p*(-q*treeEdgeWeight d))).trans
        (add_le_add happ htree)
    norm_num only [one_pow,one_mul,mul_one] at hh
    dsimp only [oldSampleFormalConstant,K]
    nlinarith only [hh,herr]
  · intro i j hij v w hv hw
    have hfar:=s.admissiblePairRoots_ambient_separated selector (by omega) i j hij v w hv hw
    have hfar':((2*r+1:ℕ):ℕ∞)<g.graph.edist v.val w.val:=
      (ENat.coe_le_coe.mpr (by omega:2*r+1≤selector-1)).trans_lt hfar
    have hzero:=g.deficient.P_eq_zero_of_edist_gt hd r q z hz (g.Q_im_nonnegative z hz) v.val w.val hfar'
    rw [g.deficient_P] at hzero
    simpa only [hzero,sub_zero] using happrox v.val w.val

end RegularGraph
end SpectralConsequences
