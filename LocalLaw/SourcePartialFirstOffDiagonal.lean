import LocalLaw.SourcePartialFirstInverseCaps
import LocalLaw.ActualPartialBOffDiagonal

/-! # Actual switched sampled-first correlations at the weak residual rate -/

open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance sourcePartialFirstOffDiagonalDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourcePartialFirstOffDiagonalConstant (d : ℕ) (β B C1 : ℝ) : ℝ :=
  let C:=4+8*finiteExtraReferenceConstant d
  2*finiteExtraReferenceConstant d*C1^2+
    2*(1+C*4)^2*(|sourcePartialCovarianceConstant d β B C1|+1)

namespace RegularGraph

theorem eventually_source_partial_first_offdiagonal (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in atTop,∀(g : RegularGraph N d)(o : Fin N)(z q : ℂ),
      0<z.im→‖z‖≤B→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→0≤q.im→
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z)→
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d)→
      ∀{ι : Type}[Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y : ((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      ∀S:Set (Tᶜ:Set (Fin N)),S⊆s.twoTargetEndpointVertices selector r x y→
      let H:=(((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S).extensionGreen q z
      ∀u v:s.partialFirstMask selector S,u≠v→
        ‖H (s.partialFirstEmbedding selector S u) (s.partialFirstEmbedding selector S v)‖≤
          sourcePartialFirstOffDiagonalConstant d β B C1*Real.log (N:ℝ)*
            graphPaperError a d N (logarithmicRadius β d N) z := by
  let Acap:=sourcePartialObservationLogCap d β
  let F:=2*(finiteOmega d:ℝ)+5
  let K:=4*finiteExtraReferenceConstant d
  let C:=4+2*K
  let M:=1+C*4
  let D:=|sourcePartialCovarianceConstant d β B C1|+1
  have hF : 1≤F := by dsimp only [F]; have hh:=Nat.cast_nonneg (α:=ℝ) (finiteOmega d); linarith
  have hAobs : 0≤sourceObservationLogCap d β := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hAcap : sourceObservationLogCap d β≤Acap := le_mul_of_one_le_left hAobs hF
  have hK : 0≤K := by dsimp only [K]; linarith [finiteExtraReferenceConstant_ge_one d hd]
  have hC : 0≤C := by dsimp only [C]; positivity
  have hD : 0≤D := by dsimp only [D]; positivity
  have hM : 0≤M := by dsimp only [M]; positivity
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_source_partial_generic_inputs a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_partial_geometry a d c β (by omega) hd hc hβ hβc,
    eventually_sourceObservationBounds_of_cap a b d c β B C1 Acap ha hb hd hc hβ hβc hC1 hAcap,
    eventually_source_formal_kernel_bounds a b d c β B C1 0 ha hb hd hc hβ hβc hC1 (by norm_num),
    eventually_source_formal_edge_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_partial_endpoint_surgery_smallness a b d β C 4 D ha hb hd hβ hC (by norm_num) hD,
    eventually_source_radius_hierarchy a d c β hd hc hβ hβc,hdepth]
    with N hinputs hgeometry hnum hformal hedge hcontract hradii hdepthN
  intro g o z q hz hzB hfloor hqim hprior hballs ι _ labels samples x y
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let R:=hereditaryReferenceRadius d (augmentedObservationDiameter d r)
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let p:=rationalTreeReference (d-1) q
  let δ:=D*L*ε
  let w:=2*‖treeEdgeWeight d‖+‖q‖*‖treeEdgeWeight d‖^2
  have hell : ell≤doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepthN).2
  have num:=hnum z hz hfloor
  have hf:=hformal z q hz hzB hfloor hprior
  have he:=hedge z q hz hzB hfloor hprior
  have hL0 : 0≤L := by linarith [num.log_one]
  have hδ : 0≤δ := mul_nonneg (mul_nonneg hD hL0) num.error_nonnegative
  have hprior' := hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative hC1)
  have hscaled : 0≤C1^2*ε := mul_nonneg (sq_nonneg C1) num.error_nonnegative
  have hαsq : ‖treeEdgeWeight d‖^2≤1 := by
    rw [treeEdgeWeight_norm_sq d hd]
    have hh : (3:ℝ)≤d := Nat.cast_le.mpr hd
    exact (div_le_one (by linarith)).mpr (by linarith)
  have hα : ‖treeEdgeWeight d‖≤1 := by nlinarith [norm_nonneg (treeEdgeWeight d)]
  have hw0 : 0≤w := by dsimp only [w]; positivity
  have hw : w≤4 := by
    have hh:=mul_le_mul he.1 hαsq (sq_nonneg ‖treeEdgeWeight d‖) (by norm_num:(0:ℝ)≤2)
    dsimp only [w]
    nlinarith
  have hMw : 1+C*w≤M := by
    have hh:=mul_le_mul_of_nonneg_left hw hC
    dsimp only [M]
    linarith
  have hMw0 : 0≤1+C*w := by positivity
  have hδprime : δ≤D*g.sourcePrime a (logarithmicRadius β d N) z := by
    have hpowers : L≤L^3 := by simpa only [pow_one] using pow_le_pow_right₀ num.log_one (by omega:1≤3)
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpowers hD) num.error_nonnegative).trans_eq (by
      change D*L^3*ε=D*(L^3*ε);ring)
  have ht : physicalTransfer d z^selector≤C1^2*ε := by
    have hρ0 := (physicalTransfer_pos d hd z).le
    have hρone : physicalTransfer d z≤1 := by nlinarith [physicalTransfer_sq_le_half d hd z]
    have hrad : 2*r≤selector := (Nat.mul_le_mul_left 2 (Nat.sub_le (logarithmicRadius β d N) (modelRadiusLoss a d N))).trans hradii.2.2.1
    exact (pow_le_pow_of_le_one hρ0 hρone hrad).trans num.tail
  have hi:=hinputs g o z q hz hzB hfloor hqim hprior hballs labels samples x y
  have hgeo:=hgeometry g o z hballs labels samples x y
  intro S hS
  let G:=((g.deficient.delete T).restrict S).extensionGreen q z
  let e:=s.partialEndpointEmbedding selector S
  let n:ℝ:=Fintype.card (s.PartialEndpointIndex selector S)
  obtain ⟨hbudget,hR,hRlog⟩:=hgeo S hS
  have hsmallOld:=(DeficientGraph.weak_localization_feedback_budgets d hd z q hz B (C1^2*ε) L Acap
    hscaled num.log_one num.log_cap_nonnegative num.error_scaled hprior'
    R (4*r+1) hRlog num.pair_log num.localization_large).1
  have hsmall : n*(1+C*w)*w*δ≤1/2 := by
    have hh:=hcontract g o ell hell labels samples selector z hz hfloor S
    have hp:=mul_le_mul hMw hw hw0 hM
    calc
      _=(n*δ)*((1+C*w)*w) := by ring
      _≤(n*(D*g.sourcePrime a (logarithmicRadius β d N) z))*(M*4) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hδprime (Nat.cast_nonneg _)) hp
          (mul_nonneg hMw0 hw0) (mul_nonneg (Nat.cast_nonneg _) (hδ.trans hδprime))
      _=n*(1+C*4)*4*(D*g.sourcePrime a (logarithmicRadius β d N) z) := by dsimp only [M];ring
      _≤1/2 := hh
  have hSinputs:=hi S hS
  have hcov : ∀i j,‖(G.submatrix e e-s.partialOldCovariance selector S G q p (treeEdgeWeight d)) i j‖≤δ := by
    intro i j
    have hcoef : sourcePartialCovarianceConstant d β B C1≤D := by dsimp only [D];linarith [le_abs_self (sourcePartialCovarianceConstant d β B C1)]
    exact (hSinputs.1 i j).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hL0) num.error_nonnegative)
  have hout:=g.partial_model_first_offdiagonal hd T labels samples selector S hbudget q p z hz hqim
    hf.1 hf.2.1 hf.2.2.2.1 R hR hsmallOld 4 K δ (by norm_num) hK hδ
    (he.1.trans (by norm_num)) hf.2.2.1 he.2 hSinputs.2.2.1 hcov hsmall
  intro u v huv
  have hlead : ‖treeEdgeWeight d*q‖^2*(2*finiteExtraReferenceConstant d*physicalTransfer d z^selector)≤
      2*finiteExtraReferenceConstant d*C1^2*L*ε := by
    have hC0 : 0≤2*finiteExtraReferenceConstant d := by linarith [finiteExtraReferenceConstant_ge_one d hd]
    have ht' : physicalTransfer d z^selector≤C1^2*L*ε := ht.trans (by
      have hh:=mul_le_mul_of_nonneg_left num.log_one hscaled
      convert hh using 1 <;> ring)
    calc
      _≤1*(2*finiteExtraReferenceConstant d*(C1^2*L*ε)) :=
        mul_le_mul (by simpa using pow_le_pow_left₀ (norm_nonneg _) he.2 2)
          (mul_le_mul_of_nonneg_left ht' hC0) (mul_nonneg hC0 (pow_nonneg (physicalTransfer_pos d hd z).le _)) (by norm_num)
      _=_ := by ring
  have hquad : 2*(1+C*w)^2*δ≤2*M^2*D*L*ε := by
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMw0 hMw 2) (by norm_num)) hδ).trans_eq (by dsimp only [δ];ring)
  exact (hout u v huv).trans ((add_le_add hlead hquad).trans_eq (by
    dsimp only [sourcePartialFirstOffDiagonalConstant,C,K,M,D]
    ring))

end RegularGraph
end LocalLaw
