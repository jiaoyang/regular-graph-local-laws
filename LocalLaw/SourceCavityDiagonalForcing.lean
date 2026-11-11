import LocalLaw.ActualCavityDiagonalLeading
import LocalLaw.ActualTruncatedBoundaryColumns
import LocalLaw.SourceBoundaryDiagonal
import LocalLaw.SourceSurgeryGoodCounts
import LocalLaw.WeightedDiagonalDefect

/-! # Actual complete cavity diagonal forcing at epsilon/log^4 -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceCavityDiagonalForcingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceCavityDiagonalConstant (d J : ℕ) (β C1 : ℝ) : ℝ :=
  let V := 22+2*(finiteOmega d:ℝ)+(J:ℝ)
  actualCavityLeadingConstant d β C1 V +
    (sourceEndpointErrorConstant d C1+1)*V*cavityWeightMaxConstant d

namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem sourceTruncatedBoundaryDefect_eligible_diagonal (g : RegularGraph N d)
    (T : Set (Fin N)) (labels : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (q z : ℂ) (i : ι) (hi : (g.admissibleState T labels samples).Eligible selector i) :
    let s := g.admissibleState T labels samples
    let gnew := g.labelledResampledGraph T labels samples selector
    g.sourceTruncatedBoundaryDefect T labels samples selector q z i i =
      (gnew.deficient.delete T).G z (s.sampledOutsideSecond i).val (s.sampledOutsideSecond i).val-q := by
  dsimp only
  simp only [sourceTruncatedBoundaryDefect,Matrix.sub_apply,Matrix.submatrix_apply,Matrix.smul_apply,
    Matrix.one_apply,if_true,smul_eq_mul,mul_one]
  congr 1
  simp only [LabelledResamplingState.endpointFinalBoundaryRoot,dif_pos hi]
  rfl

theorem eventually_source_cavity_diagonal_forcing (a b d J : ℕ) (c β γ B C1 : ℝ) (Cq : ℕ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hγ : c/4<γ) (hgap : γ+β<1)
    (hB : 0≤B) (hC1 : 1≤C1)
    (hCdel : sourceDeletionConstant d β B≤C1) (hCq : finiteOmega d≤Cq) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      ∀ badCount : ℕ, badCount≤⌊(N:ℝ)^γ⌋₊ →
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      (graphBall g.graph o (logarithmicRadius (c/4) d N/8)).IsTree →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell := actualCavityDepth a d N z-1
      let R := logarithmicRadius (c/4) d N
      let T := graphBallVertices g.graph o ell
      let r := effectiveModelRadius a d N β
      let L := Real.log (N:ℝ)
      let ε := graphPaperError a d N (logarithmicRadius β d N) z
      let φ := correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
      let gnew := g.labelledResampledGraph T labels samples (R/4)
      let D := g.sourceTruncatedBoundaryDefect T labels samples (R/4) (g.Q z) z
      gnew.SourceOmegaWithRadii a r (logarithmicRadius β d N) R (finiteOmega d) badCount z →
      ¬g.sourceGreenIsolationBad T z φ (R/4) (Nat.ceil L) samples →
      (rejectedResamplingIndices g.graph T (R/4) samples).card≤J →
      g.SourceCavityWeightGood a c β C1 o z samples → ∀ j : g.graph.neighborSet o,
      ‖∑ i,g.cavityMinorWeights o ell (g.Q z) z j (labels i)*D i i‖≤
        sourceCavityDiagonalConstant d J β C1*(ε/L^4) := by
  let Vbad : ℝ := 22+2*(finiteOmega d:ℝ)+(J:ℝ)
  let A1 := cavityWeightL1Constant d β
  let W := cavityWeightMaxConstant d
  let K := actualCavityLeadingConstant d β C1 Vbad
  let D0 := sourceEndpointErrorConstant d C1
  have hA := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hA1 : 0≤A1 := by dsimp only [A1,cavityWeightL1Constant]; positivity
  have hW : 0≤W := by dsimp only [W,cavityWeightMaxConstant]; positivity
  have hVbad : 0≤Vbad := by dsimp only [Vbad]; positivity
  have hC10 : 0≤C1 := by linarith
  have hK : 0≤K := by
    dsimp only [K,actualCavityLeadingConstant,actualFixedWeightLeadingConstant,
      DeficientGraph.singletonObservationConstant,cavityWeightNoiseConstant,cavityWeightL1Constant,cavityWeightMaxConstant]
    positivity
  have hD0 : 0≤D0 := by dsimp only [D0,sourceEndpointErrorConstant]; positivity
  filter_upwards [eventually_actual_cavity_diagonal_leading a b d c β γ B C1 Vbad Cq
      ha hb hd hc hβ hβc hγ hgap hB hC1 hVbad hCdel hCq,
    eventually_source_cavity_minor_profile a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_boundary_defect_pattern a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_cavity_residual_le_sourcePrime a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1]
    with N hforce hprofiles hpattern hres hmargin hrad hnum
  intro g o z hz hzB hfloor badCount hbadCount hplus hTree ι _ labels samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let R := logarithmicRadius (c/4) d N
  let T := graphBallVertices g.graph o ell
  let r := effectiveModelRadius a d N β
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let φ := correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
  let s := g.admissibleState T labels samples
  let gnew := g.labelledResampledGraph T labels samples (R/4)
  let D := g.sourceTruncatedBoundaryDefect T labels samples (R/4) (g.Q z) z
  let prime := g.sourcePrime a (logarithmicRadius β d N) z
  let δ := (D0+1)*prime
  intro htarget hisolation hrejected hconcentration j
  have num := hnum z hz hfloor
  have hL : 1≤L := num.log_one
  have hLp : 0<L := by linarith
  have hε : 0≤ε := num.error_nonnegative
  have hφ : 0≤φ := by dsimp only [φ,correlationThreshold]; positivity
  have hprime : 0≤prime := by dsimp only [prime,sourcePrime,inflatedPrime]; positivity
  have hδ : 0≤δ := by dsimp only [δ]; positivity
  have hellR : ell≤R/8 := by
    have hh := hrad.2.2.2 z
    change r+ell+1≤R/8 at hh
    omega
  have hTreeEll := graphBall_tree_mono g.graph o hellR hTree
  obtain ⟨hell,hprofiles⟩ := hprofiles g o z hz hfloor Cq badCount hplus
  have hell' : 2≤ell := hell
  obtain ⟨hfit,hpat⟩ := hpattern g o z hz hfloor hzB Cq badCount hplus labels samples
  have hp := hpat φ hφ
  let good := g.sourceSurgeryGoodIndices o ell R hfit labels z φ samples
  have hbad : ((Finset.univ\good).card:ℝ)≤Vbad*L^2 :=
    g.sourceSurgeryGoodIndices_bad_log_bound o ell R (finiteOmega d) J hfit (hplus.structural.1 o)
      labels z φ samples hL hisolation hrejected
  have hproperties (i : ι) (hi : i∈good) := g.sourceSurgeryGoodLabels_properties o ell R hfit z φ
    samples (labels i) (Finset.mem_filter.mp hi).2
  have heligible : ∀ i∈good,s.Eligible (R/4) i := fun i hi => (Finset.mem_filter.mp (hproperties i hi).2.2).2
  have hcorrelation : ∀ i∈good,labels i∈g.sourceCorrelationGoodLabels T z φ (R/4) samples :=
    fun i hi => (hproperties i hi).1
  have hleading := hforce g o z hz hzB hfloor badCount hbadCount hplus hTreeEll labels samples
    badCount htarget good heligible hcorrelation hbad hconcentration j
  have hweights := (hprofiles (g.cavityNeighborInBall o ell hell j) j.property.symm hTreeEll).2
  have hl1 : (∑ i,‖g.cavityMinorWeights o ell (g.Q z) z j (labels i)‖)≤A1*L := by
    rw [labels.sum_comp (fun α => ‖g.cavityMinorWeights o ell (g.Q z) z j α‖)]
    simp only [cavityMinorWeights,dif_pos hell']
    exact hweights.1
  have hgain : L^9≤resamplingDecayDenominator d ell := selected_radius_decay_gain a d N z ha hd hL
  have hmax : ∀ i∉good,‖g.cavityMinorWeights o ell (g.Q z) z j (labels i)‖≤W/L^9 := by
    intro i _
    simp only [cavityMinorWeights,dif_pos hell']
    exact (hweights.2.2 (labels i)).trans (div_le_div_of_nonneg_left hW (pow_pos hLp 9) hgain)
  have hsep : 2*r+2≤R/4 := by dsimp only [r,R]; omega
  have hr : r+2≤R/4 := by dsimp only [r,R]; omega
  have hroom : ell+r+1≤R/8 := by
    have hh := hrad.2.2.2 z
    change r+ell+1≤R/8 at hh
    omega
  have hdecomp := g.sourceTruncatedBoundaryDefect_tree_decomposition hd o ell (R/4) r (R/8) hsep hr hroom hTree
    labels samples (g.Q z) z hz (g.Q_im_nonnegative z hz)
  have hscalar : ‖cavityIterate z (g.Q z) (r+1)-g.Q z‖≤prime := by
    rw [norm_sub_rev]
    exact hres z (g.Q z) hz hzB hfloor hplus.cavity
  have hglobal (i : ι) : ‖D i i‖≤δ := by
    have heq := congrFun (congrFun hdecomp i) i
    simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply,if_true,smul_eq_mul,mul_one] at heq
    rw [show D i i = _ from heq]
    exact (norm_add_le _ _).trans ((add_le_add (hp.1 i i) hscalar).trans_eq (by dsimp only [δ,D0,prime]; ring))
  have hDgood : ∀ i∈good,D i i=(gnew.deficient.delete T).G z
      (s.sampledOutsideSecond i).val (s.sampledOutsideSecond i).val-g.Q z :=
    fun i hi => g.sourceTruncatedBoundaryDefect_eligible_diagonal T labels samples (R/4) (g.Q z) z i (heligible i hi)
  have htransfer := weighted_diagonal_defect_transfer good
    (fun i => g.cavityMinorWeights o ell (g.Q z) z j (labels i)) (fun i => D i i)
    (fun i => (gnew.deficient.delete T).G z (s.sampledOutsideSecond i).val (s.sampledOutsideSecond i).val)
    (g.Q z) (g.Q z) (K*(ε/L^4)) (A1*L) δ (W/L^9)
    (by positivity) (by positivity) hδ (by positivity) hDgood hleading hl1 hglobal hmax
  have hbadTerm : δ*((Finset.univ\good).card:ℝ)*(W/L^9)≤(D0+1)*Vbad*W*(ε/L^4) := by
    calc
      _ ≤ δ*(Vbad*L^2)*(W/L^9) := by gcongr
      _ = _ := by dsimp only [δ,prime,sourcePrime,inflatedPrime]; field_simp; ring
  simpa only [sub_self,norm_zero,zero_mul,add_zero,sourceCavityDiagonalConstant]
    using htransfer.trans ((add_le_add_left hbadTerm (K*(ε/L^4)+‖g.Q z-g.Q z‖*(A1*L))).trans_eq (by
      simp only [sub_self,norm_zero,zero_mul,add_zero]
      dsimp only [sourceCavityDiagonalConstant,K,Vbad,D0,W]
      ring))

end RegularGraph
end LocalLaw
