import LocalLaw.ActualSwitchingQChange
import LocalLaw.CavityIterationContinuity
import LocalLaw.SourceObservationParameters
import LocalLaw.BoundaryPerturbationParameters

/-! # Actual selected-depth cavity iterate transport to the target Q -/

noncomputable section
namespace LocalLaw
namespace RegularGraph

theorem eventually_actual_selected_cavity_parameter_change (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) (hB : 0≤B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let gnew := g.labelledResampledGraph T labels samples (logarithmicRadius (c/4) d N/4)
      gnew.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z →
      ‖cavityIterate z (g.Q z) (actualCavityDepth a d N z)-
        cavityIterate z (gnew.Q z) (actualCavityDepth a d N z)‖≤
        graphPaperError a d N (logarithmicRadius β d N) z/Real.log (N:ℝ)^8 := by
  have hC10 : 0≤C1 := by linarith
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_actual_switching_Q_change a b d c β B C1 ha hb hd hc hβ hβc hC10 hB,
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_kernel_feedback a b d β C1 1 1 ha hb hd hβ hC10 (by norm_num) (by norm_num),
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,
    eventually_log_ge_nat 4,hdepth] with N hchange hnum hfeedback hrad hlog hdepth
  intro g o z hz hzB hfloor Cq badCount hplus ι _ labels samples
  dsimp only
  let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let gnew := g.labelledResampledGraph T labels samples (logarithmicRadius (c/4) d N/4)
  let rn := logarithmicRadius β d N
  let n := actualCavityDepth a d N z
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N rn z
  intro htarget
  have num := hnum z hz hfloor
  have hε : 0≤ε := num.error_nonnegative
  have hL : 1≤L := num.log_one
  have hLp : 0<L := by linarith
  have hΨ : 0≤scalarScale (spectralScale z) ε := scalarScale_nonneg hε
  have hpriorNew : ‖gnew.Q z-semicircleRoot z‖≤C1*scalarScale (spectralScale z) ε :=
    htarget.2.1.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC1 hΨ)
  have hn : n≤2*rn+1 := by
    have hh := (actualCavityDepth_radius_bounds a d N z hdepth).2
    have hr := hrad.1
    unfold modelRadiusLoss at hr
    dsimp only [n,rn]
    omega
  have hnReal : (n:ℝ)≤2*(rn:ℝ)+1 := by exact_mod_cast hn
  have hsmall (q : ℂ) (hq : ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z) ε) :
      (n:ℝ)*‖q-semicircleRoot z‖≤1/2 := by
    have hh := hfeedback z q hz hfloor hq
    simp only [mul_one] at hh
    exact (mul_le_mul_of_nonneg_right hnReal (norm_nonneg _)).trans (by simpa only [mul_comm] using hh)
  have hiter := cavityIterate_lipschitz_of_small (semicircleRoot_equation z) (semicircleRoot_norm_le_one z) n
    (hsmall (g.Q z) hplus.cavity) (hsmall (gnew.Q z) hpriorNew)
  have hQ := hchange g o z hz hzB hfloor Cq badCount hplus labels samples htarget
  apply hiter.trans
  calc
    _ ≤ 4*(ε/L^16) := mul_le_mul_of_nonneg_left hQ (by norm_num)
    _ ≤ ε/L^8 := by
      have hfour : 4≤L^8 := hlog.trans (le_self_pow₀ hL (by omega))
      apply (le_div_iff₀ (pow_pos hLp 8)).mpr
      have hh := mul_le_mul_of_nonneg_right hfour hε
      have hid : (4*(ε/L^16))*L^8=4*ε/L^8 := by field_simp; ring
      rw [hid]
      exact (div_le_iff₀ (pow_pos hLp 8)).mpr (by nlinarith only [hh])

end RegularGraph
end LocalLaw
