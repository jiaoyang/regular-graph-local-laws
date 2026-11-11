import LocalLaw.NearOutsideModelComparison
import LocalLaw.SourceObservationParameters
import LocalLaw.ActualSwitchingQChange
import LocalLaw.SourceOmegaPlusTransferEffective

/-! Actual second-stage outside approximation on the genuine target model. -/
noncomputable section
set_option maxHeartbeats 3000000
namespace LocalLaw
local instance actualNearOutsideDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_actual_near_outside_comparison (a b d : ℕ) (c β B C1 : ℝ) (Cq : ℕ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c) (hβ : 0<β) (hβc : β≤c/32)
    (hB : 0≤B) (hC1 : 1≤C1) (hCdel : sourceDeletionConstant d β B≤C1) (hCq : finiteOmega d≤Cq) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (boundary : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let r:=effectiveModelRadius a d N β
      let selector:=logarithmicRadius (c/4) d N/4
      let gnew:=g.labelledResampledGraph T boundary samples selector
      gnew.SourceOmegaWithRadii a r (logarithmicRadius β d N) (logarithmicRadius (c/4) d N)
        (finiteOmega d) badCount z →
      ∀ (S : Set (Tᶜ : Set (Fin N))), ((gnew.deficient.delete T).restrict S).ComponentFiniteReferenceBudget →
      ∀ R : ℕ, (∀ u v,((gnew.deficient.delete T).restrict S).graph.dist u v≤R) →
      (R:ℝ)+1≤sourceObservationLogCap d β*Real.log (N:ℝ) →
      ∀ {I : Type} (e : I↪S),
      (∀ i,graphBallVertices (outsideGraph gnew.graph T) (e i).val r⊆S) →
      ∀ i j, ‖(gnew.deficient.delete T).G z (e i).val (e j).val-
        ((gnew.deficient.delete T).restrict S).extensionGreen (g.Q z) z (e i) (e j)‖≤
          (2*C1+1)*g.sourcePrime a (logarithmicRadius β d N) z := by
  let K:=16*finiteExtraReferenceConstant d^2*coreConvolutionConstant (finiteOmega d+1)
  have hK : 0≤K := by dsimp only [K]; have hh:=coreConvolutionConstant_nonnegative (finiteOmega d+1); positivity
  have hC10 : 0≤C1 := (by norm_num : (0:ℝ)≤1).trans hC1
  filter_upwards [eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_switching_Q_change a b d c β B C1 ha hb hd hc hβ hβc hC10 hB,
    eventually_sourceOmegaWithRadii_subset_sourceOmegaPlusWithRadii a b d c β B C1 Cq
      ha hb hd hc hβ hβc hB hC1 hCdel hCq,
    eventually_log_ge_nat K,eventually_log_ge_nat 1,Filter.eventually_ge_atTop 1]
    with N hnum hchange hplusTarget hlarge hL hN
  intro g o z hz hzB hfloor badCount hplus ι _ boundary samples
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let r:=effectiveModelRadius a d N β
  let selector:=logarithmicRadius (c/4) d N/4
  let s:=g.admissibleState T boundary samples
  let gnew:=g.labelledResampledGraph T boundary samples selector
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let L:=Real.log (N:ℝ)
  intro target S hbudget R hdiam hRlog I e hcapture i j
  have hp:=hplusTarget gnew o z badCount hz hzB hfloor target
  have hTnew : graphBallVertices gnew.graph o ell=T := by
    have hT : T=graphSetBall s.graph {o} ell := by rw [graphSetBall_singleton]; rfl
    have hh:=s.fullResample_ball selector {o} ell hT
    change graphBallVertices (s.fullResample selector).graph o ell=T
    simpa only [graphSetBall_singleton] using hh
  have hpair : ∀ u v, ‖(gnew.deficient.delete T).G z (e u).val (e v).val-
      (gnew.deficient.delete T).P r z (gnew.Q z) (e u).val (e v).val‖≤C1*L^3*ε := by
    have hh:=hp.deleted
    change ∀ u v : ((graphBallVertices gnew.graph o ell)ᶜ : Set (Fin N)),
      ‖(gnew.deficient.delete _).G z u v-gnew.deletedP _ r z (gnew.Q z) u v‖≤
        C1*gnew.sourcePrime a (logarithmicRadius β d N) z at hh
    rw [hTnew] at hh
    intro u v
    simpa only [sourcePrime,inflatedPrime,mul_assoc] using hh (e u).val (e v).val
  have hfinal:=(gnew.deficient.delete T).source_restriction_two_boundary_comparison hd S e r R
    z (g.Q z) (gnew.Q z) hz (g.Q_im_nonnegative z hz) (gnew.Q_im_nonnegative z hz)
    B C1 ε L (sourceObservationLogCap d β) hzB (hnum z hz hfloor)
    hbudget hdiam hRlog hcapture hplus.cavity hp.cavity hpair i j
  have hQ:=hchange g o z hz hzB hfloor Cq badCount hplus boundary samples target
  have hε : 0≤ε := graphPaperError_nonnegative a d N _ z hN hz.le
  have hLp : 0<L := by dsimp only [L]; linarith
  have hKpow : K≤L^16 := hlarge.trans (by simpa only [pow_one] using pow_le_pow_right₀ hL (by omega : 1≤16))
  have hterm : K*‖g.Q z-gnew.Q z‖≤L^3*ε := by
    calc
      _ ≤ K*(ε/L^16) := mul_le_mul_of_nonneg_left hQ hK
      _ = ε*(K/L^16) := by ring
      _ ≤ ε*1 := mul_le_mul_of_nonneg_left ((div_le_one (pow_pos hLp _)).mpr hKpow) hε
      _ = ε := mul_one _
      _ ≤ L^3*ε := le_mul_of_one_le_left hε (one_le_pow₀ hL)
  exact (hfinal.trans (add_le_add_left hterm _)).trans_eq (by unfold sourcePrime inflatedPrime; ring)

end RegularGraph
end LocalLaw
