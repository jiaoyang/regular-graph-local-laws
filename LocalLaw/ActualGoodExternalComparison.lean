import LocalLaw.ActualGoodDiagonalObservation
import LocalLaw.SourceGoodExternalComparison
import LocalLaw.StrongDeletedGreenCaps
import LocalLaw.PairModelFarZero
import LocalLaw.SampledErrorColumns

/-!
# Actual good sampled tip to an arbitrary external target

The retained target weak event supplies its actual strong structural budget,
global deleted caps and plus comparison. Old F2 correlation and a far new
sampled first endpoint give the two small target factors. No old strong
structural event, augmented model class or physical cap is a premise.
-/
noncomputable section
set_option maxHeartbeats 3000000
namespace LocalLaw
local instance actualGoodExternalDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceGoodExternalBudget (d : ℕ) (B μ φ δ : ℝ) : ℝ :=
  let C := guardedGreenEntryCap d
  let P := sourceGreenPivotCap d B
  (1+C*P)*φ+3*μ*((1+C*P)*φ)*endpointSurgeryCouplingCap d*(C+C^2*P)+δ^2*P

namespace RegularGraph

theorem eventually_actual_good_external_comparison (a b d : ℕ) (c β B C1 : ℝ) (Cq : ℕ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hB : 0≤B) (hC1 : 1≤C1)
    (hCdel : sourceDeletionConstant d β B≤C1) (hCq : finiteOmega d≤Cq) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let R := logarithmicRadius (c/4) d N
      let selector := R/4
      let r := effectiveModelRadius a d N β
      let s := g.admissibleState T boundary samples
      let gnew := g.labelledResampledGraph T boundary samples selector
      let φ := correlationThreshold (Real.log (N:ℝ)) a N z.im (graphKestenMcKayReference d z).im
        (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z)
      let δ := sourceEndpointErrorConstant d C1*g.sourcePrime a (logarithmicRadius β d N) z
      ∀ targetBadCount : ℕ,
      gnew.SourceOmegaWithRadii a r (logarithmicRadius β d N) R (finiteOmega d) targetBadCount z →
      ∀ i : s.AdmissibleSampleIndex selector,
      boundary i.val∈g.sourceCorrelationGoodLabels T z φ selector samples →
      ∀ j : (Tᶜ : Set (Fin N)),
      boundary i.val∉g.correlatedSampleIndices T z φ selector j samples →
      ((2*r+1:ℕ):ℕ∞)<(outsideGraph gnew.graph T).edist (s.admissibleSampleVertex selector i) j →
      ‖(gnew.deficient.delete T).G z (s.admissibleSecondVertex selector i) j‖≤
        sourceGoodExternalBudget d B (Nat.card (BoundaryOrientedEdge g.graph T):ℝ) φ δ := by
  let C := guardedGreenEntryCap d
  let P := sourceGreenPivotCap d B
  let D := sourceEndpointErrorConstant d C1
  have hCextra := finiteExtraReferenceConstant_ge_one d hd
  have hC : 0≤C := by dsimp only [C,guardedGreenEntryCap,commonGreenEntryCap]; linarith
  have hCone : 1≤C := by dsimp only [C,guardedGreenEntryCap,commonGreenEntryCap]; linarith
  have hP : 0≤P := by dsimp only [P,sourceGreenPivotCap]; have hh:=finiteReferenceConstant_ge_one d hd; positivity
  have hC10 : 0≤C1 := (by norm_num : (0:ℝ)≤1).trans hC1
  have hD : 0≤D := sourceEndpointErrorConstant_nonnegative d C1 hC10
  have hDC1 : C1≤D := by
    have hM : 1≤1+endpointSurgeryModelRowCap d (2*(finiteOmega d+1))*endpointSurgeryCouplingCap d := by
      have hp : 0≤endpointSurgeryModelRowCap d (2*(finiteOmega d+1))*endpointSurgeryCouplingCap d := by
        dsimp only [endpointSurgeryModelRowCap,endpointSurgeryCouplingCap]
        positivity
      linarith
    have hM2 : 1≤(1+endpointSurgeryModelRowCap d (2*(finiteOmega d+1))*endpointSurgeryCouplingCap d)^2 := by nlinarith
    dsimp only [D,sourceEndpointErrorConstant]
    nlinarith [mul_le_mul_of_nonneg_right hM2 hC10]
  filter_upwards [eventually_source_new_endpoint_caps_of_post_budget a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_new_sample_pivot_caps a b d c β B C1 ha hb hd hc hβ hβc hC10 hB,
    eventually_actualGuardedDeletionCaps a b d c β C1 B ha hb hd hc hβ hβc hC10 hB,
    eventually_sourceOmegaWithRadii_subset_sourceOmegaPlusWithRadii a b d c β B C1 Cq
      ha hb hd hc hβ hβc hB hC1 hCdel hCq,
    eventually_strong_deleted_green_caps a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4),
    eventually_log_ge_nat 1,Filter.eventually_ge_atTop 1]
    with N hnew hnewPivot hcaps htarget hglobal hmargin hdepth hlog hN
  intro g o z hz hzB hscale badCount hplus ι _ boundary samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let R := logarithmicRadius (c/4) d N
  let selector := R/4
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary samples
  let gnew := g.labelledResampledGraph T boundary samples selector
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let φ := correlationThreshold (Real.log (N:ℝ)) a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
  let δ := D*g.sourcePrime a (logarithmicRadius β d N) z
  intro targetBadCount target i hgood j huncorr hfar
  have targetPlus := htarget gnew o z targetBadCount hz hzB hscale target
  have hell : ell≤doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hcentral : ell+r+1≤R/8 := by dsimp only [ell,r,R]; omega
  have hsep : 2*r+2≤selector := by dsimp only [r,selector,R]; omega
  have hpost := g.switchedEndpointModel_component_budget hd o ell selector r (R/8)
    hcentral hsep (hplus.structural.1 o) boundary samples
  obtain ⟨hδone,hentry,hcross⟩ := hnew g o z hz hscale hzB Cq badCount hplus boundary samples hpost
  have hpivot := hnewPivot g o z hz hscale hzB boundary samples Cq targetBadCount targetPlus i
  have oldCaps := hcaps g o z hz hzB hscale Cq badCount hplus
  have hφ : 0≤φ := by unfold φ correlationThreshold; positivity
  have hδ : 0≤δ := by
    have he := graphPaperError_nonnegative a d N (logarithmicRadius β d N) z hN hz.le
    unfold δ sourcePrime inflatedPrime
    positivity
  have hδC : δ≤C := hδone.trans hCone
  have hTnew : graphBallVertices gnew.graph o ell=T := by
    have hT : T=graphSetBall s.graph {o} ell := by rw [graphSetBall_singleton]; rfl
    have hh:=s.fullResample_ball selector {o} ell hT
    change graphBallVertices (s.fullResample selector).graph o ell=T
    simpa only [graphSetBall_singleton] using hh
  have hNewGlobal := hglobal gnew o z hz hscale Cq targetBadCount targetPlus target.1.1
  change ∀ u v : ((graphBallVertices gnew.graph o ell)ᶜ : Set (Fin N)), ‖(gnew.deficient.delete _).G z u v‖≤_ at hNewGlobal
  rw [hTnew] at hNewGlobal
  have hGlobalC : ∀ u v : (Tᶜ : Set (Fin N)), ‖(gnew.deficient.delete T).G z u v‖≤C := by
    intro u v
    exact (hNewGlobal u v).trans (by dsimp only [C,guardedGreenEntryCap,commonGreenEntryCap]; linarith)
  let b0 := s.sampledOutsideFirst i.val
  let c0 := s.sampledOutsideSecond i.val
  have hjne : j≠b0 := by
    intro heq
    have hh : ((2*r+1:ℕ):ℕ∞)<(outsideGraph gnew.graph T).edist b0 j := hfar
    rw [heq,SimpleGraph.edist_self] at hh
    exact (not_lt_of_ge (bot_le : (0:ℕ∞)≤((2*r+1:ℕ):ℕ∞))) hh
  let jj : {v:(Tᶜ : Set (Fin N)) // v≠b0} := ⟨j,hjne⟩
  let H := normalizedAdjacency (outsideGraph s.graph T) d
  let K := normalizedAdjacency (outsideGraph (s.fullResample selector).graph T) d
  have hsym : (green H z).IsSymm := by
    have hh:=(g.deficient.delete T).extensionGreen_isSymm (0:ℂ) z
    simpa only [DeficientGraph.extensionGreen,DeficientGraph.H,boundaryGreen,boundaryMatrix,zero_smul,sub_zero,green] using hh
  have hOldTargetC : ‖green H z c0.val j‖≤φ := by
    rw [hsym.apply j c0.val]
    exact (g.sampled_endpoint_uncorrelated_norm T z φ selector samples j (boundary i.val) huncorr true).le
  have hOldTargetB : ‖green H z b0 j‖≤φ := by
    rw [hsym.apply j b0]
    exact (g.sampled_endpoint_uncorrelated_norm T z φ selector samples j (boundary i.val) huncorr false).le
  have hPzero := (gnew.deficient.delete T).P_eq_zero_of_edist_gt hd r (gnew.Q z) z hz
    (gnew.Q_im_nonnegative z hz) b0 j hfar
  have hNewBJ : ‖green K z b0 j‖≤δ := by
    have hh:=targetPlus.deleted
    change ∀ u v : ((graphBallVertices gnew.graph o ell)ᶜ : Set (Fin N)),
      ‖(gnew.deficient.delete _).G z u v-gnew.deletedP _ r z (gnew.Q z) u v‖≤
        C1*gnew.sourcePrime a (logarithmicRadius β d N) z at hh
    rw [hTnew] at hh
    have hp:=hh b0 j
    change ‖(gnew.deficient.delete T).G z b0 j-(gnew.deficient.delete T).P r z (gnew.Q z) b0 j‖≤_ at hp
    rw [hPzero,sub_zero] at hp
    have he := graphPaperError_nonnegative a d N (logarithmicRadius β d N) z hN hz.le
    have hprime : 0≤g.sourcePrime a (logarithmicRadius β d N) z := by
      unfold sourcePrime inflatedPrime
      exact mul_nonneg (pow_nonneg (by linarith : 0≤Real.log (N:ℝ)) _) he
    exact hp.trans (mul_le_mul_of_nonneg_right hDC1 hprime)
  have hfarOld:=s.admissibleSampleVertex_far_boundary selector i
  have hdiv : (4*selector)/4=selector := by omega
  have hsafeRaw:=source_far_edge_guard s.graph T (4*selector) (by omega)
    (s.samples (s.boundary i.val)) (by simpa only [hdiv] using hfarOld)
  have hsafe : b0.val∈boundaryFarGuard s.graph T (selector-1) ∧ c0.val.val∈boundaryFarGuard s.graph T (selector-1) := by
    simpa only [hdiv] using hsafeRaw
  have hguard (u v : (Tᶜ : Set (Fin N))) (hu : u.val∈boundaryFarGuard s.graph T (selector-1))
      (hv : v.val∈boundaryFarGuard s.graph T (selector-1)) :
      guardedDeletedGreen g.H T (boundaryFarGuard s.graph T (selector-1)) z u.val v.val=green H z u v := by
    have hh:=guardedDeletedGreen_of_safe g.H T _ (boundaryFarGuard_subset_complement s.graph T _) z ⟨u.val,hu⟩ ⟨v.val,hv⟩
    rw [show g.H.submatrix (Subtype.val:(Tᶜ : Set (Fin N))→Fin N) (Subtype.val:(Tᶜ : Set (Fin N))→Fin N)=H from
      (normalizedAdjacency_induce s.graph d Tᶜ).symm] at hh
    exact hh
  have hOldNear:=oldCaps.guarded_edge c0.val.val b0.val (s.samples (s.boundary i.val)).property.1.symm
  change ‖guardedDeletedGreen g.H T (boundaryFarGuard s.graph T (selector-1)) z c0.val.val b0.val‖≤C at hOldNear
  rw [hguard c0.val b0 hsafe.2 hsafe.1] at hOldNear
  have hOldPivot:=oldCaps.guarded_pivot b0.val
  change ‖(guardedDeletedGreen g.H T (boundaryFarGuard s.graph T (selector-1)) z b0.val b0.val)⁻¹‖≤P at hOldPivot
  rw [hguard b0 b0 hsafe.1 hsafe.1] at hOldPivot
  have hfinite := s.fullResample_good_external_bound selector g.regular hd z hz i.val selector C P φ δ
    hC hP hφ hδ hδC hgood jj hOldNear hOldPivot hOldTargetC hOldTargetB
    (fun u => hGlobalC (s.otherEndpointEmbedding selector i.val u).val j)
    (fun u => hGlobalC (s.otherEndpointEmbedding selector i.val u).val b0)
    hpivot (hcross i).1 hNewBJ
  exact hfinite

end RegularGraph
end LocalLaw
