import LocalLaw.ActualNearOutsideGeneral
import LocalLaw.SourceOutsideDeletedGeometry
import LocalLaw.SingleTargetOutsideBoundary
import LocalLaw.ExternalTipExceptions
import LocalLaw.GoodExternalColumnParameters
import LocalLaw.ExternalColumnAggregation

/-!
# Actual outside boundary error column on the original labels

The analytic estimates have no remaining model, pivot, correlation or
numerical premises. Only literal finite good-label and F1/F2 counting events
are retained for subsequent probability assembly.
-/
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 3500000
namespace LocalLaw
local instance actualOutsideColumnLabelsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceOutsideColumnErrorConstant (d : ℕ) (B C1 Kbad Knear : ℝ) : ℝ :=
  Kbad*(2*C1)+(2+Knear)*(2*C1)+sourceGoodExternalColumnConstant d B
    (sourceEndpointErrorConstant d C1) ((d:ℝ)*((d:ℝ)+1))

namespace RegularGraph

theorem eventually_actual_outside_column_labels (a b d : ℕ) (c β B C1 Kbad Knear : ℝ) (Cq : ℕ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c) (hβ : 0<β) (hβc : β≤c/32)
    (hB : 0≤B) (hC1 : 1≤C1) (hCdel : sourceDeletionConstant d β B≤C1) (hCq : finiteOmega d≤Cq)
    (hKbad : 0≤Kbad) (hKnear : 0≤Knear) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell:=actualCavityDepth a d N z-1
      let T:=graphBallVertices g.graph o ell
      let R:=logarithmicRadius (c/4) d N
      let r:=effectiveModelRadius a d N β
      let selector:=R/4
      let s:=g.admissibleState T labels samples
      let gnew:=g.labelledResampledGraph T labels samples selector
      let L:=Real.log (N:ℝ)
      let ε:=graphPaperError a d N (logarithmicRadius β d N) z
      let φ:=correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
      gnew.SourceOmegaWithRadii a r (logarithmicRadius β d N) R (finiteOmega d) badCount z →
      ∀ good : Finset ι,
      (∀ i∈good,s.Eligible selector i ∧ labels i∈g.sourceCorrelationGoodLabels T z φ selector samples) →
      (((Finset.univ\good).card:ℕ):ℝ)≤Kbad*L^2 →
      (∀ x : (Tᶜ : Set (Fin N)),(g.correlatedSampleIndices T z φ selector x samples).card≤Nat.ceil L) →
      (∀ x : (Tᶜ : Set (Fin N)),
        ((tripleNearIndices (s.fullResample selector).graph T selector (s.fullResample selector).samples x).card:ℝ)≤Knear*L) →
      ∀ (y : Fin N) (hy : y∉T),
      let K:=g.singleTargetOutsideVertices T labels samples selector r y
      let j:=g.singleTargetOutsideTargetVertex T labels samples selector r y hy
      ∑ i:ι, ‖(gnew.deficient.delete T).G z
        (g.singleTargetOutsideBoundaryVertex T labels samples selector r y i).val j.val-
        ((gnew.deficient.delete T).restrict K).extensionGreen (gnew.Q z) z
          (g.singleTargetOutsideBoundaryVertex T labels samples selector r y i) j‖≤
        sourceOutsideColumnErrorConstant d B C1 Kbad Knear*L^2*g.sourcePrime a (logarithmicRadius β d N) z := by
  let A:=sourceOutsideDeletedLogCap d β
  let D:=sourceEndpointErrorConstant d C1
  let U:=(d:ℝ)*((d:ℝ)+1)
  let Kfar:=sourceGoodExternalColumnConstant d B D U
  have hCextra:=finiteExtraReferenceConstant_ge_one d hd
  have hC10 : 0≤C1 := (by norm_num : (0:ℝ)≤1).trans hC1
  have hD : 0≤D := sourceEndpointErrorConstant_nonnegative d C1 hC10
  have hC : 0≤guardedGreenEntryCap d := by unfold guardedGreenEntryCap commonGreenEntryCap; linarith
  have hP : 0≤sourceGreenPivotCap d B := by unfold sourceGreenPivotCap; have hh:=finiteReferenceConstant_ge_one d hd; positivity
  have hAobs : sourceObservationLogCap d β≤A := by
    have h0:=sourceObservationLogCap_nonnegative d hd β hβ.le
    have hΩ : 0≤(finiteOmega d:ℝ) := Nat.cast_nonneg _
    have hp:=mul_nonneg hΩ h0
    dsimp only [A,sourceOutsideDeletedLogCap,singleTargetFilledLogCap,filledEndpointLogCap]
    nlinarith
  have hKfar : 0≤Kfar := by
    dsimp only [Kfar,sourceGoodExternalColumnConstant,U]
    have hw : 0≤endpointSurgeryCouplingCap d := by unfold endpointSurgeryCouplingCap; positivity
    positivity
  filter_upwards [eventually_target_near_outside_comparison_with_cap a b d c β B C1 A Cq ha hb hd hc hβ hβc hB hC1 hCdel hCq hAobs,
    eventually_source_outside_deleted_geometry a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_good_external_comparison a b d c β B C1 Cq ha hb hd hc hβ hβc hB hC1 hCdel hCq,
    eventually_good_external_column_absorption a b d β B D ha hb hd hβ hB hD,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4),
    eventually_log_ge_nat 1,Filter.eventually_ge_atTop 1]
    with N hnear hgeom hphysical hfarBudget hmargin hdepth hL hN
  intro g o z hz hzB hfloor badCount hplus ι _ labels samples
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let R:=logarithmicRadius (c/4) d N
  let r:=effectiveModelRadius a d N β
  let selector:=R/4
  let s:=g.admissibleState T labels samples
  let gnew:=g.labelledResampledGraph T labels samples selector
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let φ:=correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
  let εprime:=g.sourcePrime a (logarithmicRadius β d N) z
  let δ:=D*εprime
  intro target good hgood hbad hcorr hnewNear y hy
  let K:=g.singleTargetOutsideVertices T labels samples selector r y
  let j:=g.singleTargetOutsideTargetVertex T labels samples selector r y hy
  let root:=g.singleTargetOutsideBoundaryVertex T labels samples selector r y
  let Q:=((gnew.deficient.delete T).restrict K).extensionGreen (gnew.Q z) z
  let f : ι→ℂ := fun i => (gnew.deficient.delete T).G z (root i).val j.val-Q (root i) j
  let Bfar:=sourceGoodExternalBudget d B (Nat.card (BoundaryOrientedEdge g.graph T):ℝ) φ δ
  let exceptions:=g.sourceExternalTipExceptions T labels samples selector selector selector z φ ⟨y,hy⟩
  have hε : 0≤ε := graphPaperError_nonnegative a d N _ z hN hz.le
  have hεprime : 0≤εprime := by unfold εprime sourcePrime inflatedPrime; exact mul_nonneg (pow_nonneg (by linarith : 0≤L) _) hε
  have hφ : 0≤φ := by unfold φ correlationThreshold; positivity
  have hBfar : 0≤Bfar := by
    dsimp only [Bfar,sourceGoodExternalBudget]
    have hw : 0≤endpointSurgeryCouplingCap d := by unfold endpointSurgeryCouplingCap; positivity
    positivity
  have hsep : 2*r+2≤selector := by dsimp only [r,selector,R]; omega
  have hcutoff : 2*r+1≤selector := by omega
  have hTnew : graphBallVertices gnew.graph o ell=T := by
    have hT : T=graphSetBall s.graph {o} ell := by rw [graphSetBall_singleton]; rfl
    have hh:=s.fullResample_ball selector {o} ell hT
    change graphBallVertices (s.fullResample selector).graph o ell=T
    simpa only [graphSetBall_singleton] using hh
  have near:=hnear gnew o z hz hzB hfloor badCount target
  change ∀ S : Set ((graphBallVertices gnew.graph o ell)ᶜ : Set (Fin N)), _ at near
  rw [hTnew] at near
  have geom:=hgeom g o z hz hfloor Cq badCount hplus labels samples target y hy
  have hcap (i:ι) : ‖f i‖≤(2*C1)*εprime := by
    let pair:Set K:={root i,j}
    let e : pair↪K:=⟨Subtype.val,Subtype.val_injective⟩
    let a0:pair:=⟨root i,Or.inl rfl⟩
    let b0:pair:=⟨j,Or.inr rfl⟩
    have capture (v:pair) : graphBallVertices (outsideGraph gnew.graph T) (e v).val r⊆K := by
      rcases v.property with hv | hv
      · have heq : (e v).val=(root i).val := congrArg Subtype.val hv
        rw [heq]
        exact g.singleTargetOutsideBoundaryVertex_capture T labels samples selector r y hy i
      · have heq : (e v).val=j.val := congrArg Subtype.val hv
        rw [heq]
        exact g.singleTargetOutsideTargetVertex_capture T labels samples selector r y hy
    exact near K geom.1 (sourceOutsideDeletedDiameter d ell r) geom.2.1 geom.2.2.1 e capture a0 b0
  have hfar (i:ι) (hi:i∈good) (he:i∉exceptions) : ‖f i‖≤Bfar := by
    let ii:s.AdmissibleSampleIndex selector:=⟨i,(hgood i hi).1⟩
    have hx:=g.not_mem_sourceExternalTipExceptions T labels samples selector selector selector r z φ ⟨y,hy⟩ hcutoff i he
    have hc:=g.not_mem_sourceExternalTipExceptions_tip_far T labels samples selector selector selector r z φ ⟨y,hy⟩ hcutoff i he
    have hp:=hphysical g o z hz hzB hfloor badCount hplus labels samples badCount target ii (hgood i hi).2 ⟨y,hy⟩ hx.1 hx.2
    have hz0:=g.singleTargetOutside_tip_zero hd T labels samples selector r hsep ii y hy hc (gnew.Q z) z hz
      (gnew.Q_im_nonnegative z hz) (root i) (g.singleTargetOutsideBoundaryVertex_tip T labels samples selector r y ii)
    change ‖(gnew.deficient.delete T).G z (root i).val j.val-Q (root i) j‖≤Bfar
    rw [show Q (root i) j=0 from hz0,sub_zero,g.singleTargetOutsideBoundaryVertex_tip T labels samples selector r y ii]
    exact hp
  have hexc : (exceptions.card:ℝ)≤(2+Knear)*L := by
    have hc:=g.sourceExternalTipExceptions_card T labels samples selector selector selector z φ ⟨y,hy⟩
    have hcr : ((g.correlatedSampleIndices T z φ selector ⟨y,hy⟩ samples).card:ℝ)≤2*L :=
      (Nat.cast_le.mpr (hcorr ⟨y,hy⟩)).trans (by linarith [Nat.ceil_lt_add_one (by linarith : 0≤L)])
    have hn:=hnewNear ⟨y,hy⟩
    have hreal : (exceptions.card:ℝ)≤((g.correlatedSampleIndices T z φ selector ⟨y,hy⟩ samples).card:ℝ)+
        ((tripleNearIndices (s.fullResample selector).graph T selector (s.fullResample selector).samples ⟨y,hy⟩).card:ℝ) := by exact_mod_cast hc
    nlinarith only [hreal,hcr,hn]
  have hell : ell≤doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hfarSum : (Fintype.card ι:ℝ)*Bfar≤Kfar*εprime := by
    have hh:=hfarBudget g o ell hell z hz hfloor
    have hcard : Fintype.card ι=Nat.card (BoundaryOrientedEdge g.graph T) := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_congr labels
    simpa only [hcard] using hh
  exact external_column_log_budget f good exceptions L εprime ((2*C1)*εprime) Bfar (2*C1) Kbad (2+Knear) Kfar
    hL hεprime (by positivity) hBfar (by positivity) hKbad (by positivity) hKfar hcap hfar hbad hexc le_rfl hfarSum

end RegularGraph
end LocalLaw
