import LocalLaw.SourceOutsideReferenceComparison
import LocalLaw.SourceRetainedBoundaryMaximum
import LocalLaw.FilledCrossReference

/-! # Outside-row reduction to the actual deleted boundary column

All Schur, root-boundary, model-localization, scalar-feedback and nominal
error estimates are proved. The remaining geometric model data and the one
actual outside boundary column are kept explicit for their source factories.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance sourceOutsideRowReductionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceOutsideReductionBase (d J : ℕ) (β C1 Eout Sout : ℝ) : ℝ :=
  let C := finiteExtraReferenceConstant d
  let H := sourceRetainedBoundaryMaximumConstant d J β C1
  (2*C+H)*Eout+(H+3)*Sout+1

def sourceOutsideReductionFeedback (d : ℕ) (β B A Sout : ℝ) : ℝ :=
  (sourceInsidePairFeedbackConstant d β B+DeficientGraph.localizationFeedbackConstant d B A)*Sout+
    DeficientGraph.localizationFeedbackConstant d B A

namespace RegularGraph

theorem eventually_source_outside_row_of_boundary_column (a b d J : ℕ) (c β B C1 A Eout Sout : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c) (hβ : 0<β)
    (hβc : β≤c/32) (hC1 : 1≤C1) (hB : 0≤B) (hA : sourceObservationLogCap d β≤A)
    (hEout : 0≤Eout) (hSout : 0≤Sout) :
    ∀ᶠ N : ℕ in Filter.atTop,∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z → ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell := actualCavityDepth a d N z-1
      let r := effectiveModelRadius a d N β
      let Rstruct := logarithmicRadius (c/4) d N
      let T := graphBallVertices g.graph o ell
      let L := Real.log (N:ℝ)
      let ε := graphPaperError a d N (logarithmicRadius β d N) z
      let φ := correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
      let gnew := g.labelledResampledGraph T labels samples (Rstruct/4)
      gnew.SourceOmegaWithRadii a r (logarithmicRadius β d N) Rstruct (finiteOmega d) badCount z →
      ¬g.sourceGreenIsolationBad T z φ (Rstruct/4) (Nat.ceil L) samples →
      (rejectedResamplingIndices g.graph T (Rstruct/4) samples).card≤J →
      ∀ (K : Set (Tᶜ:Set (Fin N))) (Rmodel : ℕ)
      (hK : ∀ e : BoundaryOrientedEdge gnew.graph T,boundaryOutsideVertex gnew.graph T e∈K),
      (gnew.filledExteriorModel T K).ComponentFiniteReferenceBudget →
      (∀ u v,(gnew.filledExteriorModel T K).graph.dist u v≤Rmodel) →
      (Rmodel:ℝ)+1≤A*L →
      (∀ x : T,graphBallVertices gnew.graph x.val r⊆filledExteriorVertices T K) →
      ∀ j : K, graphBallVertices gnew.graph j.val.val r⊆filledExteriorVertices T K →
      (∑ α : BoundaryOrientedEdge gnew.graph T,
        ‖(gnew.deficient.delete T).G z (boundaryOutsideVertex gnew.graph T α) j.val-
          ((gnew.deficient.delete T).restrict K).extensionGreen (gnew.Q z) z
            (gnew.filledBoundaryVertex T K hK α) j‖)≤Eout*L^5*ε →
      (∑ α : BoundaryOrientedEdge gnew.graph T,
        ‖((gnew.deficient.delete T).restrict K).extensionGreen (gnew.Q z) z
          (gnew.filledBoundaryVertex T K hK α) j‖)≤Sout*L →
      ‖gnew.G z o j.val.val-gnew.P r z (gnew.Q z) o j.val.val‖≤
        sourceOutsideReductionBase d J β C1 Eout Sout*ε/L+
          sourceOutsideReductionFeedback d β B A Sout*L^2*gnew.sourceFeedback z := by
  let C := finiteExtraReferenceConstant d
  let H := sourceRetainedBoundaryMaximumConstant d J β C1
  let Kloc := DeficientGraph.localizationFeedbackConstant d B A
  let Kref := sourceInsidePairFeedbackConstant d β B+Kloc
  let Ktail := DeficientGraph.localizationTailConstant d*((d-1:ℕ):ℝ)^4
  have hC : 0≤C := (by norm_num : (0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have hA0 : 0≤A := (sourceObservationLogCap_nonnegative d hd β hβ.le).trans hA
  have hAfull : 0≤filledEndpointLogCap d β := by
    have hh := sourceObservationLogCap_nonnegative d hd β hβ.le
    dsimp only [filledEndpointLogCap]; linarith
  have hconv := coreConvolutionConstant_nonnegative (finiteOmega d+1)
  have hKloc : 0≤Kloc := by dsimp only [Kloc,DeficientGraph.localizationFeedbackConstant]; positivity
  have hKref : 0≤Kref := by
    dsimp only [Kref,sourceInsidePairFeedbackConstant,DeficientGraph.localizationFeedbackConstant]
    positivity
  have hH : 0≤H := by
    have hh := sourceObservationLogCap_nonnegative d hd β hβ.le
    have hC10 : 0≤C1 := by linarith
    dsimp only [H,sourceRetainedBoundaryMaximumConstant,sourceRetainedBoundaryColumnConstant,
      boundaryInnerColumnConstant,sourceBoundaryColumnBudgetConstant,sparseBoundaryColumnConstant,
      pairedBoundaryCoefficient,sourceEndpointErrorConstant,endpointSurgeryModelRowCap,endpointSurgeryCouplingCap]
    positivity
  have hTail : 0≤DeficientGraph.localizationTailConstant d := by
    unfold DeficientGraph.localizationTailConstant DeficientGraph.localizationExceptionalMass
    have hh : 0<(d:ℝ)-1 := by have hdR : (3:ℝ)≤d := Nat.cast_le.mpr hd; linarith
    positivity
  filter_upwards [eventually_source_enlarged_retained_comparison a b d c β B C1 A
      ha hb hd hc hβ hβc hC1 hB hA,
    eventually_source_retained_boundary_maximum a b d J c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,
    eventually_log_ge_nat (DeficientGraph.localizationBudgetConstant d B A),
    eventually_log_ge_nat Ktail] with N href hmax hnum hmargin hlarge htailLarge
  intro g o z hz hzB hfloor Cq badCount hplus ι _ labels samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let Rstruct := logarithmicRadius (c/4) d N
  let gnew := g.labelledResampledGraph T labels samples (Rstruct/4)
  let s := g.admissibleState T labels samples
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let F := gnew.sourceFeedback z
  let root : T := ⟨o,center_mem_graphBall g.graph o ell⟩
  intro htarget hisolation hrejected K Rmodel hK hbudget hdiam hdiamlog hcapture j hjcapture hcolumn hmodel
  let M := gnew.filledExteriorModel T K
  let e : T → filledExteriorVertices T K := fun x => ⟨x.val,Or.inl x.property⟩
  let jj : filledExteriorVertices T K := ⟨j.val.val,Or.inr ⟨j.val,j.property,rfl⟩⟩
  let ρ : BoundaryOrientedEdge gnew.graph T → ℂ := fun α => gnew.G z o (cutInsideVertex gnew.graph T α).val
  let σ : BoundaryOrientedEdge gnew.graph T → ℂ := fun α => gnew.filledRetainedGreen T K (gnew.Q z) z root (cutInsideVertex gnew.graph T α)
  let X : BoundaryOrientedEdge gnew.graph T → ℂ := fun α => (gnew.deficient.delete T).G z (boundaryOutsideVertex gnew.graph T α) j.val
  let Y : BoundaryOrientedEdge gnew.graph T → ℂ := fun α => ((gnew.deficient.delete T).restrict K).extensionGreen (gnew.Q z) z (gnew.filledBoundaryVertex T K hK α) j
  let coeff : ℂ := (↑((Real.sqrt ((d:ℝ)-1))⁻¹):ℂ)
  have num := hnum z hz hfloor
  have hL : 1≤L := num.log_one
  have hLp : 0<L := by linarith
  have hε : 0≤ε := num.error_nonnegative
  have hF : 0≤F := by dsimp only [F,sourceFeedback]; positivity
  have hmax' := hmax g o z hz hfloor hzB Cq badCount hplus labels samples hisolation hrejected
  have href' := href g o z hz hzB hfloor Cq badCount hplus labels samples htarget K Rmodel hbudget hdiam hdiamlog hcapture
  have hinner (α : ι) : cutInsideVertex gnew.graph T ((s.fullResample (Rstruct/4)).boundary α)=
      cutInsideVertex g.graph T (labels α) := by
    apply Subtype.ext
    exact s.fullResample_boundary_inner_endpoint (Rstruct/4) α
  have hρ (α) : ‖ρ α‖≤(2*C+H)/L^9 := by
    obtain ⟨i,rfl⟩ := (s.fullResample (Rstruct/4)).boundary.surjective α
    dsimp only [ρ]
    rw [hinner]
    exact hmax'.2 i
  have hΓ (α) : ‖ρ α-σ α‖≤H*ε/L^3+3*(ε/L^2)+Kref*L*F := by
    obtain ⟨i,rfl⟩ := (s.fullResample (Rstruct/4)).boundary.surjective α
    let l := cutInsideVertex g.graph T (labels i)
    have hh := href' root l
    have ht := norm_sub_le_norm_sub_add_norm_sub (gnew.G z o l.val)
      (g.sourceRetainedReference T r (g.Q z) z root l)
      (gnew.filledRetainedGreen T K (gnew.Q z) z root l)
    dsimp only [ρ,σ]
    rw [hinner]
    exact (ht.trans (add_le_add (hmax'.1 i) hh)).trans_eq (by ring)
  have hcoeff : ‖coeff‖≤1 := by
    have hh := cut_coefficient_norm_le_one d hd
    change ‖coeff^2‖≤1 at hh
    rw [norm_pow] at hh
    nlinarith only [hh,norm_nonneg coeff]
  have hcross := cut_cross_row_error_bound coeff (gnew.G z o j.val.val)
    (gnew.filledCrossGreen T K (gnew.Q z) z root j) ρ σ X Y
    ((2*C+H)/L^9) (H*ε/L^3+3*(ε/L^2)+Kref*L*F) (Eout*L^5*ε) (Sout*L)
    (by positivity) (by positivity) hcoeff
    (gnew.physical_cross_row T z hz root j.val) (gnew.filledCrossGreen_row hd T K hK (gnew.Q z) z hz
      (gnew.Q_im_nonnegative z hz) root j) hρ hΓ hcolumn hmodel
  have hεScaled : ε*L^4≤1 := by
    have hC1sq : 1≤C1^2 := one_le_pow₀ hC1
    exact (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hε hC1sq) (pow_nonneg hLp.le 4)).trans num.error_scaled
  have hεOne : ε≤1 := (le_mul_of_one_le_right hε (one_le_pow₀ hL)).trans hεScaled
  have hloc := M.componentwise_pair_localization_feedback hd hbudget (gnew.Q z) z hz (gnew.Q_im_nonnegative z hz)
    B hzB ε L A hε hεOne hL hA0 hεScaled htarget.2.1 Rmodel r hdiam hdiamlog
    (num.pair_log.trans (mul_le_mul_of_nonneg_right hA hLp.le)) hlarge (e root) jj
  have hid : M.P r z (gnew.Q z) (e root) jj=gnew.P r z (gnew.Q z) o j.val.val :=
    (gnew.deficient.restrict_pair_P (filledExteriorVertices T K) (e root) jj r (hcapture root) hjcapture
      (gnew.Q z) z).trans (gnew.deficient_P r z (gnew.Q z) o j.val.val)
  rw [hid] at hloc
  have htail := effectiveModelRadius_localization_tail a d N β hd hL hmargin.1 z hz.le
  have htailAbs : DeficientGraph.localizationTailConstant d*physicalTransfer d z^(2*r)≤ε/L^2 := by
    calc
      _ ≤ DeficientGraph.localizationTailConstant d*((((d-1:ℕ):ℝ)^4)*ε/L^(4*a)) :=
        mul_le_mul_of_nonneg_left htail hTail
      _ = Ktail*ε/L^(4*a) := by dsimp only [Ktail]; ring
      _ ≤ _ := constant_div_log_absorption (4*a) 2 L ε Ktail hL hε htailLarge (by omega)
  have hlocal : ‖gnew.filledCrossGreen T K (gnew.Q z) z root j-gnew.P r z (gnew.Q z) o j.val.val‖≤
      Kloc*L*F+ε/L^2 := by
    have hh := hloc.trans (add_le_add_left htailAbs _)
    exact hh
  have htriangle := norm_sub_le_norm_sub_add_norm_sub (gnew.G z o j.val.val)
    (gnew.filledCrossGreen T K (gnew.Q z) z root j) (gnew.P r z (gnew.Q z) o j.val.val)
  apply (htriangle.trans (add_le_add hcross hlocal)).trans
  have hdiv4 : ε/L^4≤ε/L := div_le_div_of_nonneg_left hε hLp
    (by simpa only [pow_one] using pow_le_pow_right₀ hL (show 1≤4 by omega))
  have hdiv2 : ε/L^2≤ε/L := div_le_div_of_nonneg_left hε hLp
    (by simpa only [pow_one] using pow_le_pow_right₀ hL (show 1≤2 by omega))
  have hLL : L≤L^2 := by nlinarith only [sq_nonneg (L-1),hL]
  have heq : (2*C+H)/L^9*(Eout*L^5*ε)+
      (H*ε/L^3+3*(ε/L^2)+Kref*L*F)*(Sout*L)+(Kloc*L*F+ε/L^2)=
      (2*C+H)*Eout*(ε/L^4)+(H*Sout+1)*(ε/L^2)+3*Sout*(ε/L)+
        Kref*Sout*L^2*F+Kloc*L*F := by field_simp; ring
  rw [heq]
  have hfb : Kloc*L*F≤Kloc*L^2*F := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hLL hKloc) hF
  have hbase1 := mul_le_mul_of_nonneg_left hdiv4 (show 0≤(2*C+H)*Eout by positivity)
  have hbase2 := mul_le_mul_of_nonneg_left hdiv2 (show 0≤H*Sout+1 by positivity)
  change _≤sourceOutsideReductionBase d J β C1 Eout Sout*ε/L+
    sourceOutsideReductionFeedback d β B A Sout*L^2*F
  dsimp only [sourceOutsideReductionBase,sourceOutsideReductionFeedback]
  change _≤((2*C+H)*Eout+(H+3)*Sout+1)*ε/L+(Kref*Sout+Kloc)*L^2*F
  calc
    _ ≤ (2*C+H)*Eout*(ε/L)+(H*Sout+1)*(ε/L)+3*Sout*(ε/L)+
        Kref*Sout*L^2*F+Kloc*L^2*F := by linarith only [hbase1,hbase2,hfb]
    _ = _ := by ring

end RegularGraph
end LocalLaw
