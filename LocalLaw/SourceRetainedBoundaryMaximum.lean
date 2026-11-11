import LocalLaw.SourceRetainedBoundaryColumns
import LocalLaw.BoundaryOnlyMaximum
import LocalLaw.SourceRetainedExactRow
import LocalLaw.ActualBoundaryColumnBudgets

/-! # Actual root-to-boundary gain before concentration

The boundary-only maximum uses the genuine logarithmic boundary columns.
It proves a decaying root boundary error and a physical root boundary cap
from the source event and the actual isolation/rejection good events alone.
-/

set_option maxHeartbeats 1200000

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceRetainedBoundaryMaximumDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceRetainedBoundaryMaximumConstant (d J : ℕ) (β C1 : ℝ) : ℝ :=
  4*finiteExtraReferenceConstant d*sourceBoundaryColumnBudgetConstant d J C1*
    sourceRetainedBoundaryColumnConstant d β

namespace RegularGraph

theorem eventually_source_retained_boundary_maximum (a b d J : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop,∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ‖z‖≤B → ∀ Cq badCount : ℕ,
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
      let P := g.sourceRetainedReference T r (g.Q z) z
      let gnew := g.labelledResampledGraph T labels samples (Rstruct/4)
      let root : T := ⟨o,center_mem_graphBall g.graph o ell⟩
      let l := fun α => cutInsideVertex g.graph T (labels α)
      ¬g.sourceGreenIsolationBad T z φ (Rstruct/4) (Nat.ceil L) samples →
      (rejectedResamplingIndices g.graph T (Rstruct/4) samples).card≤J →
      (∀ α,‖gnew.G z o (l α).val-P root (l α)‖≤
        sourceRetainedBoundaryMaximumConstant d J β C1*ε/L^3) ∧
      (∀ α,‖gnew.G z o (l α).val‖≤
        (2*finiteExtraReferenceConstant d+sourceRetainedBoundaryMaximumConstant d J β C1)/L^9) := by
  let C := finiteExtraReferenceConstant d
  let E := sourceBoundaryColumnBudgetConstant d J C1
  let K := sourceRetainedBoundaryColumnConstant d β
  let H := sourceRetainedBoundaryMaximumConstant d J β C1
  have hC : 0≤C := (by norm_num : (0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have hA := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hE : 0≤E := by
    have hC10 : 0≤C1 := by linarith
    dsimp only [E,sourceBoundaryColumnBudgetConstant,sparseBoundaryColumnConstant,pairedBoundaryCoefficient,
      sourceEndpointErrorConstant,endpointSurgeryModelRowCap,endpointSurgeryCouplingCap]
    positivity
  have hK : 0≤K := by dsimp only [K,sourceRetainedBoundaryColumnConstant,boundaryInnerColumnConstant]; positivity
  have hH : 0≤H := by dsimp only [H,sourceRetainedBoundaryMaximumConstant]; positivity
  filter_upwards [eventually_source_retained_boundary_columns a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_retained_entry_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_boundary_column_budget a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_paperError_small a b d β ha hb hd hβ,eventually_log_ge_nat 1,
    eventually_log_ge_nat (2*(E*K)),eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    Filter.eventually_ge_atTop 1] with N hcols hentries hDcols hsmall hlog hlarge hmargin hN
  intro g o z hz hfloor hzB Cq badCount hplus ι _ labels samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let r := effectiveModelRadius a d N β
  let Rstruct := logarithmicRadius (c/4) d N
  let T := graphBallVertices g.graph o ell
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let P := g.sourceRetainedReference T r (g.Q z) z
  let gnew := g.labelledResampledGraph T labels samples (Rstruct/4)
  let R := (gnew.G z).submatrix (Subtype.val:T→Fin N) (Subtype.val:T→Fin N)
  let root : T := ⟨o,center_mem_graphBall g.graph o ell⟩
  let l := fun α => cutInsideVertex g.graph T (labels α)
  let D := g.sourceBoundaryDefect T labels samples (Rstruct/4) r (g.Q z) z
  let coeff : ℂ := (↑((Real.sqrt ((d:ℝ)-1))⁻¹):ℂ)^2
  intro hisolation hrejected
  have hL : 1≤L := hlog
  have hLp : 0<L := by linarith
  have hε : 0≤ε := graphPaperError_nonnegative a d N _ z hN hz.le
  have hcap : ε*L^(4*a)≤1 := (le_div_iff₀ (pow_pos hLp _)).mp
    (by simpa only [one_div] using hsmall z hz hfloor)
  have hcap7 : ε*L^7≤1 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (show 7≤4*a by omega)) hε).trans hcap
  have hcap6 : ε*L^6≤1 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (show 6≤4*a by omega)) hε).trans hcap
  have hcontraction : (E*L^5*ε)*(K*L)≤1/2 := by
    have hh := mul_le_mul_of_nonneg_left hcap7 (mul_nonneg hE hK)
    have hprod : ((E*L^5*ε)*(K*L))*L≤E*K := by nlinarith only [hh]
    have hdiv : (E*L^5*ε)*(K*L)≤E*K/L := (le_div_iff₀ hLp).mpr hprod
    exact hdiv.trans ((div_le_iff₀ hLp).mpr (by linarith only [hlarge]))
  have hsep : 2*r+2≤Rstruct/4 := by dsimp only [r,Rstruct]; omega
  have hrs : r+2≤Rstruct/4 := by dsimp only [r,Rstruct]; omega
  have hroot : ∀ α,‖P root (l α)‖≤2*C/L^9 := fun α =>
    (hentries g o z hz hfloor Cq badCount hplus).2 (labels α)
  have hboundary : ∀ β,∑ α,‖P (l α) (l β)‖≤K*L :=
    hcols g o z hz hfloor Cq badCount hplus labels
  have hD : ∀ β,∑ α,‖D α β‖≤E*L^5*ε :=
    hDcols g o z hz hfloor hzB Cq badCount hplus labels samples hisolation J hrejected
  have hidentity (β : ι) := g.sourceRetained_exact_row hd T labels samples (Rstruct/4) r hsep hrs
    (g.Q z) z hz (g.Q_im_nonnegative z hz) root (l β)
  have hboot := boundary_row_max_from_boundary_columns R P l D coeff root (2*C/L^9) (E*L^5*ε) (K*L)
    (by positivity) (by positivity) (by positivity) (cut_coefficient_norm_le_one d hd)
    hroot hD hboundary hidentity hcontraction
  have hdiff (α : ι) : ‖gnew.G z o (l α).val-P root (l α)‖≤H*ε/L^3 := by
    exact (hboot α).trans_eq (by dsimp only [H,sourceRetainedBoundaryMaximumConstant]; field_simp; ring)
  constructor
  · exact hdiff
  · intro α
    have hdecay : H*ε/L^3≤H/L^9 := by
      apply (div_le_div_iff₀ (pow_pos hLp _) (pow_pos hLp _)).mpr
      have hh := mul_le_mul_of_nonneg_left hcap6 (mul_nonneg hH (pow_nonneg hLp.le 3))
      nlinarith only [hh]
    calc
      _ ≤ ‖gnew.G z o (l α).val-P root (l α)‖+‖P root (l α)‖ := by
        have hh := norm_sub_le_norm_sub_add_norm_sub (gnew.G z o (l α).val) (P root (l α)) (0:ℂ)
        simpa only [sub_zero] using hh
      _ ≤ H/L^9+2*C/L^9 := add_le_add ((hdiff α).trans hdecay) (hroot α)
      _ = _ := by ring

end RegularGraph
end LocalLaw
