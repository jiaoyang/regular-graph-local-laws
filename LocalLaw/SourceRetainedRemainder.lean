import LocalLaw.SourceRetainedProfile
import LocalLaw.SourceRetainedExactRow
import LocalLaw.ActualBoundaryColumnBudgets

/-!
# Actual source nonlinear retained-row remainder

The exact Schur identity, proved model profile and derived log-five D column
sum realize the maximum bootstrap and its source remainder budget. No row
error, D column estimate or nonlinear remainder is assumed.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceRetainedRemainderDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_retained_nonlinear_remainder (a b d J : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ‖z‖≤B → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell := actualCavityDepth a d N z-1
      let Rstruct := logarithmicRadius (c/4) d N
      let selector := Rstruct/4
      let r := effectiveModelRadius a d N β
      let T := graphBallVertices g.graph o ell
      let L := Real.log (N:ℝ)
      let ε := graphPaperError a d N (logarithmicRadius β d N) z
      let φ := correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
      let P := g.sourceRetainedReference T r (g.Q z) z
      let R := ((g.labelledResampledGraph T labels samples selector).G z).submatrix
        (Subtype.val:T→Fin N) (Subtype.val:T→Fin N)
      let U := g.sourceCutCoupling T labels
      let D := g.sourceBoundaryDefect T labels samples selector r (g.Q z) z
      let root : T := ⟨o,center_mem_graphBall g.graph o ell⟩
      ¬g.sourceGreenIsolationBad T z φ (Rstruct/4) (Nat.ceil L) samples →
      (rejectedResamplingIndices g.graph T selector samples).card≤J → ∀ y : T,
      ‖((R-P)*U*D*U.transpose*P) root y‖≤ε/(2*L^2) := by
  let U0 := (d:ℝ)*((d:ℝ)+1)
  let M0 := 2*finiteExtraReferenceConstant d*((d:ℝ)+1)
  let W0 := 8*(d:ℝ)*finiteExtraReferenceConstant d^2*sourceObservationLogCap d β
  let E := sourceBoundaryColumnBudgetConstant d J C1
  have hCref : 0≤finiteExtraReferenceConstant d := (by norm_num : (0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have hA := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hU : 0≤U0 := by dsimp only [U0]; positivity
  have hM0 : 0≤M0 := by dsimp only [M0]; positivity
  have hW0 : 0≤W0 := by dsimp only [W0]; positivity
  have hC10 : 0≤C1 := by linarith
  have hE : 0≤E := by
    dsimp only [E,sourceBoundaryColumnBudgetConstant,sparseBoundaryColumnConstant,pairedBoundaryCoefficient,
      sourceEndpointErrorConstant,endpointSurgeryModelRowCap,endpointSurgeryCouplingCap]
    positivity
  filter_upwards [eventually_source_retained_profile a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_boundary_column_budget a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_paperError_small a b d β ha hb hd hβ,eventually_log_ge_nat 1,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    eventually_log_ge_nat (2*(E*(U0+W0+1))),
    eventually_log_ge_nat (2*(2*M0*(U0+1)*E^2*W0)),Filter.eventually_ge_atTop 1] with N hprofiles hcolumns hsmall hlog hrad hmargin hlarge₁ hlarge₂ hN
  intro g o z hz hfloor hzB Cq badCount hplus ι _ labels samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let Rstruct := logarithmicRadius (c/4) d N
  let selector := Rstruct/4
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let φ := correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
  let P := g.sourceRetainedReference T r (g.Q z) z
  let R := ((g.labelledResampledGraph T labels samples selector).G z).submatrix
    (Subtype.val:T→Fin N) (Subtype.val:T→Fin N)
  let U := g.sourceCutCoupling T labels
  let D := g.sourceBoundaryDefect T labels samples selector r (g.Q z) z
  let root : T := ⟨o,center_mem_graphBall g.graph o ell⟩
  let l := fun α => cutInsideVertex g.graph T (labels α)
  let coeff : ℂ := (↑((Real.sqrt ((d:ℝ)-1))⁻¹):ℂ)^2
  let e := E*L^5*ε
  have hr : 1≤r := hrad.2.1
  have hsep : 2*r+2≤selector := by dsimp only [r,selector,Rstruct]; omega
  have hrsel : r+2≤selector := by dsimp only [r,selector,Rstruct] at *; omega
  have hL : 1≤L := hlog
  have hε : 0≤ε := graphPaperError_nonnegative a d N _ z hN hz.le
  have he : 0≤e := by dsimp only [e]; positivity
  have hcap : ε*L^(4*a)≤1 := (le_div_iff₀ (pow_pos (by linarith : 0<L) _)).mp
    (by simpa only [one_div] using hsmall z hz hfloor)
  obtain ⟨profile⟩ := hprofiles g o z hz hfloor Cq badCount hplus labels
  intro hisolation hrejected y
  have hD : ∀ β,∑ α,‖D α β‖≤e :=
    hcolumns g o z hz hfloor hzB Cq badCount hplus labels samples hisolation J hrejected
  have hidentity (j : T) : R root j-P root j=
      coeff*(∑ α,∑ β,P root (l α)*D α β*P (l β) j)+
      coeff*(∑ α,∑ β,(R root (l α)-P root (l α))*D α β*P (l β) j) :=
    g.sourceRetained_exact_row hd T labels samples selector r hsep hrsel (g.Q z) z hz (g.Q_im_nonnegative z hz) root j
  have hboot := BoundaryMaxProfile.bootstrap P R l root a L U0 M0 W0 ε E e profile D coeff
    ha hL hε hU hM0 hW0 hE he (cut_coefficient_norm_le_one d hd) hcap le_rfl hD hidentity hlarge₁ hlarge₂
  rw [g.sourceRetained_remainder_formula T labels R P D root y]
  exact hboot.2 y

end RegularGraph
end LocalLaw
