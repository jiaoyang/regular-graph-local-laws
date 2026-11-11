import LocalLaw.SourceCavityMinorProfile
import LocalLaw.CavityMinorRowIdentity
import LocalLaw.ActualTruncatedBoundaryColumns

/-! # The actual cavity-minor nonlinear error is epsilon/log^4

All column and reference-profile bounds are derived from the source event.
The physical minor and the deterministic old truncated reference are the
ones occurring in the exact cavity row identity.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceCavityMinorRemainderDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_cavity_minor_remainder (a b d J : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ‖z‖≤B → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      (graphBall g.graph o (logarithmicRadius (c/4) d N/8)).IsTree →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell := actualCavityDepth a d N z-1
      let Rstruct := logarithmicRadius (c/4) d N
      let selector := Rstruct/4
      let T := graphBallVertices g.graph o ell
      let L := Real.log (N:ℝ)
      let ε := graphPaperError a d N (logarithmicRadius β d N) z
      let φ := correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
      ¬g.sourceGreenIsolationBad T z φ selector (Nat.ceil L) samples →
      (rejectedResamplingIndices g.graph T selector samples).card≤J →
      ∃ hell : 2≤ell, ∀ (j : T) (hjo : g.graph.Adj j.val o),
      let R := (g.labelledResampledGraph T labels samples selector).retainedPhysicalMinor T j z
      let P := ((g.deficient.restrict T).deleteVertex j).extensionGreen (g.Q z) z
      let root := g.truncatedCavityRoot o ell j hjo
      let l := fun α => g.truncatedCavityBoundaryInner o ell hell j hjo (labels α)
      let D := g.sourceTruncatedBoundaryDefect T labels samples selector (g.Q z) z
      let coeff : ℂ := (↑((Real.sqrt ((d:ℝ)-1))⁻¹):ℂ)^2
      ∀ v, ‖coeff*(∑ α,∑ β,(R root (l α)-P root (l α))*D α β*P (l β) v)‖≤ε/(2*L^4) := by
  let U0 := (d:ℝ)*((d:ℝ)+1)
  let M0 := 2*finiteExtraReferenceConstant d*((d:ℝ)+1)
  let W0 := 8*(d:ℝ)*finiteExtraReferenceConstant d^2*sourceObservationLogCap d β
  let E := sourceTruncatedColumnBudgetConstant d J C1
  have hCref : 0≤finiteExtraReferenceConstant d := (by norm_num : (0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have hA := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hU : 0≤U0 := by dsimp only [U0]; positivity
  have hM0 : 0≤M0 := by dsimp only [M0]; positivity
  have hW0 : 0≤W0 := by dsimp only [W0]; positivity
  have hC10 : 0≤C1 := by linarith
  have hE : 0≤E := by
    dsimp only [E,sourceTruncatedColumnBudgetConstant,sourceBoundaryColumnBudgetConstant,
      sparseBoundaryColumnConstant,pairedBoundaryCoefficient,sourceEndpointErrorConstant,
      endpointSurgeryModelRowCap,endpointSurgeryCouplingCap]
    positivity
  filter_upwards [eventually_source_cavity_minor_profile a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_truncated_boundary_column_budget a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_paperError_small a b d β ha hb hd hβ,eventually_log_ge_nat 1,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,
    eventually_log_ge_nat (2*(E*(U0+W0+1))),
    eventually_log_ge_nat (2*(2*M0*(U0+1)*E^2*W0)),Filter.eventually_ge_atTop 1]
    with N hprofiles hcolumns hsmall hlog hrad hlarge₁ hlarge₂ hN
  intro g o z hz hfloor hzB Cq badCount hplus hTree ι _ labels samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let Rstruct := logarithmicRadius (c/4) d N
  let selector := Rstruct/4
  let T := graphBallVertices g.graph o ell
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let D := g.sourceTruncatedBoundaryDefect T labels samples selector (g.Q z) z
  let coeff : ℂ := (↑((Real.sqrt ((d:ℝ)-1))⁻¹):ℂ)^2
  let e := E*L^5*ε
  have hL : 1≤L := hlog
  have hε : 0≤ε := graphPaperError_nonnegative a d N _ z hN hz.le
  have he : 0≤e := by dsimp only [e]; positivity
  have hcap : ε*L^(4*a)≤1 := (le_div_iff₀ (pow_pos (by linarith : 0<L) _)).mp
    (by simpa only [one_div] using hsmall z hz hfloor)
  have hellR : ell≤Rstruct/8 := by
    have hh := hrad.2.2.2 z
    change effectiveModelRadius a d N β+ell+1≤Rstruct/8 at hh
    omega
  have hTreeEll := graphBall_tree_mono g.graph o hellR hTree
  obtain ⟨hell,hprofiles⟩ := hprofiles g o z hz hfloor Cq badCount hplus
  intro hisolation hrejected
  have hD : ∀ β,∑ α,‖D α β‖≤e :=
    hcolumns g o z hz hfloor hzB Cq badCount hplus hTree labels samples hisolation J hrejected
  refine ⟨hell,?_⟩
  intro j hjo
  let P := ((g.deficient.restrict T).deleteVertex j).extensionGreen (g.Q z) z
  let R := (g.labelledResampledGraph T labels samples selector).retainedPhysicalMinor T j z
  let root := g.truncatedCavityRoot o ell j hjo
  let l0 := g.truncatedCavityBoundaryInner o ell hell j hjo
  let l := fun α => l0 (labels α)
  obtain ⟨profile0⟩ := (hprofiles j hjo hTreeEll).1
  let profile : BoundaryMaxProfile P l root a L U0 M0 W0 :=
    profile0.pullback P l0 root a L U0 M0 W0 id labels l root rfl (fun _ => rfl)
  have hidentity := g.cavity_minor_row_identity hd o ell hell j hjo labels samples selector
    (g.Q z) z hz (g.Q_im_nonnegative z hz)
  exact (BoundaryMaxProfile.bootstrap_power P R l root a 4 L U0 M0 W0 ε E e profile D coeff
    ha (by omega) hL hε hU hM0 hW0 hE he (cut_coefficient_norm_le_one d hd) hcap le_rfl hD
    hidentity hlarge₁ hlarge₂).2

end RegularGraph
end LocalLaw
