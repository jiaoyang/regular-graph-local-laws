import LocalLaw.WeightedOffdiagSource
import LocalLaw.ActualBoundaryColumnBudgets
import LocalLaw.SourceRetainedEntryBounds
import LocalLaw.SourceRetainedProfile
import LocalLaw.SourceRetainedWeights

/-! # Actual inside-row off-diagonal forcing, with every profile derived -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceRetainedOffdiagDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceRetainedOffdiagConstant (d J : ℕ) (C1 : ℝ) : ℝ :=
  sourceEndpointErrorConstant d C1 * (22 + 2 * (finiteOmega d : ℝ) + (J : ℝ)) ^ 2 *
    (2 * finiteExtraReferenceConstant d) ^ 2 + 1

namespace RegularGraph

theorem eventually_source_retained_offdiag (a b d J : ℕ) (c β B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ‖z‖ ≤ B → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1)
        (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))),
      let ell := actualCavityDepth a d N z - 1
      let R := logarithmicRadius (c / 4) d N
      let T := graphBallVertices g.graph o ell
      let r := effectiveModelRadius a d N β
      let L := Real.log (N : ℝ)
      let ε := graphPaperError a d N (logarithmicRadius β d N) z
      let φ := correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
      let P := g.sourceRetainedReference T r (g.Q z) z
      let D := g.sourceBoundaryDefect T labels samples (R / 4) r (g.Q z) z
      let root : T := ⟨o, center_mem_graphBall g.graph o ell⟩
      ¬g.sourceGreenIsolationBad T z φ (R / 4) (Nat.ceil L) samples →
      (rejectedResamplingIndices g.graph T (R / 4) samples).card ≤ J → ∀ y : T,
      ‖∑ α, ∑ β, if α = β then 0 else
        P root (cutInsideVertex g.graph T (labels α)) * D α β * P (cutInsideVertex g.graph T (labels β)) y‖ ≤
        sourceRetainedOffdiagConstant d J C1 * (ε / L ^ 2) := by
  let U := 3 * (d : ℝ) * ((d : ℝ) + 1)
  let C := endpointSurgeryModelRowCap d (2 * (finiteOmega d + 1))
  let w := endpointSurgeryCouplingCap d
  let G := pairedBoundaryCoefficient C w
  let W0 := 8 * (d : ℝ) * finiteExtraReferenceConstant d ^ 2 * sourceObservationLogCap d β
  let D0 := sourceEndpointErrorConstant d C1
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_actual_boundary_defect_pattern a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_retained_profile a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_retained_entry_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_log_ge_nat (3 * G * U * W0 * D0 ^ 2),
    eventually_log_ge_nat (3 * G * U ^ 2 * W0 * D0),
    eventually_log_ge_nat (3 * G * U * W0),
    eventually_paperError_small a b d β ha hb hd hβ,eventually_log_ge_nat 9,hdepth,
    Filter.eventually_ge_atTop 1] with N hpattern hprofile hentries hlarge1 hlarge2 hlarge3 hsmall hlog hdepth hN
  intro g o z hz hfloor hzB Cq badCount hplus ι _ labels S
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let R := logarithmicRadius (c/4) d N
  let T := graphBallVertices g.graph o ell
  let r := effectiveModelRadius a d N β
  let rn := logarithmicRadius β d N
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N rn z
  let φ := correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
  let s := g.admissibleState T labels S
  let C := endpointSurgeryModelRowCap d (2*(finiteOmega d+1))
  let w := endpointSurgeryCouplingCap d
  let δ := sourceEndpointErrorConstant d C1*g.sourcePrime a rn z
  let δold := 2*C1*g.sourcePrime a rn z
  let n := 3*(Fintype.card ι:ℝ)
  let U := 3*(d:ℝ)*((d:ℝ)+1)
  let D := g.sourceBoundaryDefect T labels S (R/4) r (g.Q z) z
  have hL : 1 ≤ L := by dsimp only [L]; linarith
  have hL0 : 0 ≤ L := by linarith
  have hε : 0 ≤ ε := graphPaperError_nonnegative a d N rn z hN hz.le
  have hcap : ε*L^(4*a) ≤ 1 := (le_div_iff₀ (pow_pos (by linarith : 0<L) _)).mp
    (by simpa only [one_div] using hsmall z hz hfloor)
  have hprime : 0 ≤ g.sourcePrime a rn z := by unfold sourcePrime inflatedPrime; positivity
  have hC : 0 ≤ C := by
    dsimp only [C,endpointSurgeryModelRowCap]
    have hh := finiteExtraReferenceConstant_ge_one d hd
    positivity
  have hw : 0 ≤ w := by dsimp only [w,endpointSurgeryCouplingCap]; positivity
  have hδold : 0 ≤ δold := by dsimp only [δold]; positivity
  have hδ : δold ≤ δ := mul_le_mul_of_nonneg_right (sourceEndpointOldErrorConstant_le d hd C1
    (by linarith)) hprime
  have hD0 : 0 ≤ sourceEndpointErrorConstant d C1 := by unfold sourceEndpointErrorConstant; positivity
  have hφ : 0 ≤ φ := by unfold φ correlationThreshold; positivity
  have hcorr : φ*L^(4*a) ≤ ε := (le_div_iff₀ (pow_pos (by linarith : 0<L) _)).mp
    (sourceCorrelationThreshold_le_error a b d N rn z ha hb (by omega) hz hlog hfloor)
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hlabel : (Fintype.card ι:ℝ) = (Nat.card (BoundaryOrientedEdge g.graph T):ℝ) := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_congr labels
  have hcount : n ≤ U*L^(2*a) := by
    have hh := mul_le_mul_of_nonneg_left (g.boundary_card_log_bound o a ell hd hL hell) (by norm_num : (0:ℝ) ≤ 3)
    calc
      n = 3*(Nat.card (BoundaryOrientedEdge g.graph T):ℝ) := by dsimp only [n]; rw [hlabel]
      _ ≤ 3*((d:ℝ)*((d:ℝ)+1)*L^(2*a)) := hh
      _ = U*L^(2*a) := by dsimp only [U]; ring
  have hEndpointCount : (Fintype.card (s.endpointModelRoots (R/4)):ℝ) ≤ n := by
    have hh := s.endpointModelRoots_card (R/4)
    rw [Nat.card_eq_fintype_card] at hh
    have hreal : (Fintype.card (s.endpointModelRoots (R/4)):ℝ) ≤ 3*(Nat.card (BoundaryOrientedEdge g.graph T):ℝ) := by
      exact_mod_cast hh
    exact hreal.trans_eq (by dsimp only [n]; rw [hlabel])
  obtain ⟨hfit,hpat⟩ := hpattern g o z hz hfloor hzB Cq badCount hplus labels S
  have hp := hpat φ hφ
  let good := g.sourceSurgeryGoodIndices o ell R hfit labels z φ S
  intro hisolation hrejected y
  let bad := Finset.univ\good
  have hbad : (bad.card:ℝ) ≤ (22+2*(finiteOmega d:ℝ)+(J:ℝ))*L^2 :=
    g.sourceSurgeryGoodIndices_bad_log_bound o ell R (finiteOmega d) J hfit (hplus.structural.1 o)
      labels z φ S hL hisolation hrejected
  let P := g.sourceRetainedReference T r (g.Q z) z
  let root : T := ⟨o, center_mem_graphBall g.graph o ell⟩
  let l := fun α => cutInsideVertex g.graph T (labels α)
  let γ := pairedEndpointGoodError C w δold n φ
  have hγ : 0 ≤ γ := by dsimp only [γ, pairedEndpointGoodError]; positivity
  have hG : 0 ≤ G := by dsimp only [G, pairedBoundaryCoefficient]; positivity
  have hW0 : 0 ≤ W0 := by
    have hh := sourceObservationLogCap_nonnegative d hd β hβ.le
    dsimp only [W0]
    positivity
  have hCref : 0 ≤ 2 * finiteExtraReferenceConstant d := by
    have hh := finiteExtraReferenceConstant_ge_one d hd
    positivity
  obtain ⟨profile⟩ := hprofile g o z hz hfloor Cq badCount hplus labels
  obtain ⟨hentry,hroot⟩ := hentries g o z hz hfloor Cq badCount hplus
  apply sparse_retained_offdiag_budget P (g.sourceRetainedReference_isSymm T r (g.Q z) z) l root y
    a L _ _ W0 profile D bad ε n δ φ γ U
    (22 + 2 * (finiteOmega d : ℝ) + (J : ℝ)) D0 G (2 * finiteExtraReferenceConstant d)
    ha hL hε (by dsimp only [n]; positivity) (hδold.trans hδ) hφ hγ
    (by dsimp only [U]; positivity) (by positivity) hD0 hG hCref hW0 hcap hcount
    (by dsimp only [n]; nlinarith [(Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ Fintype.card ι)])
    hbad _ hcorr (pairedEndpointGoodError_monomial_bound C w δold δ n φ hC hw hδold hδ
      (by dsimp only [n]; positivity) hφ) hp.1 _
    (fun α => hroot (labels α)) hentry hlarge1 hlarge2 hlarge3
  · unfold δ sourcePrime inflatedPrime
    ring_nf
    exact le_rfl
  · intro u v huv hg
    have hg' : u ∈ good ∨ v ∈ good := by
      rcases hg with hu | hv
      · exact Or.inl (by simpa only [bad, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] using hu)
      · exact Or.inr (by simpa only [bad, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] using hv)
    exact (hp.2.1 u v huv hg').trans (pairedEndpointGoodError_mono_count C w δold _ n φ
      hC hw hδold hEndpointCount hφ)

end RegularGraph
end LocalLaw
