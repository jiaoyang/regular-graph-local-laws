import LocalLaw.SourceFirstStageInterface
import LocalLaw.IndependentRadiusBootstrap
import LocalLaw.ExteriorStrictAnchorEffective

/-! # Continuum weak-law reduction from the first-stage estimate

The first-stage estimate is an explicit hypothesis of this intermediate
reduction and is proved in `SourceFirstStageProof`. The exterior anchor and
selected-radius numerical hypotheses are discharged here. The factor N for
sites and the N^36 continuum forest cost are both explicit.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceBoundedBootstrapReductionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem eventually_source_bounded_weak_of_first_stage (a b d p Cq : ℕ) (c β γ B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hp : 37 ≤ p)
    (hc : 0 < c) (hc₁ : c < 1) (hβ : 0 < β) (hβc : β ≤ c / 32)
    (hγ : c / 4 < γ) (hgap : γ + β < 1) (hB : 2 * (d : ℝ) ≤ B)
    (hC1 : 1 ≤ C1) (hCdel : sourceDeletionConstant d β (2 * B) ≤ C1) (hCq : finiteOmega d ≤ Cq)
    (hfirst : SourceFirstStageEstimate a b d p Cq c β γ (2 * B) C1) :
    ∀ᶠ N : ℕ in Filter.atTop,
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        RegularGraph.offsetStructural (logarithmicRadius (c / 4) d N) (finiteOmega d) 1 ⌊(N : ℝ) ^ γ⌋₊ g ∧
          ¬∀ z ∈ boundedLocalLawDomain N b B,
            (graphLocalLawFamilyWithRadii N d a (effectiveModelRadius a d N β)
              (logarithmicRadius β d N)).weak z g) ≤
        9 * bootstrapGridConstant B / (N : ℝ) ^ (p - 37) := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hB0 : 0 ≤ B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hβone : β ≤ 1 := by linarith
  filter_upwards [hfirst,
    eventually_source_strong_defect_reduction a b d p Cq c β γ (2 * B) C1 ha hb hd hc hc₁ hβ hβc hγ hgap
      (by positivity) hC1 hCdel hCq,
    eventually_actual_graph_bounded_bootstrapWithRadii a b d (p - 1) β B 9 ha hb hd (by omega)
      hβ hβone hB0 (by norm_num),
    eventually_exterior_strict_anchor_with_radii a b d c β γ (2 * B) ha hb hd hc hβ hβc hgap.le (by positivity),
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,
    eventually_log_pow_le_nat b, eventually_log_ge_nat 1, Filter.eventually_ge_atTop 1]
    with N hfirst hdefect hbootstrap hanchor hmarg hscale hlog hN
  let R := logarithmicRadius (c / 4) d N
  let rn := logarithmicRadius β d N
  let r := effectiveModelRadius a d N β
  let A : RegularGraph N d → Prop := RegularGraph.offsetStructural R (finiteOmega d) 1 ⌊(N : ℝ) ^ γ⌋₊
  let F := graphLocalLawFamilyWithRadii N d a r rn
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hLp : 0 < Real.log (N : ℝ) := by linarith
  have hfloorpos : 0 < Real.log (N : ℝ) ^ b / (N : ℝ) := div_pos (pow_pos hLp _) hNp
  have hfloorone : Real.log (N : ℝ) ^ b / (N : ℝ) ≤ 1 := (div_le_one hNp).mpr hscale
  have anchor : ∀ E : ℝ, |E| ≤ B → ∀ g, A g → F.weak (⟨E, B⟩ : ℂ) g := by
    intro E hE g hg
    have hR : r + 1 ≤ R := by
      have hh := hmarg.2.2.2 (⟨E, B⟩ : ℂ)
      dsimp only [r, R]
      omega
    have hstruct := RegularGraph.offsetStructural_implies_structural hg
    have hbad : ((nonTreeCenters g.graph R).card : ℝ) ≤ (N : ℝ) ^ γ :=
      (Nat.cast_le.mpr hstruct.2).trans (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) γ))
    have hnorm : ‖(⟨E, B⟩ : ℂ)‖ ≤ 2 * B := by
      have hh := Complex.norm_le_abs_re_add_abs_im (⟨E, B⟩ : ℂ)
      simp only [Complex.re, Complex.im, abs_of_nonneg hB0] at hh
      linarith
    have hstrict := hanchor g R hR hbad (⟨E, B⟩ : ℂ)
      (hB.trans (Complex.im_le_norm (⟨E, B⟩ : ℂ))) hnorm (hfloorone.trans hB1)
    have hε : 0 ≤ graphPaperError a d N rn (⟨E, B⟩ : ℂ) :=
      graphPaperError_nonnegative a d N rn _ hN hB0
    have hΨ : 0 ≤ scalarScale (spectralScale (⟨E, B⟩ : ℂ)) (graphPaperError a d N rn (⟨E, B⟩ : ℂ)) :=
      scalarScale_nonneg hε
    dsimp only [LocalLawFamily.weak, LocalLawFamily.strict, WeakLocalLawAt, StrictLocalLawAt,
      F, graphLocalLawFamilyWithRadii, graphLocalLawFamily] at hstrict ⊢
    exact ⟨hstrict.1.trans (by linarith), fun i j => (hstrict.2 i j).trans (by linarith)⟩
  have localDefect : ∀ z ∈ boundedLocalLawDomain N b (2 * B),
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        A g ∧ F.weak z g ∧ ¬F.strict z g) ≤ 9 / (N : ℝ) ^ (p - 1) := by
    intro z hz
    have hzIm : 0 < z.im := hfloorpos.trans_le hz.2
    have hh := hdefect z hzIm hz.1 hz.2 (fun _ => 1 / (N : ℝ) ^ p)
      (fun o => hfirst o z hzIm hz.1 hz.2)
    apply hh.trans_eq
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hpow : (N : ℝ) ^ p = (N : ℝ) ^ (p - 1) * (N : ℝ) := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow]
    field_simp [ne_of_gt hNp]
    ring
  have hh := hbootstrap r A anchor localDefect
  simpa only [Nat.sub_sub, show (1 + 36 : ℕ) = 37 by decide, mul_comm] using hh

end LocalLaw
