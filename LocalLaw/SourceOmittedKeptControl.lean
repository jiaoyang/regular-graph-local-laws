import LocalLaw.ActualOmittedKeptRows
import LocalLaw.SourceOmittedCompletionBounds
import LocalLaw.OmittedLeafCardinality
import LocalLaw.SourceFormalKernelInverse
import LocalLaw.FormalVacuumDiagonalBounds
import LocalLaw.EffectiveLeafWeights
import LocalLaw.SelectedDepthCounting
import LocalLaw.PolynomialLeafContraction

/-! # Source-realized kept-slot rows and normalization error

The original strong-radius graph budget and weak scalar prior discharge
all model geometry, covariance and contraction inputs. Every local core
target is allowed. No switched-pair reference-class assumption is retained.
-/

open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 5000000
namespace LocalLaw
local instance sourceOmittedKeptControlDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def omittedKeptRowConstant (d : ℕ)(B : ℝ) : ℝ :=
  4*finiteExtraReferenceConstant d+2*(4*finiteExtraReferenceConstant d)*(2*|B|+3)*(4*finiteExtraReferenceConstant d)

def omittedNormalizationCoefficient (B C1 : ℝ) : ℝ :=
  |2*(B+1)*(Real.sqrt (B+2)+1)*C1^2|+1

def omittedNormalizationConstant (d : ℕ)(B C1 : ℝ) : ℝ :=
  (omittedKeptRowConstant d B)^2*omittedNormalizationCoefficient B C1*
    (1+2*omittedKeptRowConstant d B*omittedNormalizationCoefficient B C1)

namespace RegularGraph
variable {N d : ℕ}{ι : Type}[Fintype ι]

def OmittedKeptControlled (g : RegularGraph N d)(hd : 3≤d)(T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T)(samples : LocalSamplingFiber g.graph T)
    (selector : ℕ)(S : Set (Tᶜ : Set (Fin N)))(q z : ℂ)(B C1 ε : ℝ) : Prop :=
  let s := g.admissibleState T labels samples
  let J := s.OmittedOrdinaryLeaves selector S ⊕ s.OmittedExtraLeaves selector S
  letI : DecidableEq (s.OmittedCore selector S) := fun a b => Classical.propDecidable (a=b)
  letI : DecidableEq J := fun a b => Classical.propDecidable (a=b)
  let H := g.omittedKeptCompletion (by omega) T labels samples selector S
  (∀x,∑j:J,‖H.extensionGreen q z x (.inr j)‖≤omittedKeptRowConstant d B) ∧
  (∀x,∑j:J,‖H.extensionGreen q z (.inr j) x‖≤omittedKeptRowConstant d B) ∧
  (∀x y:s.OmittedCore selector S,
    ‖H.extensionGreen q z (.inl x) (.inl y)-
      (g.omittedKeptRestoredModel T labels samples selector S).extensionGreen q z x y‖≤
        omittedNormalizationConstant d B C1*ε)

theorem eventually_source_omitted_kept_control (a b d : ℕ)(c β B C1 : ℝ)
    (ha : 12≤a)(hb : 25*a≤b)(hd : 3≤d)(hc : 0<c)(hβ : 0<β)(hβc : β≤c/32)(hC1 : 1≤C1) :
    ∀ᶠ N:ℕ in atTop,∀(g : RegularGraph N d)(o : Fin N)(z q : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → 0≤q.im →
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) →
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀{ι:Type}[Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y : ((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector := logarithmicRadius (c/4) d N/4
      let r := effectiveModelRadius a d N β
      let s := g.admissibleState T labels samples
      ∀S:Set (Tᶜ:Set (Fin N)),S⊆s.twoTargetEndpointVertices selector r x y →
        g.OmittedKeptControlled hd T labels samples selector S q z B C1
          (graphPaperError a d N (logarithmicRadius β d N) z) := by
  let A := omittedCompletionObservationLogCap d β
  let Count : ℝ := (d:ℝ)*((d:ℝ)+1)^2
  let P := 2*|B|+3
  let W := 4*finiteExtraReferenceConstant d
  let C := omittedKeptRowConstant d B
  let E := omittedNormalizationCoefficient B C1
  let D := |(treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d)*C1^2|+1
  have hCount : 0≤Count := by dsimp only [Count];positivity
  have hP : 0≤P := by dsimp only [P];positivity
  have hW : 0≤W := by dsimp only [W];linarith [finiteExtraReferenceConstant_ge_one d hd]
  have hC : 0≤C := by change 0≤W+2*W*P*W;positivity
  have hE : 0≤E := by dsimp only [E,omittedNormalizationCoefficient];positivity
  have hD : 0≤D := by dsimp only [D];positivity
  have hAobs0 := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hApart0 : 0≤sourcePartialObservationLogCap d β := by unfold sourcePartialObservationLogCap;positivity
  have hAobs : sourceObservationLogCap d β≤A := by
    apply le_trans (b:=sourcePartialObservationLogCap d β)
    · unfold sourcePartialObservationLogCap
      apply le_mul_of_one_le_left hAobs0
      linarith [Nat.cast_nonneg (α:=ℝ) (finiteOmega d)]
    · unfold A omittedCompletionObservationLogCap
      apply le_mul_of_one_le_left hApart0
      linarith [Nat.cast_nonneg (α:=ℝ) (finiteOmega d)]
  have hA : 0≤A := hAobs0.trans hAobs
  filter_upwards [eventually_source_partial_geometry a d c β (by omega) hd hc hβ hβc,
    eventually_source_omitted_completion_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_sourceObservationBounds_of_cap a b d c β B C1 A ha hb hd hc hβ hβc hC1 hAobs,
    eventually_source_formal_kernel_bounds a b d c β B C1 A ha hb hd hc hβ hβc hC1 hA,
    eventually_source_formal_kernel_inverse_bound a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_formal_diagonal_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_selected_counts a d ha hd,
    eventually_effective_leaf_count_half_tail a d β Count hd hCount,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,
    eventually_paperError_small a b d β ha hb hd hβ,
    eventually_log_ge_nat (2*Count*P*D),eventually_log_ge_nat (2*Count*C*E)]
    with N hgeo hcompletion hnum hformal hinv hdiag hcounts hhalf hradii hpaper hlarge hlargeE
  intro g o z q hz hzB hfloor hqim hprior hballs ι _ labels samples x y
  dsimp only
  let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector := logarithmicRadius (c/4) d N/4
  let r := effectiveModelRadius a d N β
  let s := g.admissibleState T labels samples
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let p := rationalTreeReference (d-1) q
  have num := hnum z hz hfloor
  have hf := hformal z q hz hzB hfloor hprior
  have hqinv := (hinv z q hz hzB hfloor hprior).2
  have hpInv := (hdiag z q hz hzB hfloor hprior).2.2.2.2.2
  have hε : 0≤ε := num.error_nonnegative
  have hLp : 0<L := by linarith [num.log_one]
  have hεcap : ε*L^(4*a)≤1 :=
    (le_div_iff₀ (pow_pos hLp (4*a))).mp (by simpa only [one_div] using hpaper z hz hfloor)
  have hε1 : ε≤1 := by
    have hp1 : 1≤L^(4*a) := one_le_pow₀ num.log_one
    nlinarith only [hεcap,num.error_nonnegative,hp1]
  have hε4 : ε*L^4≤1 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ num.log_one (by omega:4≤4*a)) num.error_nonnegative).trans hεcap
  have hpRel : p*(q⁻¹-q/((d:ℂ)-1))=1 := by
    have hr : p⁻¹=q⁻¹-q/((d:ℂ)-1) := by
      rw [hf.2.2.2.1,treeEdgeWeight_sq d hd]
      simp only [mul_one_div]
    rw [←hr]
    exact mul_inv_cancel₀ hf.2.1
  have hqpow : ∀n≤4*r+1,‖q‖^n≤2 := by
    intro n hn
    exact hf.2.2.2.2 n ((by exact_mod_cast Nat.le_succ_of_le hn : (n:ℝ)≤((4*r+1:ℕ):ℝ)+1).trans num.pair_log)
  intro S hS
  let Iall := s.OmittedOldLeaves selector S ⊕ s.OmittedExtraLeaves selector S
  let J := s.OmittedOrdinaryLeaves selector S ⊕ s.OmittedExtraLeaves selector S
  letI : DecidableEq (s.OmittedCore selector S) := fun a b => Classical.propDecidable (a=b)
  letI : DecidableEq Iall := fun a b => Classical.propDecidable (a=b)
  letI : DecidableEq J := fun a b => Classical.propDecidable (a=b)
  have hn : (Fintype.card Iall:ℝ)≤Count*L^(2*a) := by
    have hc : (Fintype.card Iall:ℝ)≤((d:ℝ)+1)*(Nat.card (BoundaryOrientedEdge g.graph T):ℝ) := by
      simpa only [Nat.card_eq_fintype_card,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using
        (Nat.cast_le (α:=ℝ).mpr (g.omittedAllLeaves_card_bound T labels samples selector S))
    have hbnd := (hcounts g o z).2
    have hpow := pow_le_pow_right₀ num.log_one (by omega:2*a-4≤2*a)
    calc
      _ ≤ ((d:ℝ)+1)*((d:ℝ)*((d:ℝ)+1)*L^(2*a-4)) :=
        hc.trans (mul_le_mul_of_nonneg_left hbnd (by positivity))
      _ ≤ ((d:ℝ)+1)*((d:ℝ)*((d:ℝ)+1)*L^(2*a)) := by gcongr
      _ = Count*L^(2*a) := by dsimp only [Count];ring
  have hcount := hhalf z hz.le hradii.1 hε4 (Fintype.card Iall) (Nat.cast_nonneg _) hn
  rcases hgeo g o z hballs labels samples x y S hS with ⟨hbudget,hdiam,hDlog⟩
  have hcomp := hcompletion g o z q hz hfloor hqim hprior hballs labels samples x y S hS
  have hcovRows := g.actual_omitted_leaf_covariance_rows hd T labels samples selector r
    (by have hm := hradii.2.2.2 z
        dsimp only [selector,r]
        omega) S hbudget _ hdiam q p z hf.1 hpRel hz hqim
    B C1 ε L A hzB num hprior hcomp.2.2.1 hf.2.2.1 hqinv hqpow hcount
  have hσ : 0≤D*L*ε := mul_nonneg (mul_nonneg hD hLp.le) num.error_nonnegative
  have hcov : ∀i j:s.OmittedOldLeaves selector S,
      ‖(g.omittedAllCompletion (by omega) T labels samples selector S).extensionGreen q z
        (.inr (.inl i)) (.inr (.inl j))-(if i=j then p else 0)‖≤D*L*ε := by
    intro i j
    apply (hcovRows.1 i j).trans
    have hcoef : (treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d)*C1^2≤D :=
      (le_abs_self _).trans (by dsimp only [D];linarith)
    nlinarith only [mul_le_mul_of_nonneg_right hcoef (mul_nonneg hLp.le num.error_nonnegative)]
  have hsmall : (Fintype.card Iall:ℝ)*‖p⁻¹‖*(D*L*ε)≤1/2 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpInv (Nat.cast_nonneg _)) hσ).trans
      (polynomial_leaf_contraction a (by omega) L ε (Fintype.card Iall) Count P D num.log_one
        num.error_nonnegative (Nat.cast_nonneg _) hCount hP hD hn hεcap hlarge)
  have hkept := g.actual_omitted_kept_rows hd T labels samples selector S q p z hz hqim hf.2.1
    (D*L*ε) W hσ hW hcov hsmall hcovRows.2
  have hrow : ∀v,∑j:J,‖(g.omittedKeptCompletion (by omega) T labels samples selector S).extensionGreen q z v (.inr j)‖≤C := by
    intro v
    exact (hkept.1 v).trans (by dsimp only [C,omittedKeptRowConstant,W,P];gcongr)
  have hcol : ∀v,∑j:J,‖(g.omittedKeptCompletion (by omega) T labels samples selector S).extensionGreen q z (.inr j) v‖≤C := by
    intro v
    exact (hkept.2 v).trans (by dsimp only [C,omittedKeptRowConstant,W,P];gcongr)
  have hprior' := hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative hC1)
  have hEraw := weak_prior_quadratic_defect_div q z hz B (C1^2*ε) (2*(B+1)) hzB
    (mul_nonneg (sq_nonneg C1) num.error_nonnegative) hprior' (by linarith [(norm_nonneg z).trans hzB]) hqinv
  have hEbound : ‖(1+z*q+q^2)/q‖≤E*ε := by
    apply hEraw.trans
    have he : 2*(B+1)*(Real.sqrt (B+2)+1)*C1^2≤E :=
      (le_abs_self _).trans (by dsimp only [E,omittedNormalizationCoefficient];linarith)
    nlinarith only [mul_le_mul_of_nonneg_right he num.error_nonnegative]
  have hEone : ‖(1+z*q+q^2)/q‖≤E := hEbound.trans (mul_le_of_le_one_right hE hε1)
  have hnJ : (Fintype.card J:ℝ)≤Count*L^(2*a) := by
    have hJall : (Fintype.card J:ℝ)≤(Fintype.card Iall:ℝ) := by
      exact_mod_cast Fintype.card_le_of_injective _ (s.omittedKeptEmbedding selector S).injective
    exact hJall.trans hn
  have hsmallE : (Fintype.card J:ℝ)*C*‖(1+z*q+q^2)/q‖≤1/2 := by
    have he : ‖(1+z*q+q^2)/q‖≤E*L*ε :=
      hEbound.trans (by nlinarith only [mul_le_mul_of_nonneg_left num.log_one (mul_nonneg hE num.error_nonnegative)])
    exact (mul_le_mul_of_nonneg_left he (mul_nonneg (Nat.cast_nonneg _) hC)).trans
      (polynomial_leaf_contraction a (by omega) L ε (Fintype.card J) Count C E num.log_one
        num.error_nonnegative (Nat.cast_nonneg _) hCount hC hE hnJ hεcap hlargeE)
  refine ⟨hrow,hcol,?_⟩
  intro u v
  have hnrm := g.actual_omitted_kept_normalization hd T labels samples selector S q z hf.1 hz hqim C hC hrow hsmallE u v
  apply hnrm.trans
  calc
    _ ≤ C*(E*ε)*(C*(1+E*(2*C))) := by gcongr
    _ = omittedNormalizationConstant d B C1*ε := by
      dsimp only [omittedNormalizationConstant,C,E]
      ring

end RegularGraph
end LocalLaw
