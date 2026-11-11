import LocalLaw.SourceOmittedKeptControl

/-! # All source-realized inputs for the actual old-leaf Schur deletion -/

open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 5000000
namespace LocalLaw
local instance sourceOmittedLeafInputsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}{ι : Type}[Fintype ι]

def OmittedLeafInputs (g : RegularGraph N d)(hd : 3≤d)(T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T)(samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ)(S : Set (Tᶜ : Set (Fin N)))(q z : ℂ)(B C1 A L ε : ℝ) : Prop :=
  let s := g.admissibleState T labels samples
  let I := s.OmittedOldLeaves selector S ⊕ s.OmittedExtraLeaves selector S
  letI : DecidableEq (s.OmittedCore selector S) := fun a b => Classical.propDecidable (a=b)
  letI : DecidableEq I := fun a b => Classical.propDecidable (a=b)
  let H := g.omittedAllCompletion (by omega) T labels samples selector S
  let R := hereditaryReferenceRadius d (hereditaryReferenceRadius d (augmentedObservationDiameter d r))+2
  let D := |(treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d)*C1^2|+1
  let p := rationalTreeReference (d-1) q
  H.ComponentFiniteReferenceBudget ∧
  (∀u v,H.graph.dist u v≤R) ∧ ((R:ℝ)+1≤A*L) ∧
  (‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*coreConvolutionConstant (finiteOmega d+1)*
    ((R:ℝ)+1)≤1/2) ∧
  (∀i j:s.OmittedOldLeaves selector S,
    ‖H.extensionGreen q z (.inr (.inl i)) (.inr (.inl j))-(if i=j then p else 0)‖≤D*L*ε) ∧
  ((Fintype.card I:ℝ)*‖p⁻¹‖*(D*L*ε)≤1/2) ∧
  (∀x,∑l:I,‖H.extensionGreen q z x (.inr l)‖≤4*finiteExtraReferenceConstant d)

theorem eventually_source_omitted_leaf_inputs (a b d : ℕ)(c β B C1 : ℝ)
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
        g.OmittedLeafInputs hd T labels samples selector r S q z B C1
          (omittedCompletionObservationLogCap d β) (Real.log (N:ℝ))
          (graphPaperError a d N (logarithmicRadius β d N) z) := by
  let A := omittedCompletionObservationLogCap d β
  let Count : ℝ := (d:ℝ)*((d:ℝ)+1)^2
  let P := 2*|B|+3
  let D := |(treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d)*C1^2|+1
  have hCount : 0≤Count := by dsimp only [Count];positivity
  have hP : 0≤P := by dsimp only [P];positivity
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
    eventually_log_ge_nat (2*Count*P*D)]
    with N hgeo hcompletion hnum hformal hinv hdiag hcounts hhalf hradii hpaper hlarge
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
  exact ⟨hcomp.1,hcomp.2.1,hcomp.2.2.1,hcomp.2.2.2.1,hcov,hsmall,hcovRows.2⟩

end RegularGraph
end LocalLaw
