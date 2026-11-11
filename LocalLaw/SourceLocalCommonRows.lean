import LocalLaw.SourceOmittedLeafInputs
import LocalLaw.OmittedOldCompletionBudget
import LocalLaw.CanonicalBoundaryCore
import LocalLaw.LeafDeletedWeakMateRows
import LocalLaw.LeafDeletedSeparatedRows

/-! # Source rows of the correctly charged local common model

All old lost-B slots are kept, even when their removed B lies outside S.
The original strong-radius event supplies every old local budget; no class
for the deleted common core or switched pair model is assumed.
-/

open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
namespace LocalLaw
local instance sourceLocalCommonRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}{ι : Type}[Fintype ι]

def LocalCommonIncidenceRows (g : RegularGraph N d)(T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T)(samples : LocalSamplingFiber g.graph T)
    (selector : ℕ)(S : Set (Tᶜ:Set (Fin N)))(q z : ℂ)(KM KA : ℝ) : Prop :=
  let s := g.admissibleState T labels samples
  letI : DecidableEq (s.OmittedCore selector S) := fun a b => Classical.propDecidable (a=b)
  let C := g.omittedCommonModel T labels samples selector S
  ((∀u,∑l:s.OmittedOldLeaves selector S,‖C.extensionGreen q z u l.1‖≤KM) ∧
    (∀u,∑l:s.OmittedOldLeaves selector S,‖C.extensionGreen q z l.1 u‖≤KM)) ∧
  ((∀u,∑i:s.partialBoundaryMask selector S,‖C.extensionGreen q z u (s.canonicalBoundaryCoreEmbedding selector S i)‖≤KA) ∧
    (∀u,∑i:s.partialBoundaryMask selector S,‖C.extensionGreen q z (s.canonicalBoundaryCoreEmbedding selector S i) u‖≤KA))

theorem eventually_source_local_common_incidence_rows (a b d : ℕ)(c β B C1 : ℝ)
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
        g.LocalCommonIncidenceRows T labels samples selector S q z
          (leafDeletedMateRowCap d B) (leafDeletedSeparatedRowCap d B) := by
  let A := omittedCompletionObservationLogCap d β
  let Count : ℝ := (d:ℝ)*((d:ℝ)+1)^2
  let P := 2*|B|+3
  let D := leafCovarianceCoefficient d B A C1
  have hCount : 0≤Count := by dsimp only [Count];positivity
  have hP : 0≤P := by dsimp only [P];positivity
  have hD : 0≤D := leafCovarianceCoefficient_nonnegative d B A C1
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
  let Iall := s.OmittedOldLeaves selector S
  letI : FinEnum Iall := by unfold Iall LabelledResamplingState.OmittedOldLeaves;infer_instance
  letI : Fintype Iall := FinEnum.instFintype
  let J := s.partialBoundaryMask selector S
  letI : DecidableEq (s.OmittedCore selector S) := fun a b => Classical.propDecidable (a=b)
  letI : DecidableEq Iall := fun a b => Classical.propDecidable (a=b)
  letI : DecidableEq J := fun a b => Classical.propDecidable (a=b)
  have hn : (Fintype.card Iall:ℝ)≤Count*L^(2*a) := by
    have hc : (Fintype.card Iall:ℝ)≤((d:ℝ)+1)*(Nat.card (BoundaryOrientedEdge g.graph T):ℝ) := by
      simpa only [Nat.card_eq_fintype_card,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using
        (Nat.cast_le (α:=ℝ).mpr ((Nat.card_le_card_of_injective Sum.inl Sum.inl_injective).trans
          (g.omittedAllLeaves_card_bound T labels samples selector S)))
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
  let H0 := g.omittedOldCompletion (by omega:1≤d) T labels samples selector S
  let C0 := g.omittedCommonModel T labels samples selector S
  let oldMate : Iall → s.OmittedCore selector S := Sigma.fst
  let R := hereditaryReferenceRadius d (hereditaryReferenceRadius d (augmentedObservationDiameter d r))+2
  have hbudgetLeaf := g.omittedOldCompletion_component_budget (by omega) T labels samples selector S hbudget
  have hdiamLeaf := g.omittedOldCompletion_diameter (by omega) T labels samples selector S hbudget _ hdiam
  have hsepNat : 2*r+1≤selector := by
    have hm := hradii.2.2.2 z
    dsimp only [r,selector]
    omega
  have htree (i:Iall) := g.omittedOldCompletion_leaf_tree_zero (by omega) T labels samples selector r (by omega) S i
  have hsep (i j:Iall)(hne:i≠j) : ((2*r:ℕ):ℕ∞)<H0.graph.edist (.inr i) (.inr j) :=
    g.omittedOldCompletion_leaf_separated (by omega) T labels samples selector (2*r) hsepNat S i j hne
  let emb:Iall↪(s.OmittedCore selector S⊕Iall) := ⟨Sum.inr,Sum.inr_injective⟩
  have hcovRaw := H0.whole_leaf_scalar_covariance hd hbudgetLeaf emb r R
    (fun i => (htree i).1) (fun i => (htree i).2) (fun i j h => (hsep i j h).le)
    q p z hf.1 hpRel hz hqim B C1 ε L A hzB num hprior hdiamLeaf hcomp.2.2.1 hf.2.2.1 hqinv hqpow
  have hleafRows := H0.separated_target_leaf_rows hd hbudgetLeaf (Sum.inr : Iall → s.OmittedCore selector S ⊕ Iall) r hsep
    q z hz hqim R hdiamLeaf hcomp.2.2.2.1 hcount
  have hσ : 0≤D*L*ε := mul_nonneg (mul_nonneg hD hLp.le) num.error_nonnegative
  have hcov : ∀i j:s.OmittedOldLeaves selector S,
      ‖H0.extensionGreen q z (.inr i) (.inr j)-(if i=j then p else 0)‖≤D*L*ε := by
    intro i j
    apply (hcovRaw.2 i j).trans
    have hbase : treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d≤
        |treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d|+1 := by linarith [le_abs_self (treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d)]
    have hcoef : (treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d)*C1^2≤D :=
      mul_le_mul_of_nonneg_right hbase (sq_nonneg C1)
    nlinarith only [mul_le_mul_of_nonneg_right hcoef (mul_nonneg hLp.le num.error_nonnegative)]
  have hsmall : (Fintype.card Iall:ℝ)*‖p⁻¹‖*(D*L*ε)≤1/2 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpInv (Nat.cast_nonneg _)) hσ).trans
      (polynomial_leaf_contraction a (by omega) L ε (Fintype.card Iall) Count P D num.log_one
        num.error_nonnegative (Nat.cast_nonneg _) hCount hP hD hn hεcap hlarge)
  let W := 4*finiteExtraReferenceConstant d
  let U := ‖(treeEdgeWeight d)⁻¹‖*(1+(B+2)*W)
  have hB : 0≤B := (norm_nonneg z).trans hzB
  have hW : 0≤W := by dsimp only [W];linarith [finiteExtraReferenceConstant_ge_one d hd]
  have hU : 0≤U := by dsimp only [U];positivity
  have hqm := (hdiag z q hz hzB hfloor hprior).2.2.1
  have hm := C0.deleted_leaf_mate_rows hd oldMate
    (g.omittedOldMate_restore_budget T labels samples selector S) q z p hz hqim hf.2.1 B W (D*L*ε)
    hzB hqm hW hσ hleafRows.1 hcov hsmall
  have hmcap : U+2*W*‖p⁻¹‖*U≤leafDeletedMateRowCap d B := by
    exact add_le_add_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpInv (by positivity:0≤2*W)) hU) U
  have hnA : (Fintype.card J:ℝ)≤Count*L^(2*a) := by
    have hcard : (Fintype.card J:ℝ)≤(Nat.card (BoundaryOrientedEdge g.graph T):ℝ) := by
      simpa only [Nat.card_eq_fintype_card] using (Nat.cast_le (α:=ℝ).mpr (s.canonicalBoundaryMask_card selector S))
    have hbnd := (hcounts g o z).2
    have hpow := pow_le_pow_right₀ num.log_one (by omega:2*a-4≤2*a)
    calc
      _ ≤ (d:ℝ)*((d:ℝ)+1)*L^(2*a-4) := hcard.trans hbnd
      _ ≤ (d:ℝ)*((d:ℝ)+1)*L^(2*a) := by gcongr
      _ ≤ Count*L^(2*a) := by dsimp only [Count];gcongr;nlinarith [Nat.cast_nonneg (α:=ℝ) d]
  have hcountA := hhalf z hz.le hradii.1 hε4 (Fintype.card J) (Nat.cast_nonneg _) hnA
  let other := s.canonicalBoundaryCoreEmbedding selector S
  have hsA (i j:J)(hne:i≠j) : ((2*r:ℕ):ℕ∞)<H0.graph.edist (.inl (other i)) (.inl (other j)) := by
    change ((2*r:ℕ):ℕ∞)<(multiLeafGraph C0.graph Sigma.fst).edist (.inl (other i)) (.inl (other j))
    rw [multiLeafGraph_edist_old]
    exact (ENat.coe_le_coe.mpr (by omega:2*r≤selector)).trans_lt
      (s.canonicalBoundaryCoreEmbedding_separated selector S i j hne)
  have har := H0.separated_target_leaf_rows hd hbudgetLeaf (fun i:J => Sum.inl (other i)) r hsA
    q z hz hqim R hdiamLeaf hcomp.2.2.2.1 hcountA
  have haRows := C0.attachLeaves_remaining_rows_cols hd oldMate
    (g.omittedOldMate_restore_budget T labels samples selector S) other q z p hz hqim hf.2.1
    (D*L*ε) W W W hσ hW hcov hsmall (fun u => har.1 (.inl u))
    (fun u => hleafRows.1 (.inl u)) (fun l => har.1 (.inr l))
  have hacap : W+2*W*‖p⁻¹‖*W≤leafDeletedSeparatedRowCap d B :=
    add_le_add_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpInv (by positivity:0≤2*W)) hW) W
  simp only [LocalCommonIncidenceRows,←finsum_eq_sum_of_fintype] at hm haRows ⊢
  exact ⟨⟨fun u => (hm.1 u).trans hmcap,fun u => (hm.2 u).trans hmcap⟩,
    ⟨fun u => (haRows.1 u).trans hacap,fun u => (haRows.2 u).trans hacap⟩⟩

end RegularGraph
end LocalLaw
