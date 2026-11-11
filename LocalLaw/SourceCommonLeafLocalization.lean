import LocalLaw.SourceLeafCompletionGeometry
import LocalLaw.LeafCompletionRate
import LocalLaw.EffectiveLeafWeights
import LocalLaw.EffectiveTailCounting
import LocalLaw.LeafMultiplicityContraction
import LocalLaw.SourceFormalKernelInverse
import LocalLaw.FormalVacuumDiagonalBounds
import LocalLaw.SourceObservationGeneralCap
import LocalLaw.SelectedDepthCounting

/-! # Actual common leaf-deleted model localization at arbitrary nearby q

The original strong-radius graph budget supplies every global/local leaf
model class and geometric input. The nominal source error supplies all
covariance, row, inverse contraction and tail conditions. No reference class
for the switched pair model is used.
-/

open Filter
noncomputable section
set_option maxHeartbeats 4000000
namespace LocalLaw
local instance sourceCommonLeafLocalizationDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace DeficientGraph
variable {V : Type} [Fintype V] {d : ℕ}

def LeafCoreLocalizedAt (M : DeficientGraph V d) (B : Set V)
    (K : Set (Bᶜ:Set V)) (q z : ℂ) (δ : ℝ) (u v : (Bᶜ:Set V)) : Prop :=
  letI : DecidableEq (Bᶜ:Set V):=fun a b=>Classical.propDecidable (a=b)
  ∀i j:K,i.val=u→j.val=v→
    ‖(M.delete B).extensionGreen q z u v-((M.delete B).restrict K).extensionGreen q z i j‖≤δ

end DeficientGraph

namespace RegularGraph

theorem eventually_source_common_leaf_localization (a b d : ℕ) (c β Bcap C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in atTop,∀(g : RegularGraph N d)(o : Fin N)(z q : ℂ),
      0<z.im→‖z‖≤Bcap→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→0≤q.im→
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z)→
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d)→
      ∀{ι : Type}[Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y : ((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      let S:=s.twoTargetEndpointVertices selector r x y
      let M:=(g.deficient.delete T).restrict S
      let B:=s.partialFirstRemovedSet selector S
      ∀u v:(Bᶜ:Set S),
      let K:Set (Bᶜ:Set S):={w |w.val.val∈
        pairBallVertices (outsideGraph (s.fullResample selector).graph T) u.val.val v.val.val r}
      M.LeafCoreLocalizedAt B K q z (g.sourcePrime a (logarithmicRadius β d N) z) u v := by
  let A:=leafCompletionObservationLogCap d β
  let P:=2*|Bcap|+3
  let D:=leafCovarianceCoefficient d Bcap A C1
  let Main:=leafCompletionMainCoefficient d Bcap A C1
  let Tail:=leafCompletionTailCoefficient d Bcap
  let Count:ℝ:=(d:ℝ)^2*((d:ℝ)+1)
  have hCount : 0≤Count := by dsimp only [Count]; positivity
  have hP : 0≤P := by dsimp only [P]; positivity
  have hD : 0≤D := leafCovarianceCoefficient_nonnegative d Bcap A C1
  have hTail : 0≤Tail := leafCompletionTailCoefficient_nonnegative d hd Bcap
  have hAobs : 0≤sourceObservationLogCap d β := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hAobsA : sourceObservationLogCap d β≤A := by
    apply le_mul_of_one_le_left hAobs
    have hh:=Nat.cast_nonneg (α:=ℝ) (finiteOmega d)
    change 1≤2*(finiteOmega d:ℝ)+7
    linarith
  have hA : 0≤A := hAobs.trans hAobsA
  have hdepth:=(lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_source_leaf_completion_geometry a d c β hd hc hβ hβc,
    eventually_sourceObservationBounds_of_cap a b d c β Bcap C1 A ha hb hd hc hβ hβc hC1 hAobsA,
    eventually_source_formal_kernel_bounds a b d c β Bcap C1 A ha hb hd hc hβ hβc hC1 hA,
    eventually_source_formal_kernel_inverse_bound a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_formal_diagonal_bounds a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_selected_counts a d ha hd,
    eventually_effective_leaf_count_half_tail a d β Count hd hCount,
    eventually_effective_tail_counting a d β (Count+1) Tail ha hd (by positivity) hTail,
    eventually_paperError_small a b d β ha hb hd hβ,
    eventually_log_ge_nat (2*Count*P*D),
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,
    eventually_log_ge_nat (Main+1),hdepth]
    with N hgeometry hnum hformal hinverse hdiagonal hcounts hhalf htail hpaper hcontract hradii hlarge hdepthN
  intro g o z q hz hzB hfloor hqim hprior hballs ι _ labels samples x y
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let S:=s.twoTargetEndpointVertices selector r x y
  let M:=(g.deficient.delete T).restrict S
  let B:=s.partialFirstRemovedSet selector S
  let I:=DeletedLeafIndex M.graph B
  let mate:=deletedLeafMate M.graph B
  let H:=M.deletedLeafModel (by omega:1≤d) B
  let R:=hereditaryReferenceRadius d (augmentedObservationDiameter d r)+2
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let p:=rationalTreeReference (d-1) q
  have hell : ell≤doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepthN).2
  have num:=hnum z hz hfloor
  have hf:=hformal z q hz hzB hfloor hprior
  have hinv:=hinverse z q hz hzB hfloor hprior
  have hdiag:=hdiagonal z q hz hzB hfloor hprior
  have hp : p*(q⁻¹-q/((d:ℂ)-1))=1 := by
    have hrel:p⁻¹=q⁻¹-q/((d:ℂ)-1) := by
      rw [hf.2.2.2.1,treeEdgeWeight_sq d hd]
      simp only [mul_one_div]
    rw [←hrel]
    exact mul_inv_cancel₀ hf.2.1
  have hqpow : ∀n≤4*r+1,‖q‖^n≤2 := by
    intro n hn
    exact hf.2.2.2.2 n ((by exact_mod_cast Nat.le_succ_of_le hn : (n:ℝ)≤((4*r+1:ℕ):ℝ)+1).trans num.pair_log)
  rcases hgeometry g o ell hell hballs labels samples x y with
    ⟨hbudget,hR,hRlog,hcard,htree,hzero,hsep,hlocal⟩
  have hcountRaw : (Fintype.card I:ℝ)≤Count*L^(2*a) := by
    have hc : (Fintype.card I:ℝ)≤(d:ℝ)*(Nat.card (BoundaryOrientedEdge g.graph T):ℝ) := by
      simpa only [Nat.card_eq_fintype_card,Nat.cast_mul] using (Nat.cast_le (α:=ℝ).mpr hcard)
    have hbnd:=(hcounts g o z).2
    have hpowers : L^(2*a-4)≤L^(2*a) := pow_le_pow_right₀ num.log_one (by omega)
    calc
      _≤(d:ℝ)*((d:ℝ)*((d:ℝ)+1)*L^(2*a-4)) :=
        hc.trans (mul_le_mul_of_nonneg_left hbnd (Nat.cast_nonneg _))
      _≤(d:ℝ)*((d:ℝ)*((d:ℝ)+1)*L^(2*a)) := by gcongr
      _=Count*L^(2*a) := by dsimp only [Count]; ring
  have hεcap : ε*L^4≤1 :=
    (mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_left num.error_nonnegative (show (1:ℝ)≤C1^2 by nlinarith))
      (pow_nonneg (by linarith [num.log_one]:0≤L) 4)).trans num.error_scaled
  have hhalfTail : (Fintype.card I:ℝ)*physicalTransfer d z^r≤1 :=
    hhalf z hz.le hradii.1 hεcap (Fintype.card I) (Nat.cast_nonneg _) hcountRaw
  have hδ : 0≤D*L*ε := mul_nonneg (mul_nonneg hD (by linarith [num.log_one])) num.error_nonnegative
  have hsmall : (Fintype.card I:ℝ)*‖p⁻¹‖*(D*L*ε)≤1/2 :=
    by
      have hLp : 0<L := by linarith [num.log_one]
      have hεpower : ε*L^(4*a)≤1 :=
        (le_div_iff₀ (pow_pos hLp (4*a))).mp (by simpa only [one_div] using hpaper z hz hfloor)
      calc
        _≤(Count*L^(2*a))*P*(D*L*ε) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hcountRaw hdiag.2.2.2.2.2 (norm_nonneg _) (mul_nonneg hCount (pow_nonneg hLp.le _))) hδ
        _=Count*P*D*L^(2*a+1)*ε := by rw [pow_add,pow_one];ring
        _≤(L/2)*L^(2*a+1)*ε := by
          apply mul_le_mul_of_nonneg_right _ num.error_nonnegative
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hLp.le _)
          change 2*Count*P*D≤L at hcontract
          apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
          calc
            (Count*P*D)*2=2*Count*P*D := by ring
            _≤L := hcontract
        _=(1/2)*(L^(2*a+2)*ε) := by
          rw [show 2*a+2=(2*a+1)+1 by omega,pow_add,pow_one]
          ring
        _≤(1/2)*(L^(4*a)*ε) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              (pow_le_pow_right₀ num.log_one (show 2*a+2≤4*a by omega)) num.error_nonnegative)
            (by norm_num)
        _≤1/2 := by nlinarith only [hεpower]
  have hcountPlus : (Fintype.card I:ℝ)+1≤(Count+1)*L^(2*a) := by
    have hp1 : (1:ℝ)≤L^(2*a) := one_le_pow₀ num.log_one
    nlinarith only [hcountRaw,hp1]
  have htailBound : Tail*((Fintype.card I:ℝ)+1)*physicalTransfer d z^(2*r)≤ε/L^16 :=
    htail z hz.le hradii.1 _ (by positivity) hcountPlus
  intro u v i j hi hj
  let K:Set (Bᶜ:Set S):={w |w.val.val∈
    pairBallVertices (outsideGraph (s.fullResample selector).graph T) u.val.val v.val.val r}
  let U:=multiLeafLift mate K
  obtain ⟨_hbudgetLocal,hRs,hcapture⟩:=hlocal u v
  have hI : graphBallVertices H.graph (.inl i.val) r⊆U := by
    rw [hi]
    exact fun w hw=>hcapture (Or.inl hw)
  have hJ : graphBallVertices H.graph (.inl j.val) r⊆U := by
    rw [hj]
    exact fun w hw=>hcapture (Or.inr hw)
  let hrestore : ∀v,multiLeafMultiplicity mate v≤(M.delete B).deficit v := by
    intro v
    rw [deletedLeafMultiplicity,M.delete_deficit_eq_removed_neighbors]
    omega
  have hbound:=(M.delete B).attachLeaves_weak_localization hd mate hrestore K q z p hz hqim hf.1 hf.2.1 hp
    hbudget Bcap C1 ε L A hzB r R R num hprior hR hRs hRlog hRlog htree hzero hsep
    hf.2.2.1 hinv.2 hqpow hhalfTail hsmall i j hI hJ
  have hcoarse:=leaf_completion_error_coarsening d hd Bcap A C1 L ε (Fintype.card I)
    (physicalTransfer d z^(2*r)) (by linarith [num.log_one]) num.error_nonnegative
    (Nat.cast_nonneg _) (pow_nonneg (physicalTransfer_pos d hd z).le _) p hdiag.2.2.2.2.2
  have hbound' := hbound.trans hcoarse
  have hrest : ε/L^16≤L*ε := by
    exact (div_le_self num.error_nonnegative (one_le_pow₀ num.log_one)).trans
      (le_mul_of_one_le_left num.error_nonnegative num.log_one)
  have hsize : Main+1≤L^2 := hlarge.trans (by simpa only [pow_one] using pow_le_pow_right₀ num.log_one (by omega:1≤2))
  have hfinal : Main*L*ε+Tail*((Fintype.card I:ℝ)+1)*physicalTransfer d z^(2*r)≤g.sourcePrime a (logarithmicRadius β d N) z := by
    calc
      _≤Main*L*ε+L*ε := add_le_add_left (htailBound.trans hrest) _
      _=(Main+1)*L*ε := by ring
      _≤L^2*L*ε := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsize (by linarith [num.log_one])) num.error_nonnegative
      _=g.sourcePrime a (logarithmicRadius β d N) z := by change L^2*L*ε=L^3*ε;ring
  simpa only [hi,hj] using hbound'.trans hfinal

end RegularGraph
end LocalLaw
