import LocalLaw.SourceCommonLeafLocalization
import LocalLaw.LeafDeletedWeakKernel

/-! # Actual common leaf-deleted core decay, with no core class premise -/

open Filter
noncomputable section
set_option maxHeartbeats 4000000
namespace LocalLaw
local instance sourceCommonLeafKernelDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace DeficientGraph
variable {V : Type} [Fintype V] {d : ℕ}

def LeafCoreDecayBound (M : DeficientGraph V d) (B : Set V)
    (q z : ℂ) (K L ε : ℝ) : Prop :=
  letI : DecidableEq (Bᶜ:Set V):=fun a b=>Classical.propDecidable (a=b)
  ∀x y:(Bᶜ:Set V),∀h:ℕ,(h:ℕ∞)≤(M.delete B).graph.edist x y→
    ‖(M.delete B).extensionGreen q z x y‖≤K*L*physicalTransfer d z^h+K*L*ε

end DeficientGraph

namespace RegularGraph

theorem eventually_source_common_leaf_kernel_decay (a b d : ℕ) (c β Bcap C1 : ℝ)
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
      M.LeafCoreDecayBound B q z
        (leafDeletedCoreDecayConstant d Bcap (leafCompletionObservationLogCap d β) C1)
        (Real.log (N:ℝ)) (graphPaperError a d N (logarithmicRadius β d N) z) := by
  let A:=leafCompletionObservationLogCap d β
  let P:=2*|Bcap|+3
  let D:=leafCovarianceCoefficient d Bcap A C1
  let Count:ℝ:=(d:ℝ)^2*((d:ℝ)+1)
  have hCount : 0≤Count := by dsimp only [Count]; positivity
  have hP : 0≤P := by dsimp only [P]; positivity
  have hD : 0≤D := leafCovarianceCoefficient_nonnegative d Bcap A C1
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
    eventually_paperError_small a b d β ha hb hd hβ,
    eventually_log_ge_nat (2*Count*P*D),
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,
    hdepth]
    with N hgeometry hnum hformal hinverse hdiagonal hcounts hhalf hpaper hcontract hradii hdepthN
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
    ⟨hbudget,hR,hRlog,hcard,htree,hzero,hsep,_hlocal⟩
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
  let hrestore : ∀v,multiLeafMultiplicity mate v≤(M.delete B).deficit v := by
    intro v
    rw [deletedLeafMultiplicity,M.delete_deficit_eq_removed_neighbors]
    omega
  intro u v h hfar
  exact (M.delete B).attachLeaves_weak_edist_decay hd mate hrestore q z p hz hqim hf.1 hf.2.1 hp
    hbudget Bcap C1 ε L A hzB r R num hprior hR hRlog htree hzero hsep
    hf.2.2.1 hinv.2 hqpow hdiag.2.2.2.2.2 hhalfTail hsmall u v h hfar

end RegularGraph
end LocalLaw
