import LocalLaw.FullEndpointMasks
import LocalLaw.FullSampleSeparation
import LocalLaw.PartialEndpointWeakCovariance

/-! # Actual old full-endpoint covariance at a weak boundary value

The full retained core includes the actual deleted set and every old outer
boundary root. Ambient guard transfer proves that all accepted samples
remain far from this core and from samples with different labels.
-/

noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance fullEndpointWeakCovarianceDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type} {T:Set V} {ι:Type}

def fullOldCovariance (s:LabelledResamplingState V T ι) (selector:ℕ) (S:Set V)
    (G:Matrix S S ℂ) (q p α:ℂ):Matrix (s.FullEndpointIndex selector S) (s.FullEndpointIndex selector S) ℂ:=
  Matrix.fromBlocks (G.submatrix (s.fullCoreEmbedding S) (s.fullCoreEmbedding S)) 0 0
    (partialSampleCovariance (s.fullFirstMask selector S) (s.fullSecondMask selector S) q p α)

end LabelledResamplingState
namespace RegularGraph
variable {N d:ℕ} {ι:Type} [Fintype ι]

omit [Fintype ι] in
theorem full_endpoint_old_weak_covariance (g:RegularGraph N d) (hd:3≤d)
    (T:Set (Fin N)) (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector r:ℕ) (hr:2*r+2≤selector) (hs:1≤selector)
    (S:Set (Fin N)) (hb:(g.deficient.restrict S).ComponentFiniteReferenceBudget)
    (z q p:ℂ) (hz:0<z.im) (hq:0≤q.im) (hq0:q≠0)
    (hp:p*(q⁻¹-q/((d:ℂ)-1))=1)
    (Bcap C1 ε L Acap:ℝ) (hzB:‖z‖≤Bcap)
    (num:SourceObservationBounds d r z Bcap C1 ε L Acap)
    (hprior:‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z) ε)
    (R:ℕ) (hR:∀u v,(g.deficient.restrict S).graph.dist u v≤R)
    (hRlog:(R:ℝ)+1≤Acap*L) (hpbound:‖p‖≤4) (hqinv:‖q⁻¹‖≤2*(Bcap+1))
    (hqpow:∀n≤4*r+1,‖q‖^n≤2) :
    let s:=g.admissibleState T labels samples
    let G:=(g.deficient.restrict S).extensionGreen q z
    let e:=s.fullPartialEmbedding selector S hs
    ∀i j,‖(G.submatrix e e-s.fullOldCovariance selector S G q p (treeEdgeWeight d)) i j‖≤
      (treePatchWeakConstant d Bcap Acap+2*finiteExtraReferenceConstant d)*C1^2*L*ε := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let G:=(g.deficient.restrict S).extensionGreen q z
  let e:=s.fullPartialEmbedding selector S hs
  let A:=s.fullCoreMask S
  let B:=s.fullFirstMask selector S
  let C:=s.fullSecondMask selector S
  let K:=treePatchWeakConstant d Bcap Acap
  let τ:=physicalTransfer d z^(2*r)
  let σ:=C1^2*L*ε
  have hL:0≤L := (by norm_num : (0:ℝ)≤1).trans num.log_one
  have hε:0≤ε := num.error_nonnegative
  have hσ:0≤σ := by dsimp only [σ]; positivity
  have hτ:0≤τ := pow_nonneg (physicalTransfer_pos d hd z).le _
  have hBcap:0≤Bcap := (norm_nonneg z).trans hzB
  have hAcap:0≤Acap := num.log_cap_nonnegative
  have hK:0≤K := by
    have hloc:=DeficientGraph.localizationWeakConstant_ge_one d hd Bcap Acap num.log_cap_nonnegative
    dsimp only [K,treePatchWeakConstant]
    have hx:0≤2*(Bcap+1)*(Real.sqrt (Bcap+2)+1)*(8*finiteExtraReferenceConstant d^2+128)*Acap := by positivity
    linarith
  have hC:0≤2*finiteExtraReferenceConstant d := by
    have hh:=finiteExtraReferenceConstant_ge_one d hd
    positivity
  have hτle:τ≤σ := num.tail.trans (by
    have hh:=mul_le_mul_of_nonneg_left num.log_one (mul_nonneg (sq_nonneg C1) hε)
    dsimp only [σ]
    nlinarith only [hh])
  have hKle:K*σ≤(K+2*finiteExtraReferenceConstant d)*σ := by nlinarith
  have hCle:2*finiteExtraReferenceConstant d*τ≤(K+2*finiteExtraReferenceConstant d)*σ :=
    (mul_le_mul_of_nonneg_left hτle hC).trans (by nlinarith)
  have hprior':=hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) hε num.coefficient_one)
  have hsmall:=(DeficientGraph.weak_localization_feedback_budgets d hd z q hz Bcap (C1^2*ε)
    L Acap (mul_nonneg (sq_nonneg C1) hε) num.log_one num.log_cap_nonnegative num.error_scaled hprior'
    R (4*r+1) hRlog num.pair_log num.localization_large).1
  have hdiag (i:s.AdmissibleSampleIndex selector) (x:S)
      (hx:x.val=(s.admissibleSampleVertex selector i).val∨x.val=(s.admissibleSecondVertex selector i).val) :
      ‖G x x-p‖≤K*σ := by
    rcases hx with hx | hx
    · have hh:=g.full_sample_diagonal_weak_value hd T labels samples selector r (by omega) i
        (s.admissibleSampleVertex selector i) (Or.inl rfl) S hb x hx R q p z hq0 hp hz hq
        Bcap C1 ε L Acap hzB num hprior hR hRlog hpbound hqinv hqpow
      simpa only [K,σ,mul_assoc] using hh
    · have hh:=g.full_sample_diagonal_weak_value hd T labels samples selector r (by omega) i
        (s.admissibleSecondVertex selector i) (Or.inr (Set.mem_singleton _)) S hb x hx R q p z hq0 hp hz hq
        Bcap C1 ε L Acap hzB num hprior hR hRlog hpbound hqinv hqpow
      simpa only [K,σ,mul_assoc] using hh
  have hadj (i:s.AdmissibleSampleIndex selector) (x y:S)
      (hx:x.val=(s.admissibleSampleVertex selector i).val) (hy:y.val=(s.admissibleSecondVertex selector i).val) :
      ‖G x y-p*(-q*treeEdgeWeight d)‖≤K*σ := by
    have hh:=g.full_sample_adjacent_weak_value hd T labels samples selector r (by omega) i S hb x y hx hy
      R q p z hq0 hp hz hq Bcap C1 ε L Acap hzB num hprior hR hRlog hpbound hqinv hqpow
    simpa only [K,σ,mul_assoc] using hh
  have hfar (x y:S) (hxy:((2*r:ℕ):ℕ∞)≤g.graph.edist x.val y.val) :
      ‖G x y‖≤2*finiteExtraReferenceConstant d*τ :=
    (g.deficient.restrict S).perturbed_green_edist_bound hd hb z q hz hq R hR hsmall
      x y (2*r) (hxy.trans (ambient_edist_le_induced_edist g.graph S x y))
  let pairV (i:s.AdmissibleSampleIndex selector) (k:Bool): (Tᶜ:Set (Fin N)):=
    if k then s.admissibleSecondVertex selector i else s.admissibleSampleVertex selector i
  have hpair (i:s.AdmissibleSampleIndex selector) (k:Bool):pairV i k∈s.admissiblePairRoots selector i:=by
    cases k <;> simp [pairV,LabelledResamplingState.admissiblePairRoots]
  have hdiff (i j:s.AdmissibleSampleIndex selector) (hne:i≠j) (k l:Bool) :
      ((2*r:ℕ):ℕ∞)≤g.graph.edist (pairV i k).val (pairV j l).val :=
    (ENat.coe_le_coe.mpr (by omega:2*r≤selector-1)).trans
      (s.admissiblePairRoots_ambient_separated selector hs i j hne _ _ (hpair i k) (hpair j l)).le
  have hab (a:A) (x:S) (j:s.AdmissibleSampleIndex selector)
      (hx:x.val=(s.admissibleSampleVertex selector j).val∨x.val=(s.admissibleSecondVertex selector j).val) :
      ‖G (s.fullCoreEmbedding S a) x‖≤2*finiteExtraReferenceConstant d*τ := by
    have ha:a.val∈T∨∃α:BoundaryOrientedEdge g.graph T,a.val=(boundaryOuterEndpoint g.graph T α).val:=by
      rcases a.property.2 with ha | ⟨w,⟨α,rfl⟩,he⟩
      · exact Or.inl ha
      · exact Or.inr ⟨α,he.symm⟩
    apply hfar
    rw [SimpleGraph.edist_comm]
    rcases hx with hx | hx
    · rw [hx]
      exact (ENat.coe_le_coe.mpr (by omega:2*r≤selector-1)).trans
        (s.admissiblePairRoots_ambient_far_core selector hs j _ (Or.inl rfl) a.val ha).le
    · rw [hx]
      exact (ENat.coe_le_coe.mpr (by omega:2*r≤selector-1)).trans
        (s.admissiblePairRoots_ambient_far_core selector hs j _ (Or.inr (Set.mem_singleton _)) a.val ha).le
  have hsym:G.IsSymm := DeficientGraph.extensionGreen_isSymm _ _ _
  have hbound:(treePatchWeakConstant d Bcap Acap+2*finiteExtraReferenceConstant d)*C1^2*L*ε=
      (K+2*finiteExtraReferenceConstant d)*σ := by dsimp only [K,σ]; ring
  rw [hbound]
  intro u v
  rcases u with a | (b | c) <;> rcases v with a' | (b' | c')
  · simp [LabelledResamplingState.fullOldCovariance,LabelledResamplingState.fullPartialEmbedding,
      LabelledResamplingState.fullPartialVertex,LabelledResamplingState.fullCoreEmbedding]
    exact mul_nonneg (add_nonneg hK hC) hσ
  · change ‖G (s.fullCoreEmbedding S a) (e (.inr (.inl b')))-0‖≤_
    simpa only [sub_zero] using (hab a (e (.inr (.inl b'))) b'.val (Or.inl rfl)).trans hCle
  · change ‖G (s.fullCoreEmbedding S a) (e (.inr (.inr c')))-0‖≤_
    simpa only [sub_zero] using (hab a (e (.inr (.inr c'))) c'.val (Or.inr rfl)).trans hCle
  · change ‖G (e (.inr (.inl b))) (s.fullCoreEmbedding S a')-0‖≤_
    rw [hsym.apply]
    simpa only [sub_zero] using (hab a' (e (.inr (.inl b))) b.val (Or.inl rfl)).trans hCle
  · by_cases he:b=b'
    · subst b'
      change ‖G (e (.inr (.inl b))) (e (.inr (.inl b)))-_‖≤_
      simpa [LabelledResamplingState.fullOldCovariance,partialSampleCovariance,Matrix.smul_apply,Matrix.one_apply] using
        (hdiag b.val (e (.inr (.inl b))) (Or.inl rfl)).trans hKle
    · have hn:b.val≠b'.val:=fun h=>he (Subtype.ext h)
      have hf:=hfar (e (.inr (.inl b))) (e (.inr (.inl b')))
        (hdiff b.val b'.val hn false false)
      simpa [LabelledResamplingState.fullOldCovariance,partialSampleCovariance,Matrix.smul_apply,Matrix.one_apply,he] using hf.trans hCle
  · by_cases he:b.val=c'.val
    · have hh:=hadj b.val (e (.inr (.inl b))) (e (.inr (.inr c'))) rfl
        (by change (s.admissibleSecondVertex selector c'.val).val=(s.admissibleSecondVertex selector b.val).val;rw [he])
      have hv:p*(-q*treeEdgeWeight d)=
          -(treeEdgeWeight d:ℂ)*q*p:=by ring
      rw [hv] at hh
      simpa [LabelledResamplingState.fullOldCovariance,partialSampleCovariance,partialMatchingCoupling,he] using hh.trans hKle
    · have hf:=hfar (e (.inr (.inl b))) (e (.inr (.inr c'))) (hdiff b.val c'.val he false true)
      simpa [LabelledResamplingState.fullOldCovariance,partialSampleCovariance,partialMatchingCoupling,he] using hf.trans hCle
  · change ‖G (e (.inr (.inr c))) (s.fullCoreEmbedding S a')-0‖≤_
    rw [hsym.apply]
    simpa only [sub_zero] using (hab a' (e (.inr (.inr c))) c.val (Or.inr rfl)).trans hCle
  · have hh : ‖G (e (.inr (.inr c))) (e (.inr (.inl b')))-
        partialMatchingCoupling C B (-(treeEdgeWeight d:ℂ)*q*p) c b'‖≤
        (K+2*finiteExtraReferenceConstant d)*σ := by
      rw [hsym.apply]
      by_cases he:c.val=b'.val
      · have hg:=hadj b'.val (e (.inr (.inl b'))) (e (.inr (.inr c))) rfl
          (by change (s.admissibleSecondVertex selector c.val).val=(s.admissibleSecondVertex selector b'.val).val;rw [he])
        have hv:p*(-q*treeEdgeWeight d)=
            -(treeEdgeWeight d:ℂ)*q*p:=by ring
        rw [hv] at hg
        simpa [partialMatchingCoupling,he] using hg.trans hKle
      · have hf:=hfar (e (.inr (.inl b'))) (e (.inr (.inr c))) (hdiff b'.val c.val (Ne.symm he) false true)
        simpa [partialMatchingCoupling,he] using hf.trans hCle
    simpa [LabelledResamplingState.fullOldCovariance,partialSampleCovariance,partialMatchingCoupling,Matrix.transpose_apply,eq_comm] using hh
  · by_cases he:c=c'
    · subst c'
      change ‖G (e (.inr (.inr c))) (e (.inr (.inr c)))-_‖≤_
      simpa [LabelledResamplingState.fullOldCovariance,partialSampleCovariance,Matrix.smul_apply,Matrix.one_apply] using
        (hdiag c.val (e (.inr (.inr c))) (Or.inr rfl)).trans hKle
    · have hn:c.val≠c'.val:=fun h=>he (Subtype.ext h)
      have hf:=hfar (e (.inr (.inr c))) (e (.inr (.inr c'))) (hdiff c.val c'.val hn true true)
      simpa [LabelledResamplingState.fullOldCovariance,partialSampleCovariance,Matrix.smul_apply,Matrix.one_apply,he] using hf.trans hCle

end RegularGraph
end LocalLaw
