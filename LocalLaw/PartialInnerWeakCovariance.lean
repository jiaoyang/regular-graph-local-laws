import LocalLaw.PartialInnerAmbient
import LocalLaw.PartialEndpointWeakCovariance

/-! Formal old covariance for deletion of a retained part of T. -/
noncomputable section
set_option maxHeartbeats 2500000
namespace LocalLaw
local instance partialInnerWeakCovarianceDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

omit [Fintype ι] in
theorem partial_inner_old_weak_covariance (g:RegularGraph N d)(hd:3≤d)
    (T:Set (Fin N))(labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector r:ℕ)(hr:2*r+2≤selector)(Sfull:Set (Fin N))(S:Set (Tᶜ:Set (Fin N)))
    (hb:((g.deficient.partialInnerAmbient T Sfull).restrict S).ComponentFiniteReferenceBudget)
    (z q p:ℂ)(hz:0<z.im)(hq:0≤q.im)(hq0:q≠0)
    (hp:p*(q⁻¹-q/((d:ℂ)-1))=1)
    (Bcap C1 ε L Acap:ℝ)(hzB:‖z‖≤Bcap)
    (num:SourceObservationBounds d r z Bcap C1 ε L Acap)
    (hprior:‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z) ε)
    (R:ℕ)(hR:∀u v,((g.deficient.partialInnerAmbient T Sfull).restrict S).graph.dist u v≤R)
    (hRlog:(R:ℝ)+1≤Acap*L)(hpbound:‖p‖≤4)(hqinv:‖q⁻¹‖≤2*(Bcap+1))
    (hqpow:∀n≤4*r+1,‖q‖^n≤2) :
    let s:=g.admissibleState T labels samples
    let G:=((g.deficient.partialInnerAmbient T Sfull).restrict S).extensionGreen q z
    let P:=s.partialOldCovariance selector S G q p (treeEdgeWeight d)
    ∀i j,‖(G.submatrix (s.partialEndpointEmbedding selector S)
      (s.partialEndpointEmbedding selector S)-P) i j‖≤
        (treePatchWeakConstant d Bcap Acap+2*finiteExtraReferenceConstant d)*C1^2*L*ε := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let G:=((g.deficient.partialInnerAmbient T Sfull).restrict S).extensionGreen q z
  let e:=s.partialEndpointEmbedding selector S
  let A:=s.partialBoundaryMask selector S
  let B:=s.partialFirstMask selector S
  let C:=s.partialSecondMask selector S
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
  have hdiag (i:s.AdmissibleSampleIndex selector)(x:S)(hx:x.val∈s.admissiblePairRoots selector i) :
      ‖G x x-p‖≤K*σ := by
    have htree:=g.eligible_sample_root_tree_zero_ball T labels samples selector r (by omega) i x.val hx
    have hh:=(g.deficient.partialInnerAmbient T Sfull).restrict_tree_diagonal_weak_residual hd S hb x r R htree.1
      (fun w hw=>g.deficient.partialInnerAmbient_deficit_zero T Sfull w (htree.2 w hw))
      q p z hq0 hp hz hq Bcap C1 ε L Acap hzB num hprior hR hRlog hpbound hqinv hqpow
    simpa only [K,σ,mul_assoc] using hh
  have hadj (i:s.AdmissibleSampleIndex selector)(x y:S)
      (hx:x.val=s.admissibleSampleVertex selector i)(hy:y.val=s.admissibleSecondVertex selector i) :
      ‖G x y-p*(-q*treeEdgeWeight d)‖≤K*σ := by
    have hxpair:x.val∈s.admissiblePairRoots selector i := by
      rw [hx]
      exact Or.inl rfl
    have htree:=g.eligible_sample_root_tree_zero_ball T labels samples selector (r+1) (by omega) i x.val hxpair
    have hxy:(outsideGraph g.graph T).Adj x.val y.val := by
      rw [hx,hy]
      exact (samples (labels i.val)).property.1
    have hh:=(g.deficient.partialInnerAmbient T Sfull).restrict_tree_adjacent_weak_residual hd S hb x y hxy r R htree.1
      (fun w hw=>g.deficient.partialInnerAmbient_deficit_zero T Sfull w (htree.2 w hw))
      q p z hq0 hp hz hq Bcap C1 ε L Acap hzB num hprior hR hRlog hpbound hqinv hqpow
    simpa only [K,σ,mul_assoc] using hh
  have hfar (x y:S)(hxy:((2*r:ℕ):ℕ∞)≤(outsideGraph g.graph T).edist x.val y.val) :
      ‖G x y‖≤2*finiteExtraReferenceConstant d*τ := by
    exact ((g.deficient.partialInnerAmbient T Sfull).restrict S).perturbed_green_edist_bound hd hb z q hz hq R hR hsmall
      x y (2*r) (hxy.trans (ambient_edist_le_induced_edist (outsideGraph g.graph T) S x y))
  have hdiff (i j:s.AdmissibleSampleIndex selector)(hne:i≠j)(k l:Fin 3) :
      ((2*r:ℕ):ℕ∞)≤(outsideGraph g.graph T).edist
        (s.admissibleTripleVertex selector (i,k)) (s.admissibleTripleVertex selector (j,l)) :=
    (ENat.coe_le_coe.mpr (by omega : 2*r≤selector)).trans
      (s.admissibleTripleVertex_separated selector i j hne k l).le
  have hab (a:A)(x:S)(j:s.AdmissibleSampleIndex selector)(hx:x.val∈s.admissiblePairRoots selector j) :
      ‖G (s.partialBoundaryEmbedding selector S a) x‖≤2*finiteExtraReferenceConstant d*τ :=
    hfar _ _ (g.partial_endpoint_boundary_sample_far T labels samples selector r hr a.val j x.val hx)
  have hsym:G.IsSymm := DeficientGraph.extensionGreen_isSymm _ _ _
  have hbound:(treePatchWeakConstant d Bcap Acap+2*finiteExtraReferenceConstant d)*C1^2*L*ε=
      (K+2*finiteExtraReferenceConstant d)*σ := by dsimp only [K,σ]; ring
  rw [hbound]
  intro u v
  rcases u with a | (b | c) <;> rcases v with a' | (b' | c')
  · simp [LabelledResamplingState.partialOldCovariance,LabelledResamplingState.partialEndpointEmbedding,
      LabelledResamplingState.partialEndpointVertex,LabelledResamplingState.partialBoundaryEmbedding]
    exact mul_nonneg (add_nonneg hK hC) hσ
  · change ‖G (s.partialBoundaryEmbedding selector S a) (e (.inr (.inl b')))-0‖≤_
    simpa only [sub_zero] using (hab a (e (.inr (.inl b'))) b'.val (Or.inl rfl)).trans hCle
  · change ‖G (s.partialBoundaryEmbedding selector S a) (e (.inr (.inr c')))-0‖≤_
    simpa only [sub_zero] using (hab a (e (.inr (.inr c'))) c'.val (Or.inr (Set.mem_singleton _))).trans hCle
  · change ‖G (e (.inr (.inl b))) (s.partialBoundaryEmbedding selector S a')-0‖≤_
    rw [hsym.apply]
    simpa only [sub_zero] using (hab a' (e (.inr (.inl b))) b.val (Or.inl rfl)).trans hCle
  · by_cases he:b=b'
    · subst b'
      change ‖G (e (.inr (.inl b))) (e (.inr (.inl b)))-_‖≤_
      simpa [LabelledResamplingState.partialOldCovariance,partialSampleCovariance,Matrix.smul_apply,Matrix.one_apply] using
        (hdiag b.val (e (.inr (.inl b))) (Or.inl rfl)).trans hKle
    · have hn:b.val≠b'.val:=fun h=>he (Subtype.ext h)
      have hf:=hfar (e (.inr (.inl b))) (e (.inr (.inl b')))
        (hdiff b.val b'.val hn 1 1)
      simpa [LabelledResamplingState.partialOldCovariance,partialSampleCovariance,Matrix.smul_apply,Matrix.one_apply,he] using hf.trans hCle
  · by_cases he:b.val=c'.val
    · have hh:=hadj b.val (e (.inr (.inl b))) (e (.inr (.inr c'))) rfl
        (by change s.admissibleSecondVertex selector c'.val=s.admissibleSecondVertex selector b.val;rw [he])
      have hv:p*(-q*treeEdgeWeight d)=
          -(treeEdgeWeight d:ℂ)*q*p:=by ring
      rw [hv] at hh
      simpa [LabelledResamplingState.partialOldCovariance,partialSampleCovariance,partialMatchingCoupling,he] using hh.trans hKle
    · have hf:=hfar (e (.inr (.inl b))) (e (.inr (.inr c'))) (hdiff b.val c'.val he 1 2)
      simpa [LabelledResamplingState.partialOldCovariance,partialSampleCovariance,partialMatchingCoupling,he] using hf.trans hCle
  · change ‖G (e (.inr (.inr c))) (s.partialBoundaryEmbedding selector S a')-0‖≤_
    rw [hsym.apply]
    simpa only [sub_zero] using (hab a' (e (.inr (.inr c))) c.val (Or.inr (Set.mem_singleton _))).trans hCle
  · have hh : ‖G (e (.inr (.inr c))) (e (.inr (.inl b')))-
        partialMatchingCoupling C B (-(treeEdgeWeight d:ℂ)*q*p) c b'‖≤
        (K+2*finiteExtraReferenceConstant d)*σ := by
      rw [hsym.apply]
      by_cases he:c.val=b'.val
      · have hg:=hadj b'.val (e (.inr (.inl b'))) (e (.inr (.inr c))) rfl
          (by change s.admissibleSecondVertex selector c.val=s.admissibleSecondVertex selector b'.val;rw [he])
        have hv:p*(-q*treeEdgeWeight d)=
            -(treeEdgeWeight d:ℂ)*q*p:=by ring
        rw [hv] at hg
        simpa [partialMatchingCoupling,he] using hg.trans hKle
      · have hf:=hfar (e (.inr (.inl b'))) (e (.inr (.inr c))) (hdiff b'.val c.val (Ne.symm he) 1 2)
        simpa [partialMatchingCoupling,he] using hf.trans hCle
    simpa [LabelledResamplingState.partialOldCovariance,partialSampleCovariance,partialMatchingCoupling,Matrix.transpose_apply,eq_comm] using hh
  · by_cases he:c=c'
    · subst c'
      change ‖G (e (.inr (.inr c))) (e (.inr (.inr c)))-_‖≤_
      simpa [LabelledResamplingState.partialOldCovariance,partialSampleCovariance,Matrix.smul_apply,Matrix.one_apply] using
        (hdiag c.val (e (.inr (.inr c))) (Or.inr (Set.mem_singleton _))).trans hKle
    · have hn:c.val≠c'.val:=fun h=>he (Subtype.ext h)
      have hf:=hfar (e (.inr (.inr c))) (e (.inr (.inr c'))) (hdiff c.val c'.val hn 2 2)
      simpa [LabelledResamplingState.partialOldCovariance,partialSampleCovariance,Matrix.smul_apply,Matrix.one_apply,he] using hf.trans hCle

end RegularGraph
end LocalLaw
