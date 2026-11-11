import LocalLaw.PartialEndpointMasks
import LocalLaw.PartialSampleTreeTail
import LocalLaw.PartialSampleBenchmark

/-! # Pure tree-tail comparison for the actual partially retained endpoints -/

noncomputable section
namespace LocalLaw
local instance partialEndpointCovarianceDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem physical_green_edist_bound (g : DeficientGraph V d) (hd:3≤d)
    (hb:g.ComponentFiniteReferenceBudget) (z:ℂ) (hz:0<z.im) (x y:V) (h:ℕ)
    (hfar:(h:ℕ∞)≤g.graph.edist x y) :
    ‖g.extensionGreen (semicircleRoot z) z x y‖≤
      2*finiteExtraReferenceConstant d*physicalTransfer d z^h := by
  let R:=Finset.univ.sup (fun ij:V×V=>g.graph.dist ij.1 ij.2)
  have hR (i j:V):g.graph.dist i j≤R:=Finset.le_sup (f:=fun ij:V×V=>g.graph.dist ij.1 ij.2) (Finset.mem_univ (i,j))
  have hk:=g.componentwise_finite_kernel_decay hd hb (semicircleRoot z) z hz
    (semicircleRoot_im_pos hz).le R hR (by simp) x y
  have hC:0≤2*finiteExtraReferenceConstant d:=by
    have hh:=finiteExtraReferenceConstant_ge_one d hd; positivity
  have ht:0≤physicalTransfer d z:=(physicalTransfer_pos d hd z).le
  have ht1:physicalTransfer d z≤1:=by nlinarith [physicalTransfer_sq_le_half d hd z]
  by_cases hr:g.graph.Reachable x y
  · have heq:(g.graph.dist x y:ℕ∞)=g.graph.edist x y:=
      ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr hr)
    have hh:h≤g.graph.dist x y:=ENat.coe_le_coe.mp (hfar.trans_eq heq.symm)
    exact hk.trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht ht1 hh) hC)
  · let c:=g.graph.connectedComponentMk x
    have hy:y∉c.supp:=fun hy=>hr (SimpleGraph.ConnectedComponent.exact hy.symm)
    rw [g.extensionGreen_zero_across_cut hd c.supp (g.component_cut c) _ z hz
      (semicircleRoot_im_pos hz).le _ rfl _ hy,norm_zero]
    positivity

end DeficientGraph
namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type}

def partialOldCovariance (s : LabelledResamplingState V T ι) (selector : ℕ)
    (S : Set (Tᶜ:Set V)) (G : Matrix S S ℂ) (m p α:ℂ) :
    Matrix (s.PartialEndpointIndex selector S) (s.PartialEndpointIndex selector S) ℂ :=
  Matrix.fromBlocks (G.submatrix (s.partialBoundaryEmbedding selector S)
      (s.partialBoundaryEmbedding selector S)) 0 0
    (partialSampleCovariance (s.partialFirstMask selector S) (s.partialSecondMask selector S) m p α)

end LabelledResamplingState
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

omit [Fintype ι] in
theorem partial_endpoint_far_bound (g : RegularGraph N d) (hd:3≤d)
    (T:Set (Fin N)) (_labels:ι≃BoundaryOrientedEdge g.graph T) (_samples:LocalSamplingFiber g.graph T)
    (selector r:ℕ) (_hr:2*r+2≤selector) (S:Set (Tᶜ:Set (Fin N)))
    (hb:((g.deficient.delete T).restrict S).ComponentFiniteReferenceBudget)
    (z:ℂ) (hz:0<z.im) (x y:S)
    (hfar:((2*r:ℕ):ℕ∞)≤(outsideGraph g.graph T).edist x.val y.val) :
    ‖((g.deficient.delete T).restrict S).extensionGreen (semicircleRoot z) z x y‖≤
      2*finiteExtraReferenceConstant d*physicalTransfer d z^(2*r) := by
  apply DeficientGraph.physical_green_edist_bound _ hd hb z hz x y (2*r)
  exact hfar.trans (ambient_edist_le_induced_edist (outsideGraph g.graph T) S x y)

omit [Fintype ι] in
theorem partial_endpoint_boundary_sample_far (g : RegularGraph N d)
    (T:Set (Fin N)) (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector r:ℕ) (hr:2*r+2≤selector)
    (i j:(g.admissibleState T labels samples).AdmissibleSampleIndex selector)
    (x:(Tᶜ:Set (Fin N)))
    (hx:x∈(g.admissibleState T labels samples).admissiblePairRoots selector j) :
    ((2*r:ℕ):ℕ∞)≤(outsideGraph g.graph T).edist
      ((g.admissibleState T labels samples).admissibleBoundaryVertex selector i) x := by
  let s:=g.admissibleState T labels samples
  have hf:=s.admissiblePairRoots_far_boundary selector (by omega) j hx (s.boundary i.val)
  rw [SimpleGraph.edist_comm] at hf
  exact (ENat.coe_le_coe.mpr (by omega : 2*r≤selector-1)).trans hf.le

omit [Fintype ι] in
theorem partial_endpoint_old_covariance (g : RegularGraph N d) (hd:3≤d)
    (T:Set (Fin N)) (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector r:ℕ) (hr:2*r+2≤selector) (S:Set (Tᶜ:Set (Fin N)))
    (hb:((g.deficient.delete T).restrict S).ComponentFiniteReferenceBudget)
    (z:ℂ) (hz:0<z.im) :
    let s:=g.admissibleState T labels samples
    let G:=((g.deficient.delete T).restrict S).extensionGreen (semicircleRoot z) z
    let P:=s.partialOldCovariance selector S G (semicircleRoot z)
      (graphKestenMcKayReference d z) (treeEdgeWeight d)
    ∀ i j,‖(G.submatrix (s.partialEndpointEmbedding selector S)
      (s.partialEndpointEmbedding selector S)-P) i j‖≤
        (physicalModelTailConstant d+2*finiteExtraReferenceConstant d)*physicalTransfer d z^(2*r) := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let G:=((g.deficient.delete T).restrict S).extensionGreen (semicircleRoot z) z
  let e:=s.partialEndpointEmbedding selector S
  let A:=s.partialBoundaryMask selector S
  let B:=s.partialFirstMask selector S
  let C:=s.partialSecondMask selector S
  let τ:=physicalTransfer d z^(2*r)
  have hτ:0≤τ:=pow_nonneg (physicalTransfer_pos d hd z).le _
  have hK:0≤physicalModelTailConstant d:=by
    have hc:=finiteExtraReferenceConstant_ge_one d hd
    have hm:0≤DeficientGraph.localizationExceptionalMass d 1:=by
      have hdR:(3:ℝ)≤d:=Nat.cast_le.mpr hd
      have hden:0≤(d:ℝ)-1:=by linarith
      unfold DeficientGraph.localizationExceptionalMass
      positivity
    have hdR:(3:ℝ)≤d:=Nat.cast_le.mpr hd
    have hden:0≤(d:ℝ)-1:=by linarith
    have hc0:0≤finiteExtraReferenceConstant d:=by linarith
    unfold physicalModelTailConstant
    positivity
  have hC:0≤2*finiteExtraReferenceConstant d:=by
    have hh:=finiteExtraReferenceConstant_ge_one d hd; positivity
  have hKle:physicalModelTailConstant d*τ≤(physicalModelTailConstant d+2*finiteExtraReferenceConstant d)*τ:=by nlinarith
  have hCle:2*finiteExtraReferenceConstant d*τ≤(physicalModelTailConstant d+2*finiteExtraReferenceConstant d)*τ:=by nlinarith
  have hdiag (i:s.AdmissibleSampleIndex selector) (x:S) (hx:x.val∈s.admissiblePairRoots selector i) :
      ‖G x x-graphKestenMcKayReference d z‖≤physicalModelTailConstant d*τ :=
    g.partial_sample_diagonal_physical_tail hd T labels samples selector r (by omega) i S hb x hx z hz
  have hfar (x y:S) (hxy:((2*r:ℕ):ℕ∞)≤(outsideGraph g.graph T).edist x.val y.val) :
      ‖G x y‖≤2*finiteExtraReferenceConstant d*τ :=
    g.partial_endpoint_far_bound hd T labels samples selector r hr S hb z hz x y hxy
  have hdiff (i j:s.AdmissibleSampleIndex selector) (hne:i≠j) (k l:Fin 3) :
      ((2*r:ℕ):ℕ∞)≤(outsideGraph g.graph T).edist
        (s.admissibleTripleVertex selector (i,k)) (s.admissibleTripleVertex selector (j,l)) :=
    (ENat.coe_le_coe.mpr (by omega : 2*r≤selector)).trans
      (s.admissibleTripleVertex_separated selector i j hne k l).le
  have hab (a:A) (x:S) (j:s.AdmissibleSampleIndex selector) (hx:x.val∈s.admissiblePairRoots selector j) :
      ‖G (s.partialBoundaryEmbedding selector S a) x‖≤2*finiteExtraReferenceConstant d*τ :=
    hfar _ _ (g.partial_endpoint_boundary_sample_far T labels samples selector r hr a.val j x.val hx)
  have hsym:G.IsSymm:=DeficientGraph.extensionGreen_isSymm _ _ _
  intro u v
  rcases u with a | (b | c) <;> rcases v with a' | (b' | c')
  · simp [LabelledResamplingState.partialOldCovariance,LabelledResamplingState.partialEndpointEmbedding,
      LabelledResamplingState.partialEndpointVertex,LabelledResamplingState.partialBoundaryEmbedding]
    exact mul_nonneg (add_nonneg hK hC) hτ
  · change ‖G (s.partialBoundaryEmbedding selector S a) (e (.inr (.inl b')))-0‖≤_
    simpa only [sub_zero] using (hab a _ b'.val (Or.inl rfl)).trans hCle
  · change ‖G (s.partialBoundaryEmbedding selector S a) (e (.inr (.inr c')))-0‖≤_
    simpa only [sub_zero] using (hab a _ c'.val (Or.inr (Set.mem_singleton _))).trans hCle
  · change ‖G (e (.inr (.inl b))) (s.partialBoundaryEmbedding selector S a')-0‖≤_
    rw [hsym.apply]
    simpa only [sub_zero] using (hab a' _ b.val (Or.inl rfl)).trans hCle
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
    · have hh:=g.partial_sample_adjacent_physical_tail hd T labels samples selector r (by omega)
        b.val S hb (e (.inr (.inl b))) (e (.inr (.inr c'))) rfl
        (by change s.admissibleSecondVertex selector c'.val=s.admissibleSecondVertex selector b.val;rw [he]) z hz
      have hv:graphKestenMcKayReference d z*(-semicircleRoot z*treeEdgeWeight d)=
          -(treeEdgeWeight d:ℂ)*semicircleRoot z*graphKestenMcKayReference d z:=by ring
      rw [hv] at hh
      simpa [LabelledResamplingState.partialOldCovariance,partialSampleCovariance,partialMatchingCoupling,he] using hh.trans hKle
    · have hf:=hfar (e (.inr (.inl b))) (e (.inr (.inr c'))) (hdiff b.val c'.val he 1 2)
      simpa [LabelledResamplingState.partialOldCovariance,partialSampleCovariance,partialMatchingCoupling,he] using hf.trans hCle
  · change ‖G (e (.inr (.inr c))) (s.partialBoundaryEmbedding selector S a')-0‖≤_
    rw [hsym.apply]
    simpa only [sub_zero] using (hab a' _ c.val (Or.inr (Set.mem_singleton _))).trans hCle
  · have hh : ‖G (e (.inr (.inr c))) (e (.inr (.inl b')))-
        partialMatchingCoupling C B (-(treeEdgeWeight d:ℂ)*semicircleRoot z*graphKestenMcKayReference d z) c b'‖≤
        (physicalModelTailConstant d+2*finiteExtraReferenceConstant d)*τ := by
      rw [hsym.apply]
      by_cases he:c.val=b'.val
      · have hg:=g.partial_sample_adjacent_physical_tail hd T labels samples selector r (by omega)
          b'.val S hb (e (.inr (.inl b'))) (e (.inr (.inr c))) rfl
          (by change s.admissibleSecondVertex selector c.val=s.admissibleSecondVertex selector b'.val;rw [he]) z hz
        have hv:graphKestenMcKayReference d z*(-semicircleRoot z*treeEdgeWeight d)=
            -(treeEdgeWeight d:ℂ)*semicircleRoot z*graphKestenMcKayReference d z:=by ring
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
