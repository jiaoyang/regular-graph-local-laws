import LocalLaw.FiniteStarComparison
import LocalLaw.CapturedStarPrecision
import LocalLaw.SupportedRetainedInverse

/-! # Actual finite-star comparison across an induced restriction

Captured neighborhoods make the sampled rows of the full and restricted
precision matrices literally equal. The core Green blocks may have different
ambient sizes; their difference is lifted by the exact finite-star formula.
-/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance capturedStarReductionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type}

def capturedStarGlobalPartition (J : Set V) : ((Jᶜ : Set V) ⊕ J) ≃ V :=
  (Equiv.sumComm _ _).trans (Equiv.Set.sumCompl J)

def capturedStarLocalPartition (S J : Set V) (hJS : J ⊆ S) :
    ({v : S | v.val ∉ J} ⊕ J) ≃ S where
  toFun a := match a with
    | Sum.inl v => v.val
    | Sum.inr j => ⟨j.val,hJS j.property⟩
  invFun v := if h : v.val ∈ J then Sum.inr ⟨v.val,h⟩ else Sum.inl ⟨v,h⟩
  left_inv a := by cases a with
    | inl v => simp only [dif_neg v.property]
    | inr j => simp only [dif_pos j.property]
  right_inv v := by
    by_cases h : v.val ∈ J
    · simp only [dif_pos h]
    · simp only [dif_neg h]

def capturedStarCoreEmbedding (I J : Set V) (hIJ : ∀v∈I,v∉J) : I ↪ (Jᶜ : Set V) where
  toFun v := ⟨v.val,hIJ v.val v.property⟩
  inj' := fun _ _ h => Subtype.ext (congrArg (fun v : (Jᶜ:Set V) => v.val) h)

def capturedStarLocalCoreEmbedding (S I J : Set V) (hIS : I ⊆ S)
    (hIJ : ∀v∈I,v∉J) : I ↪ {v : S | v.val ∉ J} where
  toFun v := ⟨⟨v.val,hIS v.property⟩,hIJ v.val v.property⟩
  inj' := fun _ _ h => Subtype.ext (congrArg (fun v => v.val.val) h)

def capturedStarEmbedding (I J : Set V) (hIJ : ∀v∈I,v∉J) : I ⊕ J ↪ V :=
  (Function.Embedding.sumMap (capturedStarCoreEmbedding I J hIJ) (Function.Embedding.refl _)).trans
    (capturedStarGlobalPartition J).toEmbedding

def capturedStarLocalEmbedding (S I J : Set V) (hIS : I ⊆ S) (hJS : J ⊆ S)
    (hIJ : ∀v∈I,v∉J) : I ⊕ J ↪ S :=
  (Function.Embedding.sumMap (capturedStarLocalCoreEmbedding S I J hIS hIJ) (Function.Embedding.refl _)).trans
    (capturedStarLocalPartition S J hJS).toEmbedding

namespace DeficientGraph
variable [Fintype V] [DecidableEq V] {d : ℕ}

private theorem captured_star_offdiag_zero (g : DeficientGraph V d) (q z : ℂ)
    (v w : V) (hne : v ≠ w) (hnadj : ¬g.graph.Adj v w) :
    g.extensionMatrix q z v w = 0 := by
  simp [extensionMatrix,boundaryMatrix,spectralMatrix,boundaryDiagonal,
    Matrix.diagonal_apply,Matrix.one_apply,H,normalizedAdjacency,
    SimpleGraph.adjMatrix_apply,hne,hnadj]

/-- All units and all supported coupling equalities are consequences of the
actual finite graph and captured sampled stars. No inverse identity is assumed. -/
theorem captured_star_inverse_difference (g : DeficientGraph V d) (hd : 3≤d)
    (S I J : Set V) (hIS : I ⊆ S) (hJS : J ⊆ S) (hIJ : ∀v∈I,v∉J)
    (hcap : ∀b∈J,∀v,g.graph.Adj b v→v∈S)
    (hcore : ∀b∈J,∀v,g.graph.Adj b v→v∉J→v∈I)
    (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) :
    let e := capturedStarCoreEmbedding I J hIJ
    let f := capturedStarLocalCoreEmbedding S I J hIS hIJ
    let E := capturedStarEmbedding I J hIJ
    let F := capturedStarLocalEmbedding S I J hIS hJS hIJ
    let R := (g.delete J).extensionGreen q z |>.submatrix e e
    let P := ((g.restrict S).delete {v:S | v.val∈J}).extensionGreen q z |>.submatrix f f
    let GM := (g.extensionGreen q z).submatrix E E
    let GN := ((g.restrict S).extensionGreen q z).submatrix F F
    IsUnit R ∧ IsUnit P ∧
      GM-GN=(GM.submatrix id Sum.inl*R⁻¹)*(R-P)*(P⁻¹*GN.submatrix Sum.inl id) := by
  dsimp only
  let e := capturedStarCoreEmbedding I J hIJ
  let f := capturedStarLocalCoreEmbedding S I J hIS hIJ
  let φ := capturedStarGlobalPartition J
  let ψ := capturedStarLocalPartition S J hJS
  let A := (g.delete J).extensionMatrix q z
  let B := ((g.restrict S).delete {v:S | v.val∈J}).extensionMatrix q z
  let U := (g.extensionMatrix q z).submatrix (Subtype.val : (Jᶜ:Set V)→V) (Subtype.val : J→V)
  let W := (g.extensionMatrix q z).submatrix (Subtype.val : J→V) (Subtype.val : (Jᶜ:Set V)→V)
  let U' := ((g.restrict S).extensionMatrix q z).submatrix (Subtype.val : {v:S | v.val∉J}→S)
    (fun b:J => (⟨b.val,hJS b.property⟩:S))
  let W' := ((g.restrict S).extensionMatrix q z).submatrix
    (fun b:J => (⟨b.val,hJS b.property⟩:S)) (Subtype.val : {v:S | v.val∉J}→S)
  let D := (g.extensionMatrix q z).submatrix (Subtype.val : J→V) (Subtype.val : J→V)
  have hM : Matrix.fromBlocks A U W D=(g.extensionMatrix q z).submatrix φ φ := by
    ext a b
    cases a <;> cases b
    · exact congrFun (congrFun (g.extensionMatrix_delete J q z) _) _
    · rfl
    · rfl
    · rfl
  have hN : Matrix.fromBlocks B U' W' D=((g.restrict S).extensionMatrix q z).submatrix ψ ψ := by
    ext a b
    cases a with
    | inl a => cases b with
      | inl b => exact congrFun (congrFun ((g.restrict S).extensionMatrix_delete {v:S | v.val∈J} q z) a) b
      | inr b => rfl
    | inr a => cases b with
      | inl b => rfl
      | inr b => exact (g.restrict_extensionMatrix_captured_row S ⟨a.val,hJS a.property⟩
          (hcap a.val a.property) q z ⟨b.val,hJS b.property⟩).symm
  have hAu := (g.delete J).extensionMatrix_isUnit hd q z hz hq
  have hBu := ((g.restrict S).delete {v:S | v.val∈J}).extensionMatrix_isUnit hd q z hz hq
  have hMu : IsUnit (Matrix.fromBlocks A U W D) := by
    rw [hM]
    exact (Matrix.isUnit_submatrix_equiv φ φ).mpr (g.extensionMatrix_isUnit hd q z hz hq)
  have hNu : IsUnit (Matrix.fromBlocks B U' W' D) := by
    rw [hN]
    exact (Matrix.isUnit_submatrix_equiv ψ ψ).mpr ((g.restrict S).extensionMatrix_isUnit hd q z hz hq)
  have hR := (g.delete J).extensionGreen_submatrix_isUnit hd e q z hz hq
  have hP := ((g.restrict S).delete {v:S | v.val∈J}).extensionGreen_submatrix_isUnit hd f q z hz hq
  have hU : ∀v b,v∉Set.range e→U v b=0 := by
    intro v b hv
    have hnot : v.val∉I := by
      intro hi
      exact hv ⟨⟨v.val,hi⟩,Subtype.ext rfl⟩
    apply g.captured_star_offdiag_zero q z v.val b.val
    · exact fun he => v.property (he ▸ b.property)
    · intro hadj
      exact hnot (hcore b.val b.property v.val (g.graph.adj_symm hadj) v.property)
  have hW : ∀b v,v∉Set.range e→W b v=0 := by
    intro b v hv
    exact ((g.extensionMatrix_isSymm q z).apply v.val b.val).trans (hU v b hv)
  have hU' : ∀v b,v∉Set.range f→U' v b=0 := by
    intro v b hv
    have hnot : v.val.val∉I := by
      intro hi
      exact hv ⟨⟨v.val.val,hi⟩,Subtype.ext (Subtype.ext rfl)⟩
    have hh := g.restrict_extensionMatrix_captured_column S ⟨b.val,hJS b.property⟩
      (hcap b.val b.property) q z v.val
    change ((g.restrict S).extensionMatrix q z) v.val ⟨b.val,hJS b.property⟩=0
    rw [hh]
    apply g.captured_star_offdiag_zero q z v.val.val b.val
    · exact fun he => v.property (he ▸ b.property)
    · intro hadj
      exact hnot (hcore b.val b.property v.val.val (g.graph.adj_symm hadj) v.property)
  have hW' : ∀b v,v∉Set.range f→W' b v=0 := by
    intro b v hv
    exact (((g.restrict S).extensionMatrix_isSymm q z).apply v.val ⟨b.val,hJS b.property⟩).trans (hU' v b hv)
  have hleft : U.submatrix e id=U'.submatrix f id := by
    ext a b
    exact (g.restrict_extensionMatrix_captured_column S ⟨b.val,hJS b.property⟩
      (hcap b.val b.property) q z ⟨a.val,hIS a.property⟩).symm
  have hright : W.submatrix id e=W'.submatrix id f := by
    ext a b
    exact (g.restrict_extensionMatrix_captured_row S ⟨a.val,hJS a.property⟩
      (hcap a.val a.property) q z ⟨b.val,hIS b.property⟩).symm
  have hh := finite_star_inverse_difference A B U W U' W' D e f hAu hBu hMu hNu hR hP
    hU hW hU' hW' hleft hright
  have hmInv : (Matrix.fromBlocks A U W D)⁻¹=(g.extensionGreen q z).submatrix φ φ := by
    rw [hM]
    exact Matrix.inv_submatrix_equiv (g.extensionMatrix q z) φ φ
  have hnInv : (Matrix.fromBlocks B U' W' D)⁻¹=((g.restrict S).extensionGreen q z).submatrix ψ ψ := by
    rw [hN]
    exact Matrix.inv_submatrix_equiv ((g.restrict S).extensionMatrix q z) ψ ψ
  dsimp only at hh
  rw [hmInv,hnInv] at hh
  exact ⟨hR,hP,hh⟩

end DeficientGraph
end LocalLaw
