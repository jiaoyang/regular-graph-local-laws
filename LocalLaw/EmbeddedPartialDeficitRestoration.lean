import LocalLaw.SupportedRetainedInverse
import LocalLaw.RestoredBoundaryQRows

/-! # Retain every endpoint while restoring an arbitrary subset

This includes the A block whose B mate is omitted. The restored core is a
genuine old deficient model; its reference class and endpoint row bounds
are inherited rather than assumed for the switched model.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance embeddedPartialRestoreDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] {d:ℕ}

theorem partialDeficitRestoration_embedding_rows (g:DeficientGraph V d)(hd:3≤d)
    (hb:g.ComponentFiniteReferenceBudget)(e:I↪V)(A:Set I)
    (hpos:∀v∈Set.range e,0<g.deficit v)(h:ℕ)
    (hsep:∀i j,i≠j→(h:ℕ∞)≤g.graph.edist (e i) (e j))
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(R:ℕ)(hR:∀x y,g.graph.dist x y≤R)
    (small:‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2)
    (hcount:(Fintype.card I:ℝ)*physicalTransfer d z^h≤1) :
    let P:=(g.extensionGreen q z).submatrix e e
    let K:=P⁻¹-q•Matrix.diagonal (fun i:I=>if i∈A then ((1/((d:ℝ)-1):ℝ):ℂ) else 0)
    IsUnit K ∧ (∀i,∑j,‖K⁻¹ i j‖≤4*finiteExtraReferenceConstant d) ∧
      (∀j,∑i,‖K⁻¹ i j‖≤4*finiteExtraReferenceConstant d) := by
  dsimp only
  let F:Set V:=(e:I→V) '' A
  have hF:∀v∈F,0<g.deficit v:=by
    rintro v ⟨i,hi,rfl⟩
    exact hpos (e i) ⟨i,rfl⟩
  let M:=g.restoreOneDeficit F hF
  let P:=(g.extensionGreen q z).submatrix e e
  let Q:=(M.extensionGreen q z).submatrix e e
  have hmem (i:I):e i∈F↔i∈A:=by
    constructor
    · rintro ⟨j,hj,hji⟩
      exact e.injective hji ▸ hj
    · intro hi
      exact ⟨i,hi,rfl⟩
  have hdelta:M.extensionMatrix q z-g.extensionMatrix q z=
      -(q•Matrix.diagonal (fun v:V=>if v∈F then ((1/((d:ℝ)-1):ℝ):ℂ) else 0)):=by
    rw [g.restoreOneDeficit_extensionMatrix]
    abel
  have hs:∀x y,x∉Set.range e∨y∉Set.range e→
      (M.extensionMatrix q z-g.extensionMatrix q z) x y=0:=by
    intro x y hxy
    rw [hdelta]
    simp only [Matrix.neg_apply,Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply]
    by_cases h:x=y
    · subst y
      have hx:x∉F:=by
        rintro ⟨i,hi,hix⟩
        have hm:x∈Set.range e:=⟨i,hix⟩
        exact hxy.elim (fun h=>h hm) (fun h=>h hm)
      simp [hx]
    · simp [h]
  have hu:=g.supported_retained_inverse M hd e q z hz hq hs
  have hKi:Q⁻¹=P⁻¹-q•Matrix.diagonal
      (fun i:I=>if i∈A then ((1/((d:ℝ)-1):ℝ):ℂ) else 0):=by
    have hh:=hu.2.2
    rw [hdelta] at hh
    change Q⁻¹=P⁻¹+_ at hh
    rw [hh]
    ext i j
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.submatrix_apply,Matrix.neg_apply,
      Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply,e.injective.eq_iff,hmem]
    ring
  have hK:P⁻¹-q•Matrix.diagonal (fun i:I=>if i∈A then ((1/((d:ℝ)-1):ℝ):ℂ) else 0)=Q⁻¹:=hKi.symm
  rw [hK]
  have hQii:Q⁻¹⁻¹=Q:=Matrix.nonsing_inv_nonsing_inv Q ((Matrix.isUnit_iff_isUnit_det Q).mp hu.2.1)
  refine ⟨Matrix.isUnit_nonsing_inv_iff.mpr hu.2.1,?_,?_⟩
  · rw [hQii]
    exact (M.separated_perturbed_endpoint_rows hd (g.restoreOneDeficit_componentFiniteReferenceBudget F hF hb)
      e h hsep z q hz hq R hR small hcount).1
  · rw [hQii]
    exact (M.separated_perturbed_endpoint_rows hd (g.restoreOneDeficit_componentFiniteReferenceBudget F hF hb)
      e h hsep z q hz hq R hR small hcount).2

end DeficientGraph
end LocalLaw
