import LocalLaw.PartialEndpointWeakCovariance
import LocalLaw.SupportedRetainedInverse

/-! # Scalar covariance of separated tree leaves in arbitrary restrictions

An ambient tree patch suffices even when the restriction cuts that patch.
The retained leaf block is genuinely invertible. Its diagonal follows from
the weak tree residual, and separated off-diagonals follow from actual
finite-model kernel decay.
-/

noncomputable section
namespace LocalLaw
local instance leafScalarCovarianceDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V I:Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] {d:ℕ}

theorem restricted_leaf_scalar_covariance (g:DeficientGraph V d) (hd:3≤d)
    (S:Set V) (hbudget:(g.restrict S).ComponentFiniteReferenceBudget) (e:I↪S) (r R:ℕ)
    (htree:∀i,(graphBall g.graph (e i).val r).IsTree)
    (hzero:∀i,∀w∈graphBallVertices g.graph (e i).val r,g.deficit w=0)
    (hseparated:∀i j,i≠j→((2*r:ℕ):ℕ∞)≤g.graph.edist (e i).val (e j).val)
    (q p z:ℂ) (hq:q≠0) (hp:p*(q⁻¹-q/((d:ℂ)-1))=1) (hz:0<z.im) (hqim:0≤q.im)
    (B C1 ε L A:ℝ) (hzB:‖z‖≤B) (num:SourceObservationBounds d r z B C1 ε L A)
    (hprior:‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z) ε)
    (hR:∀a b,(g.restrict S).graph.dist a b≤R) (hRlog:(R:ℝ)+1≤A*L)
    (hpbound:‖p‖≤4) (hqinv:‖q⁻¹‖≤2*(B+1)) (hqpow:∀n≤4*r+1,‖q‖^n≤2) :
    let G:=((g.restrict S).extensionGreen q z).submatrix e e
    IsUnit G∧∀i j,‖G i j-(if i=j then p else 0)‖≤
      (treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d)*C1^2*L*ε := by
  dsimp only
  let M:=g.restrict S
  let σ:=C1^2*L*ε
  let K:=treePatchWeakConstant d B A
  have hL:0≤L:=(by norm_num:(0:ℝ)≤1).trans num.log_one
  have hε:0≤ε:=num.error_nonnegative
  have hσ:0≤σ:=by dsimp only [σ];positivity
  have hB:0≤B:=(norm_nonneg z).trans hzB
  have hA:0≤A:=num.log_cap_nonnegative
  have hK:0≤K:=by
    have hloc:=localizationWeakConstant_ge_one d hd B A hA
    dsimp only [K,treePatchWeakConstant]
    have hx:0≤2*(B+1)*(Real.sqrt (B+2)+1)*(8*finiteExtraReferenceConstant d^2+128)*A:=by positivity
    linarith
  have hC:0≤2*finiteExtraReferenceConstant d:=by
    have hc:=finiteExtraReferenceConstant_ge_one d hd
    positivity
  have hprior':=hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) hε num.coefficient_one)
  have hsmall:=(weak_localization_feedback_budgets d hd z q hz B (C1^2*ε)
    L A (mul_nonneg (sq_nonneg C1) hε) num.log_one hA num.error_scaled hprior'
    R (4*r+1) hRlog num.pair_log num.localization_large).1
  have htail:physicalTransfer d z^(2*r)≤σ:=num.tail.trans (by
    have hh:=mul_le_mul_of_nonneg_left num.log_one (mul_nonneg (sq_nonneg C1) hε)
    dsimp only [σ]
    nlinarith only [hh])
  refine ⟨M.extensionGreen_submatrix_isUnit hd e q z hz hqim,?_⟩
  intro i j
  have hbound:(treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d)*C1^2*L*ε=
      (K+2*finiteExtraReferenceConstant d)*σ:=by dsimp only [K,σ];ring
  rw [hbound]
  by_cases hij:i=j
  · subst j
    simp only [if_true,Matrix.submatrix_apply]
    have hh:=g.restrict_tree_diagonal_weak_residual hd S hbudget (e i) r R (htree i) (hzero i)
      q p z hq hp hz hqim B C1 ε L A hzB num hprior hR hRlog hpbound hqinv hqpow
    have hh':‖M.extensionGreen q z (e i) (e i)-p‖≤K*σ:=by simpa only [K,σ,mul_assoc] using hh
    exact hh'.trans (by nlinarith)
  · simp only [hij,if_false,sub_zero,Matrix.submatrix_apply]
    have hh:=M.perturbed_green_edist_bound hd hbudget z q hz hqim R hR hsmall (e i) (e j) (2*r)
      ((hseparated i j hij).trans (ambient_edist_le_induced_edist g.graph S (e i) (e j)))
    exact hh.trans ((mul_le_mul_of_nonneg_left htail hC).trans (by nlinarith))

end DeficientGraph
end LocalLaw
