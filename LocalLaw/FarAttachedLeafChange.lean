import LocalLaw.AttachedLeafMatrixBlocks
import LocalLaw.AttachedLeafReferenceBudget
import LocalLaw.SeparatedTargetLeafRows

/-! # Adding outer deficit-restoring leaves has a two-sided tail

No tree hypothesis or scalar diagonal approximation is needed at these
new leaves. Their inverse Green block is computed from the original core.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
namespace LocalLaw
local instance farAttachedLeafDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V I:Type} [Fintype V] [Fintype I] {d:ℕ}

theorem attachLeaves_inverse_leaf_rows (g:DeficientGraph V d)(hd:3≤d)
    (mate:I→V)(hr:∀v,multiLeafMultiplicity mate v≤g.deficit v)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(B W:ℝ)(hzB:‖z‖≤B)(hqnorm:‖q‖≤2)
    (hW:0≤W)(hrows:∀l,∑k:I,‖g.extensionGreen q z (mate l) (mate k)‖≤W) :
    ∀l,∑k:I,‖(((g.attachLeaves (by omega) mate hr).extensionGreen q z).submatrix Sum.inr Sum.inr)⁻¹ l k‖≤B+2+W := by
  rw [g.attachLeaves_leaf_inverse_precision hd mate hr q z hz hq]
  have hα:‖treeEdgeWeight d‖^2≤1:=by
    rw [treeEdgeWeight_norm_sq d hd]
    have hdR:(3:ℝ)≤d:=Nat.cast_le.mpr hd
    exact (div_le_one (by linarith)).mpr (by linarith)
  have hscalar:‖-z-q‖≤B+2:=(norm_sub_le (-z) q).trans (by simpa only [norm_neg] using add_le_add hzB hqnorm)
  intro l
  calc
    _≤∑k:I,(‖(Matrix.diagonal (fun _:I=>-z-q)) l k‖+
        ‖(treeEdgeWeight d)^2*g.extensionGreen q z (mate l) (mate k)‖):=
      Finset.sum_le_sum (fun k _=>norm_sub_le _ _)
    _=‖-z-q‖+‖treeEdgeWeight d‖^2*(∑k:I,‖g.extensionGreen q z (mate l) (mate k)‖):=by
      rw [Finset.sum_add_distrib]
      simp only [norm_mul,norm_pow,←Finset.mul_sum]
      simp [Matrix.diagonal_apply,apply_ite norm]
    _≤(B+2)+1*W:=add_le_add hscalar (mul_le_mul hα (hrows l)
      (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) (by norm_num:(0:ℝ)≤1))
    _=_:=by ring

theorem far_attachLeaves_target_change (g:DeficientGraph V d)(hd:3≤d)
    (hb:g.ComponentFiniteReferenceBudget)(mate:I→V)
    (hr:∀v,multiLeafMultiplicity mate v≤g.deficit v)(r:ℕ)
    (hsep:∀l k,l≠k→(2*r:ℕ∞)<g.graph.edist (mate l) (mate k))
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(B:ℝ)(hzB:‖z‖≤B)(hqnorm:‖q‖≤2)
    (Rg Rh:ℕ)(hRg:∀x y,g.graph.dist x y≤Rg)
    (hRh:∀x y,(g.attachLeaves (by omega) mate hr).graph.dist x y≤Rh)
    (smallg:‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((Rg:ℝ)+1)≤1/2)
    (smallh:‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((Rh:ℝ)+1)≤1/2)
    (hcount:(Fintype.card I:ℝ)*physicalTransfer d z^r≤1)
    (x y:V)(hfarx:∀l,(r:ℕ∞)≤g.graph.edist x (mate l))
    (hfary:∀l,(r:ℕ∞)≤g.graph.edist y (mate l)) :
    ‖(g.attachLeaves (by omega) mate hr).extensionGreen q z (.inl x) (.inl y)-g.extensionGreen q z x y‖≤
      (Fintype.card I:ℝ)*(B+2+4*finiteExtraReferenceConstant d)*
        (2*finiteExtraReferenceConstant d)^2*physicalTransfer d z^(2*r) := by
  let H:=g.attachLeaves (by omega) mate hr
  let P:=H.extensionGreen q z
  let R:=(P.submatrix Sum.inr Sum.inr)⁻¹
  let C:=2*finiteExtraReferenceConstant d
  let K:=B+2+4*finiteExtraReferenceConstant d
  let t:=physicalTransfer d z^r
  have hC:0≤C:=by dsimp only [C];linarith [finiteExtraReferenceConstant_ge_one d hd]
  have hB:0≤B:=(norm_nonneg z).trans hzB
  have hK:0≤K:=by dsimp only [K];have hc:=finiteExtraReferenceConstant_ge_one d hd;positivity
  have ht:0≤t:=pow_nonneg (physicalTransfer_pos d hd z).le _
  have hH:H.ComponentFiniteReferenceBudget:=g.attachLeaves_componentFiniteReferenceBudget (by omega) mate hr hb
  have hrowsg:∀l,∑k:I,‖g.extensionGreen q z (mate l) (mate k)‖≤4*finiteExtraReferenceConstant d:=
    fun l=>(g.separated_target_leaf_rows hd hb mate r hsep q z hz hq Rg hRg smallg hcount).1 (mate l)
  have hRrows:∀l,∑k:I,‖R l k‖≤K:=g.attachLeaves_inverse_leaf_rows hd mate hr q z hz hq B
    (4*finiteExtraReferenceConstant d) hzB hqnorm (by have hc:=finiteExtraReferenceConstant_ge_one d hd;positivity) hrowsg
  have hx:∀l,‖P (.inl x) (.inr l)‖≤C*t:=by
    intro l
    apply H.perturbed_green_edist_bound hd hH z q hz hq Rh hRh smallh _ _ r
    exact (hfarx l).trans (multiLeafGraph_edist_projection g.graph mate (.inl x) (.inr l))
  have hy:∀l,‖P (.inr l) (.inl y)‖≤C*t:=by
    intro l
    have hPsym:P.IsSymm:=H.extensionGreen_isSymm q z
    rw [hPsym.apply (.inl y) (.inr l)]
    apply H.perturbed_green_edist_bound hd hH z q hz hq Rh hRh smallh _ _ r
    exact (hfary l).trans (multiLeafGraph_edist_projection g.graph mate (.inl y) (.inr l))
  have hschur:= (g.attachLeaves_Green_leaf_schur hd mate hr q z hz hq).2 x y
  have he:P (.inl x) (.inl y)-g.extensionGreen q z x y=
      schurBilinear (fun l:I=>P (.inl x) (.inr l)) R (fun l=>P (.inr l) (.inl y)):=by
    change g.extensionGreen q z x y=P (.inl x) (.inl y)-_ at hschur
    linear_combination -hschur
  rw [he]
  have hinner (l:I):(∑k:I,‖R l k‖*‖P (.inr k) (.inl y)‖)≤K*(C*t):=by
    calc
      _≤∑k:I,‖R l k‖*(C*t):=Finset.sum_le_sum (fun k _=>mul_le_mul_of_nonneg_left (hy k) (norm_nonneg _))
      _=(∑k:I,‖R l k‖)*(C*t):=(Finset.sum_mul ..).symm
      _≤_:=mul_le_mul_of_nonneg_right (hRrows l) (mul_nonneg hC ht)
  calc
    _≤∑l:I,∑k:I,‖P (.inl x) (.inr l)‖*‖R l k‖*‖P (.inr k) (.inl y)‖:=by
      unfold schurBilinear
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro l _
      simpa only [norm_mul] using norm_sum_le Finset.univ
        (fun k=>P (.inl x) (.inr l)*R l k*P (.inr k) (.inl y))
    _=∑l:I,‖P (.inl x) (.inr l)‖*(∑k:I,‖R l k‖*‖P (.inr k) (.inl y)‖):=by
      simp only [Finset.mul_sum,mul_assoc]
    _≤∑l:I,(C*t)*(K*(C*t)):=Finset.sum_le_sum (fun l _=>mul_le_mul (hx l) (hinner l)
      (Finset.sum_nonneg (fun _ _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))) (mul_nonneg hC ht))
    _=(Fintype.card I:ℝ)*K*C^2*physicalTransfer d z^(2*r):=by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      dsimp only [t]
      rw [mul_comm 2 r,pow_mul]
      ring
    _=_:=rfl

end DeficientGraph
end LocalLaw
