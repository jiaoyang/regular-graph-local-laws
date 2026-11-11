import LocalLaw.AttachedLeafTargetBound

/-! # Two-scale Schur bounds with no count loss on the small error

Pointwise factors are bounded by a spatial term plus a uniform error.
The uniform error is paired with the actual L1 vectors; only the spatial
product pays the number of leaf slots.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance twoScaleSchurTargetDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {I:Type}[Fintype I]

theorem two_scale_product_bound (x y s t δ:ℝ)(hx:0≤x)(hy:0≤y)(hs:0≤s)(ht:0≤t)(hδ:0≤δ)
    (hxs:x≤s+δ)(hyt:y≤t+δ) : x*y≤s*t+δ*x+δ*y := by
  by_cases hxd:x≤δ
  · nlinarith [mul_le_mul_of_nonneg_right hxd hy,mul_nonneg hs ht,mul_nonneg hδ hx]
  by_cases hyd:y≤δ
  · nlinarith [mul_le_mul_of_nonneg_left hyd hx,mul_nonneg hs ht,mul_nonneg hδ hy]
  have hp: (x-δ)*(y-δ)≤s*t:=mul_le_mul (by linarith) (by linarith) (by linarith) hs
  nlinarith [sq_nonneg δ]

theorem schurBilinear_two_scale_bound (a b:I→ℂ)(R:Matrix I I ℂ)(s t δ A B C:ℝ)
    (hs:0≤s)(ht:0≤t)(hδ:0≤δ)(hC:0≤C)
    (ha:∀i,‖a i‖≤s+δ)(hb:∀i,‖b i‖≤t+δ)
    (hA:(∑i,‖a i‖)≤A)(hB:(∑i,‖b i‖)≤B)
    (hr:∀i,∑j,‖R i j‖≤C)(hc:∀j,∑i,‖R i j‖≤C) :
    ‖schurBilinear a R b‖≤(Fintype.card I:ℝ)*C*s*t+C*δ*(A+B) := by
  have hmass:(∑i:I,∑j:I,‖R i j‖)≤(Fintype.card I:ℝ)*C:=by
    exact (Finset.sum_le_sum (fun i _=>hr i)).trans_eq (by simp)
  have hleft:(∑i:I,∑j:I,‖R i j‖*‖a i‖)≤C*A:=by
    calc
      _=∑i:I,(∑j:I,‖R i j‖)*‖a i‖:=by simp only [Finset.sum_mul]
      _≤∑i:I,C*‖a i‖:=Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (hr i) (norm_nonneg _))
      _=C*∑i:I,‖a i‖:=(Finset.mul_sum ..).symm
      _≤_:=mul_le_mul_of_nonneg_left hA hC
  have hright:(∑i:I,∑j:I,‖R i j‖*‖b j‖)≤C*B:=by
    rw [Finset.sum_comm]
    calc
      _=∑j:I,(∑i:I,‖R i j‖)*‖b j‖:=by simp only [Finset.sum_mul]
      _≤∑j:I,C*‖b j‖:=Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_right (hc j) (norm_nonneg _))
      _=C*∑j:I,‖b j‖:=(Finset.mul_sum ..).symm
      _≤_:=mul_le_mul_of_nonneg_left hB hC
  calc
    _≤∑i:I,∑j:I,‖a i‖*‖R i j‖*‖b j‖:=by
      unfold schurBilinear
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_mul] using norm_sum_le Finset.univ (fun j=>a i*R i j*b j)
    _≤∑i:I,∑j:I,((s*t)*‖R i j‖+δ*(‖R i j‖*‖a i‖)+δ*(‖R i j‖*‖b j‖)):=by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hh:=mul_le_mul_of_nonneg_left (two_scale_product_bound ‖a i‖ ‖b j‖ s t δ
        (norm_nonneg _) (norm_nonneg _) hs ht hδ (ha i) (hb j)) (norm_nonneg (R i j))
      convert hh using 1 <;> ring
    _=(s*t)*(∑i:I,∑j:I,‖R i j‖)+δ*(∑i:I,∑j:I,‖R i j‖*‖a i‖)+δ*(∑i:I,∑j:I,‖R i j‖*‖b j‖):=by
      simp only [Finset.sum_add_distrib,←Finset.mul_sum]
    _≤(s*t)*((Fintype.card I:ℝ)*C)+δ*(C*A)+δ*(C*B):=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hmass (mul_nonneg hs ht))
        (mul_le_mul_of_nonneg_left hleft hδ)) (mul_le_mul_of_nonneg_left hright hδ)
    _=_:=by ring

namespace DeficientGraph
variable {V:Type}[Fintype V]{d:ℕ}

theorem attachLeaves_two_scale_target_change (g:DeficientGraph V d)(hd:3≤d)
    (mate:I→V)(hr:∀v,multiLeafMultiplicity mate v≤g.deficit v)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(B W s t δ A C:ℝ)(hzB:‖z‖≤B)(hqnorm:‖q‖≤2)
    (hW:0≤W)(hs:0≤s)(ht:0≤t)(hδ:0≤δ)
    (hrows:∀l,∑k:I,‖g.extensionGreen q z (mate l) (mate k)‖≤W)
    (x y:V)
    (hx:∀l,‖(g.attachLeaves (by omega) mate hr).extensionGreen q z (.inl x) (.inr l)‖≤s+δ)
    (hy:∀l,‖(g.attachLeaves (by omega) mate hr).extensionGreen q z (.inr l) (.inl y)‖≤t+δ)
    (hA:(∑l:I,‖(g.attachLeaves (by omega) mate hr).extensionGreen q z (.inl x) (.inr l)‖)≤A)
    (hC:(∑l:I,‖(g.attachLeaves (by omega) mate hr).extensionGreen q z (.inr l) (.inl y)‖)≤C) :
    ‖(g.attachLeaves (by omega) mate hr).extensionGreen q z (.inl x) (.inl y)-g.extensionGreen q z x y‖≤
      (Fintype.card I:ℝ)*(B+2+W)*s*t+(B+2+W)*δ*(A+C) := by
  let H:=g.attachLeaves (by omega) mate hr
  let G:=H.extensionGreen q z
  let R:=(G.submatrix Sum.inr Sum.inr)⁻¹
  have hR:∀l,∑k:I,‖R l k‖≤B+2+W:=g.attachLeaves_inverse_leaf_rows hd mate hr q z hz hq B W hzB hqnorm hW hrows
  have hRS:R.IsSymm:=by
    change R.transpose=R
    rw [Matrix.transpose_nonsing_inv]
    congr 1
    exact (H.extensionGreen_isSymm q z).submatrix Sum.inr
  have hRC:∀k,∑l:I,‖R l k‖≤B+2+W:=by
    intro k
    have he:(∑l:I,‖R l k‖)=∑l:I,‖R k l‖:=by
      apply Finset.sum_congr rfl
      intro l _
      exact congrArg norm (hRS.apply k l)
    exact he.le.trans (hR k)
  have hK:0≤B+2+W:=by linarith [(norm_nonneg z).trans hzB]
  have hschur: g.extensionGreen q z x y=G (.inl x) (.inl y)-
      schurBilinear (fun l:I=>G (.inl x) (.inr l)) R (fun l=>G (.inr l) (.inl y)):=
    (g.attachLeaves_Green_leaf_schur hd mate hr q z hz hq).2 x y
  have he:G (.inl x) (.inl y)-g.extensionGreen q z x y=
      schurBilinear (fun l:I=>G (.inl x) (.inr l)) R (fun l=>G (.inr l) (.inl y)):=by linear_combination -hschur
  change ‖G (.inl x) (.inl y)-g.extensionGreen q z x y‖≤_
  rw [he]
  exact schurBilinear_two_scale_bound _ _ R s t δ A C (B+2+W) hs ht hδ hK hx hy hA hC hR hRC

end DeficientGraph
end LocalLaw
