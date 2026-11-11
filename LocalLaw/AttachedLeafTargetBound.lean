import LocalLaw.FarAttachedLeafChange

/-! # Arbitrary core models with retained extra leaves

The core need not itself satisfy a reference-class bound. Its proved mate
row sums and the augmented target-to-leaf bounds control the exact Schur
correction, including models obtained after deleting other leaf families.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance attachedLeafTargetDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {I:Type} [Fintype I]

theorem schurBilinear_bound_of_row_mass (a b:I→ℂ)(R:Matrix I I ℂ)(A B K:ℝ)
    (hA:0≤A)(hB:0≤B)(hK:0≤K)(ha:∀i,‖a i‖≤A)(hb:∀i,‖b i‖≤B)
    (hR:∀i,∑j,‖R i j‖≤K) :
    ‖schurBilinear a R b‖≤(Fintype.card I:ℝ)*K*A*B := by
  have hinner (i:I):(∑j,‖R i j‖*‖b j‖)≤K*B:=by
    calc
      _≤∑j,‖R i j‖*B:=Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left (hb j) (norm_nonneg _))
      _=(∑j,‖R i j‖)*B:=(Finset.sum_mul ..).symm
      _≤_:=mul_le_mul_of_nonneg_right (hR i) hB
  calc
    _≤∑i,∑j,‖a i‖*‖R i j‖*‖b j‖:=by
      unfold schurBilinear
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_mul] using norm_sum_le Finset.univ (fun j=>a i*R i j*b j)
    _=∑i,‖a i‖*(∑j,‖R i j‖*‖b j‖):=by simp only [Finset.mul_sum,mul_assoc]
    _≤∑_i:I,A*(K*B):=Finset.sum_le_sum (fun i _=>mul_le_mul (ha i) (hinner i)
      (Finset.sum_nonneg (fun _ _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))) hA)
    _=_:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring

namespace DeficientGraph
variable {V:Type} [Fintype V] {d:ℕ}

theorem attachLeaves_target_change_bound (g:DeficientGraph V d)(hd:3≤d)
    (mate:I→V)(hr:∀v,multiLeafMultiplicity mate v≤g.deficit v)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(B W a b:ℝ)(hzB:‖z‖≤B)(hqnorm:‖q‖≤2)
    (hW:0≤W)(ha:0≤a)(hb:0≤b)
    (hrows:∀l,∑k:I,‖g.extensionGreen q z (mate l) (mate k)‖≤W)
    (x y:V)
    (hx:∀l,‖(g.attachLeaves (by omega) mate hr).extensionGreen q z (.inl x) (.inr l)‖≤a)
    (hy:∀l,‖(g.attachLeaves (by omega) mate hr).extensionGreen q z (.inr l) (.inl y)‖≤b) :
    ‖(g.attachLeaves (by omega) mate hr).extensionGreen q z (.inl x) (.inl y)-g.extensionGreen q z x y‖≤
      (Fintype.card I:ℝ)*(B+2+W)*a*b := by
  let H:=g.attachLeaves (by omega) mate hr
  let G:=H.extensionGreen q z
  let R:=(G.submatrix Sum.inr Sum.inr)⁻¹
  have hR:∀l,∑k:I,‖R l k‖≤B+2+W:=
    g.attachLeaves_inverse_leaf_rows hd mate hr q z hz hq B W hzB hqnorm hW hrows
  have hK:0≤B+2+W:=by linarith [(norm_nonneg z).trans hzB]
  have hs: g.extensionGreen q z x y=G (.inl x) (.inl y)-
      schurBilinear (fun l:I=>G (.inl x) (.inr l)) R (fun l=>G (.inr l) (.inl y)):=
    (g.attachLeaves_Green_leaf_schur hd mate hr q z hz hq).2 x y
  have he:G (.inl x) (.inl y)-g.extensionGreen q z x y=
      schurBilinear (fun l:I=>G (.inl x) (.inr l)) R (fun l=>G (.inr l) (.inl y)):=by
    linear_combination -hs
  change ‖G (.inl x) (.inl y)-g.extensionGreen q z x y‖≤_
  rw [he]
  exact schurBilinear_bound_of_row_mass _ _ R a b (B+2+W) ha hb hK hx hy hR

end DeficientGraph
end LocalLaw
