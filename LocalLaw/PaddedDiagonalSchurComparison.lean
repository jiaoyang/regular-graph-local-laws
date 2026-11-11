import LocalLaw.ScalarLeafPaddingStability

/-! # Two Schur corrections with different retained leaf sets

Both retained blocks are padded onto the literal common leaf index.
Invertibility, inverse stability, target corrections and L1 weights are
transported by proved identities, including omitted-leaf cases.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance paddedDiagonalSchurComparisonDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {I:Type} [Fintype I] [DecidableEq I]

theorem two_padded_leaf_schur_target_bound (E F:Set I) (x y p:ℂ)
    (a b:E→ℂ) (a' b':F→ℂ) (R:Matrix E E ℂ) (S:Matrix F F ℂ)
    (hp:p≠0) (hRunit:IsUnit R) (hSunit:IsUnit S)
    (δtarget δleaf A B A' B':ℝ) (hδleaf:0≤δleaf)
    (hA:0≤A) (hB:0≤B) (hA':0≤A') (hB':0≤B') (hxy:‖x-y‖≤δtarget)
    (ha:(∑i,‖a i‖)≤A) (hb:(∑i,‖b i‖)≤B)
    (ha':(∑i,‖a' i‖)≤A') (hb':(∑i,‖b' i‖)≤B')
    (hR:∀i j:E,‖R i j-(if i=j then p else 0)‖≤δleaf)
    (hS:∀i j:F,‖S i j-(if i=j then p else 0)‖≤δleaf)
    (hsmallE:(Fintype.card E:ℝ)*‖p⁻¹‖*δleaf≤1/2)
    (hsmallF:(Fintype.card F:ℝ)*‖p⁻¹‖*δleaf≤1/2) :
    ‖(x-schurBilinear a R⁻¹ b)-(y-schurBilinear a' S⁻¹ b')‖≤
      δtarget+‖p⁻¹‖*(∑i:I,‖scalarLeafPaddedVector E a i*scalarLeafPaddedVector E b i-
        scalarLeafPaddedVector F a' i*scalarLeafPaddedVector F b' i‖)+
        (2*‖p⁻¹‖^2*δleaf)*(A*B+A'*B') := by
  have hpa:(∑i:I,‖scalarLeafPaddedVector E a i‖)≤A:=by
    rw [scalarLeafPaddedVector_sum_norm]
    exact ha
  have hpb:(∑i:I,‖scalarLeafPaddedVector E b i‖)≤B:=by
    rw [scalarLeafPaddedVector_sum_norm]
    exact hb
  have hpa':(∑i:I,‖scalarLeafPaddedVector F a' i‖)≤A':=by
    rw [scalarLeafPaddedVector_sum_norm]
    exact ha'
  have hpb':(∑i:I,‖scalarLeafPaddedVector F b' i‖)≤B':=by
    rw [scalarLeafPaddedVector_sum_norm]
    exact hb'
  have hr:=scalarLeafPadding_inverse_stability E R p hRunit hp δleaf hδleaf hR hsmallE
  have hs:=scalarLeafPadding_inverse_stability F S p hSunit hp δleaf hδleaf hS hsmallF
  have hh:=two_diagonal_schur_target_bound x y p
    (scalarLeafPaddedVector E a) (scalarLeafPaddedVector E b)
    (scalarLeafPaddedVector F a') (scalarLeafPaddedVector F b')
    (scalarLeafPadding E R p) (scalarLeafPadding F S p)
    δtarget (2*‖p⁻¹‖^2*δleaf) A B A' B' (by positivity) hA hB hA' hB' hxy hpa hpb hpa' hpb' hr hs
  rw [scalarLeafPadding_inverse_bilinear E R p hRunit hp a b,
    scalarLeafPadding_inverse_bilinear F S p hSunit hp a' b'] at hh
  exact hh

end LocalLaw
