import LocalLaw.DeficitLocalization

/-! # Exterior deficit localization with independent target radii -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance deficitLocalizationAsymmetricDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem clearOutsideDeficit_localization_bound_asymmetric (g : DeficientGraph V d) (hd : 3 ≤ d)
    (hG : g.graph.Connected) (hbudget : g.FiniteReferenceBudget) (S : Set V)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ i j, g.graph.dist i j ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2)
    (i j : V) (ri rj : ℕ)
    (hfar : ∀ v ∉ S, ri ≤ g.graph.dist i v ∧ rj ≤ g.graph.dist v j) :
    ‖g.extensionGreen q z i j - (g.clearOutsideDeficit S).extensionGreen q z i j‖ ≤
      4 * finiteExtraReferenceConstant d ^ 2 * ‖q‖ *
        (((finiteOmega d : ℝ) + 1) / ((d : ℝ) - 1)) * physicalTransfer d z ^ (ri+rj) := by
  let g' := g.clearOutsideDeficit S
  let t := physicalTransfer d z
  let K : V → V → ℝ := fun a b => t ^ g.graph.dist a b
  let w := g.exteriorDeficitCharge S
  let C := finiteExtraReferenceConstant d
  have hC : 0 ≤ C := le_trans (by norm_num) (finiteExtraReferenceConstant_ge_one d hd)
  have ht : 0 ≤ t := (physicalTransfer_pos d hd z).le
  have htone : t ≤ 1 := by have hh := physicalTransfer_sq_le_half d hd z; change t ^ 2 ≤ 1 / 2 at hh; nlinarith
  have hw : ∀ v, 0 ≤ w v := g.exteriorDeficitCharge_nonnegative hd S
  have hconv : (∑ v, w v * K i v * K v j) ≤
      (((finiteOmega d : ℝ) + 1) / ((d : ℝ) - 1)) * t ^ (ri+rj) := by
    calc
      _ ≤ ∑ v, w v * (t ^ ri * t ^ rj) := by
        apply Finset.sum_le_sum
        intro v _
        by_cases hv : v ∈ S
        · simp only [w, exteriorDeficitCharge, if_pos hv, zero_mul, le_refl]
        · have ha := pow_le_pow_of_le_one ht htone (hfar v hv).1
          have hb := pow_le_pow_of_le_one ht htone (hfar v hv).2
          have hh' := mul_le_mul_of_nonneg_left
            (mul_le_mul ha hb (pow_nonneg ht _) (pow_nonneg ht _)) (hw v)
          convert hh' using 1; ring
      _ = (∑ v, w v) * t ^ (ri+rj) := by
        rw [← Finset.sum_mul,←pow_add]
      _ ≤ _ := mul_le_mul_of_nonneg_right (g.exteriorDeficitCharge_sum_bound hd S hbudget) (pow_nonneg ht _)
  have hP : ∀ a b, ‖g.extensionGreen q z a b‖ ≤ (2 * C) * K a b :=
    g.finite_class_kernel_bound hd hG hbudget z q hz hq R hR small
  have hQ : ∀ a b, ‖g'.extensionGreen q z a b‖ ≤ (2 * C) * K a b :=
    g'.finite_class_kernel_bound hd hG (g.clearOutsideDeficit_budget S hbudget) z q hz hq R hR small
  have hprod := diagonal_kernel_product_bound (g.extensionGreen q z) (g'.extensionGreen q z) w K K
    (2 * C) (2 * C) hw (fun a b => pow_nonneg ht _) (by positivity) (by positivity)
    hP hQ i j _ hconv
  have hid := matrix_inverse_difference (g.extensionMatrix q z) (g'.extensionMatrix q z)
    (g.extensionMatrix_isUnit hd q z hz hq) (g'.extensionMatrix_isUnit hd q z hz hq)
  rw [g.clearOutsideDeficit_extensionMatrix_difference S q z, Matrix.mul_smul, Matrix.smul_mul] at hid
  have hentry := congrArg (fun M : Matrix V V ℂ => M i j) hid
  change g.extensionGreen q z i j - g'.extensionGreen q z i j =
    (-q) * (g.extensionGreen q z * Matrix.diagonal (fun v => (w v : ℂ)) * g'.extensionGreen q z) i j at hentry
  rw [hentry, norm_mul, norm_neg]
  exact (mul_le_mul_of_nonneg_left hprod (norm_nonneg q)).trans_eq (by dsimp [C, t]; ring)



theorem clearOutsideDeficit_balls_localization_bound (g : DeficientGraph V d) (hd : 3≤d)
    (hG : g.graph.Connected) (hbudget : g.FiniteReferenceBudget) (S : Set V)
    (z q : ℂ) (hz : 0<z.im) (hq : 0 ≤ q.im)
    (R : ℕ) (hR : ∀ i j,g.graph.dist i j≤R)
    (small : ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2)
    (i j : V) (ri rj : ℕ)
    (hI : graphBallVertices g.graph i ri⊆S) (hJ : graphBallVertices g.graph j rj⊆S) :
    ‖g.extensionGreen q z i j-(g.clearOutsideDeficit S).extensionGreen q z i j‖≤
      4*finiteExtraReferenceConstant d^2*‖q‖*
        (((finiteOmega d:ℝ)+1)/((d:ℝ)-1))*physicalTransfer d z^(ri+rj) := by
  apply g.clearOutsideDeficit_localization_bound_asymmetric hd hG hbudget S z q hz hq R hR small i j ri rj
  intro v hv
  have hfar (a : V) (r : ℕ) (ha : graphBallVertices g.graph a r⊆S) : r≤g.graph.dist a v := by
    by_contra hr
    obtain ⟨p,hp⟩:=hG.exists_walk_length_eq_dist a v
    have hlen:p.length≤r := by omega
    exact hv (ha ((SimpleGraph.edist_le p).trans (ENat.coe_le_coe.mpr hlen)))
  exact ⟨hfar i ri hI,by simpa only [SimpleGraph.dist_comm] using hfar j rj hJ⟩

end DeficientGraph
end LocalLaw
