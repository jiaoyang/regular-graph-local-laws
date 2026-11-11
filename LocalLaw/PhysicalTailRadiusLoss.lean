import LocalLaw.EffectiveTailCounting

/-! # A fixed loss of target radius costs only a fixed physical tail factor -/

noncomputable section
namespace LocalLaw

theorem physicalTransfer_inverse_bound (d:ℕ)(hd:3≤d)(z:ℂ)(B:ℝ)(hzB:‖z‖≤B) :
    (physicalTransfer d z)⁻¹≤(B+1)*‖(treeEdgeWeight d)⁻¹‖ := by
  let m:=semicircleRoot z
  have hm:m≠0:=semicircleRoot_ne_zero z
  have hmi:m⁻¹= -z-m:=by
    apply mul_left_cancel₀ hm
    rw [mul_inv_cancel₀ hm]
    have hh:=semicircleRoot_equation z
    dsimp only [m]
    linear_combination hh
  have hmn:‖m⁻¹‖≤B+1:=by
    rw [hmi]
    exact (norm_sub_le (-z) m).trans (by simpa only [norm_neg] using add_le_add hzB (semicircleRoot_norm_le_one z))
  have he:(physicalTransfer d z)⁻¹=‖m⁻¹‖*‖(treeEdgeWeight d)⁻¹‖:=by
    simp only [physicalTransfer,norm_mul,norm_neg,mul_inv_rev,norm_inv,m]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right hmn (norm_nonneg _)

theorem physical_tail_radius_loss (d:ℕ)(hd:3≤d)(z:ℂ)(B:ℝ)(hzB:‖z‖≤B)
    (r loss:ℕ)(hloss:loss≤r) :
    physicalTransfer d z^(2*(r-loss))≤
      ((B+1)*‖(treeEdgeWeight d)⁻¹‖)^(2*loss)*physicalTransfer d z^(2*r) := by
  let ρ:=physicalTransfer d z
  have hρ:0<ρ:=physicalTransfer_pos d hd z
  have hk:ρ⁻¹≤(B+1)*‖(treeEdgeWeight d)⁻¹‖:=physicalTransfer_inverse_bound d hd z B hzB
  have he:2*(r-loss)=2*r-2*loss:=Nat.mul_sub_left_distrib 2 r loss
  rw [he,pow_sub₀ ρ (ne_of_gt hρ) (Nat.mul_le_mul_left 2 hloss),←inv_pow]
  have hp:ρ⁻¹^(2*loss)≤((B+1)*‖(treeEdgeWeight d)⁻¹‖)^(2*loss):=
    pow_le_pow_left₀ (inv_nonneg.mpr hρ.le) hk _
  exact (mul_le_mul_of_nonneg_left hp (pow_nonneg hρ.le _)).trans_eq (mul_comm _ _)

end LocalLaw
