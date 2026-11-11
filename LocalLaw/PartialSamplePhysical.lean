import LocalLaw.PartialSampleBenchmark
import LocalLaw.PartialVacuumRows
import LocalLaw.TreeBoundaryMass

/-! # The actual physical old-sample benchmark and its uniform bounds -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance partialSamplePhysicalDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem kestenMcKay_vacuum_relation (d : ℕ) (hd : 3≤d) (m z : ℂ)
    (hm : m^2+z*m+1=0) :
    (kestenMcKayTransform d m z)⁻¹=m⁻¹-m*(treeEdgeWeight d)^2 := by
  have hm0 := cavity_root_ne_zero hm
  have hid : m*(-z-m)=1 := by linear_combination -hm
  have hmInv : m⁻¹= -z-m := by
    calc
      m⁻¹=m⁻¹*(m*(-z-m)) := by rw [hid,mul_one]
      _= -z-m := by rw [←mul_assoc,inv_mul_cancel₀ hm0,one_mul]
  have hkcast : ((d-1:ℕ):ℂ)=(d:ℂ)-1 := by
    exact_mod_cast (Nat.cast_sub (R:=ℝ) (by omega : 1≤d))
  have hk0 : (d:ℂ)-1≠0 := by
    rw [←hkcast]
    exact Nat.cast_ne_zero.mpr (by omega)
  unfold kestenMcKayTransform
  rw [inv_inv,hmInv,treeEdgeWeight_sq d hd,hkcast]
  field_simp [hk0]
  ring

theorem physical_edge_cavity_norm_le_one (d : ℕ) (hd : 3≤d) (z : ℂ) :
    ‖treeEdgeWeight d*semicircleRoot z‖≤1 := by
  have hD : (3:ℝ)≤d := Nat.cast_le.mpr hd
  have hαsq := treeEdgeWeight_norm_sq d hd
  have hα : ‖treeEdgeWeight d‖≤1 := by
    have hi : 1/((d:ℝ)-1)≤1 := (div_le_one (by linarith)).mpr (by linarith)
    nlinarith [norm_nonneg (treeEdgeWeight d)]
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (semicircleRoot_norm_le_one z) (norm_nonneg _)).trans (by simpa using hα)

variable {L : Type} [Fintype L] [DecidableEq L]

theorem partialSampleCovariance_row_bound (B C : Set L) (m p α : ℂ) (u:B⊕C) :
    (∑v,‖partialSampleCovariance B C m p α u v‖)≤‖p‖+‖α*m*p‖ := by
  cases u with
  | inl b =>
    rw [Fintype.sum_sum_type]
    change (∑v:B,‖(p•(1:Matrix B B ℂ)) b v‖)+
      (∑v:C,‖partialMatchingCoupling B C (-α*m*p) b v‖)≤_
    have hdiag : (∑v:B,‖(p•(1:Matrix B B ℂ)) b v‖)=‖p‖ := by
      simp [Matrix.smul_apply,Matrix.one_apply,apply_ite norm]
    rw [hdiag]
    have h := partialMatching_row_sum B C (-α*m*p) b
    simpa only [neg_mul,norm_neg] using add_le_add_left h ‖p‖
  | inr c =>
    rw [Fintype.sum_sum_type]
    change (∑v:B,‖(partialMatchingCoupling B C (-α*m*p)).transpose c v‖)+
      (∑v:C,‖(p•(1:Matrix C C ℂ)) c v‖)≤_
    rw [partialMatching_transpose]
    have hdiag : (∑v:C,‖(p•(1:Matrix C C ℂ)) c v‖)=‖p‖ := by
      simp [Matrix.smul_apply,Matrix.one_apply,apply_ite norm]
    rw [hdiag]
    have h := partialMatching_row_sum C B (-α*m*p) c
    simpa only [neg_mul,norm_neg,add_comm] using add_le_add_right h ‖p‖

theorem partialSampleCovariance_column_bound (B C : Set L) (m p α : ℂ) (v:B⊕C) :
    (∑u,‖partialSampleCovariance B C m p α u v‖)≤‖p‖+‖α*m*p‖ := by
  have hsym : (partialSampleCovariance B C m p α).transpose=partialSampleCovariance B C m p α := by
    unfold partialSampleCovariance
    simp only [Matrix.fromBlocks_transpose,Matrix.transpose_smul,Matrix.transpose_one,Matrix.transpose_transpose]
  have heq : (∑u,‖partialSampleCovariance B C m p α u v‖)=
      ∑u,‖partialSampleCovariance B C m p α v u‖ := by
    apply Finset.sum_congr rfl
    intro u _
    exact congrArg norm (congrFun (congrFun hsym v) u)
  rw [heq]
  exact partialSampleCovariance_row_bound B C m p α v

/-- The old physical B/C benchmark inverse and its row and column bounds.
All inverse and scalar nonvanishing facts are derived from the spectral domain. -/
theorem physical_partialSample_benchmark (B C : Set L) (d : ℕ) (hd : 3≤d)
    (z : ℂ) (hz : 0<z.im) :
    let m:=semicircleRoot z
    let p:=kestenMcKayTransform d m z
    let α:=treeEdgeWeight d
    IsUnit (partialSamplePrecision B C m p α) ∧
      (partialSamplePrecision B C m p α)⁻¹=partialSampleCovariance B C m p α ∧
      (∀u,∑v,‖(partialSamplePrecision B C m p α)⁻¹ u v‖≤4) ∧
      (∀v,∑u,‖(partialSamplePrecision B C m p α)⁻¹ u v‖≤4) := by
  dsimp only
  let m:=semicircleRoot z
  let p:=kestenMcKayTransform d m z
  let α:=treeEdgeWeight d
  have hm : m≠0 := semicircleRoot_ne_zero z
  have hp : p≠0 := inv_ne_zero (kestenMcKay_denominator_ne_zero d m z hz (semicircleRoot_im_pos hz).le)
  have hi:=partialSamplePrecision_inverse B C m p α hm hp
    (kestenMcKay_vacuum_relation d hd m z (semicircleRoot_equation z))
  have hpnorm : ‖p‖≤2 := kestenMcKayTransform_norm_le_two d hd z hz
  have ham : ‖α*m‖≤1 := physical_edge_cavity_norm_le_one d hd z
  have hprod : ‖α*m*p‖≤2 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right ham (norm_nonneg p)).trans (by simpa using hpnorm)
  refine ⟨hi.1,hi.2,?_,?_⟩
  · intro u
    rw [hi.2]
    exact (partialSampleCovariance_row_bound B C m p α u).trans (by linarith)
  · intro v
    rw [hi.2]
    exact (partialSampleCovariance_column_bound B C m p α v).trans (by linarith)

end LocalLaw
