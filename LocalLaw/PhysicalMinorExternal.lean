import LocalLaw.PhysicalMinorSurgery

/-!
# Good sampled tip to an arbitrary external target

Delete the sample's own first vertex. Old correlations control the remaining
surgery, and the two proved new cross entries yield a quadratic restoration
term. No old augmented reference class is used.
-/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance physicalMinorExternalDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V]

private theorem external_triple_norm_bound (x y t : ℂ) (X Y T : ℝ)
    (hX : 0≤X) (hY : 0≤Y) (hx : ‖x‖≤X) (hy : ‖y‖≤Y) (ht : ‖t‖≤T) :
    ‖x*y*t‖≤X*Y*T := by
  rw [norm_mul,norm_mul]
  exact mul_le_mul (mul_le_mul hx hy (norm_nonneg _) hX) ht (norm_nonneg _) (mul_nonneg hX hY)

/-- Physical external-tip comparison through the genuine principal minors. -/
theorem physical_principal_minor_external_bound (H K : Matrix V V ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) (z : ℂ) (hz : 0<z.im)
    (b : V) (c j : {v:V // v≠b}) (e : I↪{v:V // v≠b})
    (hsupport : ∀ x y, x∉Set.range e ∨ y∉Set.range e →
      (deletedMatrix K b-deletedMatrix H b) x y=0)
    (C L φ w δ : ℝ) (hC : 0≤C) (hL : 0≤L) (hφ : 0≤φ) (hw : 0≤w)
    (hδ : 0≤δ) (hδC : δ≤C)
    (hOldNear : ‖green H z c.val b‖≤C) (hOldPivot : ‖(green H z b b)⁻¹‖≤L)
    (hOldC : ∀ u, ‖green H z c.val (e u).val‖≤φ)
    (hOldB : ∀ u, ‖green H z b (e u).val‖≤φ)
    (hOldTargetC : ‖green H z c.val j.val‖≤φ)
    (hOldTargetB : ‖green H z b j.val‖≤φ)
    (hNewJ : ∀ u, ‖green K z (e u).val j.val‖≤C)
    (hNewB : ∀ u, ‖green K z (e u).val b‖≤C)
    (hNewPivot : ‖(green K z b b)⁻¹‖≤L)
    (hNewCB : ‖green K z c.val b‖≤δ) (hNewBJ : ‖green K z b j.val‖≤δ)
    (hW : ∀ u, ∑ v, ‖(deletedMatrix K b-deletedMatrix H b) (e u) (e v)‖≤w) :
    ‖green K z c.val j.val‖≤(1+C*L)*φ+
      (Fintype.card I:ℝ)*((1+C*L)*φ)*w*(C+C^2*L)+δ^2*L := by
  have hOld (u:I) : ‖green (deletedMatrix H b) z c (e u)‖≤(1+C*L)*φ := by
    rw [green_deleted_vertex H hH z hz b c (e u)]
    have hp := external_triple_norm_bound _ _ _ C φ L hC hφ hOldNear (hOldB u) hOldPivot
    exact ((norm_sub_le _ _).trans (add_le_add (hOldC u)
      (by simpa only [div_eq_mul_inv] using hp))).trans_eq (by ring)
  have hOldTarget : ‖green (deletedMatrix H b) z c j‖≤(1+C*L)*φ := by
    rw [green_deleted_vertex H hH z hz b c j]
    have hp := external_triple_norm_bound _ _ _ C φ L hC hφ hOldNear hOldTargetB hOldPivot
    exact ((norm_sub_le _ _).trans (add_le_add hOldTargetC
      (by simpa only [div_eq_mul_inv] using hp))).trans_eq (by ring)
  have hNew (u:I) : ‖green (deletedMatrix K b) z (e u) j‖≤C+C^2*L := by
    rw [green_deleted_vertex K hK z hz b (e u) j]
    have hp := external_triple_norm_bound _ _ _ C C L hC hC (hNewB u) (hNewBJ.trans hδC) hNewPivot
    exact ((norm_sub_le _ _).trans (add_le_add (hNewJ u)
      (by simpa only [div_eq_mul_inv] using hp))).trans_eq (by ring)
  have hminor := green_supported_entry_bound (deletedMatrix H b) (deletedMatrix K b)
    (deletedMatrix_isHermitian H hH b) (deletedMatrix_isHermitian K hK b) e hsupport z hz
    ((1+C*L)*φ) (C+C^2*L) w (by positivity) (by positivity) hw c j hOld hNew hW
  have hnewMinor : ‖green (deletedMatrix K b) z c j‖≤(1+C*L)*φ+
      (Fintype.card I:ℝ)*((1+C*L)*φ)*w*(C+C^2*L) := by
    have hh := norm_sub_le_norm_sub_add_norm_sub (green (deletedMatrix K b) z c j)
      (green (deletedMatrix H b) z c j) 0
    simp only [sub_zero] at hh
    exact (hh.trans (add_le_add (by simpa only [norm_sub_rev] using hminor) hOldTarget)).trans_eq (by ring)
  have hid : green K z c.val j.val=green (deletedMatrix K b) z c j+
      green K z c.val b*green K z b j.val*(green K z b b)⁻¹ := by
    rw [green_deleted_vertex K hK z hz b c j,div_eq_mul_inv]
    ring
  rw [hid]
  have hp := external_triple_norm_bound _ _ _ δ δ L hδ hδ hNewCB hNewBJ hNewPivot
  exact ((norm_add_le _ _).trans (add_le_add hnewMinor hp)).trans_eq (by ring)

end LocalLaw
