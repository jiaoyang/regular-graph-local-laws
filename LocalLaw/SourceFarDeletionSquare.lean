import LocalLaw.FarDeletionErrorRate
import LocalLaw.PhysicalTailRadiusLoss

/-! # The actual far-deletion square with its fixed two-edge inset -/

open Filter
noncomputable section
namespace LocalLaw

theorem eventually_far_deletion_square (a b d : ℕ) (β B K C A D : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hβ : 0<β)
    (hK : 0≤K) (hC : 0≤C) (hA : 0≤A) (hD : 0≤D) :
    ∀ᶠ N : ℕ in atTop,∀z:ℂ,0<z.im→‖z‖≤B→
      Real.log (N:ℝ)^b/(N:ℝ)≤z.im→
      modelRadiusLoss a d N≤logarithmicRadius β d N→
      2≤effectiveModelRadius a d N β→
      ∀n:ℝ,0≤n→n≤K*Real.log (N:ℝ)^(2*a)→
        n*C*(A*Real.log (N:ℝ)*physicalTransfer d z^(effectiveModelRadius a d N β-2)+
          D*Real.log (N:ℝ)*graphPaperError a d N (logarithmicRadius β d N) z)^2≤
            Real.log (N:ℝ)^3*graphPaperError a d N (logarithmicRadius β d N) z := by
  let Q:=((|B|+1)*‖(treeEdgeWeight d)⁻¹‖)^4
  have hQ : 0≤Q := by dsimp only [Q]; positivity
  have hM : 0≤(2*C*A^2)*Q := by positivity
  filter_upwards [eventually_effective_tail_counting a d β K ((2*C*A^2)*Q) ha hd hK hM,
    eventually_paperError_small a b d β ha hb hd hβ,
    eventually_log_ge_nat 2,eventually_log_ge_nat ((2*C*D^2)*K)] with N htail herror hlog hlarge
  intro z hz hzB hfloor hroom hr n hn hncap
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let t:=physicalTransfer d z^(effectiveModelRadius a d N β-2)
  have hLp : 0<L := by dsimp only [L];linarith
  have hLone : 1≤L := by dsimp only [L];linarith
  have hε : 0≤ε := by
    have hh:=herror z hz hfloor
    exact graphPaperError_nonnegative a d N _ z (by
      by_contra hh
      have hN:N=0:=by omega
      subst N
      norm_num at hlog) hz.le
  have hcap : L^(4*a)*ε≤1 := by
    have hh:ε≤(L^(4*a))⁻¹ := by
      simpa only [one_div] using herror z hz hfloor
    exact (mul_le_mul_of_nonneg_left hh (pow_nonneg hLp.le _)).trans_eq
      (mul_inv_cancel₀ (ne_of_gt (pow_pos hLp _)))
  have htailInset : (2*C*A^2)*n*t^2≤ε/L^16 := by
    have hzAbs : ‖z‖≤|B| := hzB.trans (le_abs_self B)
    have hloss:=physical_tail_radius_loss d hd z |B| hzAbs (effectiveModelRadius a d N β) 2 hr
    have ht : t^2≤Q*physicalTransfer d z^(2*effectiveModelRadius a d N β) := by
      simpa only [t,←pow_mul,Nat.mul_comm] using hloss
    calc
      _≤(2*C*A^2)*n*(Q*physicalTransfer d z^(2*effectiveModelRadius a d N β)) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _=((2*C*A^2)*Q)*n*physicalTransfer d z^(2*effectiveModelRadius a d N β) := by ring
      _≤ε/L^16 := htail z hz.le hroom n hn hncap
  have hquadratic : (2*C*D^2)*n*L^2*ε≤1 := by
    calc
      _≤(2*C*D^2)*(K*L^(2*a))*L^2*ε := by gcongr
      _=((2*C*D^2)*K)*L^(2*a+2)*ε := by rw [pow_add];ring
      _≤L*L^(2*a+2)*ε := by
        apply mul_le_mul_of_nonneg_right _ hε
        exact mul_le_mul_of_nonneg_right hlarge (pow_nonneg hLp.le _)
      _=L^(2*a+3)*ε := by rw [pow_succ];ring
      _≤L^(4*a)*ε :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hLone (by omega)) hε
      _≤1 := hcap
  exact far_deletion_square_to_prime L ε n C A D t hlog hε hn hC hA hD
    (pow_nonneg (physicalTransfer_pos d hd z).le _) htailInset hquadratic

end LocalLaw
