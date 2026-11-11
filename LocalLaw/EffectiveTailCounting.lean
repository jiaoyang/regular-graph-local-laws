import LocalLaw.EffectiveModelRadius

/-! # The internal localization tail absorbs every actual leaf count

The radius loss still leaves four-a logarithmic powers in the nominal
error. A two-a power count therefore retains a sixteenth-power gain.
-/

open Filter
noncomputable section
namespace LocalLaw

theorem eventually_effective_tail_counting (a d : ℕ) (β K M : ℝ)
    (ha : 12≤a) (hd : 3≤d) (hK : 0≤K) (hM : 0≤M) :
    ∀ᶠ N : ℕ in atTop,∀ z : ℂ,0 ≤ z.im →
      modelRadiusLoss a d N≤logarithmicRadius β d N →
      ∀ n : ℝ,0≤n → n≤K*Real.log (N:ℝ)^(2*a) →
      M*n*physicalTransfer d z^(2*effectiveModelRadius a d N β)≤
        graphPaperError a d N (logarithmicRadius β d N) z/Real.log (N:ℝ)^16 := by
  let k : ℝ:=((d-1:ℕ):ℝ)
  filter_upwards [eventually_log_ge_nat 1,eventually_log_ge_nat (M*K*k^4),eventually_ge_atTop 1]
    with N hlog hlarge hN
  intro z hz hroom n hn hncap
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  let t:=physicalTransfer d z^(2*effectiveModelRadius a d N β)
  have hLp : 0<L := by dsimp only [L]; linarith
  have hε : 0≤ε := graphPaperError_nonnegative a d N _ z hN hz
  have ht : 0≤t := pow_nonneg (physicalTransfer_pos d hd z).le _
  have htail : L^(4*a)*t≤k^4*ε := by
    have hh:=effectiveModelRadius_localization_tail a d N β hd hlog hroom z hz
    have he:=(le_div_iff₀ (pow_pos hLp (4*a))).mp hh
    dsimp only [L,t,ε,k] at *
    nlinarith only [he]
  apply (le_div_iff₀ (pow_pos hLp 16)).mpr
  apply (mul_le_mul_right (pow_pos hLp (4*a))).mp
  calc
    _=(M*n*L^16)*(L^(4*a)*t) := by ring
    _≤(M*(K*L^(2*a))*L^16)*(k^4*ε) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hncap hM) (pow_nonneg hLp.le 16)
      · exact htail
      · positivity
      · positivity
    _=(M*K*k^4)*L^(2*a+16)*ε := by rw [pow_add]; ring
    _≤L*L^(2*a+16)*ε := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hlarge (pow_nonneg hLp.le _)) hε
    _=L^(2*a+17)*ε := by rw [show 2*a+17=(2*a+16)+1 by omega,pow_succ]; ring
    _≤L^(4*a)*ε := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hlog (by omega)) hε
    _=ε*L^(4*a) := mul_comm _ _

end LocalLaw
