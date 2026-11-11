import LocalLaw.BoundedGraphOperator

/-! # Contractive finite-coordinate projections and actual ell2 exhaustion -/

open scoped BigOperators ENNReal Topology
open Filter
noncomputable section
namespace LocalLaw
local instance l2FiniteProjectionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [DecidableEq V]

def l2FiniteProjectionFunction (S : Finset V) (f : GraphL2 V) : GraphL2 V := ∑ i ∈ S,lp.single 2 i (f i)

theorem l2FiniteProjection_norm (S : Finset V) (f : GraphL2 V) : ‖l2FiniteProjectionFunction S f‖≤‖f‖ := by
  have hid : ‖l2FiniteProjectionFunction S f‖^2=∑ i ∈ S,‖f i‖^2 := by
    simpa only [l2FiniteProjectionFunction,ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.norm_sum_single (by norm_num : 0<(2:ℝ≥0∞).toReal) (f : V → ℂ) S
  have hsum : (∑ i ∈ S,‖f i‖^2)≤‖f‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.sum_rpow_le_norm_rpow (by norm_num : 0<(2:ℝ≥0∞).toReal) f S
  nlinarith only [hid,hsum,norm_nonneg (l2FiniteProjectionFunction S f),norm_nonneg f]

def l2FiniteProjection (S : Finset V) : GraphL2 V →L[ℂ] GraphL2 V :=
  LinearMap.mkContinuous
    { toFun := l2FiniteProjectionFunction S
      map_add' := by
        intro f g
        simp only [l2FiniteProjectionFunction,lp.coeFn_add,Pi.add_apply,lp.single_add,Finset.sum_add_distrib]
      map_smul' := by
        intro c f
        simp only [l2FiniteProjectionFunction,lp.coeFn_smul,Pi.smul_apply,lp.single_smul,Finset.smul_sum,RingHom.id_apply] }
    1 (fun f => (l2FiniteProjection_norm S f).trans_eq (one_mul _).symm)

theorem l2FiniteProjection_apply (S : Finset V) (f : GraphL2 V) (v : V) :
    l2FiniteProjection S f v=if v∈S then f v else 0 := by
  change (∑ i ∈ S,lp.single 2 i (f i)) v=_
  simp [lp.coeFn_sum,lp.single_apply,eq_comm]

theorem l2FiniteProjection_norm_le (S : Finset V) (f : GraphL2 V) : ‖l2FiniteProjection S f‖≤‖f‖ :=
  l2FiniteProjection_norm S f

theorem l2FiniteProjection_tendsto (S : ℕ → Finset V) (hmono : Monotone S) (hcover : ∀ v,∃ n,v∈S n)
    (f : GraphL2 V) : Tendsto (fun n => l2FiniteProjection (S n) f) atTop (𝓝 f) :=
  (lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) f).comp (hmono.tendsto_atTop_finset hcover)

end LocalLaw
