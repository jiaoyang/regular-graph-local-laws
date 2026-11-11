import Mathlib

/-! # The genuine bounded adjacency operator on square-summable graph functions

No finiteness of the vertex set is assumed. A uniform finite degree bound
gives the actual continuous linear operator on ell2, starting from finite
neighbor sums and an explicit Schur bound.
-/

open scoped BigOperators ENNReal Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
namespace LocalLaw
local instance boundedGraphOperatorDecidable (p : Prop) : Decidable p := Classical.propDecidable p

abbrev GraphL2 (V : Type*) := lp (fun _ : V => ℂ) 2

end LocalLaw
open LocalLaw
namespace SimpleGraph
local instance boundedGraphOperatorRootDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

def adjacencyFunction (f : V → ℂ) (v : V) : ℂ := ∑ w ∈ G.neighborFinset v,f w

theorem finite_neighbor_sum_bound (D : ℕ) (hD : ∀ v,G.degree v≤D)
    (a : V → ℝ) (ha : ∀ v,0≤a v) (S : Finset V) :
    ∑ v ∈ S,∑ w ∈ G.neighborFinset v,a w≤(D:ℝ)*∑ w ∈ S.biUnion (fun v => G.neighborFinset v),a w := by
  let U := S.biUnion (fun v => G.neighborFinset v)
  have hrow (v : V) (hv : v∈S) :
      (∑ w ∈ G.neighborFinset v,a w)=∑ w ∈ U,if G.Adj v w then a w else 0 := by
    have hset : U.filter (G.Adj v)=G.neighborFinset v := by
      ext w
      simp only [Finset.mem_filter,SimpleGraph.mem_neighborFinset]
      exact ⟨fun h => h.2,fun h => ⟨Finset.mem_biUnion.mpr ⟨v,hv,(G.mem_neighborFinset v w).mpr h⟩,h⟩⟩
    rw [←hset,Finset.sum_filter]
  calc
    _ = ∑ v ∈ S,∑ w ∈ U,if G.Adj v w then a w else 0 := Finset.sum_congr rfl hrow
    _ = ∑ w ∈ U,∑ v ∈ S,if G.Adj v w then a w else 0 := Finset.sum_comm
    _ = ∑ w ∈ U,((S.filter (fun v => G.Adj v w)).card:ℝ)*a w := by
      apply Finset.sum_congr rfl
      intro w _
      rw [←Finset.sum_filter]
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ ∑ w ∈ U,(D:ℝ)*a w := by
      apply Finset.sum_le_sum
      intro w _
      have hsubset : S.filter (fun v => G.Adj v w)⊆G.neighborFinset w := by
        intro v hv
        exact (G.mem_neighborFinset w v).mpr (G.symm (Finset.mem_filter.mp hv).2)
      have hcard : (S.filter (fun v => G.Adj v w)).card≤D :=
        (Finset.card_le_card hsubset).trans (hD w)
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (ha w)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem adjacencyFunction_finite_square_bound (D : ℕ) (hD : ∀ v,G.degree v≤D)
    (f : GraphL2 V) (S : Finset V) :
    ∑ v ∈ S,‖G.adjacencyFunction f v‖^2≤(D:ℝ)^2*‖f‖^2 := by
  have hrow (v : V) : ‖G.adjacencyFunction f v‖^2≤(D:ℝ)*∑ w ∈ G.neighborFinset v,‖f w‖^2 := by
    calc
      _ ≤ (∑ w ∈ G.neighborFinset v,‖f w‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ ((G.neighborFinset v).card:ℝ)*∑ w ∈ G.neighborFinset v,‖f w‖^2 :=
        sq_sum_le_card_mul_sum_sq
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hD v))
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have htail : (∑ w ∈ S.biUnion (fun v => G.neighborFinset v),‖f w‖^2)≤‖f‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.sum_rpow_le_norm_rpow
      (by norm_num : 0<(2:ℝ≥0∞).toReal) f (S.biUnion (fun v => G.neighborFinset v))
  calc
    _ ≤ ∑ v ∈ S,(D:ℝ)*∑ w ∈ G.neighborFinset v,‖f w‖^2 := Finset.sum_le_sum (fun v _ => hrow v)
    _ = (D:ℝ)*(∑ v ∈ S,∑ w ∈ G.neighborFinset v,‖f w‖^2) := (Finset.mul_sum _ _ _).symm
    _ ≤ (D:ℝ)*((D:ℝ)*∑ w ∈ S.biUnion (fun v => G.neighborFinset v),‖f w‖^2) :=
      mul_le_mul_of_nonneg_left (G.finite_neighbor_sum_bound D hD (fun w => ‖f w‖^2) (fun _ => sq_nonneg _) S)
        (Nat.cast_nonneg _)
    _ ≤ (D:ℝ)*((D:ℝ)*‖f‖^2) := by gcongr
    _ = _ := by ring

def adjacencyLp (D : ℕ) (hD : ∀ v,G.degree v≤D) (f : GraphL2 V) : GraphL2 V :=
  ⟨G.adjacencyFunction f,memℓp_gen' (C:=(D:ℝ)^2*‖f‖^2) (fun S => by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using G.adjacencyFunction_finite_square_bound D hD f S)⟩

theorem adjacencyLp_norm_bound (D : ℕ) (hD : ∀ v,G.degree v≤D) (f : GraphL2 V) :
    ‖G.adjacencyLp D hD f‖≤(D:ℝ)*‖f‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num : 0<(2:ℝ≥0∞).toReal) (by positivity)
  intro S
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,mul_pow] using G.adjacencyFunction_finite_square_bound D hD f S

def boundedAdjacency (D : ℕ) (hD : ∀ v,G.degree v≤D) : GraphL2 V →L[ℂ] GraphL2 V :=
  LinearMap.mkContinuous
    { toFun := G.adjacencyLp D hD
      map_add' := by
        intro f g
        apply Subtype.ext
        funext v
        simp only [adjacencyLp,adjacencyFunction,lp.coeFn_add,Pi.add_apply,Finset.sum_add_distrib]
      map_smul' := by
        intro c f
        apply Subtype.ext
        funext v
        simp only [adjacencyLp,adjacencyFunction,lp.coeFn_smul,Pi.smul_apply,Finset.smul_sum,RingHom.id_apply] }
    D (G.adjacencyLp_norm_bound D hD)

theorem boundedAdjacency_apply (D : ℕ) (hD : ∀ v,G.degree v≤D) (f : GraphL2 V) (v : V) :
    G.boundedAdjacency D hD f v=∑ w ∈ G.neighborFinset v,f w := rfl

theorem boundedAdjacency_single (D : ℕ) (hD : ∀ v,G.degree v≤D) (v w : V) (a : ℂ) :
    G.boundedAdjacency D hD (lp.single 2 w a) v=if G.Adj v w then a else 0 := by
  simp [boundedAdjacency_apply,lp.single_apply,SimpleGraph.mem_neighborFinset]

theorem boundedAdjacency_selfAdjoint (D : ℕ) (hD : ∀ v,G.degree v≤D) :
    IsSelfAdjoint (G.boundedAdjacency D hD) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff'.mpr
  apply lp.ext_continuousLinearMap (by norm_num : (2:ℝ≥0∞)≠⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro a
  apply lp.ext
  funext v
  change ((G.boundedAdjacency D hD).adjoint (lp.single 2 w a)) v=
    G.boundedAdjacency D hD (lp.single 2 w a) v
  have hh := (G.boundedAdjacency D hD).adjoint_inner_right (lp.single 2 v (1:ℂ)) (lp.single 2 w a)
  simp only [lp.inner_single_left,lp.inner_single_right,G.boundedAdjacency_single] at hh
  by_cases hadj : G.Adj v w
  · have hadj' : G.Adj w v := G.symm hadj
    simpa only [hadj',if_true,RCLike.inner_apply,map_one,mul_one,boundedAdjacency_single,hadj] using hh
  · have hadj' : ¬G.Adj w v := fun h => hadj (G.symm h)
    simpa only [hadj',if_false,inner_zero_left,RCLike.inner_apply,map_one,map_zero,mul_one,mul_zero,boundedAdjacency_single,hadj] using hh

def normalizedOperator (d : ℕ) (hD : ∀ v,G.degree v≤d) : GraphL2 V →L[ℂ] GraphL2 V :=
  (Real.sqrt ((d:ℝ)-1))⁻¹ • G.boundedAdjacency d hD

theorem normalizedOperator_selfAdjoint (d : ℕ) (hD : ∀ v,G.degree v≤d) :
    IsSelfAdjoint (G.normalizedOperator d hD) :=
  (IsSelfAdjoint.all ((Real.sqrt ((d:ℝ)-1))⁻¹)).smul (G.boundedAdjacency_selfAdjoint d hD)

def graphSpectralOperator (d : ℕ) (hD : ∀ v,G.degree v≤d) (z : ℂ) : GraphL2 V →L[ℂ] GraphL2 V :=
  G.normalizedOperator d hD-z • 1

theorem graphSpectralOperator_isUnit (d : ℕ) (hD : ∀ v,G.degree v≤d) (z : ℂ) (hz : z.im≠0) :
    IsUnit (G.graphSpectralOperator d hD z) := by
  have hnot : z∉spectrum ℂ (G.normalizedOperator d hD) := by
    intro h
    exact hz ((G.normalizedOperator_selfAdjoint d hD).im_eq_zero_of_mem_spectrum h)
  have hu := spectrum.not_mem_iff.mp hnot
  have hneg := hu.neg
  simpa only [Algebra.algebraMap_eq_smul_one,neg_sub] using hneg

def infiniteGreenOperator (d : ℕ) (hD : ∀ v,G.degree v≤d) (z : ℂ) : GraphL2 V →L[ℂ] GraphL2 V :=
  Ring.inverse (G.graphSpectralOperator d hD z)

def infiniteGreen (d : ℕ) (hD : ∀ v,G.degree v≤d) (z : ℂ) (i j : V) : ℂ :=
  G.infiniteGreenOperator d hD z (lp.single 2 j 1) i

theorem infiniteGreenOperator_left_inverse (d : ℕ) (hD : ∀ v,G.degree v≤d) (z : ℂ) (hz : z.im≠0) :
    G.infiniteGreenOperator d hD z*G.graphSpectralOperator d hD z=1 :=
  Ring.inverse_mul_cancel _ (G.graphSpectralOperator_isUnit d hD z hz)

theorem infiniteGreenOperator_right_inverse (d : ℕ) (hD : ∀ v,G.degree v≤d) (z : ℂ) (hz : z.im≠0) :
    G.graphSpectralOperator d hD z*G.infiniteGreenOperator d hD z=1 :=
  Ring.mul_inverse_cancel _ (G.graphSpectralOperator_isUnit d hD z hz)

end SimpleGraph
