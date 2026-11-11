import SpectralConsequences.SortedHermitianSpectrum
import LocalLaw.ExteriorResolvent
import LocalLaw.FullRetainedPrecision

/-! # The actual regular-graph spectral box and the single distinguished pole

Every sorted eigenvalue lies in the degree row-sum box. The constant vector
supplies the largest eigenvalue d/sqrt(d-1), without a connectivity assumption.
Other occurrences of that eigenvalue retain their own indices.
-/
open scoped BigOperators
open Matrix
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceSpectralBoxDecidable (p:Prop):Decidable p:=Classical.propDecidable p

 def regularSpectralRadius (d:ℕ):ℝ := (d:ℝ)/Real.sqrt ((d:ℝ)-1)

theorem algebraMap_sub_eq_neg_spectralMatrix {V:Type} [Fintype V] [DecidableEq V]
    (H:Matrix V V ℂ) (x:ℝ) :
    algebraMap ℝ (Matrix V V ℂ) x-H = -spectralMatrix H (x:ℂ) := by
  ext i j
  by_cases hij:i=j
  · subst j
    simp [Matrix.algebraMap_matrix_apply,spectralMatrix]
  · simp [Matrix.algebraMap_matrix_apply,spectralMatrix,hij]

theorem sortedEigenvalues_abs_le_row_sum {N:ℕ} (H:Matrix (Fin N) (Fin N) ℂ)
    (hH:H.IsHermitian) (M:ℝ) (hrows:∀i,∑j,‖H i j‖≤M) (i:Fin N) :
    |sortedEigenvalues hH i|≤M := by
  by_contra hbad
  have hgap:M<‖(sortedEigenvalues hH i:ℂ)‖:=by
    simpa only[Complex.norm_real,Real.norm_eq_abs] using lt_of_not_ge hbad
  have hu:=spectralMatrix_isUnit_of_row_gap H (sortedEigenvalues hH i:ℂ) M hrows hgap
  have hs:sortedEigenvalues hH i∈spectrum ℝ H:=
    hH.eigenvalues_mem_spectrum_real (sortedEigenvaluePermutation hH i)
  apply (spectrum.mem_iff.mp hs)
  rw [algebraMap_sub_eq_neg_spectralMatrix]
  exact hu.neg

namespace RegularGraph
variable {N d:ℕ}

theorem sorted_eigenvalues_box (g:LocalLaw.RegularGraph N d) (i:Fin N) :
    |sortedEigenvalues g.H_hermitian i|≤regularSpectralRadius d := by
  apply sortedEigenvalues_abs_le_row_sum g.H g.H_hermitian
  intro v
  rw [LocalLaw.RegularGraph.H,normalizedAdjacency_row_sum,g.regular v]
  rfl

theorem constant_eigenvalue_mem_spectrum (g:LocalLaw.RegularGraph N d) (hN:0<N) :
    regularSpectralRadius d∈spectrum ℝ g.H := by
  rw [spectrum.mem_iff,algebraMap_sub_eq_neg_spectralMatrix,IsUnit.neg_iff]
  intro hu
  let H:=spectralMatrix g.H (regularSpectralRadius d:ℂ)
  have hker:H *ᵥ (fun _ : Fin N => (1:ℂ))=0:=by
    ext i
    change (∑j,spectralMatrix g.H (regularSpectralRadius d:ℂ) i j*(1:ℂ))=0
    simp only[spectralMatrix,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,mul_one,
      Finset.sum_sub_distrib]
    have hrow:=normalizedAdjacency_complex_row_sum g.graph d i
    rw [g.regular i] at hrow
    change (∑j,g.H i j)=treeEdgeWeight d*(d:ℂ) at hrow
    rw [hrow]
    simp only[Matrix.one_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    dsimp only[regularSpectralRadius,treeEdgeWeight]
    push_cast
    ring
  have hinv:H⁻¹*H=1:=Matrix.nonsing_inv_mul H ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  have hh:=congrArg (fun A:Matrix (Fin N) (Fin N) ℂ=>A *ᵥ (fun _=>1)) hinv
  change (H⁻¹*H) *ᵥ (fun _:Fin N=>1)=(1:Matrix (Fin N) (Fin N) ℂ) *ᵥ (fun _=>1) at hh
  rw [←Matrix.mulVec_mulVec,hker,Matrix.mulVec_zero,Matrix.one_mulVec] at hh
  have h01:=congrFun hh ⟨0,hN⟩
  norm_num at h01

theorem sorted_top_eigenvalue (g:LocalLaw.RegularGraph N d) (hN:0<N) :
    sortedEigenvalues g.H_hermitian ⟨0,hN⟩=regularSpectralRadius d := by
  have hs:=constant_eigenvalue_mem_spectrum g hN
  rw [g.H_hermitian.eigenvalues_eq_spectrum_real] at hs
  obtain ⟨j,hj⟩:=hs
  let i:Fin N:=(sortedEigenvaluePermutation g.H_hermitian).symm j
  have hi:sortedEigenvalues g.H_hermitian i=regularSpectralRadius d:=by
    simpa only[sortedEigenvalues,i,Equiv.apply_symm_apply] using hj
  apply le_antisymm
  · exact (le_abs_self _).trans (sorted_eigenvalues_box g ⟨0,hN⟩)
  · rw [←hi]
    have h0i : (⟨0,hN⟩:Fin N) ≤ i := by
      change 0 ≤ i.val
      omega
    exact sortedEigenvalues_antitone g.H_hermitian h0i

end RegularGraph
end SpectralConsequences
