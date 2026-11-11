import SpectralConsequences.PaperTheorem14

/-! # Literal all-eigenvectors formulation with complex eigenvalue parameter

Hermitian reality is proved for every nonzero eigenvector. The zero vector
is handled separately, so the public homogeneous statement quantifies all
complex eigenvalues and all complex vectors without a normalization premise.
-/
open scoped BigOperators
open Matrix
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem hermitian_eigenvalue_eq_real {V:Type*} [Fintype V] [DecidableEq V]
    (H:Matrix V V ℂ)(hH:H.IsHermitian)(eig:ℂ)(v:V→ℂ)(hv:v≠0)
    (heig:H *ᵥ v=eig • v): (eig.re:ℂ)=eig:=by
  let w:EuclideanSpace ℂ V:=(WithLp.equiv 2 (V→ℂ)).symm v
  have hw:w≠0:=by
    intro hzero
    apply hv
    have hh:=congrArg (WithLp.equiv 2 (V→ℂ)) hzero
    simpa only [w,Equiv.apply_symm_apply,map_zero] using hh
  have he:H.toEuclideanLin w=eig • w:=by
    dsimp only [w]
    rw [Matrix.toEuclideanLin_piLp_equiv_symm]
    change (WithLp.equiv 2 (V→ℂ)).symm (H *ᵥ v)=eig • (WithLp.equiv 2 (V→ℂ)).symm v
    rw [heig,WithLp.equiv_symm_smul]
  have heigen:Module.End.HasEigenvalue H.toEuclideanLin eig:=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr he,hw⟩
  exact Complex.conj_eq_iff_re.mp ((Matrix.isHermitian_iff_isSymmetric.mp hH).conj_eigenvalue_eq_self heigen)

/-- Every vector in every complex eigenspace, with the actual homogeneous
supremum/Euclidean norm bound of Theorem 1.4. -/
def PaperAllEigenvectors {N d:ℕ}(g:RegularGraph N d):Prop:=
  ∀eig:ℂ,∀v:Fin N→ℂ,g.H *ᵥ v=eig • v→
    ‖v‖≤Real.log (N:ℝ)^151/Real.sqrt (N:ℝ)*Real.sqrt (∑j,‖v j‖^2)

theorem paperAllEigenvectors_iff_paperDelocalized {N d:ℕ}(g:RegularGraph N d):
    PaperAllEigenvectors g↔PaperDelocalized g:=by
  constructor
  · intro h eig v heig
    exact h (eig:ℂ) v heig
  · intro h eig v heig
    by_cases hv:v=0
    · simp only [hv,norm_zero,Pi.zero_apply,norm_zero,zero_pow (by norm_num:2≠0),
        Finset.sum_const_zero,Real.sqrt_zero,mul_zero,le_refl]
    · have he:=hermitian_eigenvalue_eq_real g.H g.H_hermitian eig v hv heig
      exact h eig.re v (by simpa only [he] using heig)

/-- The original conditional paper probability statement with the unrestricted
complex eigenvalue/all-vector conclusion. -/
theorem paper_theorem_1_4_all_eigenvectors (d ω:ℕ)(c:ℝ)
    (hd:3≤d)(hω:1≤ω)(hωmax:ω≤finiteOmega d)(hc:0<c)(hc1:c<1):
    ∀C:ℝ,∀ᶠ N:ℕ in Filter.atTop,Nonempty (RegularGraph N d)→
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        RegularGraph.structural (logarithmicRadius (c/4) d N) ω ⌊(N:ℝ)^c⌋₊ g∧¬PaperAllEigenvectors g)/
      eventMass (RegularGraph.weight (N:=N) (d:=d))
        (RegularGraph.structural (logarithmicRadius (c/4) d N) ω ⌊(N:ℝ)^c⌋₊)≤1/(N:ℝ)^C:=by
  simpa only [paperAllEigenvectors_iff_paperDelocalized] using paper_theorem_1_4 d ω c hd hω hωmax hc hc1

end SpectralConsequences
