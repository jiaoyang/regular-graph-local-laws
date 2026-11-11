import LocalLaw.SourceFormalKernelInverse
import LocalLaw.SourceFormalEdgeBounds

/-! # A fixed inverse bound for the formal full-tree diagonal -/

open Filter
noncomputable section
namespace LocalLaw

theorem formal_vacuum_inverse_norm_bound (d:ℕ) (hd:3≤d) (q p:ℂ) (B:ℝ)
    (hrel:p⁻¹=q⁻¹-q*treeEdgeWeight d^2) (hq:‖q‖≤2) (hqinv:‖q⁻¹‖≤2*(B+1)) :
    ‖p⁻¹‖≤2*(B+1)+1 := by
  have hD:(3:ℝ)≤d:=Nat.cast_le.mpr hd
  have hα:‖treeEdgeWeight d‖^2≤1/2:=by
    rw [treeEdgeWeight_norm_sq d hd]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hprod:=mul_le_mul hq hα (sq_nonneg ‖treeEdgeWeight d‖) (by norm_num:(0:ℝ)≤2)
  have hterm:‖q*treeEdgeWeight d^2‖≤1:=by
    rw [norm_mul,norm_pow]
    nlinarith only [hprod]
  rw [hrel]
  exact (norm_sub_le _ _).trans (add_le_add hqinv hterm)

theorem eventually_source_formal_diagonal_bounds (a b d:ℕ) (c β B C1:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hβ:0<β) (hβc:β≤c/32) (hC1:1≤C1) :
    ∀ᶠ N:ℕ in atTop,∀z q:ℂ,0<z.im→‖z‖≤B→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z)→
      let p:=rationalTreeReference (d-1) q
      q≠0∧p≠0∧‖q‖≤2∧‖p‖≤4∧‖treeEdgeWeight d*q‖≤1∧‖p⁻¹‖≤2*|B|+3 := by
  filter_upwards [eventually_source_formal_kernel_bounds a b d c β B C1 0 ha hb hd hc hβ hβc hC1 (by norm_num),
    eventually_source_formal_edge_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_formal_kernel_inverse_bound a b d c β B C1 ha hb hd hc hβ hβc hC1]
    with N hformal hedge hinv
  intro z q hz hzB hfloor hprior
  dsimp only
  have hf:=hformal z q hz hzB hfloor hprior
  have he:=hedge z q hz hzB hfloor hprior
  have hi:=hinv z q hz hzB hfloor hprior
  refine ⟨hf.1,hf.2.1,he.1,hf.2.2.1,he.2,?_⟩
  have hh:=formal_vacuum_inverse_norm_bound d hd q (rationalTreeReference (d-1) q) B
    hf.2.2.2.1 he.1 hi.2
  exact hh.trans (by linarith [le_abs_self B])

end LocalLaw
