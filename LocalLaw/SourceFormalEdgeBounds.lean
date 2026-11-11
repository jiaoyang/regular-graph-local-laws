import LocalLaw.SourceFormalKernelBounds

/-! # The old formal cavity and edge parameters have bounded norm -/
open Filter
noncomputable section
namespace LocalLaw

theorem eventually_source_formal_edge_bounds (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in atTop,∀ z q : ℂ,0<z.im → ‖z‖≤B →
      Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) →
      ‖q‖≤2 ∧ ‖treeEdgeWeight d*q‖≤1 := by
  filter_upwards [eventually_source_formal_kernel_bounds a b d c β B C1 1 ha hb hd hc hβ hβc hC1 (by norm_num),
    eventually_log_ge_nat 2] with N hbase hlog
  intro z q hz hzB hfloor hprior
  have hs:‖q‖^2≤2 := (hbase z q hz hzB hfloor hprior).2.2.2.2 2 (by simpa only [one_mul,Nat.cast_ofNat] using hlog)
  have hαsq:=treeEdgeWeight_norm_sq d hd
  have hD:(3:ℝ)≤d := Nat.cast_le.mpr hd
  have hα:‖treeEdgeWeight d‖^2≤1/2 := by
    rw [hαsq]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hprod:=mul_le_mul hα hs (sq_nonneg ‖q‖) (by norm_num : (0:ℝ)≤1/2)
  have hprod':‖treeEdgeWeight d*q‖^2≤1 := by
    rw [norm_mul,mul_pow]
    nlinarith only [hprod]
  constructor <;> nlinarith [norm_nonneg q,norm_nonneg (treeEdgeWeight d*q)]

namespace RegularGraph
theorem eventually_source_Q_edge_bounds (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z:ℂ)(rModel R ell ω Cq badCount:ℕ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      g.SourceOmegaPlusWithRadii a rModel (logarithmicRadius β d N) R ell ω Cq badCount C1 o z →
      ‖g.Q z‖≤2 ∧ ‖treeEdgeWeight d*g.Q z‖≤1 := by
  filter_upwards [eventually_source_formal_edge_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1] with N hN
  intro g o z rModel R ell ω Cq badCount hz hzB hfloor hplus
  exact hN z (g.Q z) hz hzB hfloor hplus.cavity
end RegularGraph
end LocalLaw
