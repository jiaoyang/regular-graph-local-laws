import LocalLaw.ActualBoundaryWeights
import LocalLaw.SharpBallCounting

/-!
# Actual model row inputs for the finite maximum bootstrap

Kernel decay, sharp boundary counting and genuine squared Green rows derive
the root/count cancellation and every boundary-column L1 budget.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance actualBoundaryRowBudgetsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}

theorem boundary_model_max_budgets (g : RegularGraph N d) (hd : 3≤d)
    (S : Set (Fin N)) (hbudget : (g.deficient.restrict S).ComponentFiniteReferenceBudget)
    (o : Fin N) (ell : ℕ) (hS : graphBallVertices g.graph o ell ⊆ S)
    (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) (R : ℕ)
    (hR : ∀ u v, (g.deficient.restrict S).graph.dist u v≤R)
    (small : ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2) :
    let K := (g.deficient.restrict S).extensionGreen q z
    let root : S := ⟨o,hS (center_mem_graphBall g.graph o ell)⟩
    let l := inducedBoundaryInner g.graph o ell S hS
    let n := (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)):ℝ)
    let M := 2*finiteExtraReferenceConstant d*physicalTransfer d z^ell
    let W := 8*(d:ℝ)*finiteExtraReferenceConstant d^2*((R:ℝ)+1)
    (∀ a, ‖K root (l a)‖≤M) ∧
      (∀ j, ∑ a, ‖K (l a) j‖≤Real.sqrt (n*W)) ∧
      (Real.sqrt (n*W))^2=n*W ∧
      M*Real.sqrt n≤2*finiteExtraReferenceConstant d*((d:ℝ)+1) := by
  dsimp only
  let model := g.deficient.restrict S
  let K := model.extensionGreen q z
  let root : S := ⟨o,hS (center_mem_graphBall g.graph o ell)⟩
  let l := inducedBoundaryInner g.graph o ell S hS
  let n := (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)):ℝ)
  let C := finiteExtraReferenceConstant d
  let t := physicalTransfer d z
  let M := 2*C*t^ell
  let W := 8*(d:ℝ)*C^2*((R:ℝ)+1)
  have hC : 0≤C := (by norm_num : (0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have ht : 0≤t := (physicalTransfer_pos d hd z).le
  have hn : 0≤n := Nat.cast_nonneg _
  have hM : 0≤M := by dsimp only [M]; positivity
  have hW : 0≤W := by dsimp only [W]; positivity
  have hroot (a : BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ‖K root (l a)‖≤M := by
    have hh := model.componentwise_finite_kernel_decay hd hbudget q z hz hq R hR small root (l a)
    have heq : model.graph.dist root (l a)=ell := induced_boundary_inner_distance g.graph o ell S hS a
    change ‖K root (l a)‖≤2*C*t^model.graph.dist root (l a) at hh
    rwa [heq] at hh
  have hSq (j : S) : (∑ v, ‖K v j‖^2)≤8*C^2*((R:ℝ)+1) := by
    have hh := model.componentwise_extensionGreen_square_sum hd hbudget z q hz hq R hR small j
    calc
      _ = ∑ v, ‖K j v‖^2 := Finset.sum_congr rfl (fun v _ => by
        change ‖model.extensionGreen q z v j‖^2 = ‖model.extensionGreen q z j v‖^2
        rw [(model.extensionGreen_isSymm q z).apply])
      _ ≤ _ := hh
  have hrow (j : S) : (∑ a, ‖K (l a) j‖)^2≤n*W := by
    have hfiber := inducedBoundaryInner_fiber_bound g.graph o ell S hS d (fun v => (g.regular v).le)
    have hb := (finite_fiber_nonnegative_sum_bound l d hfiber (fun v => ‖K v j‖^2) (fun _ => sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hSq j) (Nat.cast_nonneg d))
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)))
      (fun a => ‖K (l a) j‖) (fun _ => (1:ℝ))
    simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hcs
    have hncard : (Fintype.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)):ℝ)=n := by
      simp only [n,Nat.card_eq_fintype_card]
    rw [hncard] at hcs
    exact hcs.trans ((mul_le_mul_of_nonneg_right hb hn).trans_eq (by dsimp only [W]; ring))
  refine ⟨hroot,?_,Real.sq_sqrt (mul_nonneg hn hW),?_⟩
  · intro j
    have hs := Real.sq_sqrt (mul_nonneg hn hW)
    have hsum : 0≤∑ a, ‖K (l a) j‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    nlinarith only [hs,hrow j,Real.sqrt_nonneg (n*W),hsum]
  · have hk : 0<((d-1:ℕ):ℝ)^ell := pow_pos (Nat.cast_pos.mpr (by omega)) _
    have hcount : n≤(d:ℝ)*((d:ℝ)+1)*(((d-1:ℕ):ℝ)^ell) := by
      dsimp only [n]
      exact_mod_cast g.boundary_card_sharp o ell hd
    have htail := physical_transfer_two_sided_tail d hd z ell
    have hprod : t^(2*ell)*n≤(d:ℝ)*((d:ℝ)+1) := by
      apply (mul_le_mul htail hcount hn (inv_nonneg.mpr hk.le)).trans_eq
      calc
        _ = ((d:ℝ)*((d:ℝ)+1))*(((((d-1:ℕ):ℝ)^ell)⁻¹)*(((d-1:ℕ):ℝ)^ell)) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hk.ne',mul_one]
    have hs : (M*Real.sqrt n)^2≤(2*C*((d:ℝ)+1))^2 := by
      have hh := mul_le_mul_of_nonneg_left hprod (show 0≤4*C^2 by positivity)
      have hp : t^(2*ell)=(t^ell)^2 := by rw [Nat.mul_comm 2 ell,pow_mul]
      rw [hp] at hh
      rw [mul_pow,Real.sq_sqrt hn]
      dsimp only [M]
      nlinarith [sq_nonneg C]
    have hright : 0≤2*C*((d:ℝ)+1) := by positivity
    have hleft : 0≤M*Real.sqrt n := mul_nonneg hM (Real.sqrt_nonneg n)
    change M*Real.sqrt n ≤ 2*C*((d:ℝ)+1)
    nlinarith only [hs,hright,hleft]

end RegularGraph
end LocalLaw
