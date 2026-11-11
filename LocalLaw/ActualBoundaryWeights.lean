import LocalLaw.BoundaryDepthAndIncidence

/-!
# Actual source Green-product boundary weights

The genuine embedded finite model supplies all weight estimates. Exact
boundary depth yields the root decay; actual incidence fibers and the
componentwise squared-row estimate give the L1 and squared-L2 budgets used
by local resampling concentration.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance actualBoundaryWeightsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

def boundaryProductWeight (g : DeficientGraph V d) (S : Set V) (o : V) (ell : ℕ)
    (hS : graphBallVertices g.graph o ell ⊆ S) (q z : ℂ) (i : S)
    (a : BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℂ :=
  (g.restrict S).extensionGreen q z ⟨o, hS (center_mem_graphBall g.graph o ell)⟩
      (inducedBoundaryInner g.graph o ell S hS a) *
    (g.restrict S).extensionGreen q z i (inducedBoundaryInner g.graph o ell S hS a)

theorem boundaryProductWeight_bounds (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (hbudget : (g.restrict S).ComponentFiniteReferenceBudget)
    (o : V) (ell : ℕ) (hS : graphBallVertices g.graph o ell ⊆ S)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (R : ℕ)
    (hR : ∀ a b, (g.restrict S).graph.dist a b ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2) (i : S) :
    (∑ a, ‖g.boundaryProductWeight S o ell hS q z i a‖) ≤
        8 * (d : ℝ) * finiteExtraReferenceConstant d ^ 2 * ((R : ℝ) + 1) ∧
      (∑ a, ‖g.boundaryProductWeight S o ell hS q z i a‖ ^ 2) ≤
        32 * (d : ℝ) * finiteExtraReferenceConstant d ^ 4 * ((R : ℝ) + 1) *
          physicalTransfer d z ^ (2 * ell) ∧
      ∀ a, ‖g.boundaryProductWeight S o ell hS q z i a‖ ≤
        4 * finiteExtraReferenceConstant d ^ 2 * physicalTransfer d z ^ ell := by
  let model := g.restrict S
  let K := model.extensionGreen q z
  let root : S := ⟨o, hS (center_mem_graphBall g.graph o ell)⟩
  let l := inducedBoundaryInner g.graph o ell S hS
  let C := 2 * finiteExtraReferenceConstant d
  let M := C * physicalTransfer d z ^ ell
  let W := 8 * finiteExtraReferenceConstant d ^ 2 * ((R : ℝ) + 1)
  have hC : 0 ≤ C := by dsimp only [C]; linarith [finiteExtraReferenceConstant_ge_one d hd]
  have ht : 0 ≤ physicalTransfer d z := (physicalTransfer_pos d hd z).le
  have htone : physicalTransfer d z ≤ 1 := by nlinarith [physicalTransfer_sq_le_half d hd z]
  have hM : 0 ≤ M := mul_nonneg hC (pow_nonneg ht ell)
  have hfiber : ∀ v : S, Nat.card {a // l a = v} ≤ d :=
    inducedBoundaryInner_fiber_bound g.graph o ell S hS d g.degree_le
  have hsquare (v : S) : (∑ y, ‖K v y‖ ^ 2) ≤ W :=
    model.componentwise_extensionGreen_square_sum hd hbudget z q hz hq R hR small v
  have hroot : ∀ a, ‖K root (l a)‖ ≤ M := by
    intro a
    have hh := model.componentwise_finite_kernel_decay hd hbudget q z hz hq R hR small root (l a)
    have heq : model.graph.dist root (l a) = ell := induced_boundary_inner_distance g.graph o ell S hS a
    change ‖K root (l a)‖ ≤ C * physicalTransfer d z ^ model.graph.dist root (l a) at hh
    rwa [heq] at hh
  have hrow : ∀ a, ‖K i (l a)‖ ≤ C := by
    intro a
    have hh := model.componentwise_finite_kernel_decay hd hbudget q z hz hq R hR small i (l a)
    exact hh.trans (mul_le_of_le_one_right hC (pow_le_one₀ ht htone))
  constructor
  · have hh := product_weight_l1_bound l d hfiber K root i W (hsquare root) (hsquare i)
    convert hh using 1
    dsimp only [W]
    ring
  constructor
  · have hh := product_weight_l2_bound l d hfiber K root i M W hM hroot (hsquare i)
    convert hh using 1
    dsimp only [M, C, W]
    rw [mul_pow, ← pow_mul, Nat.mul_comm ell 2]
    ring
  · intro a
    have hh := product_weight_max_bound l K root i M C hM hroot hrow a
    convert hh using 1
    dsimp only [M, C]
    ring

end DeficientGraph
end LocalLaw
