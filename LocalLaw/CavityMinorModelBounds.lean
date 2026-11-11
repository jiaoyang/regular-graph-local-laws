import LocalLaw.TruncatedTreeCavity
import LocalLaw.ActualBoundaryRowBudgets
import LocalLaw.SingletonBallModel
import LocalLaw.BoundaryWeightParameters

/-! # Actual neighbor-deleted cavity model profiles and deterministic weights

The model is the literal principal minor of Ext(T,q). Its component class,
diameter, boundary multiplicity and root decay are derived from the old tree
ball. The weights are deterministic functions of that old graph and q.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2600000
namespace LocalLaw
local instance cavityMinorModelBoundsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) cavityMinorModelBoundsComponentMem {A : Type*}
    (G : SimpleGraph A) (c : G.ConnectedComponent) : DecidablePred (fun a => a ∈ c.supp) :=
  fun _ => Classical.propDecidable _
namespace RegularGraph
variable {N d : ℕ}

def truncatedCavityRoot (g : RegularGraph N d) (o : Fin N) (ell : ℕ)
    (j : graphBallVertices g.graph o ell) (hjo : g.graph.Adj j.val o) :
    {v : graphBallVertices g.graph o ell // v ≠ j} :=
  ⟨⟨o, center_mem_graphBall g.graph o ell⟩, fun h => hjo.ne.symm (congrArg Subtype.val h)⟩

def truncatedCavityBoundaryInner (g : RegularGraph N d) (o : Fin N) (ell : ℕ) (hell : 2 ≤ ell)
    (j : graphBallVertices g.graph o ell) (hjo : g.graph.Adj j.val o)
    (a : BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) :
    {v : graphBallVertices g.graph o ell // v ≠ j} :=
  ⟨⟨a.val.1, a.property.2.1⟩, fun he => by
    have hraw := congrArg Subtype.val he
    change a.val.1 = j.val at hraw
    have hdist := ball_boundary_inner_edist g.graph o ell a
    rw [hraw, SimpleGraph.edist_eq_one_iff_adj.mpr hjo.symm] at hdist
    have heq : ell = 1 := by exact_mod_cast hdist.symm
    omega⟩

theorem truncatedMinor_component_budget (g : RegularGraph N d) (o : Fin N) (ell : ℕ)
    (j : graphBallVertices g.graph o ell) (hTree : (graphBall g.graph o ell).IsTree) :
    ((g.deficient.restrict (graphBallVertices g.graph o ell)).deleteVertex j).ComponentFiniteReferenceBudget := by
  let M := g.deficient.restrict (graphBallVertices g.graph o ell)
  have hz : ∀ v, M.deficit v = 0 := fun _ => rfl
  have hb : graphExcess M.graph ≤ finiteOmega d := by
    have he : graphExcess M.graph = 0 := tree_graphExcess_zero M.graph (show M.graph.IsTree from hTree)
    rw [he]
    exact Nat.zero_le _
  exact M.deleteVertex_component_budget j hz
    (M.connected_zero_component_budget hTree.isConnected hz hb)

theorem truncatedMinor_distance_bound (g : RegularGraph N d) (o : Fin N) (ell : ℕ)
    (j : graphBallVertices g.graph o ell) (hTree : (graphBall g.graph o ell).IsTree)
    (x y : {v : graphBallVertices g.graph o ell // v ≠ j}) :
    ((g.deficient.restrict (graphBallVertices g.graph o ell)).deleteVertex j).graph.dist x y ≤
      (finiteOmega d + 1) * (4 * ell + 1) := by
  let M := g.deficient.restrict (graphBallVertices g.graph o ell)
  have hb : graphExcess M.graph ≤ finiteOmega d := by
    have he : graphExcess M.graph = 0 := tree_graphExcess_zero M.graph (show M.graph.IsTree from hTree)
    rw [he]
    exact Nat.zero_le _
  have h := M.deleteVertex_distance_bound hTree.isConnected hb j (2 * ell)
    (graphBall_distance_le_twice_radius g.graph o ell) x y
  convert h using 1
  ring

theorem truncatedCavityBoundaryInner_fiber_bound (g : RegularGraph N d) (o : Fin N)
    (ell : ℕ) (hell : 2 ≤ ell) (j : graphBallVertices g.graph o ell) (hjo : g.graph.Adj j.val o)
    (v : {v : graphBallVertices g.graph o ell // v ≠ j}) :
    Nat.card {a : BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell) //
      g.truncatedCavityBoundaryInner o ell hell j hjo a = v} ≤ d := by
  let T := graphBallVertices g.graph o ell
  let l := g.truncatedCavityBoundaryInner o ell hell j hjo
  let oldl := inducedBoundaryInner g.graph o ell T (Set.Subset.refl _)
  let f : {a // l a = v} → {a // oldl a = v.val} := fun a => ⟨a.val, congrArg Subtype.val a.property⟩
  have hf : Function.Injective f := fun _ _ h => Subtype.ext
    (congrArg (fun a : {a // oldl a = v.val} => a.val) h)
  exact (Nat.card_le_card_of_injective f hf).trans
    (inducedBoundaryInner_fiber_bound g.graph o ell T (Set.Subset.refl _) d (fun v => (g.regular v).le) v.val)

theorem truncatedMinor_root_boundary_bound (g : RegularGraph N d) (hd : 3 ≤ d) (o : Fin N)
    (ell : ℕ) (hell : 2 ≤ ell) (j : graphBallVertices g.graph o ell) (hjo : g.graph.Adj j.val o)
    (hTree : (graphBall g.graph o ell).IsTree) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d * coreConvolutionConstant (finiteOmega d + 1) *
      ((((finiteOmega d + 1) * (4 * ell + 1) : ℕ) : ℝ) + 1) ≤ 1 / 2)
    (a : BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) :
    ‖((g.deficient.restrict (graphBallVertices g.graph o ell)).deleteVertex j).extensionGreen q z
      (g.truncatedCavityRoot o ell j hjo) (g.truncatedCavityBoundaryInner o ell hell j hjo a)‖ ≤
      2 * finiteExtraReferenceConstant d * physicalTransfer d z ^ ell := by
  let M := (g.deficient.restrict (graphBallVertices g.graph o ell)).deleteVertex j
  let root := g.truncatedCavityRoot o ell j hjo
  let leaf := g.truncatedCavityBoundaryInner o ell hell j hjo a
  have ht := (physicalTransfer_pos d hd z).le
  have htone : physicalTransfer d z ≤ 1 := by nlinarith [physicalTransfer_sq_le_half d hd z]
  have hC : 0 ≤ 2 * finiteExtraReferenceConstant d := by linarith [finiteExtraReferenceConstant_ge_one d hd]
  by_cases hr : M.graph.Reachable root leaf
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
    let f : M.graph →g g.graph := ⟨fun v => v.val.val, fun {_ _} h => h⟩
    have hlen := g.graph.edist_le (p.map f)
    change g.graph.edist o a.val.1 ≤ (p.map f).length at hlen
    rw [ball_boundary_inner_edist g.graph o ell a, SimpleGraph.Walk.length_map, hp] at hlen
    have hdist : ell ≤ M.graph.dist root leaf := by exact_mod_cast hlen
    have hk := M.componentwise_finite_kernel_decay hd (g.truncatedMinor_component_budget o ell j hTree) q z hz hq
      ((finiteOmega d + 1) * (4 * ell + 1)) (g.truncatedMinor_distance_bound o ell j hTree) small root leaf
    exact hk.trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht htone hdist) hC)
  · let c := M.graph.connectedComponentMk root
    have hnot : leaf ∉ c.supp := fun h => hr (SimpleGraph.ConnectedComponent.exact h.symm)
    rw [M.extensionGreen_zero_across_cut hd c.supp (M.component_cut c) q z hz hq root rfl leaf hnot, norm_zero]
    positivity

def truncatedCavityWeight (g : RegularGraph N d) (o : Fin N) (ell : ℕ) (hell : 2 ≤ ell)
    (j : graphBallVertices g.graph o ell) (hjo : g.graph.Adj j.val o) (q z : ℂ)
    (a : BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℂ :=
  (((g.deficient.restrict (graphBallVertices g.graph o ell)).deleteVertex j).extensionGreen q z
    (g.truncatedCavityRoot o ell j hjo) (g.truncatedCavityBoundaryInner o ell hell j hjo a)) ^ 2

theorem truncatedCavityWeight_bounds (g : RegularGraph N d) (hd : 3 ≤ d) (o : Fin N)
    (ell : ℕ) (hell : 2 ≤ ell) (j : graphBallVertices g.graph o ell) (hjo : g.graph.Adj j.val o)
    (hTree : (graphBall g.graph o ell).IsTree) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d * coreConvolutionConstant (finiteOmega d + 1) *
      ((((finiteOmega d + 1) * (4 * ell + 1) : ℕ) : ℝ) + 1) ≤ 1 / 2) :
    (∑ a, ‖g.truncatedCavityWeight o ell hell j hjo q z a‖) ≤
      8 * (d : ℝ) * finiteExtraReferenceConstant d ^ 2 *
        ((((finiteOmega d + 1) * (4 * ell + 1) : ℕ) : ℝ) + 1) ∧
    ∀ a, ‖g.truncatedCavityWeight o ell hell j hjo q z a‖ ≤
      4 * finiteExtraReferenceConstant d ^ 2 * ((((d - 1 : ℕ) : ℝ) ^ ell)⁻¹) := by
  let M := (g.deficient.restrict (graphBallVertices g.graph o ell)).deleteVertex j
  let K := M.extensionGreen q z
  let root := g.truncatedCavityRoot o ell j hjo
  let l := g.truncatedCavityBoundaryInner o ell hell j hjo
  let R := (finiteOmega d + 1) * (4 * ell + 1)
  have hsquare := M.componentwise_extensionGreen_square_sum hd (g.truncatedMinor_component_budget o ell j hTree)
    z q hz hq R (g.truncatedMinor_distance_bound o ell j hTree) small root
  have hfiber := g.truncatedCavityBoundaryInner_fiber_bound o ell hell j hjo
  constructor
  · have h := (finite_fiber_nonnegative_sum_bound l d hfiber (fun v => ‖K root v‖ ^ 2)
      (fun _ => sq_nonneg _)).trans (mul_le_mul_of_nonneg_left hsquare (Nat.cast_nonneg d))
    simp only [truncatedCavityWeight, norm_pow]
    convert h using 1
    dsimp only [R]
    ring
  · intro a
    have hroot := g.truncatedMinor_root_boundary_bound hd o ell hell j hjo hTree q z hz hq small a
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hroot 2
    have htail := physical_transfer_two_sided_tail d hd z ell
    have hC : 0 ≤ 4 * finiteExtraReferenceConstant d ^ 2 := by positivity
    calc
      _ = ‖K root (l a)‖ ^ 2 := by simp only [truncatedCavityWeight, norm_pow]; rfl
      _ ≤ (2 * finiteExtraReferenceConstant d * physicalTransfer d z ^ ell) ^ 2 := hsq
      _ = 4 * finiteExtraReferenceConstant d ^ 2 * physicalTransfer d z ^ (2 * ell) := by
        rw [mul_pow, mul_pow, ← pow_mul, Nat.mul_comm ell 2]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htail hC

theorem truncatedCavityWeight_square_sum_bound (g : RegularGraph N d) (hd : 3 ≤ d) (o : Fin N)
    (ell : ℕ) (hell : 2 ≤ ell) (j : graphBallVertices g.graph o ell) (hjo : g.graph.Adj j.val o)
    (hTree : (graphBall g.graph o ell).IsTree) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d * coreConvolutionConstant (finiteOmega d + 1) *
      ((((finiteOmega d + 1) * (4 * ell + 1) : ℕ) : ℝ) + 1) ≤ 1 / 2) :
    (∑ a, ‖g.truncatedCavityWeight o ell hell j hjo q z a‖ ^ 2) ≤
      32 * (d : ℝ) * finiteExtraReferenceConstant d ^ 4 *
        ((((finiteOmega d + 1) * (4 * ell + 1) : ℕ) : ℝ) + 1) * ((((d - 1 : ℕ) : ℝ) ^ ell)⁻¹) := by
  let w := g.truncatedCavityWeight o ell hell j hjo q z
  let C := finiteExtraReferenceConstant d
  let R := (finiteOmega d + 1) * (4 * ell + 1)
  let m := 4 * C ^ 2 * ((((d - 1 : ℕ) : ℝ) ^ ell)⁻¹)
  have hb := g.truncatedCavityWeight_bounds hd o ell hell j hjo hTree q z hz hq small
  have hm : 0 ≤ m := by dsimp only [m]; positivity
  calc
    _ ≤ ∑ a, m * ‖w a‖ := Finset.sum_le_sum (fun a _ => by
      have hmax : ‖w a‖ ≤ m := hb.2 a
      change ‖w a‖ ^ 2 ≤ m * ‖w a‖
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hmax (norm_nonneg (w a)))
    _ = m * ∑ a, ‖w a‖ := (Finset.mul_sum ..).symm
    _ ≤ m * (8 * (d : ℝ) * C ^ 2 * ((R : ℝ) + 1)) := mul_le_mul_of_nonneg_left hb.1 hm
    _ = _ := by dsimp only [m, C, R]; ring

theorem truncatedCavityWeight_log_bounds (g : RegularGraph N d) (hd : 3 ≤ d) (o : Fin N)
    (ell : ℕ) (hell : 2 ≤ ell) (j : graphBallVertices g.graph o ell) (hjo : g.graph.Adj j.val o)
    (hTree : (graphBall g.graph o ell).IsTree) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d * coreConvolutionConstant (finiteOmega d + 1) *
      ((((finiteOmega d + 1) * (4 * ell + 1) : ℕ) : ℝ) + 1) ≤ 1 / 2)
    (A L : ℝ) (hA : 0 ≤ A) (hL : 1 ≤ L)
    (hRlog : ((((finiteOmega d + 1) * (4 * ell + 1) : ℕ) : ℝ) + 1) ≤ A * L) :
    (∑ a, ‖g.truncatedCavityWeight o ell hell j hjo q z a‖) ≤
      (8 * (d : ℝ) * finiteExtraReferenceConstant d ^ 2 * A) * L ∧
    Real.sqrt (∑ a, ‖g.truncatedCavityWeight o ell hell j hjo q z a‖ ^ 2) ≤
      (32 * (d : ℝ) * finiteExtraReferenceConstant d ^ 4 * A + 1) * L / resamplingDecayDenominator d ell ∧
    ∀ a, ‖g.truncatedCavityWeight o ell hell j hjo q z a‖ ≤
      4 * finiteExtraReferenceConstant d ^ 2 / resamplingDecayDenominator d ell := by
  have hb := g.truncatedCavityWeight_bounds hd o ell hell j hjo hTree q z hz hq small
  have hsq := g.truncatedCavityWeight_square_sum_bound hd o ell hell j hjo hTree q z hz hq small
  let D := resamplingDecayDenominator d ell
  let R := (finiteOmega d + 1) * (4 * ell + 1)
  have hD : 0 < D := resamplingDecayDenominator_pos d ell hd
  have hDsq : D ^ 2 = (((d - 1 : ℕ) : ℝ) ^ ell) := Real.sq_sqrt (by positivity)
  have hD1 : 1 ≤ D := Real.one_le_sqrt.mpr (one_le_pow₀ (by exact_mod_cast (show 1 ≤ d - 1 by omega)))
  constructor
  · apply hb.1.trans
    have h := mul_le_mul_of_nonneg_left hRlog (show 0 ≤ 8 * (d : ℝ) * finiteExtraReferenceConstant d ^ 2 by positivity)
    convert h using 1
    ring
  constructor
  · apply square_root_weight_log_bound _ (32 * (d : ℝ) * finiteExtraReferenceConstant d ^ 4) A L D R
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity) hA hL hD hRlog
    simpa only [hDsq, div_eq_mul_inv] using hsq
  · intro a
    apply (hb.2 a).trans
    rw [← hDsq]
    change (4 * finiteExtraReferenceConstant d ^ 2) / D ^ 2 ≤ (4 * finiteExtraReferenceConstant d ^ 2) / D
    exact div_le_div_of_nonneg_left (by positivity) hD (by nlinarith)

theorem truncatedMinor_max_budgets (g : RegularGraph N d) (hd : 3 ≤ d) (o : Fin N)
    (ell : ℕ) (hell : 2 ≤ ell) (j : graphBallVertices g.graph o ell) (hjo : g.graph.Adj j.val o)
    (hTree : (graphBall g.graph o ell).IsTree) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d * coreConvolutionConstant (finiteOmega d + 1) *
      ((((finiteOmega d + 1) * (4 * ell + 1) : ℕ) : ℝ) + 1) ≤ 1 / 2) :
    let P := ((g.deficient.restrict (graphBallVertices g.graph o ell)).deleteVertex j).extensionGreen q z
    let root := g.truncatedCavityRoot o ell j hjo
    let l := g.truncatedCavityBoundaryInner o ell hell j hjo
    let n := (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ)
    let M := 2 * finiteExtraReferenceConstant d * physicalTransfer d z ^ ell
    let W := 8 * (d : ℝ) * finiteExtraReferenceConstant d ^ 2 *
      ((((finiteOmega d + 1) * (4 * ell + 1) : ℕ) : ℝ) + 1)
    (∀ a, ‖P root (l a)‖ ≤ M) ∧ (∀ v, ∑ a, ‖P (l a) v‖ ≤ Real.sqrt (n * W)) ∧
      (Real.sqrt (n * W)) ^ 2 = n * W ∧ M * Real.sqrt n ≤ 2 * finiteExtraReferenceConstant d * ((d : ℝ) + 1) := by
  dsimp only
  let model := (g.deficient.restrict (graphBallVertices g.graph o ell)).deleteVertex j
  let P := model.extensionGreen q z
  let root := g.truncatedCavityRoot o ell j hjo
  let l := g.truncatedCavityBoundaryInner o ell hell j hjo
  let n := (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ)
  let C := finiteExtraReferenceConstant d
  let R := (finiteOmega d + 1) * (4 * ell + 1)
  let M := 2 * C * physicalTransfer d z ^ ell
  let W := 8 * (d : ℝ) * C ^ 2 * ((R : ℝ) + 1)
  have hC : 0 ≤ C := by dsimp only [C]; linarith [finiteExtraReferenceConstant_ge_one d hd]
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have ht : 0 ≤ physicalTransfer d z := (physicalTransfer_pos d hd z).le
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hsquare (v) : (∑ u, ‖P u v‖ ^ 2) ≤ 8 * C ^ 2 * ((R : ℝ) + 1) := by
    have h := model.componentwise_extensionGreen_square_sum hd (g.truncatedMinor_component_budget o ell j hTree)
      z q hz hq R (g.truncatedMinor_distance_bound o ell j hTree) small v
    calc
      _ = ∑ u, ‖P v u‖ ^ 2 := Finset.sum_congr rfl (fun u _ => by
        change ‖model.extensionGreen q z u v‖ ^ 2 = ‖model.extensionGreen q z v u‖ ^ 2
        rw [(model.extensionGreen_isSymm q z).apply])
      _ ≤ _ := h
  have hcol (v) : (∑ a, ‖P (l a) v‖) ^ 2 ≤ n * W := by
    have hf := (finite_fiber_nonnegative_sum_bound l d
      (g.truncatedCavityBoundaryInner_fiber_bound o ell hell j hjo) (fun u => ‖P u v‖ ^ 2)
      (fun _ => sq_nonneg _)).trans (mul_le_mul_of_nonneg_left (hsquare v) (Nat.cast_nonneg d))
    have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)))
      (fun a => ‖P (l a) v‖) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hc
    have hcard : (Fintype.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ) = n := by
      simp only [n, Nat.card_eq_fintype_card]
    rw [hcard] at hc
    exact hc.trans ((mul_le_mul_of_nonneg_right hf hn).trans_eq (by dsimp only [W]; ring))
  refine ⟨g.truncatedMinor_root_boundary_bound hd o ell hell j hjo hTree q z hz hq small, ?_,
    Real.sq_sqrt (mul_nonneg hn hW), ?_⟩
  · intro v
    have hh := Real.sq_sqrt (mul_nonneg hn hW)
    have hs : 0 ≤ ∑ a, ‖P (l a) v‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    nlinarith only [hh, hcol v, Real.sqrt_nonneg (n * W), hs]
  · have hk : 0 < ((d - 1 : ℕ) : ℝ) ^ ell := pow_pos (Nat.cast_pos.mpr (by omega)) _
    have hc : n ≤ (d : ℝ) * ((d : ℝ) + 1) * (((d - 1 : ℕ) : ℝ) ^ ell) := by
      dsimp only [n]
      exact_mod_cast g.boundary_card_sharp o ell hd
    have htprod : physicalTransfer d z ^ (2 * ell) * n ≤ (d : ℝ) * ((d : ℝ) + 1) := by
      apply (mul_le_mul (physical_transfer_two_sided_tail d hd z ell) hc hn (inv_nonneg.mpr hk.le)).trans_eq
      calc
        _ = ((d : ℝ) * ((d : ℝ) + 1)) * (((((d - 1 : ℕ) : ℝ) ^ ell)⁻¹) * (((d - 1 : ℕ) : ℝ) ^ ell)) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hk.ne', mul_one]
    have hs : (M * Real.sqrt n) ^ 2 ≤ (2 * C * ((d : ℝ) + 1)) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left htprod (show 0 ≤ 4 * C ^ 2 by positivity)
      have he : physicalTransfer d z ^ (2 * ell) = (physicalTransfer d z ^ ell) ^ 2 := by rw [Nat.mul_comm 2 ell, pow_mul]
      rw [he] at h
      rw [mul_pow, Real.sq_sqrt hn]
      dsimp only [M]
      nlinarith [sq_nonneg C]
    have hr : 0 ≤ 2 * C * ((d : ℝ) + 1) := by positivity
    have hl : 0 ≤ M * Real.sqrt n := mul_nonneg hM (Real.sqrt_nonneg n)
    change M * Real.sqrt n ≤ 2 * C * ((d : ℝ) + 1)
    nlinarith only [hs, hr, hl]

end RegularGraph
end LocalLaw
