import LocalLaw.CoreBranchDistance
import LocalLaw.TreeKernelConvolution
import LocalLaw.RadialKernelSum
import LocalLaw.CoreBoundaryCounting

/-!
# Boundary kernel products reduced to the actual spanning core

Outside components have their actual unique attachment and cavity deficit.
Tree boundary mass and the exact branch-distance identity therefore control
their contribution without assuming a convolution or attachment estimate.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw

local instance coreConvolutionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The genuine unique boundary edge identifies the exact pointwise deletion
deficit, rather than only its sum. -/
theorem cutDeficit_of_unique_boundary (G : SimpleGraph V) (C : Set V)
    (A : CutComponent G C) (hcount : cutMultiplicity G C A = 1)
    (e : CutBoundaryEdge G C A) (v : A.supp) :
    cutDeficit G C A v = if v = cutAttachmentRoot G C A e then 1 else 0 := by
  letI : Subsingleton (CutBoundaryEdge G C A) := (Nat.card_eq_one_iff_unique.mp hcount).1
  let E := {u : C // G.Adj u.val v.val.val}
  let F : E → CutBoundaryEdge G C A := fun u =>
    ⟨⟨(u.val.val, v.val.val), u.property, u.val.property, v.val.property⟩, v.property⟩
  by_cases hv : v = cutAttachmentRoot G C A e
  · rw [if_pos hv]
    letI : Nonempty E := ⟨⟨⟨e.val.val.1, e.val.property.2.1⟩,
      by simpa only [hv, cutAttachmentRoot] using e.val.property.1⟩⟩
    letI : Subsingleton E := ⟨fun a b => by
      have h := congrArg (fun f : CutBoundaryEdge G C A => f.val.val.1)
        (Subsingleton.elim (F a) (F b))
      exact Subtype.ext (Subtype.ext h)⟩
    exact Nat.card_unique
  · rw [if_neg hv]
    letI : IsEmpty E := ⟨fun u => by
      apply hv
      have h := congrArg (fun f : CutBoundaryEdge G C A => f.val.val.2)
        (Subsingleton.elim (F u) e)
      exact Subtype.ext (Subtype.ext h)⟩
    change Nat.card E = 0
    simp

/-- Exact physical degree partition into the component degree and lost
core-neighbor degree. Canonical cardinalities avoid enumeration choices. -/
theorem cut_degree_balance (G : SimpleGraph V) (C : Set V) (A : CutComponent G C)
    (v : A.supp) :
    G.degree v.val.val = cutDeficit G C A v + (cutComponentGraph G C A).degree v := by
  have hδ := cutDeficit_degree_loss G C A v
  have hcomp := cutComponent_degree_eq G C A v
  have hind := induced_degree_le G {x | x ∉ C} v.val
  simp only [outsideGraph, SimpleGraph.degree, SimpleGraph.neighborFinset,
    Set.toFinset_card, ← Nat.card_eq_fintype_card] at hδ hcomp hind ⊢
  omega

/-- The actual graph boundary coefficient on a singly attached component is
exactly its physical cavity-tree boundary coefficient. -/
theorem unique_component_boundaryCoefficient (G : SimpleGraph V) (C : Set V)
    (A : CutComponent G C) (hcount : cutMultiplicity G C A = 1)
    (e : CutBoundaryEdge G C A) (d : ℕ) (v : A.supp) :
    treeBoundaryWeight G d v.val.val =
      forestBoundaryCoefficient (cutComponentGraph G C A) d (cutAttachmentRoot G C A e) 1 v := by
  have hbalance : (G.degree v.val.val : ℝ) = (cutDeficit G C A v : ℝ) +
      ((cutComponentGraph G C A).degree v : ℝ) := by exact_mod_cast cut_degree_balance G C A v
  have hδ : (cutDeficit G C A v : ℝ) =
      if v = cutAttachmentRoot G C A e then (1 : ℝ) else 0 := by
    exact_mod_cast cutDeficit_of_unique_boundary G C A hcount e v
  unfold treeBoundaryWeight forestBoundaryCoefficient
  rw [hbalance, hδ]
  norm_num only [Nat.cast_one]
  congr 1
  ring

/-- Critical boundary mass in any actual singly attached tree component. -/
theorem unique_component_boundary_mass (G : SimpleGraph V) (C : Set V)
    (A : CutComponent G C) (hA : (cutComponentGraph G C A).IsTree)
    (hcount : cutMultiplicity G C A = 1) (e : CutBoundaryEdge G C A) (d : ℕ) (hd : 3 ≤ d) :
    (∑ v : A.supp, treeBoundaryWeight G d v.val.val *
      treeFlowWeight (cutComponentGraph G C A) (cutAttachmentRoot G C A e) ((d : ℝ) - 1) v) = 1 := by
  have hmass := tree_cavity_boundary_mass (cutComponentGraph G C A) hA d hd (cutAttachmentRoot G C A e)
  have hcoef := fun v : A.supp => unique_component_boundaryCoefficient G C A hcount e d v
  simp only [← finsum_eq_sum_of_fintype] at hmass ⊢
  simp_rw [← hcoef] at hmass
  exact hmass

/-- Actual outside components of the constructed core have critical weighted
boundary mass exactly one. -/
theorem spanningCore_component_boundary_mass (G T : SimpleGraph V) (hTG : T ≤ G)
    (hT : T.IsTree) (i j : V) (d : ℕ) (hd : 3 ≤ d)
    (A : CutComponent G (spanningCore G T hT i j : Set V))
    (e : CutBoundaryEdge G (spanningCore G T hT i j : Set V) A) :
    (∑ v : A.supp, treeBoundaryWeight G d v.val.val *
      treeFlowWeight (cutComponentGraph G (spanningCore G T hT i j : Set V) A)
        (cutAttachmentRoot G (spanningCore G T hT i j : Set V) A e) ((d : ℝ) - 1) v) = 1 := by
  have hmass := unique_component_boundary_mass G (spanningCore G T hT i j : Set V) A
    (spanningCore_actual_component_isTree G T hTG hT i j A)
    (spanningCore_cutMultiplicity_one G T hTG hT i j A) e d hd
  simp only [← finsum_eq_sum_of_fintype] at hmass ⊢
  exact hmass

omit [DecidableEq V] in
theorem treeBoundaryWeight_nonnegative (G : SimpleGraph V) (d : ℕ) (hd : 3 ≤ d)
    (hdegree : ∀ v, G.degree v ≤ d) (v : V) : 0 ≤ treeBoundaryWeight G d v := by
  have hdeg : (G.degree v : ℝ) ≤ d := by exact_mod_cast hdegree v
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  exact div_nonneg (by linarith) (by linarith)

/-- The whole boundary-product contribution of a genuine outside component
is bounded by the distance kernel at its actual core attachment port. -/
theorem spanningCore_branch_boundary_product (G T : SimpleGraph V) (hTG : T ≤ G)
    (hT : T.IsTree) (i j : V) (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, G.degree v ≤ d)
    (t : ℝ) (ht : 0 ≤ t) (htsq : t ^ 2 ≤ ((d : ℝ) - 1)⁻¹)
    (A : CutComponent G (spanningCore G T hT i j : Set V))
    (e : CutBoundaryEdge G (spanningCore G T hT i j : Set V) A) :
    (∑ v : A.supp, treeBoundaryWeight G d v.val.val *
      t ^ (G.dist i v.val.val + G.dist v.val.val j)) ≤
      t ^ (G.dist i e.val.val.1 + G.dist e.val.val.1 j + 2) := by
  let C : Set V := (spanningCore G T hT i j : Set V)
  let H := cutComponentGraph G C A
  let root := cutAttachmentRoot G C A e
  let base := G.dist i e.val.val.1 + G.dist e.val.val.1 j + 2
  have hi : i ∈ spanningCore G T hT i j :=
    spanningCoreTerminals_subset G T hT i j (Finset.mem_insert_self _ _)
  have hj : j ∈ spanningCore G T hT i j := spanningCoreTerminals_subset G T hT i j
    (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _)))
  have hper : ∀ v : A.supp,
      treeBoundaryWeight G d v.val.val * t ^ (G.dist i v.val.val + G.dist v.val.val j) ≤
        t ^ base * (treeBoundaryWeight G d v.val.val * treeFlowWeight H root ((d : ℝ) - 1) v) := by
    intro v
    have hdi := spanningCore_branch_distance G T hTG hT i j A e i hi v
    have hdj := spanningCore_branch_distance G T hTG hT i j A e j hj v
    have hcomm₁ : G.dist v.val.val j = G.dist j v.val.val := G.dist_comm
    have hcomm₂ : G.dist j e.val.val.1 = G.dist e.val.val.1 j := G.dist_comm
    change G.dist i v.val.val = G.dist i e.val.val.1 + 1 + H.dist root v at hdi
    change G.dist j v.val.val = G.dist j e.val.val.1 + 1 + H.dist root v at hdj
    have heq : G.dist i v.val.val + G.dist v.val.val j = base + 2 * H.dist root v := by
      dsimp only [base]
      omega
    have hflow : (t ^ 2) ^ H.dist root v ≤ treeFlowWeight H root ((d : ℝ) - 1) v := by
      unfold treeFlowWeight
      rw [show H.dist v root = H.dist root v from H.dist_comm]
      exact pow_le_pow_left₀ (sq_nonneg t) htsq _
    rw [heq, pow_add, pow_mul]
    calc
      _ = t ^ base * (treeBoundaryWeight G d v.val.val * (t ^ 2) ^ H.dist root v) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hflow (treeBoundaryWeight_nonnegative G d hd hdegree _)) (pow_nonneg ht _)
  calc
    _ ≤ ∑ v : A.supp, t ^ base *
        (treeBoundaryWeight G d v.val.val * treeFlowWeight H root ((d : ℝ) - 1) v) :=
      Finset.sum_le_sum (fun v _ => hper v)
    _ = t ^ base * ∑ v : A.supp,
        treeBoundaryWeight G d v.val.val * treeFlowWeight H root ((d : ℝ) - 1) v := by rw [Finset.mul_sum]
    _ = t ^ base := by rw [spanningCore_component_boundary_mass G T hTG hT i j d hd A e, mul_one]

omit [DecidableEq V] in
/-- The inside coefficient and all attachment edges at a core vertex combine
into at most its own core boundary coefficient, hence at most two. -/
theorem core_boundary_coefficient_aggregation (G : SimpleGraph V) (C : Set V)
    (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (htsq : t ^ 2 ≤ ((d : ℝ) - 1)⁻¹) (u : C) :
    treeBoundaryWeight G d u.val + (outsideCoreNeighborCount G C u : ℝ) * t ^ 2 ≤ 2 := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hbalance : (G.degree u.val : ℝ) = ((G.induce C).degree u : ℝ) +
      (outsideCoreNeighborCount G C u : ℝ) := by exact_mod_cast core_neighbor_degree_partition G C u
  have hcoeff : treeBoundaryWeight G d u.val +
      (outsideCoreNeighborCount G C u : ℝ) * ((d : ℝ) - 1)⁻¹ =
        treeBoundaryWeight (G.induce C) d u := by
    unfold treeBoundaryWeight
    rw [hbalance]
    ring
  calc
    _ ≤ treeBoundaryWeight G d u.val +
        (outsideCoreNeighborCount G C u : ℝ) * ((d : ℝ) - 1)⁻¹ :=
      add_le_add_left (mul_le_mul_of_nonneg_left htsq (Nat.cast_nonneg _)) _
    _ = treeBoundaryWeight (G.induce C) d u := hcoeff
    _ ≤ 2 := by
      unfold treeBoundaryWeight
      apply (div_le_iff₀ (show 0 < (d : ℝ) - 1 by linarith)).mpr
      have hdeg : (0 : ℝ) ≤ (G.induce C).degree u := Nat.cast_nonneg _
      linarith

/-- A concrete actual attachment edge selected from its proved cardinality. -/
def spanningCorePickEdge (G T : SimpleGraph V) (hTG : T ≤ G) (hT : T.IsTree)
    (i j : V) (A : CutComponent G (spanningCore G T hT i j : Set V)) :
    CutBoundaryEdge G (spanningCore G T hT i j : Set V) A :=
  Classical.choose (Nat.card_eq_one_iff_exists.mp (spanningCore_cutMultiplicity_one G T hTG hT i j A))

/-- The whole actual boundary-product sum collapses to the constructed core,
with all component sums and actual port degrees derived from finite counts. -/
theorem spanningCore_boundary_product_reduction (G T : SimpleGraph V) (hTG : T ≤ G)
    (hT : T.IsTree) (i j : V) (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, G.degree v ≤ d)
    (t : ℝ) (ht : 0 ≤ t) (htsq : t ^ 2 ≤ ((d : ℝ) - 1)⁻¹) :
    (∑ v : V, treeBoundaryWeight G d v * t ^ (G.dist i v + G.dist v j)) ≤
      2 * ∑ᶠ v : (spanningCore G T hT i j : Set V), t ^ (G.dist i v.val + G.dist v.val j) := by
  let C : Set V := (spanningCore G T hT i j : Set V)
  let f := fun v : V => t ^ (G.dist i v + G.dist v j)
  let pick := spanningCorePickEdge G T hTG hT i j
  have hbranch : ∀ A : CutComponent G C,
      (∑ᶠ v : A.supp, treeBoundaryWeight G d v.val.val * f v.val.val) ≤
        t ^ 2 * f (pick A).val.val.1 := by
    intro A
    have h := spanningCore_branch_boundary_product G T hTG hT i j d hd hdegree t ht htsq A (pick A)
    simp only [← finsum_eq_sum_of_fintype] at h ⊢
    apply h.trans_eq
    dsimp only [f]
    rw [pow_add]
    ring
  have hresult := boundary_sum_reduction G C
    (fun A => spanningCore_cutMultiplicity_one G T hTG hT i j A) pick
    (fun v => treeBoundaryWeight G d v) f (t ^ 2) 2 hbranch
    (fun u => core_boundary_coefficient_aggregation G C d hd t htsq u)
    (fun _ => pow_nonneg ht _)
  simp only [← finsum_eq_sum_of_fintype] at hresult ⊢
  exact hresult

/-- The complete geometry-only bounded-excess convolution bound underlying
Appendix B.6. Every sphere count, branch mass and port aggregation is proved. -/
theorem bounded_excess_boundary_convolution (G : SimpleGraph V) (hG : G.Connected)
    (ω : ℕ) (hω : graphExcess G ≤ ω) (d : ℕ) (hd : 3 ≤ d)
    (hdegree : ∀ v, G.degree v ≤ d) (t : ℝ) (ht : 0 ≤ t)
    (htsq : t ^ 2 ≤ ((d : ℝ) - 1)⁻¹) (i j : V) :
    (∑ v : V, treeBoundaryWeight G d v * t ^ (G.dist i v + G.dist v j)) ≤
      4 * ((2 * (2 * ω + 2) * (2 * ω + 1) : ℕ) : ℝ) *
        ((G.dist i j : ℝ) + 1) * t ^ G.dist i j := by
  obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
  let C := spanningCore G T hT i j
  let f := fun v : V => t ^ (G.dist i v + G.dist v j)
  let A := 2 * (2 * ω + 2) * (2 * ω + 1)
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hrecip : ((d : ℝ) - 1)⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (show 2 ≤ (d : ℝ) - 1 by linarith)
  have hhalf := htsq.trans hrecip
  have htone : t ≤ 1 := by nlinarith [sq_nonneg (t - 1)]
  have hradius := radial_kernel_finset_sum C (fun v => G.dist i v)
    (fun v => G.dist i v + G.dist v j) (G.dist i j) A t ht htone hhalf
    (fun n => spanningCoreLayer_card_bound G T hTG hT i j n ω hω)
    (by
      intro v _
      have h₁ : G.dist i j ≤ G.dist i v + G.dist v j := hG.dist_triangle
      have h₂ : G.dist i v ≤ G.dist i j + G.dist j v := hG.dist_triangle
      have hcomm : G.dist j v = G.dist v j := G.dist_comm
      change G.dist i j ≤ G.dist i v + G.dist v j ∧
        2 * G.dist i v ≤ (G.dist i v + G.dist v j) + G.dist i j
      exact ⟨h₁, by omega⟩)
  have hcollapse := spanningCore_boundary_product_reduction G T hTG hT i j d hd hdegree t ht htsq
  have hcoe := C.sum_coe_sort f
  simp only [← finsum_eq_sum_of_fintype] at hcollapse hcoe
  have hcollapse' : (∑ v : V, treeBoundaryWeight G d v * f v) ≤ 2 * ∑ v ∈ C, f v := by
    rw [← hcoe]
    simpa only [← finsum_eq_sum_of_fintype] using hcollapse
  apply hcollapse'.trans
  calc
    _ ≤ 2 * (2 * (A : ℝ) * ((G.dist i j : ℝ) + 1) * t ^ G.dist i j) :=
      mul_le_mul_of_nonneg_left hradius (by norm_num)
    _ = _ := by ring

/-- Explicit bounded-excess convolution constant, quadratic in omega. -/
def coreConvolutionConstant (ω : ℕ) : ℝ := 4 * ((2 * (2 * ω + 2) * (2 * ω + 1) : ℕ) : ℝ)

theorem coreConvolutionConstant_nonnegative (ω : ℕ) : 0 ≤ coreConvolutionConstant ω := by
  unfold coreConvolutionConstant
  positivity

/-- Product-kernel form for direct use by the proved boundary perturbation
theorem. The convolution estimate is derived from graph geometry. -/
theorem bounded_excess_product_kernel_convolution (G : SimpleGraph V) (hG : G.Connected)
    (ω : ℕ) (hω : graphExcess G ≤ ω) (d : ℕ) (hd : 3 ≤ d)
    (hdegree : ∀ v, G.degree v ≤ d) (t : ℝ) (ht : 0 ≤ t)
    (htsq : t ^ 2 ≤ ((d : ℝ) - 1)⁻¹) (i j : V) :
    (∑ v : V, treeBoundaryWeight G d v * t ^ G.dist i v * t ^ G.dist v j) ≤
      coreConvolutionConstant ω * ((G.dist i j : ℝ) + 1) * t ^ G.dist i j := by
  simpa only [coreConvolutionConstant, pow_add, mul_assoc] using
    bounded_excess_boundary_convolution G hG ω hω d hd hdegree t ht htsq i j

/-- The physical cavity transfer is in the range of the graph convolution
theorem, solely from norm(m)<=1 and the normalized edge weight. -/
theorem cavity_transfer_norm_sq_bound (d : ℕ) (hd : 3 ≤ d) (m : ℂ) (hm : ‖m‖ ≤ 1) :
    ‖-m * treeEdgeWeight d‖ ^ 2 ≤ ((d : ℝ) - 1)⁻¹ := by
  calc
    _ = ‖m‖ ^ 2 * ‖treeEdgeWeight d‖ ^ 2 := by rw [norm_mul, norm_neg, mul_pow]
    _ ≤ 1 * ‖treeEdgeWeight d‖ ^ 2 := mul_le_mul_of_nonneg_right
      (pow_le_one₀ (norm_nonneg m) hm) (sq_nonneg _)
    _ = _ := by rw [treeEdgeWeight_norm_sq d hd, one_mul, one_div]

theorem cavity_power_boundary_convolution (G : SimpleGraph V) (hG : G.Connected)
    (ω : ℕ) (hω : graphExcess G ≤ ω) (d : ℕ) (hd : 3 ≤ d)
    (hdegree : ∀ v, G.degree v ≤ d) (m : ℂ) (hm : ‖m‖ ≤ 1) (i j : V) :
    (∑ v : V, treeBoundaryWeight G d v * ‖-m * treeEdgeWeight d‖ ^ G.dist i v *
      ‖-m * treeEdgeWeight d‖ ^ G.dist v j) ≤
      coreConvolutionConstant ω * ((G.dist i j : ℝ) + 1) * ‖-m * treeEdgeWeight d‖ ^ G.dist i j :=
  bounded_excess_product_kernel_convolution G hG ω hω d hd hdegree _ (norm_nonneg _)
    (cavity_transfer_norm_sq_bound d hd m hm) i j

end LocalLaw
