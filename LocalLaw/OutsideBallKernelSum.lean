import LocalLaw.SharpBallCounting
import LocalLaw.CoreBoundaryConvolution

/-!
# Kernel sums over a ball seen from outside

The target vertex is outside the ball. This is the scope needed in source
Claim 5.5. Inside targets cannot satisfy the same logarithmic bound.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance outsideBallSumDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A finite growing geometric sum, with a constant independent of its length. -/
theorem geometric_sum_le_four_last (a : ℝ) (ha : 4 / 3 ≤ a) (R : ℕ) :
    (∑ n ∈ Finset.range (R + 1), a ^ n) ≤ 4 * a ^ R := by
  have ha0 : 0 ≤ a := by linarith
  induction R with
  | zero => norm_num
  | succ R ih =>
      rw [Finset.sum_range_succ]
      have hh := mul_le_mul_of_nonneg_right (show 4 + a ≤ 4 * a by linarith)
        (pow_nonneg ha0 R)
      calc
        _ ≤ 4 * a ^ R + a ^ (R + 1) := add_le_add_right ih _
        _ ≤ 4 * a ^ (R + 1) := by rw [pow_succ] at *; nlinarith

section Finite
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Uniform finite layer counts give a linear count below a height cap. -/
theorem finset_card_below_layer_bound (S : Finset V) (depth : V → ℕ) (A ell : ℕ)
    (layers : ∀ n, (S.filter (fun v => depth v = n)).card ≤ A) :
    (S.filter (fun v => depth v ≤ ell)).card ≤ A * (ell + 1) := by
  let B := S.filter (fun v => depth v ≤ ell)
  have hmaps : Set.MapsTo depth B (Finset.range (ell + 1)) := by
    intro v hv
    have hh := (Finset.mem_filter.mp hv).2
    exact Finset.mem_range.mpr (by omega)
  calc
    _ = ∑ n ∈ Finset.range (ell + 1), (B.filter (fun v => depth v = n)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _n ∈ Finset.range (ell + 1), A := by
      apply Finset.sum_le_sum
      intro n _
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans (layers n)
    _ = _ := by simp [Nat.mul_comm]

theorem connected_dist_sphere_card (G : SimpleGraph V) (hG : G.Connected)
    (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, G.degree v ≤ d) (o : V) (n : ℕ) :
    (((Finset.univ.filter (fun v => G.dist o v = n)).card : ℕ) : ℝ) ≤
      2 * ((d : ℝ) - 1) ^ n := by
  have hsphere : Finset.univ.filter (fun v => G.dist o v = n) = graphSphereFinset G o n := by
    ext v
    have heq : ((G.dist o v : ℕ) : ℕ∞) = G.edist o v :=
      ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr (hG o v))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_graphSphereFinset]
    constructor
    · intro hh
      exact heq.symm.trans (congrArg (fun k : ℕ => (k : ℕ∞)) hh)
    · intro hh
      exact ENat.coe_inj.mp (heq.trans hh)
  rw [hsphere]
  cases n with
  | zero => simp
  | succ n =>
      have hcard := graphSphere_card_bound G o d n hdegree
      have hcast : ((graphSphereFinset G o (n + 1)).card : ℝ) ≤
          (d : ℝ) * ((d : ℝ) - 1) ^ n := by
        simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (show 1 ≤ d by omega), Nat.cast_one]
          using Nat.cast_le (α := ℝ).mpr hcard
      have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
      have hk : 0 ≤ (d : ℝ) - 1 := by linarith
      exact hcast.trans (by rw [pow_succ]; nlinarith [pow_nonneg hk n])

/-- Critical decay summed over a finite ball grows at most like the square
root of its volume. This follows from actual graph sphere counts. -/
theorem critical_ball_kernel_sum (G : SimpleGraph V) (hG : G.Connected)
    (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, G.degree v ≤ d) (o : V) (R : ℕ) :
    (∑ v : V, if G.dist o v ≤ R then
      (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ G.dist o v else 0) ≤
        8 * (Real.sqrt ((d : ℝ) - 1)) ^ R := by
  let a := Real.sqrt ((d : ℝ) - 1)
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hasq : a ^ 2 = (d : ℝ) - 1 := Real.sq_sqrt (by linarith)
  have ha43 : 4 / 3 ≤ a := by nlinarith [Real.sqrt_nonneg ((d : ℝ) - 1)]
  have hbase : ((d : ℝ) - 1) * a⁻¹ = a := by
    rw [← hasq]
    field_simp
    ring
  let S := Finset.univ.filter (fun v => G.dist o v ≤ R)
  have hmaps : ∀ v ∈ S, G.dist o v ∈ Finset.range (R + 1) := by
    intro v hv
    exact Finset.mem_range.mpr (by have hh := (Finset.mem_filter.mp hv).2; omega)
  have hsplit : (∑ v ∈ S, a⁻¹ ^ G.dist o v) =
      ∑ n ∈ Finset.range (R + 1), ∑ v ∈ S.filter (fun v => G.dist o v = n),
        a⁻¹ ^ G.dist o v := (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  have hper (n : ℕ) : (∑ v ∈ S.filter (fun v => G.dist o v = n), a⁻¹ ^ G.dist o v) ≤
      2 * a ^ n := by
    have hsub : S.filter (fun v => G.dist o v = n) ⊆
        Finset.univ.filter (fun v => G.dist o v = n) :=
      Finset.filter_subset_filter _ (Finset.subset_univ _)
    have hcard : ((S.filter (fun v => G.dist o v = n)).card : ℝ) ≤
        2 * ((d : ℝ) - 1) ^ n :=
      (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (connected_dist_sphere_card G hG d hd hdegree o n)
    calc
      _ = ∑ _v ∈ S.filter (fun v => G.dist o v = n), a⁻¹ ^ n := by
        exact Finset.sum_congr rfl (fun v hv => by rw [(Finset.mem_filter.mp hv).2])
      _ = ((S.filter (fun v => G.dist o v = n)).card : ℝ) * a⁻¹ ^ n := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * ((d : ℝ) - 1) ^ n) * a⁻¹ ^ n :=
        mul_le_mul_of_nonneg_right hcard (pow_nonneg (inv_nonneg.mpr ha.le) _)
      _ = 2 * a ^ n := by rw [mul_assoc, ← mul_pow, hbase]
  calc
    _ = ∑ v ∈ S, a⁻¹ ^ G.dist o v := by rw [← Finset.sum_filter]
    _ = _ := hsplit
    _ ≤ ∑ n ∈ Finset.range (R + 1), 2 * a ^ n := Finset.sum_le_sum (fun n _ => hper n)
    _ = 2 * ∑ n ∈ Finset.range (R + 1), a ^ n := (Finset.mul_sum ..).symm
    _ ≤ 2 * (4 * a ^ R) := mul_le_mul_of_nonneg_left (geometric_sum_le_four_last a ha43 R) (by norm_num)
    _ = _ := by ring

/-- A singly attached branch contributes a uniformly bounded amount to
the inner ball when the target is outside that ball. -/
theorem unique_cut_branch_ball_kernel_sum (G : SimpleGraph V) (hG : G.Connected)
    (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, G.degree v ≤ d)
    (C : Set V) (o i : V) (ho : o ∈ C) (hi : i ∈ C) (ell : ℕ)
    (hout : ell < G.dist o i) (A : CutComponent G C)
    (hcount : cutMultiplicity G C A = 1) (e : CutBoundaryEdge G C A) :
    (∑ y : A.supp, if G.dist o y.val.val ≤ ell then
      (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ G.dist i y.val.val else 0) ≤
        if G.dist o e.val.val.1 ≤ ell then 8 else 0 := by
  let a := Real.sqrt ((d : ℝ) - 1)
  let root := cutAttachmentRoot G C A e
  let H := cutComponentGraph G C A
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have haone : 1 ≤ a := by have hh := Real.sq_sqrt (show 0 ≤ (d : ℝ) - 1 by linarith); nlinarith [Real.sqrt_nonneg ((d : ℝ) - 1)]
  have ht : 0 ≤ a⁻¹ := inv_nonneg.mpr ha.le
  have htone : a⁻¹ ≤ 1 := (inv_le_one₀ ha).mpr haone
  have hHdegree (v : A.supp) : H.degree v ≤ d := by
    have hcomp := cutComponent_degree_eq G C A v
    have hind := induced_degree_le G Cᶜ v.val
    have hamb := hdegree v.val.val
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      at hcomp hind hamb ⊢
    exact hcomp.trans_le (hind.trans hamb)
  have hdo (y : A.supp) : G.dist o y.val.val = G.dist o e.val.val.1 + 1 + H.dist root y :=
    unique_cut_attachment_distance G hG C A hcount e o ho y
  have hdi (y : A.supp) : G.dist i y.val.val = G.dist i e.val.val.1 + 1 + H.dist root y :=
    unique_cut_attachment_distance G hG C A hcount e i hi y
  by_cases hbase : G.dist o e.val.val.1 + 1 ≤ ell
  · let R := ell - (G.dist o e.val.val.1 + 1)
    have hR : R ≤ G.dist i e.val.val.1 + 1 := by
      have htriangle : G.dist o i ≤ G.dist o e.val.val.1 + G.dist i e.val.val.1 := by
        simpa only [G.dist_comm] using (hG.dist_triangle (u := o) (v := e.val.val.1) (w := i))
      dsimp [R]
      omega
    have hsum := critical_ball_kernel_sum H A.connected_induce_supp d hd hHdegree root R
    have hfactor : a⁻¹ ^ (G.dist i e.val.val.1 + 1) * a ^ R ≤ 1 := by
      calc
        _ ≤ a⁻¹ ^ R * a ^ R := mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one ht htone hR) (pow_nonneg ha.le _)
        _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ ha.ne', one_pow]
    rw [if_pos (show G.dist o e.val.val.1 ≤ ell by omega)]
    calc
      _ = a⁻¹ ^ (G.dist i e.val.val.1 + 1) *
          ∑ y : A.supp, if H.dist root y ≤ R then a⁻¹ ^ H.dist root y else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        rw [hdo y, hdi y]
        have hh : G.dist o e.val.val.1 + 1 + H.dist root y ≤ ell ↔ H.dist root y ≤ R := by
          dsimp [R]
          omega
        by_cases hy : H.dist root y ≤ R
        · simp only [if_pos hy, if_pos (hh.mpr hy), pow_add]
          rfl
        · simp only [if_neg hy, if_neg (fun h => hy (hh.mp h)), mul_zero]
      _ ≤ a⁻¹ ^ (G.dist i e.val.val.1 + 1) * (8 * a ^ R) :=
        mul_le_mul_of_nonneg_left hsum (pow_nonneg ht _)
      _ ≤ 8 := by nlinarith
  · have hzero : (∑ y : A.supp, if G.dist o y.val.val ≤ ell then
        (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ G.dist i y.val.val else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro y _
      rw [if_neg]
      rw [hdo y]
      omega
    rw [hzero]
    split_ifs <;> norm_num

/-- The actual critical kernel has only a linear-in-radius mass on a ball
seen from outside, even when the finite connected graph has bounded excess. -/
theorem outside_ball_critical_kernel_sum (G : SimpleGraph V) (hG : G.Connected)
    (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, G.degree v ≤ d)
    (ω : ℕ) (hω : graphExcess G ≤ ω) (o i : V) (ell : ℕ)
    (hout : ell < G.dist o i) :
    (∑ y : V, if G.dist o y ≤ ell then
      (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ G.dist i y else 0) ≤
      (1 + 8 * (d : ℝ)) * (2 * (2 * (ω : ℝ) + 2) * (2 * (ω : ℝ) + 1)) *
        ((ell : ℝ) + 1) := by
  obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
  let C := spanningCore G T hT o i
  let α := (Real.sqrt ((d : ℝ) - 1))⁻¹
  let f := fun y : V => if G.dist o y ≤ ell then α ^ G.dist i y else 0
  let I := ∑ u : C, if G.dist o u.val ≤ ell then (1 : ℝ) else 0
  let A := 2 * (2 * ω + 2) * (2 * ω + 1)
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hsqrt : 1 ≤ Real.sqrt ((d : ℝ) - 1) := by
    have hh := Real.sq_sqrt (show 0 ≤ (d : ℝ) - 1 by linarith)
    nlinarith [Real.sqrt_nonneg ((d : ℝ) - 1)]
  have hα : 0 ≤ α := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hαone : α ≤ 1 := (inv_le_one₀ (by linarith : 0 < Real.sqrt ((d : ℝ) - 1))).mpr hsqrt
  have ho : o ∈ (C : Set V) := spanningCoreTerminals_subset G T hT o i (by simp [spanningCoreTerminals])
  have hi : i ∈ (C : Set V) := spanningCoreTerminals_subset G T hT o i (by simp [spanningCoreTerminals])
  have hcount (c : CutComponent G (C : Set V)) : cutMultiplicity G (C : Set V) c = 1 :=
    spanningCore_cutMultiplicity_one G T hTG hT o i c
  let pick : ∀ c : CutComponent G (C : Set V), CutBoundaryEdge G (C : Set V) c :=
    fun c => Classical.choice (Nat.card_eq_one_iff_unique.mp (hcount c)).2
  have hbranch (c : CutComponent G (C : Set V)) :
      (∑ y : c.supp, f y.val.val) ≤ if G.dist o (pick c).val.val.1 ≤ ell then 8 else 0 := by
    have hh := unique_cut_branch_ball_kernel_sum G hG d hd hdegree (C : Set V) o i ho hi ell hout c (hcount c) (pick c)
    simp only [← finsum_eq_sum_of_fintype] at hh ⊢
    exact hh
  have hcore : (∑ u : C, f u.val) ≤ I := by
    apply Finset.sum_le_sum
    intro u _
    dsimp [f]
    by_cases hu : G.dist o u.val ≤ ell
    · simp only [if_pos hu]
      exact pow_le_one₀ hα hαone
    · simp only [if_neg hu]
      exact le_rfl
  have hports := sum_unique_cut_ports G (C : Set V) hcount pick
    (fun v => if G.dist o v ≤ ell then (8 : ℝ) else 0)
  have hbranches : (∑ c : CutComponent G (C : Set V), ∑ y : c.supp, f y.val.val) ≤
      8 * (d : ℝ) * I := by
    calc
      _ ≤ ∑ c : CutComponent G (C : Set V), if G.dist o (pick c).val.val.1 ≤ ell then 8 else 0 :=
        Finset.sum_le_sum (fun c _ => hbranch c)
      _ = ∑ u : C, (outsideCoreNeighborCount G (C : Set V) u : ℝ) *
          (if G.dist o u.val ≤ ell then 8 else 0) := by
        simp only [← finsum_eq_sum_of_fintype] at hports ⊢
        exact hports
      _ ≤ ∑ u : C, (8 * (d : ℝ)) * (if G.dist o u.val ≤ ell then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro u _
        have hdeg := core_neighbor_degree_partition G (C : Set V) u
        have hamb := hdegree u.val
        have houtcount : outsideCoreNeighborCount G (C : Set V) u ≤ d := by
          simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hdeg hamb
          omega
        by_cases hu : G.dist o u.val ≤ ell
        · simp only [if_pos hu, mul_one]
          exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr houtcount) (by norm_num) |>.trans_eq (mul_comm _ _)
        · simp only [if_neg hu, mul_zero, le_refl]
      _ = _ := (Finset.mul_sum ..).symm
  have hcard := finset_card_below_layer_bound C (fun v => G.dist o v) A ell
    (fun n => spanningCoreLayer_card_bound G T hTG hT o i n ω hω)
  have hI : I ≤ (A : ℝ) * ((ell : ℝ) + 1) := by
    have hcoe := C.sum_coe_sort (fun v => if G.dist o v ≤ ell then (1 : ℝ) else 0)
    have heq : I = ((C.filter (fun v => G.dist o v ≤ ell)).card : ℝ) := by
      change (∑ u : C, if G.dist o u.val ≤ ell then (1 : ℝ) else 0) = _
      simp only [← finsum_eq_sum_of_fintype] at hcoe ⊢
      rw [hcoe, ← Finset.sum_filter]
      simp
    rw [heq]
    exact_mod_cast hcard
  have hsplit := sum_core_components G (C : Set V) f
  calc
    _ = (∑ u : C, f u.val) + ∑ c : CutComponent G (C : Set V), ∑ y : c.supp, f y.val.val := by
      simp only [← finsum_eq_sum_of_fintype] at hsplit ⊢
      exact hsplit
    _ ≤ I + 8 * (d : ℝ) * I := add_le_add hcore hbranches
    _ = (1 + 8 * (d : ℝ)) * I := by ring
    _ ≤ (1 + 8 * (d : ℝ)) * ((A : ℝ) * ((ell : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by dsimp [A]; push_cast; ring

/-- Every smaller nonnegative decay parameter satisfies the same bound. -/
theorem outside_ball_kernel_sum (G : SimpleGraph V) (hG : G.Connected)
    (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, G.degree v ≤ d)
    (ω : ℕ) (hω : graphExcess G ≤ ω) (o i : V) (ell : ℕ)
    (hout : ell < G.dist o i) (t : ℝ) (ht : 0 ≤ t)
    (htcap : t ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹) :
    (∑ y : V, if G.dist o y ≤ ell then t ^ G.dist i y else 0) ≤
      (1 + 8 * (d : ℝ)) * (2 * (2 * (ω : ℝ) + 2) * (2 * (ω : ℝ) + 1)) *
        ((ell : ℝ) + 1) := by
  calc
    _ ≤ ∑ y : V, if G.dist o y ≤ ell then
        (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ G.dist i y else 0 := by
      apply Finset.sum_le_sum
      intro y _
      split_ifs
      · exact pow_le_pow_left₀ ht htcap _
      · exact le_rfl
    _ ≤ _ := outside_ball_critical_kernel_sum G hG d hd hdegree ω hω o i ell hout

end Finite
end LocalLaw
