import LocalLaw.ExteriorGraphApproximation
import LocalLaw.TreeReferenceKernel
import LocalLaw.MinorIdentity
import LocalLaw.Abstract

/-!
# Exterior cavity anchor

On a bounded exterior annulus, the actual entry localization and exact forest
kernel yield the deleted-vertex cavity estimate. The exceptional-center density
is retained when averaging, rather than silently absorbed into the error.
-/

open scoped BigOperators

namespace LocalLaw

/-- Stability of the one-vertex Schur formula without dividing by the
reference diagonal. The reference product quotient is p*t². -/
theorem schur_cavity_error_bound (a b c e p t m : ℂ) (δ γ : ℝ)
    (hδ : 0 ≤ δ) (hγ : 0 < γ) (he : γ ≤ ‖e‖)
    (ha : ‖a - p‖ ≤ δ) (hb : ‖b - p * t‖ ≤ δ) (hc : ‖c - p * t‖ ≤ δ)
    (hd : ‖e - p‖ ≤ δ) (hcnorm : ‖c‖ ≤ 1) (hpt : ‖p * t‖ ≤ 1)
    (hpt2 : ‖p * t ^ 2‖ ≤ 1) (href : p - p * t ^ 2 = m) :
    ‖a - b * c / e - m‖ ≤ δ + 3 * δ / γ := by
  have he0 : e ≠ 0 := norm_pos_iff.mp (hγ.trans_le he)
  let X := (b - p * t) * c + (p * t) * (c - p * t) + (p * t ^ 2) * (p - e)
  have hX : ‖X‖ ≤ 3 * δ := by
    have h₁ : ‖(b - p * t) * c‖ ≤ δ := by
      rw [norm_mul]
      exact (mul_le_mul hb hcnorm (norm_nonneg _) hδ).trans_eq (mul_one _)
    have h₂ : ‖(p * t) * (c - p * t)‖ ≤ δ := by
      rw [norm_mul]
      exact (mul_le_mul hpt hc (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
    have h₃ : ‖(p * t ^ 2) * (p - e)‖ ≤ δ := by
      rw [norm_mul]
      have hh : ‖p - e‖ ≤ δ := by simpa only [norm_sub_rev] using hd
      exact (mul_le_mul hpt2 hh (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
    exact (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans (by linarith))
  have hid : a - b * c / e - m = (a - p) - X / e := by
    rw [← href]
    dsimp [X]
    field_simp
    ring
  rw [hid]
  calc
    ‖(a - p) - X / e‖ ≤ ‖a - p‖ + ‖X / e‖ := norm_sub_le _ _
    _ ≤ δ + 3 * δ / γ := by
      apply add_le_add ha
      rw [norm_div]
      exact div_le_div₀ (by positivity) hX hγ he

/-- Uniform reference controls on the bounded exterior annulus. -/
theorem exterior_reference_bounds (d : ℕ) (hd : 3 ≤ d) (m z : ℂ)
    (hm : ‖m‖ ≤ 1) (hz : 2 * (d : ℝ) ≤ ‖z‖) (B : ℝ) (hB : ‖z‖ ≤ B) :
    ‖kestenMcKayTransform d m z‖ ≤ 1 ∧
      1 / (B + 2) ≤ ‖kestenMcKayTransform d m z‖ ∧
      ‖-m * treeEdgeWeight d‖ ≤ 1 := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hkp : 0 < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
  have hkcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hq : ‖(d : ℂ) / ((d - 1 : ℕ) : ℂ)‖ ≤ 2 := by
    simp only [norm_div, Complex.norm_natCast]
    apply (div_le_iff₀ hkp).mpr
    rw [hkcast]
    linarith
  have hself : ‖((d : ℂ) / ((d - 1 : ℕ) : ℂ)) * m‖ ≤ 2 := by
    rw [norm_mul]
    exact (mul_le_mul hq hm (norm_nonneg _) (by norm_num)).trans_eq (mul_one _)
  let den := -z - ((d : ℂ) / ((d - 1 : ℕ) : ℂ)) * m
  have hdenLo : (d : ℝ) ≤ ‖den‖ := by
    have hh := norm_sub_norm_le (-z) (((d : ℂ) / ((d - 1 : ℕ) : ℂ)) * m)
    rw [norm_neg] at hh
    change ‖z‖ - _ ≤ ‖den‖ at hh
    linarith
  have hdenUp : ‖den‖ ≤ B + 2 := by
    have hh := norm_sub_le (-z) (((d : ℂ) / ((d - 1 : ℕ) : ℂ)) * m)
    rw [norm_neg] at hh
    exact hh.trans (add_le_add hB hself)
  have hdenPos : 0 < ‖den‖ := by linarith
  have hp : ‖kestenMcKayTransform d m z‖ = 1 / ‖den‖ := by
    simp only [kestenMcKayTransform, norm_inv, one_div]
    rfl
  constructor
  · rw [hp]
    exact (div_le_one hdenPos).mpr (by linarith)
  constructor
  · rw [hp]
    exact one_div_le_one_div_of_le hdenPos hdenUp
  · have hsone : 1 ≤ Real.sqrt ((d : ℝ) - 1) := by
      have hh := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ d - 1 by linarith)
      simpa only [Real.sqrt_one] using hh
    have hα : ‖treeEdgeWeight d‖ ≤ 1 := by
      simp only [treeEdgeWeight, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
      rw [← one_div]
      exact (div_le_one (by linarith : 0 < Real.sqrt ((d : ℝ) - 1))).mpr hsone
    rw [norm_mul, norm_neg]
    exact (mul_le_mul hm hα (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

/-- The Kesten--McKay/semicircle relation in the Schur formula. -/
theorem kestenMcKay_cavity_identity (d : ℕ) (hd : 3 ≤ d) (m z : ℂ)
    (hm : m ^ 2 + z * m + 1 = 0) (hz : 0 < z.im) (hmim : 0 ≤ m.im) :
    kestenMcKayTransform d m z - kestenMcKayTransform d m z * (-m * treeEdgeWeight d) ^ 2 = m := by
  have hkcast : ((d - 1 : ℕ) : ℂ) = (d : ℂ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hsq : (-m * treeEdgeWeight d) ^ 2 = m ^ 2 / ((d - 1 : ℕ) : ℂ) := by
    rw [mul_pow, neg_sq, treeEdgeWeight_sq d hd, hkcast]
    ring
  rw [hsq, kestenMcKayTransform_eq d hd m z hm hz hmim]
  have hden := kestenMcKay_algebraic_denominator_ne_zero d hd m z hm hz hmim
  convert div_mul_cancel₀ m hden using 1; ring

/-- Acyclicity descends along an actual injective graph embedding. -/
theorem acyclic_of_embedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ↪g H) (hH : H.IsAcyclic) : G.IsAcyclic := by
  intro v p hp
  exact hH (p.map e.toHom) (hp.map e.injective)

theorem induced_acyclic_mono {V : Type*} (G : SimpleGraph V) {S U : Set V}
    (hSU : S ⊆ U) (hU : (G.induce U).IsAcyclic) : (G.induce S).IsAcyclic :=
  acyclic_of_embedding (G.induceHomOfLE hSU) hU

noncomputable section
local instance cavityAnchorDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section ForestNeighborhoods
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem pairBall_acyclic_left_diagonal (G : SimpleGraph V) (i j : V) (r : ℕ)
    (h : (pairBallGraph G i j r).IsAcyclic) : (pairBallGraph G i i r).IsAcyclic := by
  apply induced_acyclic_mono G _ h
  intro v hv
  exact Or.inl (hv.elim id id)

omit [Fintype V] [DecidableEq V] in
theorem pairBall_acyclic_right_diagonal (G : SimpleGraph V) (i j : V) (r : ℕ)
    (h : (pairBallGraph G i j r).IsAcyclic) : (pairBallGraph G j j r).IsAcyclic := by
  apply induced_acyclic_mono G _ h
  intro v hv
  exact Or.inr (hv.elim id id)

omit [Fintype V] [DecidableEq V] in
theorem pairBall_acyclic_swap (G : SimpleGraph V) (i j : V) (r : ℕ)
    (h : (pairBallGraph G i j r).IsAcyclic) : (pairBallGraph G j i r).IsAcyclic := by
  apply induced_acyclic_mono G _ h
  exact fun _ hv => hv.symm

omit [Fintype V] [DecidableEq V] in
/-- A neighbor pair's radius-r neighborhood is inside the radius-R ball of
its first endpoint once r+1≤R. -/
theorem pairBall_subset_neighbor_ball (G : SimpleGraph V) (i j : V) (r R : ℕ)
    (hij : G.Adj i j) (hR : r + 1 ≤ R) :
    pairBallVertices G i j r ⊆ graphBallVertices G i R := by
  intro v hv
  rcases hv with hi | hj
  · exact hi.trans (ENat.coe_le_coe.mpr (by omega))
  · calc
      G.edist i v ≤ G.edist i j + G.edist j v := G.edist_triangle
      _ ≤ 1 + (r : ℕ∞) := by rw [SimpleGraph.edist_eq_one_iff_adj.mpr hij]; exact add_le_add_left hj 1
      _ = ((r + 1 : ℕ) : ℕ∞) := by simp [Nat.cast_add, add_comm]
      _ ≤ R := ENat.coe_le_coe.mpr hR

omit [Fintype V] [DecidableEq V] in
theorem pairBall_acyclic_of_neighbor_ball (G : SimpleGraph V) (i j : V) (r R : ℕ)
    (hij : G.Adj i j) (hR : r + 1 ≤ R) (hball : (graphBall G i R).IsAcyclic) :
    (pairBallGraph G i j r).IsAcyclic :=
  induced_acyclic_mono G (pairBall_subset_neighbor_ball G i j r R hij hR) hball

end ForestNeighborhoods

namespace RegularGraph
variable {N d : ℕ}

/-- The actual diagonal resolvent entry after deleting vertex j. -/
def orientedCavity (g : RegularGraph N d) (z : ℂ) (i j : Fin N) (hne : i ≠ j) : ℂ :=
  g.minorG j z ⟨i, hne⟩ ⟨i, hne⟩

theorem orientedCavity_eq_schur (g : RegularGraph N d) (z : ℂ) (hz : 0 < z.im)
    (i j : Fin N) (hne : i ≠ j) :
    g.orientedCavity z i j hne = g.G z i i - g.G z i j * g.G z j i / g.G z j j :=
  green_deleted_vertex g.H g.H_hermitian z hz j ⟨i, hne⟩ ⟨i, hne⟩

/-- Exterior cavity control at an actual adjacent pair with an acyclic
pair-neighborhood. All reference entries and the Schur denominator are proved. -/
theorem orientedCavity_exterior_error (g : RegularGraph N d) (hd : 3 ≤ d) (r : ℕ)
    (z : ℂ) (hzIm : 0 < z.im) (hz : 2 * (d : ℝ) ≤ ‖z‖) (B : ℝ) (hB : ‖z‖ ≤ B)
    (hsmall : 1 / (((d : ℝ) - 1) ^ r) ≤ 1 / (2 * (B + 2)))
    (i j : Fin N) (hij : g.graph.Adj i j) (hforest : (pairBallGraph g.graph i j r).IsAcyclic) :
    ‖g.orientedCavity z i j hij.ne - semicircleRoot z‖ ≤
      (1 + 6 * (B + 2)) * (1 / (((d : ℝ) - 1) ^ r)) := by
  let m := semicircleRoot z
  let p := kestenMcKayTransform d m z
  let t := -m * treeEdgeWeight d
  let δ := 1 / (((d : ℝ) - 1) ^ r)
  let γ := 1 / (2 * (B + 2))
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hBpos : 0 < B + 2 := by linarith [norm_nonneg z]
  have hkpos : 0 < (d : ℝ) - 1 := by linarith
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hm := semicircleRoot_equation z
  have hmim := (semicircleRoot_im_pos hzIm).le
  obtain ⟨hp, hplower, ht⟩ := exterior_reference_bounds d hd m z (semicircleRoot_norm_le_one z) hz B hB
  have ha : ‖g.G z i i - p‖ ≤ δ := by
    have hh := g.exterior_reference_approximation hd r z hz i i
    rw [g.P_diagonal_of_acyclic hd r z m hm hzIm hmim i (pairBall_acyclic_left_diagonal g.graph i j r hforest)] at hh
    exact hh
  have he : ‖g.G z j j - p‖ ≤ δ := by
    have hh := g.exterior_reference_approximation hd r z hz j j
    rw [g.P_diagonal_of_acyclic hd r z m hm hzIm hmim j (pairBall_acyclic_right_diagonal g.graph i j r hforest)] at hh
    exact hh
  have hb : ‖g.G z i j - p * t‖ ≤ δ := by
    have hh := g.exterior_reference_approximation hd r z hz i j
    rw [g.P_adjacent_of_acyclic hd r z m hm hzIm hmim i j hij hforest] at hh
    exact hh
  have hc : ‖g.G z j i - p * t‖ ≤ δ := by
    have hh := g.exterior_reference_approximation hd r z hz j i
    rw [g.P_adjacent_of_acyclic hd r z m hm hzIm hmim j i hij.symm (pairBall_acyclic_swap g.graph i j r hforest)] at hh
    exact hh
  have hden : γ ≤ ‖g.G z j j‖ := by
    have hh := norm_sub_norm_le p (g.G z j j)
    rw [norm_sub_rev] at hh
    have hsmall' : δ ≤ γ := hsmall
    have hsplit : 1 / (B + 2) = 2 * γ := by
      dsimp [γ]
      field_simp
    have hp' : 2 * γ ≤ ‖p‖ := by rw [← hsplit]; exact hplower
    linarith
  have hcnorm : ‖g.G z j i‖ ≤ 1 := by
    have hh := normalizedAdjacency_exterior_entry_bound g.graph d hd (fun v => (g.regular v).le) z hz j i
    exact hh.trans ((div_le_one (by linarith : (0 : ℝ) < d)).mpr (by linarith))
  have hpt : ‖p * t‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul hp ht (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hpt2 : ‖p * t ^ 2‖ ≤ 1 := by
    rw [norm_mul, norm_pow]
    exact (mul_le_mul hp (pow_le_one₀ (norm_nonneg _) ht) (sq_nonneg _) (by norm_num)).trans_eq (one_mul _)
  rw [g.orientedCavity_eq_schur z hzIm i j hij.ne]
  have hh := schur_cavity_error_bound _ _ _ _ p t m δ γ hδ hγ hden ha hb hc he hcnorm hpt hpt2
    (kestenMcKay_cavity_identity d hd m z hm hzIm hmim)
  convert hh using 1
  dsimp [γ, δ]
  field_simp
  ring

/-- Genuine deleted adjacency equals normalized adjacency on the remaining
vertices, with the original normalization d. -/
theorem minorH_eq_normalized_induce (g : RegularGraph N d) (j : Fin N) :
    g.minorH j = normalizedAdjacency (g.graph.induce {v | v ≠ j}) d := by
  rw [normalizedAdjacency_induce_eq_submatrix]
  rfl

/-- The exterior inverse bound applies to every actual cavity minor, including
vertices with cycles. This supplies a uniform exceptional-center bound. -/
theorem orientedCavity_exterior_norm (g : RegularGraph N d) (hd : 3 ≤ d) (z : ℂ)
    (hz : 2 * (d : ℝ) ≤ ‖z‖) (i j : Fin N) (hne : i ≠ j) :
    ‖g.orientedCavity z i j hne‖ ≤ 1 / (d : ℝ) := by
  change ‖green (g.minorH j) z ⟨i, hne⟩ ⟨i, hne⟩‖ ≤ _
  rw [g.minorH_eq_normalized_induce]
  apply normalizedAdjacency_exterior_entry_bound _ d hd _ z hz
  intro v
  convert (induced_degree_le g.graph {x | x ≠ j} v).trans (g.regular v.val).le using 1
  apply congrArg (fun inst => @SimpleGraph.degree _ _ v inst)
  exact Subsingleton.elim _ _

/-- Totalized diagonal cavity entry. The i=j value is zero and is never used
by an oriented edge; it enables honest full finite sums. -/
def cavityEntry (g : RegularGraph N d) (z : ℂ) (i j : Fin N) : ℂ :=
  if h : i ≠ j then g.orientedCavity z i j h else 0

@[simp] theorem cavityEntry_of_adj (g : RegularGraph N d) (z : ℂ) (i j : Fin N)
    (hij : g.graph.Adj i j) : g.cavityEntry z i j = g.orientedCavity z i j hij.ne := by
  simp only [cavityEntry, dif_pos hij.ne]

/-- Exact oriented-edge representation of the actual cavity average Q. -/
theorem Q_eq_neighbor_cavityEntry_sum (g : RegularGraph N d) (z : ℂ) :
    g.Q z = ((N : ℂ) * (d : ℂ))⁻¹ *
      ∑ i, ∑ j, if g.graph.Adj i j then g.cavityEntry z i j else 0 := by
  unfold Q cavityAverage
  simp only [Fintype.card_fin]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∑ i : {i : Fin N // i ≠ j},
        if g.graph.Adj i.val j then green (deletedMatrix (normalizedAdjacency g.graph d) j) z i i else 0) =
        ∑ i : {i : Fin N // i ≠ j}, if g.graph.Adj i.val j then g.cavityEntry z i.val j else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : g.graph.Adj i.val j
      · simp only [h, if_true, cavityEntry, dif_pos i.property]
        rfl
      · simp only [h, if_false]
    _ = ∑ i : Fin N, if g.graph.Adj i j then g.cavityEntry z i j else 0 :=
      sum_deleted_eq_sum_of_zero j (fun i => if g.graph.Adj i j then g.cavityEntry z i j else 0)
        (by dsimp only; rw [if_neg (g.graph.loopless j)])

/-- A full neighbor sum of a constant has exactly d terms. -/
theorem neighbor_sum_constant (g : RegularGraph N d) (i : Fin N) (c : ℂ) :
    (∑ j, if g.graph.Adj i j then c else 0) = (d : ℂ) * c := by
  calc
    _ = ∑ _j ∈ g.graph.neighborFinset i, c := by
      rw [g.graph.neighborFinset_eq_filter, Finset.sum_filter]
    _ = (d : ℂ) * c := by simp [nsmul_eq_mul, g.regular i]

/-- Centered Q is precisely the average of centered neighbor averages. -/
theorem Q_sub_reference_sum (g : RegularGraph N d) (hN : 0 < N) (hd : 0 < d) (z m : ℂ) :
    g.Q z - m = (N : ℂ)⁻¹ *
      ∑ i, (d : ℂ)⁻¹ * ∑ j, if g.graph.Adj i j then g.cavityEntry z i j - m else 0 := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hN)
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hd)
  have hinner : ∀ i, (∑ j, if g.graph.Adj i j then g.cavityEntry z i j - m else 0) =
      (∑ j, if g.graph.Adj i j then g.cavityEntry z i j else 0) - (d : ℂ) * m := by
    intro i
    rw [← g.neighbor_sum_constant i m, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : g.graph.Adj i j <;> simp [h]
  rw [g.Q_eq_neighbor_cavityEntry_sum]
  simp_rw [hinner]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- A normalized neighbor average obeys the common bound on its actual d
neighbors. -/
theorem neighbor_average_norm_le (g : RegularGraph N d) (hd : 0 < d)
    (i : Fin N) (f : Fin N → ℂ) (C : ℝ) (_hC : 0 ≤ C)
    (hf : ∀ j, g.graph.Adj i j → ‖f j‖ ≤ C) :
    ‖(d : ℂ)⁻¹ * ∑ j, if g.graph.Adj i j then f j else 0‖ ≤ C := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hsum : ‖∑ j, if g.graph.Adj i j then f j else 0‖ ≤ (d : ℝ) * C := by
    calc
      _ ≤ ∑ j : Fin N, ‖if g.graph.Adj i j then f j else 0‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin N, if g.graph.Adj i j then C else 0 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases h : g.graph.Adj i j
        · simpa only [h, if_true] using hf j h
        · simp only [h, if_false, norm_zero, le_refl]
      _ = (d : ℝ) * C := by
        rw [← Finset.sum_filter, ← g.graph.neighborFinset_eq_filter]
        simp only [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
          g.regular i, nsmul_eq_mul]
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hdR.le)).trans_eq
    (by field_simp)

/-- Uniform exterior control of a neighbor's centered actual cavity entry. -/
theorem cavityEntry_exterior_error_le_two (g : RegularGraph N d) (hd : 3 ≤ d)
    (z : ℂ) (hz : 2 * (d : ℝ) ≤ ‖z‖) (i j : Fin N) (hij : g.graph.Adj i j) :
    ‖g.cavityEntry z i j - semicircleRoot z‖ ≤ 2 := by
  rw [g.cavityEntry_of_adj z i j hij]
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hfirst := g.orientedCavity_exterior_norm hd z hz i j hij.ne
  have hm := semicircleRoot_norm_le_one z
  exact (norm_sub_le _ _).trans (by linarith [(div_le_one (by linarith : (0 : ℝ) < d)).mpr (by linarith : (1 : ℝ) ≤ d)])

/-- Genuine bounded-exterior anchor for the paper's actual Q. The density of
centers whose radius-R neighborhood fails to be a tree is explicit. -/
theorem Q_exterior_anchor (g : RegularGraph N d) (hN : 0 < N) (hd : 3 ≤ d)
    (r R : ℕ) (hR : r + 1 ≤ R) (z : ℂ) (hzIm : 0 < z.im)
    (hz : 2 * (d : ℝ) ≤ ‖z‖) (B : ℝ) (hB : ‖z‖ ≤ B)
    (hsmall : 1 / (((d : ℝ) - 1) ^ r) ≤ 1 / (2 * (B + 2))) :
    ‖g.Q z - semicircleRoot z‖ ≤
      (1 + 6 * (B + 2)) * (1 / (((d : ℝ) - 1) ^ r)) +
        ((nonTreeCenters g.graph R).card : ℝ) / (N : ℝ) * 2 := by
  let a := (1 + 6 * (B + 2)) * (1 / (((d : ℝ) - 1) ^ r))
  let f := fun i => (d : ℂ)⁻¹ * ∑ j, if g.graph.Adj i j then
    g.cavityEntry z i j - semicircleRoot z else 0
  have hdpos : 0 < d := by omega
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hapos : 0 ≤ a := by
    have hBpos : 0 < B + 2 := by linarith [norm_nonneg z]
    have hkpos : 0 < (d : ℝ) - 1 := by linarith
    dsimp [a]
    positivity
  have hgood : ∀ i, i ∉ nonTreeCenters g.graph R → ‖f i‖ ≤ a := by
    intro i hi
    apply g.neighbor_average_norm_le hdpos i _ a hapos
    intro j hij
    have htree : (graphBall g.graph i R).IsTree := by
      exact not_not.mp (fun hn => hi ((nonTreeCenters_membership g.graph R i).mpr hn))
    rw [g.cavityEntry_of_adj z i j hij]
    exact g.orientedCavity_exterior_error hd r z hzIm hz B hB hsmall i j hij
      (pairBall_acyclic_of_neighbor_ball g.graph i j r R hij hR htree.2)
  have hbad : ∀ i, i ∈ nonTreeCenters g.graph R → ‖f i‖ ≤ a + 2 := by
    intro i _
    exact (g.neighbor_average_norm_le hdpos i _ 2 (by norm_num)
      (fun j hj => g.cavityEntry_exterior_error_le_two hd z hz i j hj)).trans (by linarith)
  have hh := sparse_average_bound f (nonTreeCenters g.graph R) a 2
    (by simpa only [Fintype.card_fin] using hN) hgood hbad
  rw [g.Q_sub_reference_sum hN hdpos z (semicircleRoot z)]
  simpa only [Fintype.card_fin, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_natCast] using hh

/-- All actual cavity minors obey the exterior bound, so does their empirical
average Q, without any tree-like hypothesis. -/
theorem Q_exterior_norm (g : RegularGraph N d) (hN : 0 < N) (hd : 3 ≤ d)
    (z : ℂ) (hz : 2 * (d : ℝ) ≤ ‖z‖) : ‖g.Q z‖ ≤ 1 / (d : ℝ) := by
  have hdpos : 0 < d := by omega
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hdpos
  let f := fun i => (d : ℂ)⁻¹ * ∑ j,
    if g.graph.Adj i j then g.cavityEntry z i j else 0
  have hf : ∀ i, ‖f i‖ ≤ 1 / (d : ℝ) := by
    intro i
    apply g.neighbor_average_norm_le hdpos i _ _ (by positivity)
    intro j hj
    rw [g.cavityEntry_of_adj z i j hj]
    exact g.orientedCavity_exterior_norm hd z hz i j hj.ne
  have hh := sparse_average_bound f ∅ (1 / (d : ℝ)) 0
    (by simpa only [Fintype.card_fin] using hN)
    (fun i _ => hf i) (fun i hi => by simp only [Finset.not_mem_empty] at hi)
  have hQ := g.Q_sub_reference_sum hN hdpos z 0
  simp only [sub_zero] at hQ
  rw [hQ]
  simpa only [Finset.card_empty, Nat.cast_zero, zero_div, zero_mul, add_zero,
    Fintype.card_fin, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast] using hh

/-- Actual exterior entry anchor with boundary parameter Q itself. The only
parameter bound needed for localization follows from the genuine minor average. -/
theorem exterior_Q_reference_approximation (g : RegularGraph N d) (hN : 0 < N)
    (hd : 3 ≤ d) (r : ℕ) (z : ℂ) (hz : 2 * (d : ℝ) ≤ ‖z‖) (i j : Fin N) :
    ‖g.G z i j - g.P r z (g.Q z) i j‖ ≤ 1 / (((d : ℝ) - 1) ^ r) := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hQ : ‖g.Q z‖ ≤ 1 := (g.Q_exterior_norm hN hd z hz).trans
    ((div_le_one (by linarith : (0 : ℝ) < d)).mpr (by linarith))
  exact g.exterior_pair_approximation hd r z (g.Q z) hQ hz i j

end RegularGraph
end

end LocalLaw
