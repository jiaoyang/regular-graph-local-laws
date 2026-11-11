import LocalLaw.FiniteModel

/-!
# Exterior resolvent bounds from diagonal dominance

The large-|z| anchor is derived for genuine finite matrix inverses. Strict row
diagonal dominance proves nonsingularity; a column maximum gives the uniform
inverse-entry bound. Graph support then turns the resolvent row equation into
geometric off-diagonal decay, without an infinite Neumann series.
-/

open scoped BigOperators

namespace LocalLaw

section MatrixExterior
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A zero-diagonal matrix with row absolute sums ≤M has a nonsingular
spectral matrix as soon as |z|>M. No imaginary-part assumption is needed. -/
theorem spectralMatrix_isUnit_exterior (H : Matrix V V ℂ) (z : ℂ) (M : ℝ)
    (hdiag : ∀ i, H i i = 0) (hrow : ∀ i, ∑ k, ‖H i k‖ ≤ M)
    (hgap : M < ‖z‖) : IsUnit (spectralMatrix H z) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  apply det_ne_zero_of_sum_row_lt_diag
  intro i
  have hsum : (∑ k ∈ Finset.univ.erase i, ‖spectralMatrix H z i k‖) = ∑ k, ‖H i k‖ := by
    calc
      _ = ∑ k ∈ Finset.univ.erase i, ‖H i k‖ := by
        apply Finset.sum_congr rfl
        intro k hk
        have hki := (Finset.mem_erase.mp hk).1
        simp [spectralMatrix, Matrix.one_apply, hki.symm]
      _ = ∑ k, ‖H i k‖ := by
        simpa only [hdiag i, norm_zero, add_zero] using
          (Finset.sum_erase_add Finset.univ (fun k => ‖H i k‖) (Finset.mem_univ i))
  rw [hsum]
  have hdiagA : spectralMatrix H z i i = -z := by simp [spectralMatrix, hdiag]
  rw [hdiagA, norm_neg]
  exact (hrow i).trans_lt hgap

/-- A strict row-sum spectral gap proves nonsingularity even when H has
nonzero diagonal entries, as needed for finite boundary-self-energy models. -/
theorem spectralMatrix_isUnit_of_row_gap (H : Matrix V V ℂ) (z : ℂ) (M : ℝ)
    (hrow : ∀ i, ∑ k, ‖H i k‖ ≤ M) (hgap : M < ‖z‖) :
    IsUnit (spectralMatrix H z) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  apply det_ne_zero_of_sum_row_lt_diag
  intro i
  have hoff : (∑ k ∈ Finset.univ.erase i, ‖spectralMatrix H z i k‖) =
      ∑ k ∈ Finset.univ.erase i, ‖H i k‖ := by
    apply Finset.sum_congr rfl
    intro k hk
    have hki := (Finset.mem_erase.mp hk).1
    simp [spectralMatrix, Matrix.one_apply, hki.symm]
  rw [hoff]
  have hsum := Finset.sum_erase_add Finset.univ (fun k => ‖H i k‖) (Finset.mem_univ i)
  have hlow : ‖z‖ - ‖H i i‖ ≤ ‖spectralMatrix H z i i‖ := by
    simpa only [spectralMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one, norm_sub_rev] using norm_sub_norm_le z (H i i)
  linarith [hrow i]

/-- The entrywise resolvent equation follows from the proved matrix inverse. -/
theorem exterior_green_row_identity (H : Matrix V V ℂ) (z : ℂ)
    (hunit : IsUnit (spectralMatrix H z)) (i j : V) :
    z * green H z i j = (∑ k, H i k * green H z k j) - if i = j then 1 else 0 := by
  have hinv := Matrix.mul_nonsing_inv (spectralMatrix H z)
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
  have hid : H * green H z - z • green H z = 1 := by
    simpa only [spectralMatrix, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] using hinv
  have he := congrFun (congrFun hid i) j
  change (∑ k, H i k * green H z k j) - z * green H z i j = if i = j then 1 else 0 at he
  linear_combination -he

/-- A column maximum turns row-sum control into an entrywise inverse bound. -/
theorem exterior_green_entry_bound (H : Matrix V V ℂ) (z : ℂ) (M : ℝ)
    (hrow : ∀ i, ∑ k, ‖H i k‖ ≤ M) (hgap : M < ‖z‖)
    (hunit : IsUnit (spectralMatrix H z)) (i j : V) :
    ‖green H z i j‖ ≤ 1 / (‖z‖ - M) := by
  obtain ⟨a, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun k => ‖green H z k j‖) ⟨i, Finset.mem_univ i⟩
  let Γ := ‖green H z a j‖
  have hΓ : 0 ≤ Γ := norm_nonneg _
  have hdelta : ‖(if a = j then (1 : ℂ) else 0)‖ ≤ 1 := by
    split_ifs <;> norm_num
  have hmain : ‖z‖ * Γ ≤ M * Γ + 1 := by
    calc
      ‖z‖ * Γ = ‖z * green H z a j‖ := (norm_mul _ _).symm
      _ = ‖(∑ k, H a k * green H z k j) - if a = j then 1 else 0‖ :=
        congrArg norm (exterior_green_row_identity H z hunit a j)
      _ ≤ ‖∑ k, H a k * green H z k j‖ + ‖if a = j then (1 : ℂ) else 0‖ := norm_sub_le _ _
      _ ≤ (∑ k, ‖H a k * green H z k j‖) + 1 := add_le_add (norm_sum_le _ _) hdelta
      _ ≤ (∑ k, ‖H a k‖ * Γ) + 1 := by
        apply add_le_add_right
        apply Finset.sum_le_sum
        intro k _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hmax k (Finset.mem_univ k)) (norm_nonneg _)
      _ = (∑ k, ‖H a k‖) * Γ + 1 := by rw [Finset.sum_mul]
      _ ≤ M * Γ + 1 := add_le_add_right (mul_le_mul_of_nonneg_right (hrow a) hΓ) _
  have hpos : 0 < ‖z‖ - M := sub_pos.mpr hgap
  have hbound : Γ ≤ 1 / (‖z‖ - M) := by
    apply (le_div_iff₀ hpos).mpr
    nlinarith [hmain]
  exact (hmax i (Finset.mem_univ i)).trans hbound

end MatrixExterior

/-- A lower bound for every walk length is exactly a lower bound for extended
graph distance, including disconnected pairs. -/
theorem graph_edist_lower_of_walk_lengths {V : Type*} (G : SimpleGraph V) (i j : V) (r : ℕ)
    (h : ∀ p : G.Walk i j, r ≤ p.length) : (r : ℕ∞) ≤ G.edist i j := by
  unfold SimpleGraph.edist
  apply le_iInf
  intro p
  exact ENat.coe_le_coe.mpr (h p)

section GraphDecay
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Resolvent row recursion gives geometric decay with graph distance. The
matrix is supported on graph edges and has row absolute sums at most M. -/
theorem exterior_green_graph_decay (G : SimpleGraph V) (H : Matrix V V ℂ)
    (z : ℂ) (M : ℝ) (hM : 0 ≤ M) (hrow : ∀ i, ∑ k, ‖H i k‖ ≤ M)
    (hsupport : ∀ i k, ¬G.Adj i k → H i k = 0) (hgap : M < ‖z‖)
    (hunit : IsUnit (spectralMatrix H z)) (r : ℕ) (i j : V)
    (hdist : (r : ℕ∞) ≤ G.edist i j) :
    ‖green H z i j‖ ≤ (M / ‖z‖) ^ r * (1 / (‖z‖ - M)) := by
  have hzpos : 0 < ‖z‖ := hM.trans_lt hgap
  have hgapPos : 0 < ‖z‖ - M := sub_pos.mpr hgap
  induction r generalizing i with
  | zero => simpa using exterior_green_entry_bound H z M hrow hgap hunit i j
  | succ r ih =>
      have hne : i ≠ j := by
        intro heq
        subst i
        have hh := ENat.coe_le_coe.mp (hdist.trans (SimpleGraph.edist_le (SimpleGraph.Walk.nil : G.Walk j j)))
        simp only [SimpleGraph.Walk.length_nil] at hh
        omega
      have hid := exterior_green_row_identity H z hunit i j
      rw [if_neg hne, sub_zero] at hid
      have hfactor : 0 ≤ (M / ‖z‖) ^ r * (1 / (‖z‖ - M)) := by positivity
      have hmain : ‖z‖ * ‖green H z i j‖ ≤ M * ((M / ‖z‖) ^ r * (1 / (‖z‖ - M))) := by
        calc
          ‖z‖ * ‖green H z i j‖ = ‖z * green H z i j‖ := (norm_mul _ _).symm
          _ = ‖∑ k, H i k * green H z k j‖ := congrArg norm hid
          _ ≤ ∑ k, ‖H i k‖ * ‖green H z k j‖ := by
            simpa only [norm_mul] using norm_sum_le Finset.univ (fun k => H i k * green H z k j)
          _ ≤ ∑ k, ‖H i k‖ * ((M / ‖z‖) ^ r * (1 / (‖z‖ - M))) := by
            apply Finset.sum_le_sum
            intro k _
            by_cases hik : G.Adj i k
            · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
              apply ih
              apply graph_edist_lower_of_walk_lengths G k j r
              intro p
              have hh := ENat.coe_le_coe.mp (hdist.trans (SimpleGraph.edist_le (p.cons hik)))
              simp only [SimpleGraph.Walk.length_cons] at hh
              omega
            · simp [hsupport i k hik]
          _ = (∑ k, ‖H i k‖) * ((M / ‖z‖) ^ r * (1 / (‖z‖ - M))) := by rw [Finset.sum_mul]
          _ ≤ M * ((M / ‖z‖) ^ r * (1 / (‖z‖ - M))) :=
            mul_le_mul_of_nonneg_right (hrow i) hfactor
      apply (mul_le_mul_left hzpos).mp
      convert hmain using 1
      rw [pow_succ]
      field_simp
      ring

/-- Different graph components have exactly zero resolvent coupling. The proof
uses the finite-distance estimates for every radius and a geometric limit. -/
theorem exterior_green_eq_zero_of_not_reachable (G : SimpleGraph V) (H : Matrix V V ℂ)
    (z : ℂ) (M : ℝ) (hM : 0 ≤ M) (hrow : ∀ i, ∑ k, ‖H i k‖ ≤ M)
    (hsupport : ∀ i k, ¬G.Adj i k → H i k = 0) (hgap : M < ‖z‖)
    (hunit : IsUnit (spectralMatrix H z)) (i j : V) (hnot : ¬G.Reachable i j) :
    green H z i j = 0 := by
  have hzpos : 0 < ‖z‖ := hM.trans_lt hgap
  have hq0 : 0 ≤ M / ‖z‖ := div_nonneg hM (norm_nonneg _)
  have hq1 : M / ‖z‖ < 1 := (div_lt_one hzpos).mpr hgap
  have hlimit : Filter.Tendsto
      (fun r : ℕ => (M / ‖z‖) ^ r * (1 / (‖z‖ - M))) Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (1 / (‖z‖ - M))
  have hzero : ‖green H z i j‖ ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlimit (fun r =>
      exterior_green_graph_decay G H z M hM hrow hsupport hgap hunit r i j (by
        rw [SimpleGraph.edist_eq_top_of_not_reachable hnot]
        exact le_top))
  exact norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _))

end GraphDecay

noncomputable section
local instance exteriorDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section NormalizedGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem normalizedAdjacency_zero_diagonal (G : SimpleGraph V) (d : ℕ) (i : V) :
    normalizedAdjacency G d i i = 0 := by
  simp [normalizedAdjacency, Matrix.smul_apply, SimpleGraph.adjMatrix_apply]

omit [Fintype V] [DecidableEq V] in
theorem normalizedAdjacency_eq_zero_of_not_adj (G : SimpleGraph V) (d : ℕ) (i k : V)
    (h : ¬G.Adj i k) : normalizedAdjacency G d i k = 0 := by
  simp [normalizedAdjacency, Matrix.smul_apply, SimpleGraph.adjMatrix_apply, h]

omit [Fintype V] [DecidableEq V] in
theorem normalizedAdjacency_norm (G : SimpleGraph V) (d : ℕ) (i k : V) :
    ‖normalizedAdjacency G d i k‖ =
      if G.Adj i k then (Real.sqrt ((d : ℝ) - 1))⁻¹ else 0 := by
  have hs : 0 ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  by_cases h : G.Adj i k
  · simp [normalizedAdjacency, Matrix.smul_apply, SimpleGraph.adjMatrix_apply, h,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
  · simp [normalizedAdjacency, Matrix.smul_apply, SimpleGraph.adjMatrix_apply, h]

omit [DecidableEq V] in
/-- The row absolute sum of normalized adjacency is exactly the degree divided
by sqrt(d-1), for the actual finite graph. -/
theorem normalizedAdjacency_row_sum (G : SimpleGraph V) (d : ℕ) (i : V) :
    (∑ k, ‖normalizedAdjacency G d i k‖) =
      (G.degree i : ℝ) / Real.sqrt ((d : ℝ) - 1) := by
  calc
    (∑ k, ‖normalizedAdjacency G d i k‖) =
        ∑ _k ∈ G.neighborFinset i, (Real.sqrt ((d : ℝ) - 1))⁻¹ := by
      rw [G.neighborFinset_eq_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k _
      exact normalizedAdjacency_norm G d i k
    _ = (G.degree i : ℝ) / Real.sqrt ((d : ℝ) - 1) := by
      simp [nsmul_eq_mul, div_eq_mul_inv]

/-- Explicit large-|z| constants for d≥3. -/
theorem normalized_exterior_constants (d : ℕ) (hd : 3 ≤ d) (z : ℂ)
    (hz : 2 * (d : ℝ) ≤ ‖z‖) :
    let M := (d : ℝ) / Real.sqrt ((d : ℝ) - 1)
    0 ≤ M ∧ M < ‖z‖ ∧ (d : ℝ) ≤ ‖z‖ - M ∧
      M / ‖z‖ ≤ 1 / (2 * Real.sqrt ((d : ℝ) - 1)) := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hs : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  have hsone : 1 ≤ Real.sqrt ((d : ℝ) - 1) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ d - 1 by linarith)
    simpa only [Real.sqrt_one] using h
  have hMle : (d : ℝ) / Real.sqrt ((d : ℝ) - 1) ≤ d := by
    apply (div_le_iff₀ hs).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsone hdpos.le]
  have hzpos : 0 < ‖z‖ := by linarith
  dsimp only
  refine ⟨by positivity, by linarith, by linarith, ?_⟩
  apply (div_le_div_iff₀ hzpos (by positivity : 0 < 2 * Real.sqrt ((d : ℝ) - 1))).mpr
  have heq : ((d : ℝ) / Real.sqrt ((d : ℝ) - 1)) * (2 * Real.sqrt ((d : ℝ) - 1)) = 2 * d := by
    field_simp
    ring
  simpa only [heq, one_mul] using hz

/-- The actual normalized finite graph resolvent exists throughout the exterior
domain, including real spectral parameters there. -/
theorem normalizedAdjacency_exterior_isUnit (G : SimpleGraph V) (d : ℕ) (hd : 3 ≤ d)
    (hdeg : ∀ i, G.degree i ≤ d) (z : ℂ) (hz : 2 * (d : ℝ) ≤ ‖z‖) :
    IsUnit (spectralMatrix (normalizedAdjacency G d) z) := by
  obtain ⟨hM, hgap, _, _⟩ := normalized_exterior_constants d hd z hz
  apply spectralMatrix_isUnit_exterior _ _ _ (normalizedAdjacency_zero_diagonal G d) _ hgap
  intro i
  rw [normalizedAdjacency_row_sum]
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hdeg i)) (Real.sqrt_nonneg _)

/-- Uniform entry bound in equation (4.21), with the genuine finite inverse. -/
theorem normalizedAdjacency_exterior_entry_bound (G : SimpleGraph V) (d : ℕ) (hd : 3 ≤ d)
    (hdeg : ∀ i, G.degree i ≤ d) (z : ℂ) (hz : 2 * (d : ℝ) ≤ ‖z‖) (i j : V) :
    ‖green (normalizedAdjacency G d) z i j‖ ≤ 1 / (d : ℝ) := by
  obtain ⟨hM, hgap, hden, _⟩ := normalized_exterior_constants d hd z hz
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hrow : ∀ i, ∑ k, ‖normalizedAdjacency G d i k‖ ≤
      (d : ℝ) / Real.sqrt ((d : ℝ) - 1) := by
    intro i
    rw [normalizedAdjacency_row_sum]
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hdeg i)) (Real.sqrt_nonneg _)
  exact (exterior_green_entry_bound _ z _ hrow hgap
    (normalizedAdjacency_exterior_isUnit G d hd hdeg z hz) i j).trans
      (one_div_le_one_div_of_le hdpos hden)

/-- A stronger integer-distance version of the exterior decay estimate:
(2 sqrt(d-1))^(-r)/d whenever the graph distance is at least r. -/
theorem normalizedAdjacency_exterior_decay_strong (G : SimpleGraph V) (d : ℕ) (hd : 3 ≤ d)
    (hdeg : ∀ i, G.degree i ≤ d) (z : ℂ) (hz : 2 * (d : ℝ) ≤ ‖z‖)
    (r : ℕ) (i j : V) (hdist : (r : ℕ∞) ≤ G.edist i j) :
    ‖green (normalizedAdjacency G d) z i j‖ ≤
      (1 / (2 * Real.sqrt ((d : ℝ) - 1))) ^ r / (d : ℝ) := by
  obtain ⟨hM, hgap, hden, hratio⟩ := normalized_exterior_constants d hd z hz
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hrow : ∀ i, ∑ k, ‖normalizedAdjacency G d i k‖ ≤
      (d : ℝ) / Real.sqrt ((d : ℝ) - 1) := by
    intro i
    rw [normalizedAdjacency_row_sum]
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hdeg i)) (Real.sqrt_nonneg _)
  have hdecay := exterior_green_graph_decay G (normalizedAdjacency G d) z _ hM hrow
    (normalizedAdjacency_eq_zero_of_not_adj G d) hgap
    (normalizedAdjacency_exterior_isUnit G d hd hdeg z hz) r i j hdist
  calc
    ‖green (normalizedAdjacency G d) z i j‖ ≤ _ := hdecay
    _ ≤ (1 / (2 * Real.sqrt ((d : ℝ) - 1))) ^ r * (1 / (d : ℝ)) := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (div_nonneg hM (norm_nonneg _)) hratio r
      · exact one_div_le_one_div_of_le hdpos hden
      · exact div_nonneg (by norm_num) (sub_nonneg.mpr hgap.le)
      · positivity
    _ = (1 / (2 * Real.sqrt ((d : ℝ) - 1))) ^ r / (d : ℝ) := by ring

/-- Equation (4.21) in square-root power form. -/
theorem normalizedAdjacency_exterior_decay (G : SimpleGraph V) (d : ℕ) (hd : 3 ≤ d)
    (hdeg : ∀ i, G.degree i ≤ d) (z : ℂ) (hz : 2 * (d : ℝ) ≤ ‖z‖)
    (r : ℕ) (i j : V) (hdist : (r : ℕ∞) ≤ G.edist i j) :
    ‖green (normalizedAdjacency G d) z i j‖ ≤ ((Real.sqrt ((d : ℝ) - 1))⁻¹) ^ r := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hs : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  have hratio : 1 / (2 * Real.sqrt ((d : ℝ) - 1)) ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹ := by
    rw [← one_div]
    exact one_div_le_one_div_of_le hs (by linarith)
  have hinvd : (1 : ℝ) / d ≤ 1 := (div_le_one hdpos).mpr (by linarith)
  calc
    ‖green (normalizedAdjacency G d) z i j‖ ≤ _ :=
      normalizedAdjacency_exterior_decay_strong G d hd hdeg z hz r i j hdist
    _ = (1 / (2 * Real.sqrt ((d : ℝ) - 1))) ^ r * (1 / (d : ℝ)) := by ring
    _ ≤ ((Real.sqrt ((d : ℝ) - 1))⁻¹) ^ r * 1 := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (by positivity) hratio r
      · exact hinvd
      · positivity
      · positivity
    _ = ((Real.sqrt ((d : ℝ) - 1))⁻¹) ^ r := mul_one _

/-- Equality of the integer square-root power with the customary real power. -/
theorem sqrt_inverse_pow_eq_rpow {x : ℝ} (hx : 0 ≤ x) (r : ℕ) :
    (Real.sqrt x)⁻¹ ^ r = x ^ (-(r : ℝ) / 2) := by
  rw [inv_pow, Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hx,
    ← Real.rpow_neg hx]
  congr 1
  ring

/-- The paper's exact graph-distance form of the exterior decay estimate.
Disconnected pairs use mathlib's natural-distance value zero, giving the valid
bound one; the stronger extended-distance estimates above remain available. -/
theorem normalizedAdjacency_exterior_distance_bound (G : SimpleGraph V) (d : ℕ) (hd : 3 ≤ d)
    (hdeg : ∀ i, G.degree i ≤ d) (z : ℂ) (hz : 2 * (d : ℝ) ≤ ‖z‖) (i j : V) :
    ‖green (normalizedAdjacency G d) z i j‖ ≤
      ((d : ℝ) - 1) ^ (-(G.dist i j : ℝ) / 2) := by
  have hdist : (G.dist i j : ℕ∞) ≤ G.edist i j := ENat.coe_toNat_le_self _
  have h := normalizedAdjacency_exterior_decay G d hd hdeg z hz (G.dist i j) i j hdist
  rw [sqrt_inverse_pow_eq_rpow (by have : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd; linarith)] at h
  exact h

/-- The disconnected case of equation (4.21) has an exactly zero entry. -/
theorem normalizedAdjacency_exterior_eq_zero_of_not_reachable
    (G : SimpleGraph V) (d : ℕ) (hd : 3 ≤ d) (hdeg : ∀ i, G.degree i ≤ d)
    (z : ℂ) (hz : 2 * (d : ℝ) ≤ ‖z‖) (i j : V) (hnot : ¬G.Reachable i j) :
    green (normalizedAdjacency G d) z i j = 0 := by
  obtain ⟨hM, hgap, _, _⟩ := normalized_exterior_constants d hd z hz
  apply exterior_green_eq_zero_of_not_reachable G _ z _ hM _
    (normalizedAdjacency_eq_zero_of_not_adj G d) hgap
    (normalizedAdjacency_exterior_isUnit G d hd hdeg z hz) i j hnot
  intro k
  rw [normalizedAdjacency_row_sum]
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hdeg k)) (Real.sqrt_nonneg _)

end NormalizedGraph
end

end LocalLaw
