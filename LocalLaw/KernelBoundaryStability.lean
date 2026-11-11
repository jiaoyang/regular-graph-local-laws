import LocalLaw.FiniteModel

/-!
# Boundary perturbations controlled by a positive reference kernel

This is the analytic perturbation argument behind Appendix B, (B.6)--(B.10).
The geometric kernel-convolution estimate is explicit; the nonlinear maximum
inequality and resulting boundary sensitivity are proved from genuine inverse
identities. Invertibility is an input here and is independently established
for the actual Herglotz boundary parameters by BoundaryResolvent/Resolvent.
-/

open scoped BigOperators

namespace LocalLaw

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Weighted products inherit a kernel convolution bound. -/
theorem diagonal_kernel_product_bound (A B : Matrix V V ℂ) (d : V → ℝ)
    (K L : V → V → ℝ) (a b : ℝ) (hd : ∀ k, 0 ≤ d k)
    (hK : ∀ i j, 0 ≤ K i j)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, ‖A i j‖ ≤ a * K i j)
    (hB : ∀ i j, ‖B i j‖ ≤ b * L i j)
    (i j : V) (R : ℝ) (hconv : (∑ k, d k * K i k * L k j) ≤ R) :
    ‖(A * Matrix.diagonal (fun k => (d k : ℂ)) * B) i j‖ ≤ a * b * R := by
  calc
    _ ≤ ∑ k, ‖(A i k * (d k : ℂ)) * B k j‖ := by
      change ‖∑ k, (A * Matrix.diagonal (fun k => (d k : ℂ))) i k * B k j‖ ≤ _
      simp only [Matrix.mul_diagonal]
      exact norm_sum_le Finset.univ _
    _ = ∑ k, ‖A i k‖ * d k * ‖B k j‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd _)]
    _ ≤ ∑ k, (a * b) * (d k * K i k * L k j) := by
      apply Finset.sum_le_sum
      intro k _
      calc
        ‖A i k‖ * d k * ‖B k j‖ ≤ (a * K i k) * d k * ‖B k j‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hA i k) (hd k)) (norm_nonneg _)
        _ ≤ (a * K i k) * d k * (b * L k j) :=
          mul_le_mul_of_nonneg_left (hB k j) (mul_nonneg (mul_nonneg ha (hK i k)) (hd k))
        _ = (a * b) * (d k * K i k * L k j) := by ring
    _ = (a * b) * ∑ k, d k * K i k * L k j := (Finset.mul_sum ..).symm
    _ ≤ a * b * R := mul_le_mul_of_nonneg_left hconv (mul_nonneg ha hb)

/-- The reference-side resolvent identity, with the order of the three
matrix factors chosen for the perturbation feedback argument. -/
theorem boundary_reference_resolvent_identity (H D : Matrix V V ℂ) (q m z : ℂ)
    (hq : IsUnit (boundaryMatrix H D q z)) (hm : IsUnit (boundaryMatrix H D m z)) :
    boundaryGreen H D q z - boundaryGreen H D m z =
      (q - m) • (boundaryGreen H D m z * D * boundaryGreen H D q z) := by
  have h := boundaryGreen_sub H D m q z hm hq
  calc
    boundaryGreen H D q z - boundaryGreen H D m z =
        -(boundaryGreen H D m z - boundaryGreen H D q z) := by abel
    _ = -((m - q) • (boundaryGreen H D m z * D * boundaryGreen H D q z)) := by rw [h]
    _ = (q - m) • (boundaryGreen H D m z * D * boundaryGreen H D q z) := by
      rw [← neg_smul, neg_sub]

/-- Positive-kernel boundary stability, derived by an attained finite weighted
maximum. B is the companion kernel (1+distance)*K in the paper; Ddiam bounds
its ratio to K. No final maximum inequality or Lipschitz conclusion is assumed. -/
theorem boundary_kernel_stability (H : Matrix V V ℂ) (d : V → ℝ) (q m z : ℂ)
    (hq : IsUnit (boundaryMatrix H (Matrix.diagonal (fun k => (d k : ℂ))) q z))
    (hm : IsUnit (boundaryMatrix H (Matrix.diagonal (fun k => (d k : ℂ))) m z))
    (K B : V → V → ℝ) (C C₀ Ddiam : ℝ)
    (hd : ∀ k, 0 ≤ d k) (hK : ∀ i j, 0 ≤ K i j) (hB : ∀ i j, 0 < B i j)
    (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hDdiam : 0 ≤ Ddiam)
    (reference : ∀ i j,
      ‖boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) m z i j‖ ≤ C * K i j)
    (companion : ∀ i j, B i j ≤ Ddiam * K i j)
    (convolution : ∀ i j, (∑ k, d k * K i k * K k j) ≤ C₀ * B i j)
    (small : ‖q - m‖ * C * C₀ * Ddiam ≤ 1 / 2) (i j : V) :
    ‖(boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) q z -
        boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) m z) i j‖
        ≤ 2 * ‖q - m‖ * C ^ 2 * C₀ * B i j ∧
    ‖boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) q z i j‖ ≤ 2 * C * K i j := by
  classical
  letI : Nonempty V := ⟨i⟩
  let D := Matrix.diagonal (fun k => (d k : ℂ))
  let P₀ := boundaryGreen H D m z
  let Pq := boundaryGreen H D q z
  let X := Pq - P₀
  obtain ⟨p, hp⟩ := Finite.exists_max (fun ij : V × V => ‖X ij.1 ij.2‖ / B ij.1 ij.2)
  let Γ := ‖X p.1 p.2‖ / B p.1 p.2
  have hΓ : ∀ k l, ‖X k l‖ ≤ Γ * B k l := by
    intro k l
    exact (div_le_iff₀ (hB k l)).mp (hp (k, l))
  have hΓnonneg : 0 ≤ Γ := div_nonneg (norm_nonneg _) (hB p.1 p.2).le
  have hmaxeq : Γ * B p.1 p.2 = ‖X p.1 p.2‖ := by
    dsimp only [Γ]
    exact div_mul_cancel₀ _ (ne_of_gt (hB p.1 p.2))
  have hconvB : ∀ k l, (∑ x, d x * K k x * B x l) ≤ Ddiam * C₀ * B k l := by
    intro k l
    calc
      (∑ x, d x * K k x * B x l) ≤ ∑ x, Ddiam * (d x * K k x * K x l) := by
        apply Finset.sum_le_sum
        intro x _
        have h := mul_le_mul_of_nonneg_left (companion x l) (mul_nonneg (hd x) (hK k x))
        nlinarith
      _ = Ddiam * ∑ x, d x * K k x * K x l := (Finset.mul_sum ..).symm
      _ ≤ Ddiam * (C₀ * B k l) := mul_le_mul_of_nonneg_left (convolution k l) hDdiam
      _ = Ddiam * C₀ * B k l := by ring
  have hforce : ∀ k l, ‖(P₀ * D * P₀) k l‖ ≤ C ^ 2 * C₀ * B k l := by
    intro k l
    have h := diagonal_kernel_product_bound P₀ P₀ d K K C C hd hK hC hC
      reference reference k l (C₀ * B k l) (convolution k l)
    convert h using 1
    ring
  have hfeedback : ∀ k l, ‖(P₀ * D * X) k l‖ ≤ C * C₀ * Ddiam * Γ * B k l := by
    intro k l
    have h := diagonal_kernel_product_bound P₀ X d K B C Γ hd hK hC hΓnonneg reference hΓ k l
      (Ddiam * C₀ * B k l) (hconvB k l)
    convert h using 1
    ring
  have hplus : P₀ + X = Pq := by dsimp only [X]; abel
  have hidentity : X = (q - m) • (P₀ * D * (P₀ + X)) := by
    rw [hplus]
    exact boundary_reference_resolvent_identity H D q m z hq hm
  have hentry : ∀ k l, ‖X k l‖ ≤
      ‖q - m‖ * (C ^ 2 * C₀ * B k l + C * C₀ * Ddiam * Γ * B k l) := by
    intro k l
    have hid := congrArg (fun M : Matrix V V ℂ => M k l) hidentity
    change X k l = (q - m) * (P₀ * D * (P₀ + X)) k l at hid
    rw [Matrix.mul_add] at hid
    change X k l = (q - m) * ((P₀ * D * P₀) k l + (P₀ * D * X) k l) at hid
    rw [hid, norm_mul]
    exact mul_le_mul_of_nonneg_left
      ((norm_add_le _ _).trans (add_le_add (hforce k l) (hfeedback k l))) (norm_nonneg _)
  have hscalar : Γ ≤ ‖q - m‖ * C ^ 2 * C₀ + ‖q - m‖ * C * C₀ * Ddiam * Γ := by
    apply (mul_le_mul_right (hB p.1 p.2)).mp
    calc
      Γ * B p.1 p.2 = ‖X p.1 p.2‖ := hmaxeq
      _ ≤ _ := hentry p.1 p.2
      _ = (‖q - m‖ * C ^ 2 * C₀ + ‖q - m‖ * C * C₀ * Ddiam * Γ) * B p.1 p.2 := by ring
  have hsmallΓ := mul_le_mul_of_nonneg_right small hΓnonneg
  have habsorb : Γ ≤ 2 * ‖q - m‖ * C ^ 2 * C₀ := by nlinarith
  have hdiff : ‖X i j‖ ≤ 2 * ‖q - m‖ * C ^ 2 * C₀ * B i j :=
    (hΓ i j).trans (mul_le_mul_of_nonneg_right habsorb (hB i j).le)
  refine ⟨hdiff, ?_⟩
  have hconstant : 2 * ‖q - m‖ * C ^ 2 * C₀ * Ddiam ≤ C := by
    have h := mul_le_mul_of_nonneg_left small (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC)
    nlinarith
  have hcap : ‖X i j‖ ≤ C * K i j := by
    calc
      ‖X i j‖ ≤ 2 * ‖q - m‖ * C ^ 2 * C₀ * B i j := hdiff
      _ ≤ 2 * ‖q - m‖ * C ^ 2 * C₀ * (Ddiam * K i j) :=
        mul_le_mul_of_nonneg_left (companion i j) (by positivity)
      _ ≤ C * K i j := by nlinarith [mul_le_mul_of_nonneg_right hconstant (hK i j)]
  have hsum : Pq = P₀ + X := hplus.symm
  change ‖Pq i j‖ ≤ _
  rw [hsum]
  exact (norm_add_le (P₀ i j) (X i j)).trans (by nlinarith [reference i j])

/-- Two perturbed weights inherit the mixed-kernel Lipschitz bound. This is
Remark 2.13's analytic content, with graph convolution still explicit. -/
theorem boundary_kernel_two_weight_lipschitz (H : Matrix V V ℂ) (d : V → ℝ)
    (q v m z : ℂ)
    (hq : IsUnit (boundaryMatrix H (Matrix.diagonal (fun k => (d k : ℂ))) q z))
    (hv : IsUnit (boundaryMatrix H (Matrix.diagonal (fun k => (d k : ℂ))) v z))
    (hm : IsUnit (boundaryMatrix H (Matrix.diagonal (fun k => (d k : ℂ))) m z))
    (K B : V → V → ℝ) (C C₀ Ddiam : ℝ)
    (hd : ∀ k, 0 ≤ d k) (hK : ∀ i j, 0 ≤ K i j) (hB : ∀ i j, 0 < B i j)
    (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hDdiam : 0 ≤ Ddiam)
    (reference : ∀ i j,
      ‖boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) m z i j‖ ≤ C * K i j)
    (companion : ∀ i j, B i j ≤ Ddiam * K i j)
    (convolution : ∀ i j, (∑ k, d k * K i k * K k j) ≤ C₀ * B i j)
    (smallq : ‖q - m‖ * C * C₀ * Ddiam ≤ 1 / 2)
    (smallv : ‖v - m‖ * C * C₀ * Ddiam ≤ 1 / 2) (i j : V) :
    ‖boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) q z i j -
      boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) v z i j‖ ≤
        4 * C ^ 2 * C₀ * B i j * dist q v := by
  let D := Matrix.diagonal (fun k => (d k : ℂ))
  let Pq := boundaryGreen H D q z
  let Pv := boundaryGreen H D v z
  have hqbound : ∀ k l, ‖Pq k l‖ ≤ (2 * C) * K k l := fun k l =>
    (boundary_kernel_stability H d q m z hq hm K B C C₀ Ddiam hd hK hB hC hC₀ hDdiam
      reference companion convolution smallq k l).2
  have hvbound : ∀ k l, ‖Pv k l‖ ≤ (2 * C) * K k l := fun k l =>
    (boundary_kernel_stability H d v m z hv hm K B C C₀ Ddiam hd hK hB hC hC₀ hDdiam
      reference companion convolution smallv k l).2
  have hproduct := diagonal_kernel_product_bound Pq Pv d K K (2 * C) (2 * C)
    hd hK (by positivity) (by positivity) hqbound hvbound i j (C₀ * B i j) (convolution i j)
  have hid := congrArg (fun M : Matrix V V ℂ => M i j) (boundaryGreen_sub H D q v z hq hv)
  change Pq i j - Pv i j = (q - v) * (Pq * D * Pv) i j at hid
  rw [hid, norm_mul]
  calc
    _ ≤ ‖q - v‖ * ((2 * C) * (2 * C) * (C₀ * B i j)) :=
      mul_le_mul_of_nonneg_left hproduct (norm_nonneg _)
    _ = 4 * C ^ 2 * C₀ * B i j * dist q v := by rw [dist_eq_norm]; ring

/-- A uniform bound on the explicit companion kernel gives an order-one
boundary Lipschitz constant, rather than assuming that final constant. -/
theorem boundary_kernel_uniform_lipschitz (H : Matrix V V ℂ) (d : V → ℝ)
    (q v m z : ℂ)
    (hq : IsUnit (boundaryMatrix H (Matrix.diagonal (fun k => (d k : ℂ))) q z))
    (hv : IsUnit (boundaryMatrix H (Matrix.diagonal (fun k => (d k : ℂ))) v z))
    (hm : IsUnit (boundaryMatrix H (Matrix.diagonal (fun k => (d k : ℂ))) m z))
    (K B : V → V → ℝ) (C C₀ Ddiam Bmax : ℝ)
    (hd : ∀ k, 0 ≤ d k) (hK : ∀ i j, 0 ≤ K i j) (hB : ∀ i j, 0 < B i j)
    (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hDdiam : 0 ≤ Ddiam)
    (reference : ∀ i j,
      ‖boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) m z i j‖ ≤ C * K i j)
    (companion : ∀ i j, B i j ≤ Ddiam * K i j)
    (convolution : ∀ i j, (∑ k, d k * K i k * K k j) ≤ C₀ * B i j)
    (bound : ∀ i j, B i j ≤ Bmax)
    (smallq : ‖q - m‖ * C * C₀ * Ddiam ≤ 1 / 2)
    (smallv : ‖v - m‖ * C * C₀ * Ddiam ≤ 1 / 2) (i j : V) :
    ‖boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) q z i j -
      boundaryGreen H (Matrix.diagonal (fun k => (d k : ℂ))) v z i j‖ ≤
        (4 * C ^ 2 * C₀ * Bmax) * dist q v := by
  have h := boundary_kernel_two_weight_lipschitz H d q v m z hq hv hm K B C C₀ Ddiam
    hd hK hB hC hC₀ hDdiam reference companion convolution smallq smallv i j
  apply h.trans
  have hmul := mul_le_mul_of_nonneg_left (bound i j) (by positivity : 0 ≤ 4 * C ^ 2 * C₀)
  exact mul_le_mul_of_nonneg_right hmul (dist_nonneg)

end LocalLaw
