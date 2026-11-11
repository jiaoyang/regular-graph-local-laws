import LocalLaw.FullSwitchIndicator
import LocalLaw.SupportedRetainedInverse
import LocalLaw.SourceCavityTreeIdentity

/-! # Exact full retained precision, including every crossing-edge charge

Keeping the deficit fixed turns the diagonal correction into the row sum
of the physical adjacency update. Support capture then restricts this sum
to the independently retained core/B/C endpoint index.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2500000
namespace LocalLaw
local instance fullRetainedPrecisionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem normalizedAdjacency_complex_row_sum (G : SimpleGraph V) (d : ℕ) (i : V) :
    ∑ j, normalizedAdjacency G d i j = treeEdgeWeight d * (G.degree i : ℂ) := by
  have hh := normalizedAdjacency_mulVec_neighbor G d (fun _ => (1 : ℂ)) i
  simpa [Matrix.mulVec, dotProduct] using hh

namespace DeficientGraph
variable {d : ℕ}

/-- Exact precision correction for two graphs with the same physical deficit. -/
theorem extensionMatrix_difference_row_charge (g h : DeficientGraph V d) (hd : 3 ≤ d)
    (hδ : ∀ i, h.deficit i = g.deficit i) (q z : ℂ) :
    h.extensionMatrix q z - g.extensionMatrix q z = h.H - g.H +
      (q * treeEdgeWeight d) • Matrix.diagonal (fun i => ∑ j, (h.H - g.H) i j) := by
  have hcoef (i : V) : (h.boundaryCoefficient i : ℂ) - (g.boundaryCoefficient i : ℂ) =
      -treeEdgeWeight d * (∑ j, (h.H - g.H) i j) := by
    change _ = -treeEdgeWeight d * (∑ j, (normalizedAdjacency h.graph d i j - normalizedAdjacency g.graph d i j))
    rw [Finset.sum_sub_distrib, normalizedAdjacency_complex_row_sum, normalizedAdjacency_complex_row_sum]
    simp only [boundaryCoefficient, hδ i, Complex.ofReal_div, Complex.ofReal_sub,
      Complex.ofReal_natCast, Complex.ofReal_one]
    have hsq := treeEdgeWeight_sq d hd
    rw [mul_sub]
    linear_combination ((h.graph.degree i : ℂ) - (g.graph.degree i : ℂ)) * hsq
  ext i j
  change (h.H i j - (z • (1 : Matrix V V ℂ)) i j - q * h.boundaryDiagonal i j) -
    (g.H i j - (z • (1 : Matrix V V ℂ)) i j - q * g.boundaryDiagonal i j) = _
  by_cases hij : i = j
  · subst j
    simp only [boundaryDiagonal, Matrix.diagonal_apply_eq, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    have hc := hcoef i
    linear_combination -q * hc
  · simp only [boundaryDiagonal, Matrix.diagonal_apply_ne _ hij, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_zero, add_zero, sub_zero]
    ring

variable {I : Type} [Fintype I] [DecidableEq I]

theorem supported_extensionMatrix_difference_row_charge (g h : DeficientGraph V d)
    (hd : 3 ≤ d) (hδ : ∀ i, h.deficit i = g.deficit i) (e : I ↪ V)
    (hsupport : ∀ x y, x ∉ Set.range e ∨ y ∉ Set.range e → (h.H - g.H) x y = 0)
    (q z : ℂ) :
    (h.extensionMatrix q z - g.extensionMatrix q z).submatrix e e =
      (h.H - g.H).submatrix e e + (q * treeEdgeWeight d) •
        Matrix.diagonal (fun i => ∑ j, (h.H - g.H) (e i) (e j)) := by
  rw [g.extensionMatrix_difference_row_charge h hd hδ q z]
  have hsum (i : I) : (∑ v, (h.H - g.H) (e i) v) = ∑ j, (h.H - g.H) (e i) (e j) :=
    sum_embedding_of_supported e _ (fun v hv => hsupport (e i) v (Or.inr hv))
  simp only [Matrix.sub_apply] at hsum
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply, e.injective.eq_iff]
  by_cases hij : i = j
  · subst j
    simp only [if_true]
    rw [hsum i]
  · simp [hij]

omit [Fintype I] [DecidableEq I] in
theorem extensionMatrix_difference_supported_of_H (g h : DeficientGraph V d)
    (hd : 3 ≤ d) (hδ : ∀ i, h.deficit i = g.deficit i) (e : I ↪ V)
    (hsupport : ∀ x y, x ∉ Set.range e ∨ y ∉ Set.range e → (h.H - g.H) x y = 0)
    (q z : ℂ) :
    ∀ x y, x ∉ Set.range e ∨ y ∉ Set.range e →
      (h.extensionMatrix q z - g.extensionMatrix q z) x y = 0 := by
  rw [g.extensionMatrix_difference_row_charge h hd hδ q z]
  intro x y hxy
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply,
    hsupport x y hxy, zero_add]
  by_cases he : x = y
  · subst y
    have hx : x ∉ Set.range e := hxy.elim id id
    have hrow : (∑ j, (h.H - g.H) x j) = 0 :=
      Finset.sum_eq_zero (fun j _ => hsupport x j (Or.inl hx))
    simp only [if_true, hrow, mul_zero]
  · simp [he]

end DeficientGraph
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

/-- The literal full-model update, even when the retained set cuts T. -/
theorem full_partial_retained_precision (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (labels : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T) (selector : ℕ) (hs : 1 ≤ selector)
    (S : Set (Fin N)) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let s := g.admissibleState T labels samples
    let h := g.labelledResampledGraph T labels samples selector
    let e := s.fullPartialEmbedding selector S hs
    let f : s.FullEndpointIndex selector S ↪ Fin N :=
      ⟨fun u => (e u).val, fun _ _ he => e.injective (Subtype.ext he)⟩
    let R := ((g.deficient.restrict S).extensionGreen q z).submatrix e e
    let U := ((h.deficient.restrict S).extensionGreen q z).submatrix e e
    let Δ := (h.H - g.H).submatrix f f
    IsUnit R ∧ IsUnit U ∧
      U⁻¹ = R⁻¹ + Δ + (q * treeEdgeWeight d) • Matrix.diagonal (fun i => ∑ j, Δ i j) := by
  dsimp only
  let s := g.admissibleState T labels samples
  let h := g.labelledResampledGraph T labels samples selector
  let e := s.fullPartialEmbedding selector S hs
  let old := g.deficient.restrict S
  let new := h.deficient.restrict S
  have hδ : ∀ v, new.deficit v = old.deficit v := fun _ => rfl
  have haway (x : S) (hx : x ∉ Set.range e) : x.val ∉ s.fullResampleEndpoints selector :=
    fun hm => hx (s.fullPartialEmbedding_captures selector S hs x hm)
  have hH : ∀ x y : S, x ∉ Set.range e ∨ y ∉ Set.range e → (new.H - old.H) x y = 0 := by
    intro x y hxy
    exact s.fullResample_difference_supported selector d x.val y.val
      (hxy.imp (haway x) (haway y))
  have hh := old.supported_retained_inverse new hd e q z hz hq
    (old.extensionMatrix_difference_supported_of_H new hd hδ e hH q z)
  have hc := old.supported_extensionMatrix_difference_row_charge new hd hδ e hH q z
  refine ⟨hh.1, hh.2.1, ?_⟩
  rw [hh.2.2, hc]
  simp only [add_assoc]
  rfl

end RegularGraph
end LocalLaw
