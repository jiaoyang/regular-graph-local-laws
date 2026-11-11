import LocalLaw.CutIncidence

/-!
# Common boundary labels for different-size physical and local models

A retained vertex whose incident edges stay inside the finite model has the
same actual cut edges in the ambient and finite graph. Ambient deleted
self-energy therefore uses the local cut-incidence matrix and the actual
ambient deleted kernel at its embedded endpoints, with no omitted rows or
artificial padding.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance embeddedCutIncidenceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section SupportedSum
variable {I J W : Type*} [Fintype J] [Fintype W] [DecidableEq J] [DecidableEq W]

omit [DecidableEq J] in
theorem sum_embedding_of_supported (f : J ↪ W) (F : W → ℂ)
    (hF : ∀ w, w ∉ Set.range f → F w = 0) : (∑ w, F w) = ∑ j, F (f j) := by
  calc
    _ = ∑ w ∈ Finset.univ.image f, F w := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro w _ hw
      apply hF w
      simpa only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using hw
    _ = _ := Finset.sum_image (fun _ _ _ _ h => f.injective h)

omit [DecidableEq J] in
/-- A genuine rectangular sandwich reduces to a supported embedded index
set, even when the ambient and finite graphs have different sizes. -/
theorem sandwich_embedding_of_supported (f : J ↪ W) (A : Matrix I W ℂ) (K : Matrix W W ℂ)
    (B : Matrix W I ℂ) (hA : ∀ i w, w ∉ Set.range f → A i w = 0)
    (hB : ∀ w i, w ∉ Set.range f → B w i = 0) :
    A * K * B = A.submatrix id f * K.submatrix f f * B.submatrix f id := by
  ext i j
  simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.submatrix_apply, id_eq]
  calc
    _ = ∑ b, ∑ v, A i v * K v (f b) * B (f b) j := by
      apply sum_embedding_of_supported f
      intro w hw
      simp only [hB w j hw, mul_zero, Finset.sum_const_zero]
    _ = ∑ b, ∑ a, A i (f a) * K (f a) (f b) * B (f b) j := by
      apply Finset.sum_congr rfl
      intro b _
      apply sum_embedding_of_supported f
      intro v hv
      simp only [hA i v hv, zero_mul]

end SupportedSum

section ActualEmbedding
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

/-- The outside embedding is genuinely injective. -/
def outsideImageEmbedding (e : V ↪ A) (T : Set V) : (Tᶜ : Set V) ↪ ((e '' T)ᶜ : Set A) :=
  ⟨embeddingOutsideImage e T, fun _ _ h => Subtype.ext (e.injective (congrArg Subtype.val h))⟩

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] in
private theorem outside_not_range_of_not_outside_range (e : V ↪ A) (T : Set V)
    (w : ((e '' T)ᶜ : Set A)) (hw : w ∉ Set.range (outsideImageEmbedding e T)) :
    w.val ∉ Set.range e := by
  rintro ⟨v, hv⟩
  have hvT : v ∉ T := fun h => w.property ⟨v, h, hv⟩
  apply hw
  exact ⟨⟨v, hvT⟩, Subtype.ext hv⟩

omit [DecidableEq V] in
/-- All incident ambient edges of the retained set are captured by the
finite model. Only this literal geometric condition is required. -/
theorem embeddedSelfEnergy_on_model_outside (H : Matrix A A ℂ) (hH : H.IsHermitian)
    (e : V ↪ A) (T : Set V) (z : ℂ)
    (hcapture : ∀ i : T, ∀ a, a ∉ Set.range e → H (e i.val) a = 0) :
    embeddedSelfEnergy H e T z =
      (H.submatrix e e).submatrix (Subtype.val : T → V) (Subtype.val : (Tᶜ : Set V) → V) *
        (green (H.submatrix (Subtype.val : ((e '' T)ᶜ : Set A) → A)
          (Subtype.val : ((e '' T)ᶜ : Set A) → A)) z).submatrix
            (outsideImageEmbedding e T) (outsideImageEmbedding e T) *
      (H.submatrix e e).submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V) := by
  let f := outsideImageEmbedding e T
  have hleft (i : T) (w : ((e '' T)ᶜ : Set A)) (hw : w ∉ Set.range f) : H (e i.val) w.val = 0 :=
    hcapture i w.val (outside_not_range_of_not_outside_range e T w hw)
  have hright (w : ((e '' T)ᶜ : Set A)) (i : T) (hw : w ∉ Set.range f) : H w.val (e i.val) = 0 := by
    rw [← hH.apply w.val (e i.val), hleft i w hw, star_zero]
  exact sandwich_embedding_of_supported f
    (H.submatrix (fun i : T => e i.val) Subtype.val) _
    (H.submatrix Subtype.val (fun i : T => e i.val)) hleft hright

end ActualEmbedding

namespace DeficientGraph
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] {d : ℕ}

/-- Ambient self-energy and the actual deleted-model self-energy now use
one common cut-incidence matrix and the difference of the genuine two
outside kernels, indexed by the actual boundary-edge endpoints. -/
theorem embeddedSelfEnergy_sub_retainedSelfEnergy (g : DeficientGraph V d)
    (H : Matrix A A ℂ) (hH : H.IsHermitian) (e : V ↪ A) (hHmodel : g.H = H.submatrix e e)
    (T : Set V) (q z : ℂ)
    (hcapture : ∀ i : T, ∀ a, a ∉ Set.range e → H (e i.val) a = 0) :
    embeddedSelfEnergy H e T z - g.retainedSelfEnergy T q z =
      cutInnerCoupling g.graph d T *
        (((green (H.submatrix (Subtype.val : ((e '' T)ᶜ : Set A) → A)
          (Subtype.val : ((e '' T)ᶜ : Set A) → A)) z).submatrix
            (outsideImageEmbedding e T) (outsideImageEmbedding e T) -
          (g.delete T).extensionGreen q z).submatrix
            (boundaryOutsideVertex g.graph T) (boundaryOutsideVertex g.graph T)) *
        (cutInnerCoupling g.graph d T).transpose := by
  rw [embeddedSelfEnergy_on_model_outside H hH e T z hcapture, ← hHmodel]
  unfold retainedSelfEnergy DeficientGraph.H
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  exact normalized_cut_selfEnergy g.graph d T _

end DeficientGraph
end LocalLaw
