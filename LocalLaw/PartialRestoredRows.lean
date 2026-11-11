import LocalLaw.EmbeddedDeficitRestoration
import LocalLaw.PartialEndpointMasks
import LocalLaw.EndpointFarTailParameters
import LocalLaw.ParameterSmallness

/-! # Actual restored A-block rows, with all masks and source numerics derived -/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance partialRestoredRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem partial_restored_boundary_rows (g : RegularGraph N d) (hd : 3≤d)
    (T : Set (Fin N)) (labels : ι≃BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (S : Set (Tᶜ:Set (Fin N)))
    (hb : ((g.deficient.delete T).restrict S).ComponentFiniteReferenceBudget)
    (z : ℂ) (hz : 0<z.im)
    (hsmall : (Fintype.card ((g.admissibleState T labels samples).partialBoundaryMask selector S):ℝ)*physicalTransfer d z^selector≤1) :
    let s := g.admissibleState T labels samples
    let e := s.partialBoundaryEmbedding selector S
    let P := (((g.deficient.delete T).restrict S).extensionGreen (semicircleRoot z) z).submatrix e e
    let K := P⁻¹-Matrix.diagonal (fun _ : s.partialBoundaryMask selector S => semicircleRoot z*treeEdgeWeight d^2)
    (∀ i,∑ j,‖K⁻¹ i j‖≤4*finiteExtraReferenceConstant d) ∧
      (∀ j,∑ i,‖K⁻¹ i j‖≤4*finiteExtraReferenceConstant d) := by
  dsimp only
  let s := g.admissibleState T labels samples
  let e := s.partialBoundaryEmbedding selector S
  let M := (g.deficient.delete T).restrict S
  let A := s.partialBoundaryMask selector S
  have hpos : ∀ v∈Set.range e,0<M.deficit v := by
    intro v hv
    have hi : v∈s.includedEligibleBoundary selector S := s.partialBoundaryEmbedding_range selector S ▸ hv
    change 0<((g.deficient.delete T).restrict S).deficit v
    rw [g.includedEligibleBoundary_deficit_one T labels samples selector S v hi]
    norm_num
  have hsep (i j : A) (hij : i≠j) : (selector:ℕ∞)≤M.graph.edist (e i) (e j) :=
    (s.partialBoundaryEmbedding_separated selector S i j hij).le.trans
      (graphHom_edist_le (SimpleGraph.Embedding.induce (G:=outsideGraph g.graph T) S).toHom (e i) (e j))
  have hrows := M.restored_physical_block_rows hd hb e hpos selector hsep z hz hsmall
  have hcast : ((1/((d:ℝ)-1):ℝ):ℂ)=(1:ℂ)/((d:ℂ)-1) := by push_cast; rfl
  have hD : Matrix.diagonal (fun _ : A => semicircleRoot z*treeEdgeWeight d^2)=
      (semicircleRoot z) • Matrix.diagonal (fun _ : A => ((1/((d:ℝ)-1):ℝ):ℂ)) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp only [Matrix.diagonal_apply_eq,Matrix.smul_apply,smul_eq_mul,treeEdgeWeight_sq d hd,hcast]
    · simp [Matrix.diagonal_apply,hij]
  rw [hD]
  exact hrows

end RegularGraph

namespace LabelledResamplingState
variable {V : Type} [Fintype V] {T : Set V} {ι : Type} [Fintype ι]

theorem partialBoundaryMask_card_le_roots (s : LabelledResamplingState V T ι)
    (selector : ℕ) (S : Set (Tᶜ:Set V)) :
    Nat.card (s.partialBoundaryMask selector S)≤Nat.card (s.endpointModelRoots selector) := by
  let f : s.partialBoundaryMask selector S → s.endpointModelRoots selector := fun i =>
    ⟨s.admissibleBoundaryVertex selector i.val,Or.inl ⟨s.boundary i.val.val,rfl⟩⟩
  have hf : Function.Injective f := by
    intro i j h
    apply (s.partialBoundaryEmbedding selector S).injective
    exact Subtype.ext (congrArg (fun v : s.endpointModelRoots selector => v.val) h)
  exact Nat.card_le_card_of_injective f hf

end LabelledResamplingState
namespace RegularGraph

theorem eventually_partial_restored_boundary_rows (a b d : ℕ) (c β : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c) (hβ : 0<β) (hβc : β≤c/32) :
    ∀ᶠ N : ℕ in Filter.atTop,∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ {ι : Type} [Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector := logarithmicRadius (c/4) d N/4
      let s := g.admissibleState T labels samples
      ∀ S : Set (Tᶜ:Set (Fin N)),((g.deficient.delete T).restrict S).ComponentFiniteReferenceBudget →
      let e := s.partialBoundaryEmbedding selector S
      let P := (((g.deficient.delete T).restrict S).extensionGreen (semicircleRoot z) z).submatrix e e
      let K := P⁻¹-Matrix.diagonal (fun _ : s.partialBoundaryMask selector S => semicircleRoot z*treeEdgeWeight d^2)
      (∀ i,∑ j,‖K⁻¹ i j‖≤4*finiteExtraReferenceConstant d) ∧
        (∀ j,∑ i,‖K⁻¹ i j‖≤4*finiteExtraReferenceConstant d) := by
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_endpoint_far_tail_small a d 1 ha hd (by norm_num),
    eventually_paperError_small a b d β ha hb hd hβ,eventually_source_radius_hierarchy a d c β hd hc hβ hβc,
    eventually_log_ge_nat 1,hdepth,Filter.eventually_ge_atTop 1] with N htail hsmall hrad hlog hdepth hN
  intro g o z hz hfloor ι _ labels samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let T := graphBallVertices g.graph o ell
  let selector := logarithmicRadius (c/4) d N/4
  let s := g.admissibleState T labels samples
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  intro S hbS
  have hell : ell≤doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have ht := htail g o ell hell labels samples selector (logarithmicRadius β d N) selector hrad.2.2.1 z hz.le
  simp only [one_mul] at ht
  have hLp : 0<L := by linarith
  have hεcap : ε≤1 :=
    (hsmall z hz hfloor).trans (inv_le_one_of_one_le₀ (one_le_pow₀ hlog))
  have hcap : ε/L^16≤1 :=
    (div_le_self (graphPaperError_nonnegative a d N _ z hN hz.le)
      (one_le_pow₀ hlog)).trans hεcap
  have hcard := Nat.cast_le (α:=ℝ).mpr (s.partialBoundaryMask_card_le_roots selector S)
  have hmask : (Fintype.card (s.partialBoundaryMask selector S):ℝ)*physicalTransfer d z^selector≤1 := by
    have hh := (mul_le_mul_of_nonneg_right hcard (pow_nonneg (physicalTransfer_pos d hd z).le _)).trans (ht.trans hcap)
    simpa only [Nat.card_eq_fintype_card] using hh
  exact g.partial_restored_boundary_rows hd T labels samples selector S hbS z hz hmask

end RegularGraph
end LocalLaw
