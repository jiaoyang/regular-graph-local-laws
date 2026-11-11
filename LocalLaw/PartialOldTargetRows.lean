import LocalLaw.AugmentedOldEndpointRows
import LocalLaw.PartialSurgeryCoupling

/-! # Actual partial endpoint target weights from F1 occupancy

The restriction may cut old endpoint balls arbitrarily. Only the old class,
its proved diameter and the literal occupancy count enter the estimate.
-/
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000
namespace LocalLaw
local instance partialOldTargetRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem partial_old_endpoint_rows (g : RegularGraph N d) (hd : 3 ≤ d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (Saug : Set (Tᶜ : Set (Fin N)))
    (hbudget : ((g.deficient.delete T).restrict Saug).ComponentFiniteReferenceBudget)
    (R : ℕ) (hR : ∀ x y, ((g.deficient.delete T).restrict Saug).graph.dist x y ≤ R)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2)
    (h B : ℕ) (x : Saug) (hnear : (tripleNearIndices g.graph T h samples x.val).card ≤ B) :
    let s := g.admissibleState T boundary samples
    let e := s.partialEndpointEmbedding selector Saug
    let M := (g.deficient.delete T).restrict Saug
    (∑ i : s.PartialEndpointIndex selector Saug, ‖M.extensionGreen q z x (e i)‖) ≤
      2 * finiteExtraReferenceConstant d *
        (3 * (B : ℝ) + (Nat.card (s.endpointModelRoots selector) : ℝ) * physicalTransfer d z ^ h) := by
  dsimp only
  let s := g.admissibleState T boundary samples
  let H := outsideGraph g.graph T
  let e := s.partialEndpointEmbedding selector Saug
  let M := (g.deficient.delete T).restrict Saug
  let C := 2 * finiteExtraReferenceConstant d
  let t := physicalTransfer d z
  have hmem (u : s.PartialEndpointIndex selector Saug) : (e u).val∈s.endpointModelRoots selector := by
    rcases u with a | (b | c)
    · exact Or.inl ⟨s.boundary a.val.val,rfl⟩
    · exact Or.inr (Set.mem_iUnion.mpr ⟨b.val,Or.inl rfl⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨c.val,Or.inr rfl⟩)
  let f : s.PartialEndpointIndex selector Saug → s.endpointModelRoots selector := fun u=>⟨(e u).val,hmem u⟩
  have hf : Function.Injective f := by
    intro i j h
    apply e.injective
    exact Subtype.ext (congrArg (fun u : s.endpointModelRoots selector=>u.val) h)
  let near := fun i : s.PartialEndpointIndex selector Saug => H.edist x.val (e i).val ≤ (h : ℕ∞)
  have hC : 0 ≤ C := by dsimp only [C]; linarith [finiteExtraReferenceConstant_ge_one d hd]
  have ht : 0 ≤ t := norm_nonneg _
  have htone : t ≤ 1 := by dsimp only [t]; nlinarith [physicalTransfer_sq_le_half d hd z]
  have hkernel := M.componentwise_finite_kernel_decay hd hbudget q z hz hq R hR small
  have hcap : ∀ i, ‖M.extensionGreen q z x (e i)‖ ≤ C := fun i =>
    (hkernel x (e i)).trans (mul_le_of_le_one_right hC (pow_le_one₀ ht htone))
  have hfar : ∀ i, ¬near i → ‖M.extensionGreen q z x (e i)‖ ≤ C * t ^ h := by
    intro i hi
    by_cases hreach : M.graph.Reachable x (e i)
    · obtain ⟨p, _, hp⟩ := hreach.exists_path_of_dist
      let f : M.graph →g H := { toFun := Subtype.val, map_rel' := fun hh => hh }
      have hpath := SimpleGraph.edist_le (p.map f)
      simp only [SimpleGraph.Walk.length_map, hp] at hpath
      have hlocal : h ≤ M.graph.dist x (e i) := ENat.coe_le_coe.mp ((lt_of_not_ge hi).le.trans hpath)
      exact (hkernel x (e i)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht htone hlocal) hC)
    · let c := M.graph.connectedComponentMk x
      have hnot : e i ∉ c.supp := fun hh => hreach (SimpleGraph.ConnectedComponent.exact hh.symm)
      rw [M.extensionGreen_zero_across_cut hd c.supp (M.component_cut c) q z hz hq x rfl (e i) hnot, norm_zero]
      positivity
  have hcount : (Nat.card {i : s.PartialEndpointIndex selector Saug // near i} : ℝ) ≤ 3 * (B : ℝ) := by
    let ff : {i : s.PartialEndpointIndex selector Saug // near i} →
        {i : s.endpointModelRoots selector // H.edist x.val i.val≤(h:ℕ∞)} := fun i=>⟨f i.val,i.property⟩
    have hff : Function.Injective ff := by
      intro i j h
      exact Subtype.ext (hf (congrArg Subtype.val h))
    have hh := (Nat.card_le_card_of_injective ff hff).trans
      ((s.endpointModelRoots_near_card selector h x.val).trans (Nat.mul_le_mul_left 3 hnear))
    exact_mod_cast hh
  have hcard : (Fintype.card (s.PartialEndpointIndex selector Saug):ℝ)≤(Nat.card (s.endpointModelRoots selector):ℝ) := by
    exact_mod_cast (by simpa only [Nat.card_eq_fintype_card] using Nat.card_le_card_of_injective f hf)
  have hh := finite_kernel_near_far_sum (fun i => M.extensionGreen q z x (e i)) near
    (3 * (B : ℝ)) C (t ^ h) hC (pow_nonneg ht _) hcount hcap hfar
  apply hh.trans
  have hc := mul_le_mul_of_nonneg_right hcard (mul_nonneg hC (pow_nonneg ht h))
  dsimp only [C,t] at *
  nlinarith only [hc]

end RegularGraph
end LocalLaw
