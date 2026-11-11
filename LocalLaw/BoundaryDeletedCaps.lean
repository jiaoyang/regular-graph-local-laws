import LocalLaw.ComponentRestrictionBudget
import LocalLaw.SourceGuardedCaps

/-! # Deleted Green entry caps on the actual outer boundary

Both endpoints adjacent to the removed ball have their local pair model
inside one common original ball. Actual connected deletion and arbitrary
component restriction give the extended finite reference class. Perturbed
kernel decay and the deleted approximation bound then control the physical
outer-boundary matrix, without any inverse-diagonal claim near the boundary.
-/

noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw

local instance boundaryDeletedCapsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def boundaryDeletedEntryCap (d : ℕ) : ℝ := 2 * finiteExtraReferenceConstant d + 1

namespace RegularGraph
variable {N d : ℕ}

theorem boundary_deleted_pair_component_budget (g : RegularGraph N d) (o : Fin N)
    (ell r R : ℕ) (hmargin : r + 2 * ell + 2 ≤ R)
    (hballs : ∀ v, graphBallExcess g.graph v R ≤ finiteOmega d)
    (i j : ((graphBallVertices g.graph o ell)ᶜ : Set (Fin N)))
    (hi : ∃ t : graphBallVertices g.graph o ell, g.graph.Adj t.val i.val)
    (hj : ∃ t : graphBallVertices g.graph o ell, g.graph.Adj t.val j.val) :
    ((g.deficient.delete (graphBallVertices g.graph o ell)).restrict
      (pairBallVertices (outsideGraph g.graph (graphBallVertices g.graph o ell)) i j r)).ComponentFiniteReferenceBudget := by
  let T := graphBallVertices g.graph o ell
  let H := outsideGraph g.graph T
  let M := graphBallVertices g.graph o (r + ell + 1)
  let K := pairBallVertices H i j r
  have hTM : T ⊆ M := graphBallVertices_mono g.graph o (by omega)
  have houter (v : (Tᶜ : Set (Fin N))) (hv : ∃ t : T, g.graph.Adj t.val v.val) :
      g.graph.edist o v.val ≤ ((ell + 1 : ℕ) : ℕ∞) := by
    obtain ⟨t, htv⟩ := hv
    apply (SimpleGraph.edist_triangle (G := g.graph) (u := o) (v := t.val)).trans
    exact (add_le_add t.property (le_of_eq (SimpleGraph.edist_eq_one_iff_adj.mpr htv))).trans_eq
      (by simp only [Nat.cast_add, Nat.cast_one])
  have hKM : ∀ v ∈ K, v.val ∈ M := by
    intro v hv
    let f : H →g g.graph := { toFun := Subtype.val, map_rel' := fun h => h }
    rcases hv with hv | hv
    · have hold := (graphHom_edist_le f i v).trans hv
      apply ((SimpleGraph.edist_triangle (G := g.graph) (u := o) (v := i.val)).trans
        (add_le_add (houter i hi) hold)).trans_eq
      exact_mod_cast (show ell + 1 + r = r + ell + 1 by omega)
    · have hold := (graphHom_edist_le f j v).trans hv
      apply ((SimpleGraph.edist_triangle (G := g.graph) (u := o) (v := j.val)).trans
        (add_le_add (houter j hj) hold)).trans_eq
      exact_mod_cast (show ell + 1 + r = r + ell + 1 by omega)
  have hMbudget : graphExcess (g.graph.induce M) ≤ finiteOmega d :=
    (graphBallExcess_mono_radius g.graph o (by omega : r + ell + 1 ≤ R)).trans (hballs o)
  exact g.deficient.deleted_restriction_componentFiniteReferenceBudget M T (fun _ => rfl)
    (graphBall_connected g.graph o _) (graphBall_connected g.graph o ell) hTM hMbudget K hKM

end RegularGraph

namespace RegularGraph.SourceOmegaPlusWithRadii
variable {N d a rModel rError R ell Cq badCount : ℕ} {C1 : ℝ} {o : Fin N} {z : ℂ}
variable {g : RegularGraph N d}

theorem outer_boundary_deleted_entry_cap
    (h : g.SourceOmegaPlusWithRadii a rModel rError R ell (finiteOmega d) Cq badCount C1 o z)
    (hd : 3 ≤ d) (hz : 0 < z.im) (hmargin : rModel + 2 * ell + 2 ≤ R / 8)
    (hE : C1 * g.sourcePrime a rError z ≤ 1)
    (small : ‖g.Q z - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * (4 * (rModel : ℝ) + 2) ≤ 1 / 2)
    (i j : ((graphBallVertices g.graph o ell)ᶜ : Set (Fin N)))
    (hi : ∃ t : graphBallVertices g.graph o ell, g.graph.Adj t.val i.val)
    (hj : ∃ t : graphBallVertices g.graph o ell, g.graph.Adj t.val j.val) :
    ‖(g.deficient.delete (graphBallVertices g.graph o ell)).G z i j‖ ≤ boundaryDeletedEntryCap d := by
  let T := graphBallVertices g.graph o ell
  let H := outsideGraph g.graph T
  let M := (g.deficient.delete T).restrict (pairBallVertices H i j rModel)
  have hbudget : M.ComponentFiniteReferenceBudget :=
    g.boundary_deleted_pair_component_budget o ell rModel (R / 8) hmargin h.structural.1 i j hi hj
  have hsmall : ‖g.Q z - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * (((4 * rModel + 1 : ℕ) : ℝ) + 1) ≤ 1 / 2 := by
    convert small using 1
    push_cast
    ring
  have hmodel := M.componentwise_finite_kernel_decay hd hbudget (g.Q z) z hz (g.Q_im_nonnegative z hz)
    (4 * rModel + 1) (pairBall_distance_bound H i j rModel) hsmall
    (pairBallLeft H i j rModel) (pairBallRight H i j rModel)
  have hC : 0 ≤ 2 * finiteExtraReferenceConstant d := by
    have hh := finiteExtraReferenceConstant_ge_one d hd
    positivity
  have ht : physicalTransfer d z ≤ 1 := by
    nlinarith [physicalTransfer_sq_le_half d hd z, (physicalTransfer_pos d hd z).le]
  have hmodelCap : ‖M.extensionGreen (g.Q z) z
      (pairBallLeft H i j rModel) (pairBallRight H i j rModel)‖ ≤ 2 * finiteExtraReferenceConstant d :=
    hmodel.trans (mul_le_of_le_one_right hC (pow_le_one₀ (physicalTransfer_pos d hd z).le ht))
  have happ : ‖(g.deficient.delete T).G z i j - M.extensionGreen (g.Q z) z
      (pairBallLeft H i j rModel) (pairBallRight H i j rModel)‖ ≤ C1 * g.sourcePrime a rError z :=
    h.deleted i j
  have htri := norm_add_le (M.extensionGreen (g.Q z) z (pairBallLeft H i j rModel) (pairBallRight H i j rModel))
    ((g.deficient.delete T).G z i j - M.extensionGreen (g.Q z) z
      (pairBallLeft H i j rModel) (pairBallRight H i j rModel))
  rw [add_sub_cancel] at htri
  change ‖(g.deficient.delete T).G z i j‖ ≤ 2 * finiteExtraReferenceConstant d + 1
  linarith

end RegularGraph.SourceOmegaPlusWithRadii
end LocalLaw
