import LocalLaw.AugmentedSelectedCutRows
import LocalLaw.SourceCommonLeafMateRows
import LocalLaw.SourceCommonBoundaryRows

/-! # Source-derived actual new-B cut-coupling rows

The actual old common model supplies lost-neighbor and A-root rows. The
new cut incidence inequality is derived from the physical switches. The
partial B mask and all accepted A roots are retained by the augmented set.
-/

open Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 3500000
namespace LocalLaw
local instance sourceSelectedCutRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type}[Fintype V]{T : Set V}{ι : Type}[Fintype ι]

def twoTargetBoundaryMaskEquiv (s : LabelledResamplingState V T ι)(selector r : ℕ)
    (x y : (Tᶜ:Set V)) : s.AdmissibleSampleIndex selector ≃
      s.partialBoundaryMask selector (s.twoTargetEndpointVertices selector r x y) where
  toFun i := ⟨i,s.admissibleBoundaryVertex_mem_twoTarget selector r x y i⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl

end LabelledResamplingState
namespace RegularGraph
variable {N d : ℕ}{ι : Type}[Fintype ι]

def SelectedCutRowsControlled (g : RegularGraph N d)(T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T)(samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ)(x y : (Tᶜ:Set (Fin N)))(q z : ℂ)(K : ℝ) : Prop :=
  let s := g.admissibleState T labels samples
  let A := s.twoTargetEndpointVertices selector r x y
  let M := (g.deficient.delete T).restrict A
  let B := s.partialFirstRemovedSet selector A
  letI : DecidableEq (Bᶜ:Set A) := fun a b => Classical.propDecidable (a=b)
  ∀u:(Bᶜ:Set A),
    (∑b:B,‖∑v:(Bᶜ:Set A),(M.delete B).extensionGreen q z u v*
      normalizedAdjacency ((outsideGraph (s.fullResample selector).graph T).induce A) d v.val b.val‖)≤K

theorem selected_cut_rows_of_common_rows (g : RegularGraph N d)(T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T)(samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ)(x y : (Tᶜ:Set (Fin N)))(q z : ℂ)(KM KA : ℝ) :
    let s := g.admissibleState T labels samples
    let A := s.twoTargetEndpointVertices selector r x y
    let M := (g.deficient.delete T).restrict A
    let B := s.partialFirstRemovedSet selector A
    M.LeafCoreMateRows B q z KM →
    M.DeletedCoreEmbeddedRows B (s.partialBoundaryCoreEmbedding selector A) q z KA →
    g.SelectedCutRowsControlled T labels samples selector r x y q z
      ((Real.sqrt ((d:ℝ)-1))⁻¹*(KM+KA)) := by
  dsimp only [SelectedCutRowsControlled,DeficientGraph.LeafCoreMateRows,DeficientGraph.DeletedCoreEmbeddedRows]
  let s := g.admissibleState T labels samples
  let A := s.twoTargetEndpointVertices selector r x y
  let M := (g.deficient.delete T).restrict A
  let B := s.partialFirstRemovedSet selector A
  letI : DecidableEq (Bᶜ:Set A) := fun a b => Classical.propDecidable (a=b)
  intro hmate hboundary u
  have hA : (∑i:s.AdmissibleSampleIndex selector,
      ‖(M.delete B).extensionGreen q z u (s.twoTargetBoundaryCommonVertex selector r x y i)‖)≤KA := by
    let e := s.twoTargetBoundaryMaskEquiv selector r x y
    have he (i:s.AdmissibleSampleIndex selector) : s.partialBoundaryCoreEmbedding selector A (e i)=
        s.twoTargetBoundaryCommonVertex selector r x y i := rfl
    have hs := e.sum_comp (fun j => ‖(M.delete B).extensionGreen q z u (s.partialBoundaryCoreEmbedding selector A j)‖)
    have hsum : (∑i:s.AdmissibleSampleIndex selector,
        ‖(M.delete B).extensionGreen q z u (s.twoTargetBoundaryCommonVertex selector r x y i)‖)=
      ∑j:s.partialBoundaryMask selector A,‖(M.delete B).extensionGreen q z u (s.partialBoundaryCoreEmbedding selector A j)‖ := by
      simpa only [he] using hs
    exact hsum.le.trans (hboundary.1 u)
  have hn := s.twoTarget_selectedFirst_new_cut_rows d selector r x y
    (fun v => (M.delete B).extensionGreen q z u v)
  have hb : ((∑l:DeletedLeafIndex M.graph B,‖(M.delete B).extensionGreen q z u (deletedLeafMate M.graph B l)‖)+
      ∑i:s.AdmissibleSampleIndex selector,‖(M.delete B).extensionGreen q z u (s.twoTargetBoundaryCommonVertex selector r x y i)‖)≤KM+KA :=
    add_le_add (hmate.1 u) hA
  simp only [←finsum_eq_sum_of_fintype] at hn hb ⊢
  exact hn.trans (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (Real.sqrt_nonneg _)))

theorem eventually_source_selected_cut_rows (a b d : ℕ)(c β Bcap C1 : ℝ)
    (ha : 12≤a)(hb : 25*a≤b)(hd : 3≤d)(hc : 0<c)(hβ : 0<β)(hβc : β≤c/32)(hC1 : 1≤C1) :
    ∀ᶠ N:ℕ in atTop,∀(g : RegularGraph N d)(o : Fin N)(z q : ℂ),
      0<z.im → ‖z‖≤Bcap → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → 0≤q.im →
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) →
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀{ι:Type}[Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y : ((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N))),
      g.SelectedCutRowsControlled (graphBallVertices g.graph o (actualCavityDepth a d N z-1)) labels samples
        (logarithmicRadius (c/4) d N/4) (effectiveModelRadius a d N β) x y q z
        ((Real.sqrt ((d:ℝ)-1))⁻¹*(leafDeletedMateRowCap d Bcap+leafDeletedSeparatedRowCap d Bcap)) := by
  filter_upwards [eventually_source_common_leaf_mate_rows a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_source_common_boundary_rows a b d c β Bcap C1 ha hb hd hc hβ hβc hC1]
    with N hmate hboundary
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  exact g.selected_cut_rows_of_common_rows _ labels samples _ _ x y q z _ _
    (hmate g o z q hz hzB hfloor hq hprior hballs labels samples x y)
    (hboundary g o z q hz hzB hfloor hq hprior hballs labels samples x y)

end RegularGraph
end LocalLaw
