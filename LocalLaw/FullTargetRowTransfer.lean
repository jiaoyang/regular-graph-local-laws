import LocalLaw.FullQuadCouplingMass
import LocalLaw.FullQuadInstanceTransport
import LocalLaw.AugmentedRowTransfer

/-! # Actual full-model target rows after arbitrary partial switching -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance fullTargetRowTransferDecidable (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 2500000
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem full_model_difference_supported (g : RegularGraph N d) (hd : 3≤d)
    (T : Set (Fin N)) (labels : ι≃BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (hs : 1≤selector) (S : Set (Fin N)) (q z : ℂ) :
    let s := g.admissibleState T labels samples
    let e := s.fullPartialEmbedding selector S hs
    let old := g.deficient.restrict S
    let new := (g.labelledResampledGraph T labels samples selector).deficient.restrict S
    ∀x y:S,x∉Set.range e ∨ y∉Set.range e → (new.extensionMatrix q z-old.extensionMatrix q z) x y=0 := by
  dsimp only
  let s := g.admissibleState T labels samples
  let e := s.fullPartialEmbedding selector S hs
  let old := g.deficient.restrict S
  let new := (g.labelledResampledGraph T labels samples selector).deficient.restrict S
  have haway (x:S) (hx:x∉Set.range e) : x.val∉s.fullResampleEndpoints selector :=
    fun hm=>hx (s.fullPartialEmbedding_captures selector S hs x hm)
  have hH : ∀x y:S,x∉Set.range e∨y∉Set.range e→(new.H-old.H) x y=0 := by
    intro x y hxy
    exact s.fullResample_difference_supported selector d x.val y.val (hxy.imp (haway x) (haway y))
  exact old.extensionMatrix_difference_supported_of_H new hd (fun _=>rfl) e hH q z

theorem full_model_difference_coupling (g : RegularGraph N d) (hd : 3≤d)
    (T : Set (Fin N)) (labels : ι≃BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (hs : 1≤selector) (S : Set (Fin N)) (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) :
    let s := g.admissibleState T labels samples
    let e := s.fullPartialEmbedding selector S hs
    let old := g.deficient.restrict S
    let new := (g.labelledResampledGraph T labels samples selector).deficient.restrict S
    (new.extensionMatrix q z-old.extensionMatrix q z).submatrix e e =
      fullQuadSurgeryCoupling (s.fullInnerMate selector S) (s.fullOuterMate selector S)
        (s.fullFirstMask selector S) (s.fullSecondMask selector S) q (treeEdgeWeight d) := by
  dsimp only
  let s := g.admissibleState T labels samples
  let e := s.fullPartialEmbedding selector S hs
  let old := g.deficient.restrict S
  let new := (g.labelledResampledGraph T labels samples selector).deficient.restrict S
  have hh := old.supported_retained_inverse new hd e q z hz hq
    (g.full_model_difference_supported hd T labels samples selector hs S q z)
  have hp := g.full_partial_retained_quad_precision hd T labels samples selector hs S q z hz hq
  dsimp only at hh hp
  exact add_left_cancel (hh.2.2.symm.trans hp.2.2)

theorem full_model_endpoint_mass (g : RegularGraph N d) (hd : 3≤d)
    (T : Set (Fin N)) (labels : ι≃BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (hs : 1≤selector) (S : Set (Fin N)) (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im)
    (hαq : ‖q*treeEdgeWeight d‖≤1) :
    let s := g.admissibleState T labels samples
    let e := s.fullPartialEmbedding selector S hs
    let A := (g.deficient.restrict S).extensionMatrix q z
    let B := ((g.labelledResampledGraph T labels samples selector).deficient.restrict S).extensionMatrix q z
    (∀i,∑j,‖(B-A) (e i) (e j)‖≤4*(d:ℝ)/Real.sqrt ((d:ℝ)-1)) ∧
      (∀j,∑i,‖(B-A) (e i) (e j)‖≤4*(d:ℝ)/Real.sqrt ((d:ℝ)-1)) := by
  dsimp only
  let s := g.admissibleState T labels samples
  let e := s.fullPartialEmbedding selector S hs
  have he := g.full_model_difference_coupling hd T labels samples selector hs S q z hz hq
  have hm := s.fullQuadSurgeryCoupling_mass selector S hs d (fun v=>(g.regular v).le) q hαq
  dsimp only at hm
  constructor
  · intro i
    refine (le_of_eq ?_).trans (hm.1 i)
    apply Finset.sum_congr rfl
    intro j _
    apply congrArg norm
    refine (congrArg (fun M:Matrix (s.FullEndpointIndex selector S) (s.FullEndpointIndex selector S) ℂ=>M i j) he).trans ?_
    exact congrArg (fun M:Matrix (s.FullEndpointIndex selector S) (s.FullEndpointIndex selector S) ℂ=>M i j)
      (fullQuadSurgeryCoupling_decidableCongr _ _ _ _ (s.fullInnerMate selector S) (s.fullOuterMate selector S)
        (s.fullFirstMask selector S) (s.fullSecondMask selector S) q (treeEdgeWeight d))
  · intro j
    refine (le_of_eq ?_).trans (hm.2 j)
    apply Finset.sum_congr rfl
    intro i _
    apply congrArg norm
    refine (congrArg (fun M:Matrix (s.FullEndpointIndex selector S) (s.FullEndpointIndex selector S) ℂ=>M i j) he).trans ?_
    exact congrArg (fun M:Matrix (s.FullEndpointIndex selector S) (s.FullEndpointIndex selector S) ℂ=>M i j)
      (fullQuadSurgeryCoupling_decidableCongr _ _ _ _ (s.fullInnerMate selector S) (s.fullOuterMate selector S)
        (s.fullFirstMask selector S) (s.fullSecondMask selector S) q (treeEdgeWeight d))

theorem full_new_target_endpoint_row (g : RegularGraph N d) (hd : 3≤d)
    (T : Set (Fin N)) (labels : ι≃BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (hs : 1≤selector) (S : Set (Fin N)) (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im)
    (hαq : ‖q*treeEdgeWeight d‖≤1) (a C:ℝ) (ha:0≤a) (hC:0≤C) :
    let s := g.admissibleState T labels samples
    let e := s.fullPartialEmbedding selector S hs
    let old := g.deficient.restrict S
    let new := (g.labelledResampledGraph T labels samples selector).deficient.restrict S
    ∀x:S,(∑i,‖old.extensionGreen q z x (e i)‖)≤a →
      (∀i,∑j,‖new.extensionGreen q z (e i) (e j)‖≤C) →
      (∑i,‖new.extensionGreen q z x (e i)‖)≤a*(1+(4*(d:ℝ)/Real.sqrt ((d:ℝ)-1))*C) := by
  dsimp only
  let s := g.admissibleState T labels samples
  let e := s.fullPartialEmbedding selector S hs
  let old := g.deficient.restrict S
  let new := (g.labelledResampledGraph T labels samples selector).deficient.restrict S
  intro x hOld hNew
  exact inverse_supported_endpoint_row_sum (old.extensionMatrix q z) (new.extensionMatrix q z)
    (old.extensionMatrix_isUnit hd q z hz hq) (new.extensionMatrix_isUnit hd q z hz hq) e
    (g.full_model_difference_supported hd T labels samples selector hs S q z) a C _ ha hC (by positivity)
    x hOld hNew (g.full_model_endpoint_mass hd T labels samples selector hs S q z hz hq hαq).1

end RegularGraph
end LocalLaw
