import LocalLaw.EligibleBoundaryCavity

/-! # Exact old endpoint rows at every accepted boundary root

The accepted central tree is isolated from every other endpoint root. Its
actual finite kernel row is exactly diagonal with the scalar cavity value.
-/

noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance eligibleBoundaryRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type*}

theorem eligible_boundary_ball_subset_model (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (i : s.AdmissibleSampleIndex selector) :
    graphBallVertices (outsideGraph s.graph T) (boundaryOuterEndpoint s.graph T (s.boundary i.val)) r ⊆
      s.endpointModelVertices selector r := by
  intro v hv
  exact ⟨_, Or.inl ⟨s.boundary i.val, rfl⟩, hv⟩

theorem eligible_boundary_ball_old_cut (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2 * r + 2 ≤ selector) (i : s.AdmissibleSampleIndex selector) :
    ∀ x ∈ s.endpointModelVertices selector r,
      x ∈ graphBallVertices (outsideGraph s.graph T) (boundaryOuterEndpoint s.graph T (s.boundary i.val)) r →
      ∀ y ∈ s.endpointModelVertices selector r,
        y ∉ graphBallVertices (outsideGraph s.graph T) (boundaryOuterEndpoint s.graph T (s.boundary i.val)) r →
        ¬(outsideGraph s.graph T).Adj x y := by
  intro x _ hx y hy hyn hxy
  have hxc : x ∈ s.centralEndpointPatch r := ⟨_, ⟨s.boundary i.val, rfl⟩, hx⟩
  rcases s.endpointModelVertices_cell_cover selector r y hy with hyc | ⟨j, hyj⟩
  · rcases hyc with ⟨a, ⟨β, rfl⟩, hβ⟩
    by_cases hβi : β = s.boundary i.val
    · exact hyn (by simpa only [hβi] using hβ)
    · exact graphBalls_no_edge_of_edist_gt (outsideGraph s.graph T)
        (boundaryOuterEndpoint s.graph T (s.boundary i.val)) (boundaryOuterEndpoint s.graph T β) r
        ((ENat.coe_le_coe.mpr (by omega : 2 * r + 1 ≤ selector)).trans_lt
          (s.eligible_boundary_root_far selector i β hβi)) x hx y hβ hxy
  · exact (s.central_sampledEndpointPatch_disjoint_no_edge selector r hsep j).2 x hxc y hyj hxy

theorem eligible_boundary_ball_only_endpoint (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2 * r + 2 ≤ selector) (i : s.AdmissibleSampleIndex selector)
    (v : s.endpointModelRoots selector)
    (hv : v.val ∈ graphBallVertices (outsideGraph s.graph T)
      (boundaryOuterEndpoint s.graph T (s.boundary i.val)) r) :
    v.val = boundaryOuterEndpoint s.graph T (s.boundary i.val) := by
  have hc : v.val ∈ s.centralEndpointPatch r := ⟨_, ⟨s.boundary i.val, rfl⟩, hv⟩
  obtain ⟨β, hβ⟩ := s.endpointRoot_in_central_is_boundary selector r hsep v hc
  have he := s.eligible_boundary_label_unique_in_ball selector r (by omega) i v.val hv β hβ
  have he' : boundaryOuterEndpoint s.graph T (s.boundary i.val) = v.val := by
    simpa only [he] using hβ
  exact he'.symm

end LabelledResamplingState

namespace RegularGraph
variable {N d : ℕ} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem endpointModel_accepted_boundary_diagonal (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector)
    (i : (g.admissibleState T boundary S).AdmissibleSampleIndex selector)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let s := g.admissibleState T boundary S
    (g.endpointModel T boundary S selector r).extensionGreen q z
      (s.endpointBoundaryRoot selector r (boundary i.val))
      (s.endpointBoundaryRoot selector r (boundary i.val)) = cavityIterate z q (r + 1) := by
  dsimp only
  let s := g.admissibleState T boundary S
  let H := outsideGraph g.graph T
  let a := boundaryOuterEndpoint g.graph T (boundary i.val)
  let B := graphBallVertices H a r
  let K := s.endpointModelVertices selector r
  let F : Set K := {v | v.val ∈ B}
  let M := g.endpointModel T boundary S selector r
  let MB := (g.deficient.delete T).restrict B
  let root : F := ⟨s.endpointBoundaryRoot selector r (boundary i.val), by
    change H.edist a a ≤ (r : ℕ∞)
    simp⟩
  let e : (M.restrict F).graph ≃g MB.graph :=
    inducePreimageIso H K B (s.eligible_boundary_ball_subset_model selector r i)
  have hcut : ∀ x ∈ F, ∀ y ∉ F, ¬M.graph.Adj x y := by
    intro x hx y hy
    exact s.eligible_boundary_ball_old_cut selector r hsep i x.val x.property hx y.val y.property hy
  have hblock := M.restrict_extensionGreen_of_isolated hd F hcut q z hz hq
  have hblockEntry : (M.restrict F).extensionGreen q z root root =
      M.extensionGreen q z (s.endpointBoundaryRoot selector r (boundary i.val))
        (s.endpointBoundaryRoot selector r (boundary i.val)) :=
    congrFun (congrFun hblock root) root
  have hiso := MB.extensionGreen_iso (M.restrict F) e (fun _ => rfl) q z
  have hisoEntry : MB.extensionGreen q z (cavityBallRoot H a r) (cavityBallRoot H a r) =
      (M.restrict F).extensionGreen q z root root := congrFun (congrFun hiso root) root
  have hY := g.eligible_boundary_ball_diagonal hd T boundary S selector r (by omega) i q z hz hq
  exact hblockEntry.symm.trans (hisoEntry.symm.trans hY)

omit [Fintype ι] in
theorem endpointModel_accepted_boundary_endpoint_row (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector)
    (i : (g.admissibleState T boundary S).AdmissibleSampleIndex selector)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (v : (g.admissibleState T boundary S).endpointModelRoots selector) :
    let s := g.admissibleState T boundary S
    let e := s.endpointModelKernelEmbedding selector r
    let own := s.endpointRootLabel selector (Sum.inl (boundary i.val))
    (g.endpointModel T boundary S selector r).extensionGreen q z (e own) (e v) =
      if v = own then cavityIterate z q (r + 1) else 0 := by
  dsimp only
  let s := g.admissibleState T boundary S
  let own := s.endpointRootLabel selector (Sum.inl (boundary i.val))
  by_cases hv : v = own
  · rw [if_pos hv, hv]
    exact g.endpointModel_accepted_boundary_diagonal hd T boundary S selector r hsep i q z hz hq
  · rw [if_neg hv]
    let H := outsideGraph g.graph T
    let a := boundaryOuterEndpoint g.graph T (boundary i.val)
    let B := graphBallVertices H a r
    let F : Set (s.endpointModelVertices selector r) := {v | v.val ∈ B}
    let M := g.endpointModel T boundary S selector r
    have hcut : ∀ x ∈ F, ∀ y ∉ F, ¬M.graph.Adj x y := by
      intro x hx y hy
      exact s.eligible_boundary_ball_old_cut selector r hsep i x.val x.property hx y.val y.property hy
    have hstart : s.endpointModelKernelEmbedding selector r own ∈ F := by
      change H.edist a a ≤ (r : ℕ∞)
      simp
    have hnot : s.endpointModelKernelEmbedding selector r v ∉ F := fun h =>
      hv (Subtype.ext (s.eligible_boundary_ball_only_endpoint selector r hsep i v h))
    exact M.extensionGreen_zero_across_cut hd F hcut q z hz hq
      (s.endpointModelKernelEmbedding selector r own) hstart (s.endpointModelKernelEmbedding selector r v) hnot

omit [Fintype ι] in
theorem endpointModel_boundary_sampledPatch_cross_zero (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector)
    (i : (g.admissibleState T boundary S).AdmissibleSampleIndex selector)
    (β : BoundaryOrientedEdge g.graph T)
    (x : (g.admissibleState T boundary S).endpointModelVertices selector r)
    (hx : x.val ∈ (g.admissibleState T boundary S).sampledEndpointPatch selector r i)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let s := g.admissibleState T boundary S
    let M := g.endpointModel T boundary S selector r
    M.extensionGreen q z (s.endpointBoundaryRoot selector r β) x = 0 ∧
      M.extensionGreen q z x (s.endpointBoundaryRoot selector r β) = 0 := by
  dsimp only
  let s := g.admissibleState T boundary S
  let M := g.endpointModel T boundary S selector r
  let F : Set (s.endpointModelVertices selector r) := {v | v.val ∈ s.centralEndpointPatch r}
  have hcut : ∀ u ∈ F, ∀ v ∉ F, ¬M.graph.Adj u v := by
    intro u hu v hv
    exact s.endpointModel_central_closed selector r hsep u.val u.property hu v.val v.property hv
  have hstart : s.endpointBoundaryRoot selector r β ∈ F := s.endpointBoundaryRoot_mem_central selector r β
  have hxnot : x ∉ F := fun h =>
    Set.disjoint_left.mp (s.central_sampledEndpointPatch_disjoint_no_edge selector r hsep i).1 h hx
  constructor
  · exact M.extensionGreen_zero_across_cut hd F hcut q z hz hq
      (s.endpointBoundaryRoot selector r β) hstart x hxnot
  · have hcut' : ∀ u ∈ Fᶜ, ∀ v ∉ Fᶜ, ¬M.graph.Adj u v := by
      intro u hu v hv huv
      exact hcut v (not_not.mp hv) u hu huv.symm
    exact M.extensionGreen_zero_across_cut hd Fᶜ hcut' q z hz hq x hxnot
      (s.endpointBoundaryRoot selector r β) (not_not.mpr hstart)

end RegularGraph
end LocalLaw
