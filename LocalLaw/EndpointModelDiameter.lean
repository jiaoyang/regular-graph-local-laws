import LocalLaw.SetBallComponentDiameter
import LocalLaw.EndpointModelInvariance
import LocalLaw.SourceSingletonObservation

/-!
# Actual common endpoint-model diameter at both graphs

Old and new neighborhoods are literally the same vertex set. Their proved
component endpoint counts control intrinsic diameter by finite ball covers;
no total-label-count factor enters the feedback parameter.
-/

noncomputable section
namespace LocalLaw
local instance endpointModelDiameterDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} [Fintype V] {T : Set V} {ι : Type*} [Fintype ι]

def endpointModelKernelEmbedding (s : LabelledResamplingState V T ι) (selector r : ℕ) :
    s.endpointModelRoots selector ↪ s.endpointModelVertices selector r where
  toFun := setBallRoot (outsideGraph s.graph T) (s.endpointModelRoots selector) r
  inj' := by
    intro a b hab
    exact Subtype.ext (congrArg (fun v : s.endpointModelVertices selector r => v.val) hab)

omit [Fintype ι] in
theorem endpointModel_old_distance_bound (s : LabelledResamplingState V T ι)
    (selector r m : ℕ) (hm : 1 ≤ m)
    (hcount : ∀ c : ((outsideGraph s.graph T).induce (s.endpointModelVertices selector r)).ConnectedComponent,
      Nat.card {a : s.endpointModelRoots selector // s.endpointModelKernelEmbedding selector r a ∈ c.supp} ≤ m)
    (x y : s.endpointModelVertices selector r) :
    ((outsideGraph s.graph T).induce (s.endpointModelVertices selector r)).dist x y ≤ m * (2 * r + 1) :=
  setBall_restriction_distance_bound (outsideGraph s.graph T) (s.endpointModelVertices selector r)
    (s.endpointModelRoots selector) r m hm rfl (s.endpointModelKernelEmbedding selector r)
    (fun _ => rfl) hcount x y

theorem endpointModel_new_distance_bound (s : LabelledResamplingState V T ι)
    (selector r m : ℕ) (hm : 1 ≤ m)
    (hcount : ∀ c : ((outsideGraph (s.fullResample selector).graph T).induce
      (s.endpointModelVertices selector r)).ConnectedComponent,
      Nat.card {a : s.endpointModelRoots selector // s.endpointModelKernelEmbedding selector r a ∈ c.supp} ≤ m)
    (x y : s.endpointModelVertices selector r) :
    ((outsideGraph (s.fullResample selector).graph T).induce (s.endpointModelVertices selector r)).dist x y ≤
      m * (2 * r + 1) :=
  setBall_restriction_distance_bound (outsideGraph (s.fullResample selector).graph T)
    (s.endpointModelVertices selector r) (s.endpointModelRoots selector) r m hm
    (s.endpointModelVertices_fullResample selector r) (s.endpointModelKernelEmbedding selector r)
    (fun _ => rfl) hcount x y

end LabelledResamplingState

theorem endpoint_component_diameter_le_observation (d r : ℕ) :
    (2 * (finiteOmega d + 1)) * (2 * r + 1) ≤ singletonObservationDiameter d r := by
  unfold singletonObservationDiameter
  nlinarith only [Nat.zero_le (finiteOmega d)]

end LocalLaw
