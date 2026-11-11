import SpectralConsequences.SwitchedBoundaryObservables
import SpectralConsequences.SampledSingletonMinor
import SpectralConsequences.ProductCoordinateMeans
import SpectralConsequences.EndpointQuadraticMean
import SpectralConsequences.FiniteGoodSetMean

/-! # Conditional boundary-entry means under the genuine sampling fiber

The independent-coordinate law is proved by finite function-space
equivalences. The exceptional contribution is its actual sampling mass.
-/
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
namespace SpectralConsequences
open LocalLaw
local instance boundaryConditionalMeansDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ} {T:Set (Fin N)} {ι:Type} [Fintype ι]

def allSamplesEligible (g:LocalLaw.RegularGraph N d)
    (labels:ι≃BoundaryOrientedEdge g.graph T) (selector:ℕ)
    (S:LocalSamplingFiber g.graph T) : Prop :=
  ∀j:ι,(g.admissibleState T labels S).Eligible selector j

omit [Fintype ι] in
theorem sampledBoundaryLeading_norm (g:LocalLaw.RegularGraph N d)
    (labels:ι≃BoundaryOrientedEdge g.graph T) (S:LocalSamplingFiber g.graph T)
    (z:ℂ) (j k:ι) (C:ℝ) (_hC:0≤C)
    (hG:∀u v,‖g.G z u v‖≤C) (ha:‖treeEdgeWeight d*g.Q z‖≤1) :
    ‖sampledBoundaryLeading g labels S z j k‖≤4*C := by
  let A:=treeEdgeWeight d*g.Q z
  have hterm (u v:Fin N):‖A*g.G z u v‖≤C:=by
    rw [norm_mul]
    exact (mul_le_mul ha (hG u v) (norm_nonneg _) (by norm_num)).trans_eq (one_mul C)
  have hterm2 (u v:Fin N):‖A^2*g.G z u v‖≤C:=by
    rw [norm_mul,norm_pow]
    exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ha 2) (hG u v)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  dsimp only [sampledBoundaryLeading]
  have h : ‖g.G z (S (labels j)).val.2 (S (labels k)).val.2+
      A*g.G z (S (labels j)).val.1 (S (labels k)).val.2+
      A*g.G z (S (labels j)).val.2 (S (labels k)).val.1+
      A^2*g.G z (S (labels j)).val.1 (S (labels k)).val.1‖ ≤ C+C+C+C :=
    (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (hG _ _) (hterm _ _))) (hterm _ _))) (hterm2 _ _))
  linarith

omit [Fintype ι] in
theorem sampledBoundaryLeading_mean (g:LocalLaw.RegularGraph N d)
    (labels:ι≃BoundaryOrientedEdge g.graph T) [Nonempty (OutsideOrientedEdge g.graph T)]
    (z:ℂ) (j k:ι) (hjk:j≠k) :
    finiteComplexMean (fun S:LocalSamplingFiber g.graph T=>sampledBoundaryLeading g labels S z j k)=
      finiteComplexMean (fun e:OutsideOrientedEdge g.graph T=>
        finiteComplexMean (fun f:OutsideOrientedEdge g.graph T=>
          g.G z e.val.2 f.val.2+(treeEdgeWeight d*g.Q z)*g.G z e.val.1 f.val.2+
          (treeEdgeWeight d*g.Q z)*g.G z e.val.2 f.val.1+
          (treeEdgeWeight d*g.Q z)^2*g.G z e.val.1 f.val.1)) := by
  exact uniform_function_two_coordinate_mean (E:=OutsideOrientedEdge g.graph T)
    (I:=BoundaryOrientedEdge g.graph T) (labels j) (labels k)
    (fun h=>hjk (labels.injective h))
    (fun e f:OutsideOrientedEdge g.graph T=>
      g.G z e.val.2 f.val.2+(treeEdgeWeight d*g.Q z)*g.G z e.val.1 f.val.2+
      (treeEdgeWeight d*g.Q z)*g.G z e.val.2 f.val.1+
      (treeEdgeWeight d*g.Q z)^2*g.G z e.val.1 f.val.1)

theorem switched_boundary_offdiag_mean (g:LocalLaw.RegularGraph N d)
    (labels:ι≃BoundaryOrientedEdge g.graph T) (selector:ℕ)
    (hN:0<N) (hd:0<d) (hT:4*Nat.card T≤N) (z:ℂ) (hz:0<z.im)
    (j k:ι) (hjk:j≠k) (C V err:ℝ) (hC:0≤C) (herr:0≤err)
    (hG:∀u v,‖g.G z u v‖≤C) (ha:‖treeEdgeWeight d*g.Q z‖≤1)
    (hV:∀S,‖switchedBoundaryEntry g labels S selector z j k‖≤V)
    (hgood:∀S,allSamplesEligible g labels selector S→
      ‖switchedBoundaryEntry g labels S selector z j k-sampledBoundaryLeading g labels S z j k‖≤err) :
    ‖finiteComplexMean (fun S:LocalSamplingFiber g.graph T=>switchedBoundaryEntry g labels S selector z j k)-
      (1+treeEdgeWeight d*g.Q z)^2*((N:ℂ)⁻¹*(treeEdgeWeight d*(d:ℂ)-z)⁻¹)‖≤
      err+(V+4*C)*eventMass (localSamplingWeight g.graph T)
        (fun S=>¬allSamplesEligible g labels selector S)+32*C*(Nat.card T:ℝ)/(N:ℝ) := by
  letI : Nonempty (OutsideOrientedEdge g.graph T):=g.outside_edge_nonempty T hN hd hT
  letI : Nonempty (LocalSamplingFiber g.graph T):=⟨fun _=>Classical.choice inferInstance⟩
  have hbad (S:LocalSamplingFiber g.graph T) (_h:¬allSamplesEligible g labels selector S):
      ‖switchedBoundaryEntry g labels S selector z j k-sampledBoundaryLeading g labels S z j k‖≤V+4*C:=
    (norm_sub_le _ _).trans (add_le_add (hV S) (sampledBoundaryLeading_norm g labels S z j k C hC hG ha))
  have hc:=finiteComplexMean_comparison_of_good_event (allSamplesEligible g labels selector)
    (fun S=>switchedBoundaryEntry g labels S selector z j k)
    (fun S=>sampledBoundaryLeading g labels S z j k) err (V+4*C) herr hgood hbad
  have hm:=outside_quadratic_green_mean g T hN hd hT z hz C hC hG (treeEdgeWeight d*g.Q z) ha
  rw [←sampledBoundaryLeading_mean g labels z j k hjk] at hm
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hc hm)

theorem switched_boundary_diagonal_mean (g:LocalLaw.RegularGraph N d)
    (labels:ι≃BoundaryOrientedEdge g.graph T) (selector:ℕ)
    (hN:0<N) (hd:0<d) (hT:4*Nat.card T≤N) (z:ℂ) (hz:0<z.im)
    (j:ι) (C P V Qcap err:ℝ) (hC:0≤C) (hP:0≤P) (herr:0≤err)
    (hG:∀u v,‖g.G z u v‖≤C) (hGi:∀u,‖(g.G z u u)⁻¹‖≤P) (hQ:‖g.Q z‖≤Qcap)
    (hV:∀S,‖switchedBoundaryEntry g labels S selector z j j-g.Q z‖≤V)
    (hgood:∀S,allSamplesEligible g labels selector S→
      ‖switchedBoundaryEntry g labels S selector z j j-
        fullEdgeCavity g z ⟨(S (labels j)).val,(S (labels j)).property.1⟩‖≤err) :
    ‖finiteComplexMean (fun S:LocalSamplingFiber g.graph T=>switchedBoundaryEntry g labels S selector z j j-g.Q z)‖≤
      err+(V+C+C^2*P+Qcap)*eventMass (localSamplingWeight g.graph T)
        (fun S=>¬allSamplesEligible g labels selector S)+
      4*(C+C^2*P)*(Nat.card T:ℝ)/(N:ℝ) := by
  letI : Nonempty (OutsideOrientedEdge g.graph T):=g.outside_edge_nonempty T hN hd hT
  letI : Nonempty (LocalSamplingFiber g.graph T):=⟨fun _=>Classical.choice inferInstance⟩
  let f:=fun S:LocalSamplingFiber g.graph T=>switchedBoundaryEntry g labels S selector z j j-g.Q z
  let h:=fun S:LocalSamplingFiber g.graph T=>
    fullEdgeCavity g z ⟨(S (labels j)).val,(S (labels j)).property.1⟩-g.Q z
  have hbad (S:LocalSamplingFiber g.graph T) (_h:¬allSamplesEligible g labels selector S):
      ‖f S-h S‖≤V+C+C^2*P+Qcap:=by
    have hh:‖h S‖≤C+C^2*P+Qcap:=
      (norm_sub_le _ _).trans (add_le_add
        (matrixCavityTerm_norm_bound _ C P hC hP hG hGi _ _) hQ)
    exact ((norm_sub_le _ _).trans (add_le_add (hV S) hh)).trans_eq (by ring)
  have hgood' (S:LocalSamplingFiber g.graph T) (hs:allSamplesEligible g labels selector S):
      ‖f S-h S‖≤err:=by
    dsimp only [f,h]
    simpa only [sub_sub_sub_cancel_right] using hgood S hs
  have hc:=finiteComplexMean_comparison_of_good_event (allSamplesEligible g labels selector)
    f h err (V+C+C^2*P+Qcap) herr hgood' hbad
  have hmean:finiteComplexMean h=
      finiteComplexMean (fun e:OutsideOrientedEdge g.graph T=>fullEdgeCavity g z ⟨e.val,e.property.1⟩)-g.Q z:=by
    dsimp only [h]
    rw [finiteComplexMean_sub,finiteComplexMean_const]
    exact congrArg (fun w:ℂ=>w-g.Q z)
      (uniform_function_coordinate_mean (E:=OutsideOrientedEdge g.graph T)
        (I:=BoundaryOrientedEdge g.graph T) (labels j)
        (fun e:OutsideOrientedEdge g.graph T=>fullEdgeCavity g z ⟨e.val,e.property.1⟩))
  have hm:=outside_full_cavity_mean g T hN hd hT z hz C P hC hP hG hGi
  rw [←hmean] at hm
  calc
    _ = ‖(finiteComplexMean f-finiteComplexMean h)+finiteComplexMean h‖:=by rw [sub_add_cancel]
    _ ≤ ‖finiteComplexMean f-finiteComplexMean h‖+‖finiteComplexMean h‖:=norm_add_le _ _
    _ ≤ _:=add_le_add hc hm

end RegularGraph
end SpectralConsequences
