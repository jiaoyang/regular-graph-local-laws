import SpectralConsequences.RegularRootRecursion
import SpectralConsequences.TrivialCorrections
import LocalLaw.CavityAverage
import LocalLaw.SourceLocalCertificate
import SpectralConsequences.FiniteResolventSpectrum

/-! Actual tree-restricted graph residuals and exact removal of the cutoff. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance treeRestrictedResidualsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def restrictedVertexMean {N:ℕ}(good:Fin N→Prop)(f:Fin N→ℂ):ℂ:=
  (N:ℂ)⁻¹*∑i,if good i then f i else 0

theorem restrictedVertexMean_error {N:ℕ}(good:Fin N→Prop)(f:Fin N→ℂ)(M:ℝ)
    (_hM:0≤M)(hbad:∀i,¬good i→‖f i‖≤M):
    ‖(N:ℂ)⁻¹*∑i,f i-restrictedVertexMean good f‖≤
      (((Finset.univ.filter (fun i:Fin N=>¬good i)).card:ℝ)/(N:ℝ))*M:=by
  have hsplit:(∑i,f i)-(∑i,if good i then f i else 0)=
      ∑i,if good i then 0 else f i:=by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi:good i <;> simp only [hi,if_true,if_false,sub_self,sub_zero]
  have hsum:‖∑i,if good i then 0 else f i‖≤
      ((Finset.univ.filter (fun i:Fin N=>¬good i)).card:ℝ)*M:=by
    apply (norm_sum_le _ _).trans
    calc
      _≤∑i:Fin N,if good i then 0 else M:=by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi:good i
        · simp only [hi,if_true,norm_zero]; exact le_rfl
        · simpa only [hi,if_false] using hbad i hi
      _=∑i∈Finset.univ.filter (fun i:Fin N=>¬good i),M:=by
        simp only [Finset.sum_filter,ite_not]
      _=_:=by rw [Finset.sum_const,nsmul_eq_mul]
  unfold restrictedVertexMean
  rw [←mul_sub,hsplit,norm_mul,norm_inv,Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg N))).trans_eq
  ring

namespace RegularGraph
variable {N d:ℕ}

def treeRestrictedCavityResidual (g:LocalLaw.RegularGraph N d)(R ell:ℕ)(z:ℂ):ℂ:=
  restrictedVertexMean (fun o=>(graphBall g.graph o R).IsTree)
    (fun o=>cavityAtVertex g.graph d z o-cavityIterate z (g.Q z) (ell+1)-trivialCavityCorrection N d ell z)

def treeRestrictedTraceResidual (g:LocalLaw.RegularGraph N d)(R ell:ℕ)(z:ℂ):ℂ:=
  restrictedVertexMean (fun o=>(graphBall g.graph o R).IsTree)
    (fun o=>g.G z o o-regularRootValue d ell (g.Q z) z-trivialTraceCorrection N d ell z)

theorem Q_eq_vertex_mean (g:LocalLaw.RegularGraph N d)(z:ℂ):
    g.Q z=(N:ℂ)⁻¹*∑o:Fin N,cavityAtVertex g.graph d z o:=by
  have h:=cavityAverage_eq_mean g.graph d z
  simpa only [LocalLaw.RegularGraph.Q,Fintype.card_fin,Complex.real_smul,
    Complex.ofReal_inv,Complex.ofReal_natCast] using h

theorem residual_vertex_mean {N:ℕ}(hN:0<N)(f:Fin N→ℂ)(target:ℂ):
    (N:ℂ)⁻¹*∑i,f i-target=(N:ℂ)⁻¹*∑i,(f i-target):=by
  rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hNc:(N:ℂ)≠0:=Nat.cast_ne_zero.mpr (by omega)
  field_simp

theorem treeRestrictedCavityResidual_error (g:LocalLaw.RegularGraph N d)(hN:0<N)
    (R ell:ℕ)(z:ℂ)(M:ℝ)(hM:0≤M)
    (hbad:∀o,¬(graphBall g.graph o R).IsTree→
      ‖cavityAtVertex g.graph d z o-cavityIterate z (g.Q z) (ell+1)-trivialCavityCorrection N d ell z‖≤M):
    ‖g.Q z-cavityIterate z (g.Q z) (ell+1)-trivialCavityCorrection N d ell z-
      treeRestrictedCavityResidual g R ell z‖≤
      ((nonTreeCenters g.graph R).card:ℝ)/(N:ℝ)*M:=by
  have hfull:g.Q z-cavityIterate z (g.Q z) (ell+1)-trivialCavityCorrection N d ell z=
      (N:ℂ)⁻¹*∑i,(cavityAtVertex g.graph d z i-cavityIterate z (g.Q z) (ell+1)-trivialCavityCorrection N d ell z):=by
    have hh:=residual_vertex_mean hN (cavityAtVertex g.graph d z)
      (cavityIterate z (g.Q z) (ell+1)+trivialCavityCorrection N d ell z)
    rw [←Q_eq_vertex_mean g z] at hh
    simpa only [sub_add_eq_sub_sub] using hh
  rw [hfull]
  have hbadset:Finset.univ.filter (fun o:Fin N=>¬(graphBall g.graph o R).IsTree)=
      nonTreeCenters g.graph R:=by
    ext o
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,nonTreeCenters_membership]
  simpa only [treeRestrictedCavityResidual,hbadset] using
    restrictedVertexMean_error (fun o=>(graphBall g.graph o R).IsTree)
      (fun o=>cavityAtVertex g.graph d z o-
        cavityIterate z (g.Q z) (ell+1)-trivialCavityCorrection N d ell z) M hM hbad

theorem empiricalTransform_eq_vertex_mean (g:LocalLaw.RegularGraph N d)(z:ℂ):
    empiricalTransform g.H z=(N:ℂ)⁻¹*∑o:Fin N,g.G z o o:=by
  simp only [empiricalTransform,Fintype.card_fin,Matrix.trace,Matrix.diag_apply,LocalLaw.RegularGraph.G]

theorem treeRestrictedTraceResidual_error (g:LocalLaw.RegularGraph N d)(hN:0<N)
    (R ell:ℕ)(z:ℂ)(M:ℝ)(hM:0≤M)
    (hbad:∀o,¬(graphBall g.graph o R).IsTree→
      ‖g.G z o o-regularRootValue d ell (g.Q z) z-trivialTraceCorrection N d ell z‖≤M):
    ‖empiricalTransform g.H z-regularRootValue d ell (g.Q z) z-trivialTraceCorrection N d ell z-
      treeRestrictedTraceResidual g R ell z‖≤
      ((nonTreeCenters g.graph R).card:ℝ)/(N:ℝ)*M:=by
  have hfull:empiricalTransform g.H z-regularRootValue d ell (g.Q z) z-trivialTraceCorrection N d ell z=
      (N:ℂ)⁻¹*∑i,(g.G z i i-regularRootValue d ell (g.Q z) z-trivialTraceCorrection N d ell z):=by
    have hh:=residual_vertex_mean hN (fun i=>g.G z i i)
      (regularRootValue d ell (g.Q z) z+trivialTraceCorrection N d ell z)
    rw [←empiricalTransform_eq_vertex_mean g z] at hh
    simpa only [sub_add_eq_sub_sub] using hh
  rw [hfull]
  have hbadset:Finset.univ.filter (fun o:Fin N=>¬(graphBall g.graph o R).IsTree)=
      nonTreeCenters g.graph R:=by
    ext o
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,nonTreeCenters_membership]
  simpa only [treeRestrictedTraceResidual,hbadset] using
    restrictedVertexMean_error (fun o=>(graphBall g.graph o R).IsTree)
      (fun o=>g.G z o o-regularRootValue d ell (g.Q z) z-trivialTraceCorrection N d ell z) M hM hbad

end RegularGraph
end SpectralConsequences
