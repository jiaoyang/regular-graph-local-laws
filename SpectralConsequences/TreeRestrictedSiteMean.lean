import SpectralConsequences.TreeRestrictedResiduals
import LocalLaw.GraphConcentration

/-! The tree-restricted residuals are the literal site means in the finite
reversible moment identity. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance treeRestrictedSiteMeanDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem restrictedVertexMean_eq_site_mean {N:ℕ}(good:Fin N→Prop)(f:Fin N→ℂ):
    restrictedVertexMean good f=finiteComplexMean (fun i=>if good i then f i else 0):=by
  simp only [restrictedVertexMean,finiteComplexMean,Fintype.card_fin,Complex.real_smul,
    Complex.ofReal_inv,Complex.ofReal_natCast]

namespace RegularGraph
variable {N d:ℕ}

theorem treeRestrictedCavityResidual_eq_site_mean (g:LocalLaw.RegularGraph N d)(R ell:ℕ)(z:ℂ):
    treeRestrictedCavityResidual g R ell z=finiteComplexMean (fun o:Fin N=>
      if (graphBall g.graph o R).IsTree then
        cavityAtVertex g.graph d z o-(cavityIterate z (g.Q z) (ell+1)+trivialCavityCorrection N d ell z) else 0):=by
  unfold treeRestrictedCavityResidual
  rw [restrictedVertexMean_eq_site_mean]
  simp only [sub_add_eq_sub_sub]

theorem treeRestrictedTraceResidual_eq_site_mean (g:LocalLaw.RegularGraph N d)(R ell:ℕ)(z:ℂ):
    treeRestrictedTraceResidual g R ell z=finiteComplexMean (fun o:Fin N=>
      if (graphBall g.graph o R).IsTree then
        g.G z o o-(regularRootValue d ell (g.Q z) z+trivialTraceCorrection N d ell z) else 0):=by
  unfold treeRestrictedTraceResidual
  rw [restrictedVertexMean_eq_site_mean]
  simp only [sub_add_eq_sub_sub]

end RegularGraph
end SpectralConsequences
