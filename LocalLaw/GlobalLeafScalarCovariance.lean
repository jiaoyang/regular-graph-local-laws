import LocalLaw.LeafScalarCovariance
import LocalLaw.ComponentBallGeometry

/-! # The unrestricted scalar leaf covariance from the actual finite model -/

noncomputable section
namespace LocalLaw
local instance globalLeafScalarCovarianceDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] {d : ℕ}

theorem leaf_scalar_covariance (g : DeficientGraph V d) (hd : 3≤d)
    (hbudget : g.ComponentFiniteReferenceBudget) (e : I↪V) (r R : ℕ)
    (htree : ∀i,(graphBall g.graph (e i) r).IsTree)
    (hzero : ∀i,∀w∈graphBallVertices g.graph (e i) r,g.deficit w=0)
    (hsep : ∀i j,i≠j→((2*r:ℕ):ℕ∞)≤g.graph.edist (e i) (e j))
    (q p z : ℂ) (hq : q≠0) (hp : p*(q⁻¹-q/((d:ℂ)-1))=1) (hz : 0<z.im) (hqim : 0≤q.im)
    (B C1 ε L A : ℝ) (hzB : ‖z‖≤B) (num : SourceObservationBounds d r z B C1 ε L A)
    (hprior : ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z) ε)
    (hR : ∀a b,g.graph.dist a b≤R) (hRlog : (R:ℝ)+1≤A*L)
    (hpbound : ‖p‖≤4) (hqinv : ‖q⁻¹‖≤2*(B+1)) (hqpow : ∀n≤4*r+1,‖q‖^n≤2) :
    IsUnit ((g.extensionGreen q z).submatrix e e) ∧
      ∀i j,‖g.extensionGreen q z (e i) (e j)-(if i=j then p else 0)‖≤
        (treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d)*C1^2*L*ε := by
  let U : Set V:=Set.univ
  letI : DecidablePred (fun v:V=>v∈U):=fun _=>Classical.propDecidable _
  letI : Fintype U:=Subtype.fintype (fun v:V=>v∈U)
  let e' : I↪U:={toFun:=fun i=>⟨e i,Set.mem_univ _⟩,inj':=fun _ _ h=>e.injective (congrArg Subtype.val h)}
  have hR' : ∀a b,(g.restrict U).graph.dist a b≤R := by
    intro a b
    have he:=graphIso_dist (SimpleGraph.induceUnivIso g.graph) a b
    exact he.symm.le.trans (hR a.val b.val)
  have hh:=g.restricted_leaf_scalar_covariance hd U (g.restrict_componentFiniteReferenceBudget U hbudget)
    e' r R htree hzero hsep q p z hq hp hz hqim B C1 ε L A hzB num hprior hR' hRlog hpbound hqinv hqpow
  have hGreen: (g.restrict U).extensionGreen q z=
      (g.extensionGreen q z).submatrix (Subtype.val:U→V) (Subtype.val:U→V) :=
    g.restrict_extensionGreen_of_isolated hd U (by intro a ha b hb;exact (hb (Set.mem_univ b)).elim)
      q z hz hqim
  dsimp only at hh
  rw [hGreen] at hh
  exact hh

end DeficientGraph
end LocalLaw
