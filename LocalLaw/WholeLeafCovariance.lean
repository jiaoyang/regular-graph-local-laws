import LocalLaw.LeafScalarCovariance
import LocalLaw.DeficientGraphIso

/-! # Scalar covariance for an actual whole completed model -/

noncomputable section
set_option maxHeartbeats 2000000
namespace LocalLaw
local instance wholeLeafCovarianceDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V I : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]{d : ℕ}

private theorem whole_leaf_scalar_covariance_aux (g : DeficientGraph V d)(hd : 3≤d)
    (S : Set V)(hS : ∀v,v∈S)
    (hb : g.ComponentFiniteReferenceBudget)(e : I↪V)(r R : ℕ)
    (htree : ∀i,(graphBall g.graph (e i) r).IsTree)
    (hzero : ∀i,∀w∈graphBallVertices g.graph (e i) r,g.deficit w=0)
    (hsep : ∀i j,i≠j→((2*r:ℕ):ℕ∞)≤g.graph.edist (e i) (e j))
    (q p z : ℂ)(hq : q≠0)(hp : p*(q⁻¹-q/((d:ℂ)-1))=1)(hz : 0<z.im)(hqim : 0≤q.im)
    (B C1 ε L A : ℝ)(hzB : ‖z‖≤B)(num : SourceObservationBounds d r z B C1 ε L A)
    (hprior : ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z) ε)
    (hR : ∀a b,g.graph.dist a b≤R)(hRlog : (R:ℝ)+1≤A*L)
    (hpbound : ‖p‖≤4)(hqinv : ‖q⁻¹‖≤2*(B+1))(hqpow : ∀n≤4*r+1,‖q‖^n≤2) :
    let G := (g.extensionGreen q z).submatrix e e
    IsUnit G ∧ ∀i j,‖G i j-(if i=j then p else 0)‖≤
      (treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d)*C1^2*L*ε := by
  dsimp only
  letI : DecidablePred (fun v : V => v ∈ S) := fun _ => Classical.propDecidable _
  let M := g.restrict S
  let eu : M.graph ≃g g.graph :=
    {toEquiv :=
      {toFun := Subtype.val
       invFun := fun v => ⟨v,hS _⟩
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl}
     map_rel_iff' := Iff.rfl}
  let ee : I↪S := {toFun := fun i => ⟨e i,hS _⟩,inj' := fun _ _ h => e.injective (congrArg Subtype.val h)}
  have hi := g.extensionGreen_iso M eu (fun _ => rfl) q z
  have hdiam : ∀a b,M.graph.dist a b≤R := by
    intro a b
    exact (graphIso_dist eu a b).symm.le.trans (hR a.val b.val)
  have hh := g.restricted_leaf_scalar_covariance hd S (g.restrict_componentFiniteReferenceBudget S hb)
    ee r R htree hzero hsep q p z hq hp hz hqim B C1 ε L A hzB num hprior hdiam hRlog hpbound hqinv hqpow
  refine ⟨g.extensionGreen_submatrix_isUnit hd e q z hz hqim,?_⟩
  intro i j
  have hg : M.extensionGreen q z (ee i) (ee j)=g.extensionGreen q z (e i) (e j) :=
    (congrArg (fun P => P (ee i) (ee j)) hi).symm
  have hij := hh.2 i j
  change ‖M.extensionGreen q z (ee i) (ee j)-(if i=j then p else 0)‖ ≤ _ at hij
  rw [hg] at hij
  exact hij

theorem whole_leaf_scalar_covariance (g : DeficientGraph V d)(hd : 3≤d)
    (hb : g.ComponentFiniteReferenceBudget)(e : I↪V)(r R : ℕ)
    (htree : ∀i,(graphBall g.graph (e i) r).IsTree)
    (hzero : ∀i,∀w∈graphBallVertices g.graph (e i) r,g.deficit w=0)
    (hsep : ∀i j,i≠j→((2*r:ℕ):ℕ∞)≤g.graph.edist (e i) (e j))
    (q p z : ℂ)(hq : q≠0)(hp : p*(q⁻¹-q/((d:ℂ)-1))=1)(hz : 0<z.im)(hqim : 0≤q.im)
    (B C1 ε L A : ℝ)(hzB : ‖z‖≤B)(num : SourceObservationBounds d r z B C1 ε L A)
    (hprior : ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z) ε)
    (hR : ∀a b,g.graph.dist a b≤R)(hRlog : (R:ℝ)+1≤A*L)
    (hpbound : ‖p‖≤4)(hqinv : ‖q⁻¹‖≤2*(B+1))(hqpow : ∀n≤4*r+1,‖q‖^n≤2) :
    let G := (g.extensionGreen q z).submatrix e e
    IsUnit G ∧ ∀i j,‖G i j-(if i=j then p else 0)‖≤
      (treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d)*C1^2*L*ε := by
  exact whole_leaf_scalar_covariance_aux g hd Set.univ (fun _ => Set.mem_univ _) hb e r R htree hzero hsep
    q p z hq hp hz hqim B C1 ε L A hzB num hprior hR hRlog hpbound hqinv hqpow

end DeficientGraph
end LocalLaw
