import LocalLaw.BoundaryGuardAmbientDistance
import LocalLaw.PartialSampleTreeTail
import LocalLaw.TreePatchWeakValues

/-! # Actual full-graph sampled tree values

The outside I/J tests and the far-boundary guard imply the required
ambient tree balls. The literal full regular model has zero inherited
deficit, so its diagonal and sampled-edge entries have the formal vacuum
values up to the proved logarithmic weak-prior error.
-/

noncomputable section
namespace LocalLaw
local instance fullSampleTreeValuesDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem boundaryFarOutside_ambient_far_of_outside_far {V:Type*}
    (G:SimpleGraph V) (T:Set V) (h:ℕ) (b c:(Tᶜ:Set V))
    (hb:b∈boundaryFarOutside G T h) (hfar:(h:ℕ∞)<(outsideGraph G T).edist b c) :
    (h:ℕ∞)<G.edist b.val c.val := by
  apply lt_of_not_ge
  intro hnear
  have hfinite:=ne_top_of_le_ne_top (ENat.coe_ne_top h) hnear
  obtain ⟨p,hp⟩:=SimpleGraph.exists_walk_of_edist_ne_top hfinite
  have hlen:p.length≤h:=ENat.coe_le_coe.mp (hp.trans_le hnear)
  have hsupp:=boundaryFarOutside_short_walk_avoids G T h b hb p (by omega)
  obtain ⟨q,hq⟩:=walk_lift_induced_of_support G Tᶜ p hsupp b.property c.property
  have hshort:(outsideGraph G T).edist b c≤(h:ℕ∞):=
    (SimpleGraph.edist_le q).trans (ENat.coe_le_coe.mpr (by simpa only [hq] using hlen))
  exact not_lt_of_ge hshort hfar

namespace RegularGraph
variable {N d:ℕ} {ι:Type} [Fintype ι]

omit [Fintype ι] in
theorem eligible_full_sample_ball_isTree (g:RegularGraph N d)
    (T:Set (Fin N)) (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector R:ℕ) (hR:R+1≤selector)
    (i:(g.admissibleState T labels samples).AdmissibleSampleIndex selector)
    (c:(Tᶜ:Set (Fin N)))
    (hc:c∈(g.admissibleState T labels samples).admissiblePairRoots selector i) :
    (graphBall g.graph c.val R).IsTree := by
  let s:=g.admissibleState T labels samples
  have htree:=(g.eligible_sample_root_tree_zero_ball T labels samples selector R hR i c hc).1
  have hguard:=s.admissiblePairRoots_far_boundary selector (by omega) i hc
  exact boundaryFarOutside_ambient_ball_isTree g.graph T (selector-1) R (by omega) c hguard htree

omit [Fintype ι] in
theorem full_sample_diagonal_weak_value (g:RegularGraph N d) (hd:3≤d)
    (T:Set (Fin N)) (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector r:ℕ) (hr:r+1≤selector)
    (i:(g.admissibleState T labels samples).AdmissibleSampleIndex selector)
    (c:(Tᶜ:Set (Fin N)))
    (hc:c∈(g.admissibleState T labels samples).admissiblePairRoots selector i)
    (S:Set (Fin N)) (hbudget:(g.deficient.restrict S).ComponentFiniteReferenceBudget)
    (u:S) (hu:u.val=c.val) (R:ℕ) (q p z:ℂ) (hq:q≠0)
    (hp:p*(q⁻¹-q/((d:ℂ)-1))=1) (hz:0<z.im) (hqim:0≤q.im)
    (B C ε L A:ℝ) (hzB:‖z‖≤B) (num:SourceObservationBounds d r z B C ε L A)
    (hprior:‖q-semicircleRoot z‖≤C*scalarScale (spectralScale z) ε)
    (hR:∀a b,(g.deficient.restrict S).graph.dist a b≤R) (hRlog:(R:ℝ)+1≤A*L)
    (hpbound:‖p‖≤4) (hqinv:‖q⁻¹‖≤2*(B+1)) (hqpow:∀n≤4*r+1,‖q‖^n≤2) :
    ‖(g.deficient.restrict S).extensionGreen q z u u-p‖≤treePatchWeakConstant d B A*C^2*L*ε := by
  have htree:(graphBall g.deficient.graph u.val r).IsTree:=by
    change (graphBall g.graph u.val r).IsTree
    rw [hu]
    exact g.eligible_full_sample_ball_isTree T labels samples selector r hr i c hc
  exact g.deficient.restrict_tree_diagonal_weak_residual hd S hbudget u r R htree
    (fun _ _=>rfl) q p z hq hp hz hqim B C ε L A hzB num hprior hR hRlog hpbound hqinv hqpow

omit [Fintype ι] in
theorem full_sample_adjacent_weak_value (g:RegularGraph N d) (hd:3≤d)
    (T:Set (Fin N)) (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector r:ℕ) (hr:r+2≤selector)
    (i:(g.admissibleState T labels samples).AdmissibleSampleIndex selector)
    (S:Set (Fin N)) (hbudget:(g.deficient.restrict S).ComponentFiniteReferenceBudget)
    (u v:S)
    (hu:u.val=((g.admissibleState T labels samples).admissibleSampleVertex selector i).val)
    (hv:v.val=((g.admissibleState T labels samples).admissibleSecondVertex selector i).val)
    (R:ℕ) (q p z:ℂ) (hq:q≠0) (hp:p*(q⁻¹-q/((d:ℂ)-1))=1) (hz:0<z.im) (hqim:0≤q.im)
    (B C ε L A:ℝ) (hzB:‖z‖≤B) (num:SourceObservationBounds d r z B C ε L A)
    (hprior:‖q-semicircleRoot z‖≤C*scalarScale (spectralScale z) ε)
    (hR:∀a b,(g.deficient.restrict S).graph.dist a b≤R) (hRlog:(R:ℝ)+1≤A*L)
    (hpbound:‖p‖≤4) (hqinv:‖q⁻¹‖≤2*(B+1)) (hqpow:∀n≤4*r+1,‖q‖^n≤2) :
    ‖(g.deficient.restrict S).extensionGreen q z u v-p*(-q*treeEdgeWeight d)‖≤
      treePatchWeakConstant d B A*C^2*L*ε := by
  let s:=g.admissibleState T labels samples
  have htree:(graphBall g.deficient.graph u.val (r+1)).IsTree:=by
    change (graphBall g.graph u.val (r+1)).IsTree
    rw [hu]
    exact g.eligible_full_sample_ball_isTree T labels samples selector (r+1) (by omega) i
      (s.admissibleSampleVertex selector i) (Or.inl rfl)
  have huv:g.deficient.graph.Adj u.val v.val:=by
    rw [hu,hv]
    exact (samples (labels i.val)).property.1
  exact g.deficient.restrict_tree_adjacent_weak_residual hd S hbudget u v huv r R htree
    (fun _ _=>rfl) q p z hq hp hz hqim B C ε L A hzB num hprior hR hRlog hpbound hqinv hqpow

end RegularGraph
end LocalLaw
