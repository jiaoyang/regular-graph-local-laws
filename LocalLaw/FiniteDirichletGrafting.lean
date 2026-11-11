import LocalLaw.DirichletExtensionLimit
import LocalLaw.BlockSchur

/-! # Actual finite Dirichlet tree attachments to every missing degree slot

Each missing degree gets its own disjoint normalized cavity tree. The
compressed inverse on the original finite graph is exactly the finite
extension at the Dirichlet cavity value. The physical reference is its limit.
-/

open scoped BigOperators Topology
open Filter
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance finiteDirichletGraftingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Repeated
variable {X S : Type*} [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]

theorem repeatedBranches_isUnit (M : Matrix X X ℂ) (hM : IsUnit M) :
    IsUnit (Matrix.blockDiagonal (fun _ : S => M)) := by
  change IsUnit ((Matrix.blockDiagonalRingHom X S ℂ) (fun _ => M))
  exact IsUnit.map (Matrix.blockDiagonalRingHom X S ℂ) (Pi.isUnit_iff.mpr (fun _ => hM))

theorem repeatedBranches_inverse (M : Matrix X X ℂ) (hM : IsUnit M) :
    (Matrix.blockDiagonal (fun _ : S => M))⁻¹=Matrix.blockDiagonal (fun _ : S => M⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [←Matrix.blockDiagonal_mul]
  have hh : M⁻¹*M=1 := M.nonsing_inv_mul (M.isUnit_iff_isUnit_det.mp hM)
  simp only [hh]
  exact Matrix.blockDiagonal_one

end Repeated
namespace DeficientGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

def treeExtensionSlots (g : DeficientGraph V d) := Σ v : V,Fin (d-g.deficit v-g.graph.degree v)

instance treeExtensionSlotsFintype (g : DeficientGraph V d) : Fintype g.treeExtensionSlots := by
  unfold treeExtensionSlots
  infer_instance

instance treeExtensionSlotsDecidableEq (g : DeficientGraph V d) : DecidableEq g.treeExtensionSlots := by
  unfold treeExtensionSlots
  infer_instance

def dirichletTailCoupling (g : DeficientGraph V d) (n : ℕ) :
    Matrix V (CavityTreeIndex (d-1) n × g.treeExtensionSlots) ℂ :=
  fun v p => if p.1=cavityTreeRoot (d-1) n ∧ p.2.1=v then normalizedCavityEdge (d-1) else 0

def dirichletTailMatrix (g : DeficientGraph V d) (n : ℕ) (z : ℂ) :
    Matrix (CavityTreeIndex (d-1) n × g.treeExtensionSlots) (CavityTreeIndex (d-1) n × g.treeExtensionSlots) ℂ :=
  Matrix.blockDiagonal (fun _ : g.treeExtensionSlots => cavityTreeMatrix (d-1) (normalizedCavityEdge (d-1)) z 0 n)

def dirichletGraftMatrix (g : DeficientGraph V d) (n : ℕ) (z : ℂ) :
    Matrix (V ⊕ (CavityTreeIndex (d-1) n × g.treeExtensionSlots))
      (V ⊕ (CavityTreeIndex (d-1) n × g.treeExtensionSlots)) ℂ :=
  Matrix.fromBlocks (spectralMatrix g.H z) (g.dirichletTailCoupling n)
    (g.dirichletTailCoupling n).transpose (g.dirichletTailMatrix n z)

omit [DecidableEq V] in
theorem treeExtensionSlots_count_cast (g : DeficientGraph V d) (v : V) :
    ((d-g.deficit v-g.graph.degree v:ℕ):ℂ)=(d:ℂ)-(g.deficit v:ℂ)-(g.graph.degree v:ℂ) := by
  have hh := g.degree_deficit_le v
  rw [Nat.cast_sub (show g.graph.degree v≤d-g.deficit v by omega),Nat.cast_sub (by omega)]

theorem dirichletTail_selfEnergy (g : DeficientGraph V d) (hd : 3≤d) (n : ℕ) (z : ℂ) (hz : 0<z.im) :
    g.dirichletTailCoupling n*(g.dirichletTailMatrix n z)⁻¹*(g.dirichletTailCoupling n).transpose=
      cavityIterate z 0 (n+1) • g.boundaryDiagonal := by
  have hk : 0<d-1 := by omega
  have ht := dirichlet_cavityTree_inverse_root (d-1) hk z hz n
  have hinv := repeatedBranches_inverse (S:=g.treeExtensionSlots)
    (cavityTreeMatrix (d-1) (normalizedCavityEdge (d-1)) z 0 n) ht.1
  change g.dirichletTailCoupling n*(Matrix.blockDiagonal (fun _ : g.treeExtensionSlots =>
    cavityTreeMatrix (d-1) (normalizedCavityEdge (d-1)) z 0 n))⁻¹*(g.dirichletTailCoupling n).transpose=_
  rw [hinv]
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,dirichletTailCoupling,Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type,ite_and,mul_ite,ite_mul,mul_zero,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp only [treeExtensionSlots,Fintype.sum_sigma]
  by_cases hij : i=j
  · subst j
    simp only [Finset.sum_ite_irrel,Finset.sum_const,Fintype.card_fin,Finset.card_univ,nsmul_eq_mul,
      mul_zero,zero_mul,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true,
      ht.2,Matrix.smul_apply,boundaryDiagonal,Matrix.diagonal_apply_eq,smul_eq_mul]
    have hc := g.treeExtensionSlots_count_cast i
    have hkcast : ((d-1:ℕ):ℂ)=(d:ℂ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
    simp only [boundaryCoefficient,Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_natCast]
    rw [hc]
    simp only [Complex.ofReal_one]
    have hα := normalizedCavityEdge_sq (d-1) hk
    rw [hkcast] at hα
    rw [div_eq_mul_inv]
    linear_combination (cavityIterate z 0 (n+1)*((d:ℂ)-(g.deficit i:ℂ)-(g.graph.degree i:ℂ)))*hα
  · simp only [Matrix.smul_apply,boundaryDiagonal,Matrix.diagonal_apply_ne _ hij,smul_eq_mul,mul_zero]
    apply Finset.sum_eq_zero
    intro v _
    split_ifs <;> simp_all [Ne.symm hij]

theorem dirichletGraftMatrix_inverse_core (g : DeficientGraph V d) (hd : 3≤d)
    (n : ℕ) (z : ℂ) (hz : 0<z.im) :
    IsUnit (g.dirichletGraftMatrix n z) ∧
      ((g.dirichletGraftMatrix n z)⁻¹).toBlocks₁₁=g.extensionGreen (cavityIterate z 0 (n+1)) z := by
  have hk : 0<d-1 := by omega
  have ht := dirichlet_cavityTree_inverse_root (d-1) hk z hz n
  have hD : IsUnit (g.dirichletTailMatrix n z) := repeatedBranches_isUnit _ ht.1
  letI : Invertible (g.dirichletTailMatrix n z) := Classical.choice hD.nonempty_invertible
  have hS : spectralMatrix g.H z-g.dirichletTailCoupling n*⅟(g.dirichletTailMatrix n z)*
      (g.dirichletTailCoupling n).transpose=g.extensionMatrix (cavityIterate z 0 (n+1)) z := by
    rw [Matrix.invOf_eq_nonsing_inv,g.dirichletTail_selfEnergy hd n z hz]
    rfl
  have hU := g.extensionMatrix_isUnit hd (cavityIterate z 0 (n+1)) z hz
    (cavityIterate_im_nonnegative z 0 hz (by norm_num) (n+1))
  have hfull : IsUnit (g.dirichletGraftMatrix n z) := by
    apply Matrix.isUnit_fromBlocks_iff_of_invertible₂₂.mpr
    rw [hS]
    exact hU
  refine ⟨hfull,?_⟩
  have hcore := inverse_block11 (g.dirichletGraftMatrix n z) hfull hD
  have hschur : blockSchur (g.dirichletGraftMatrix n z)=g.extensionMatrix (cavityIterate z 0 (n+1)) z := by
    simpa only [dirichletGraftMatrix,blockSchur,Matrix.toBlocks_fromBlocks₁₁,
      Matrix.toBlocks_fromBlocks₁₂,Matrix.toBlocks_fromBlocks₂₁,Matrix.toBlocks_fromBlocks₂₂,
      Matrix.invOf_eq_nonsing_inv] using hS
  rw [hschur] at hcore
  exact hcore

/-- The entire core block of the actual finite branch-attachment inverse
converges to the finite reference. This is a Dirichlet exhaustion theorem,
not an assumed identity with an unspecified infinite Green function. -/
theorem dirichletGraftMatrix_core_tendsto (g : DeficientGraph V d) (hd : 3≤d)
    (z : ℂ) (hz : 0<z.im) :
    Tendsto (fun n : ℕ => ((g.dirichletGraftMatrix n z)⁻¹).toBlocks₁₁) atTop
      (𝓝 (g.extensionGreen (semicircleRoot z) z)) := by
  have h := (g.dirichlet_extensionGreen_tendsto hd z hz).comp (tendsto_add_atTop_nat 1)
  exact h.congr' (Filter.Eventually.of_forall (fun n => (g.dirichletGraftMatrix_inverse_core hd n z hz).2.symm))

end DeficientGraph
end LocalLaw
