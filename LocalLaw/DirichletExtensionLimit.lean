import LocalLaw.DirichletCavityLimit
import LocalLaw.DeficientGraphModel

/-! # Finite-core reference continuity along Dirichlet tree boundary values -/

open Filter
open scoped Topology
noncomputable section
namespace LocalLaw
namespace DeficientGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

theorem extensionMatrix_continuous (g : DeficientGraph V d) (z : ℂ) :
    Continuous (fun w : ℂ => g.extensionMatrix w z) := by
  unfold extensionMatrix boundaryMatrix spectralMatrix
  fun_prop

theorem extensionGreen_continuousAt (g : DeficientGraph V d) (hd : 3≤d) (q z : ℂ)
    (hz : 0<z.im) (hq : 0≤q.im) : ContinuousAt (fun w : ℂ => g.extensionGreen w z) q := by
  have hu := g.extensionMatrix_isUnit hd q z hz hq
  have hdet : (g.extensionMatrix q z).det≠0 :=
    isUnit_iff_ne_zero.mp ((g.extensionMatrix q z).isUnit_iff_isUnit_det.mp hu)
  have hinv : ContinuousAt Ring.inverse (g.extensionMatrix q z).det := by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet
  change ContinuousAt (fun w : ℂ => (g.extensionMatrix w z)⁻¹) q
  exact ContinuousAt.comp (f:=fun w : ℂ => g.extensionMatrix w z) (x:=q)
    (continuousAt_matrix_inv (g.extensionMatrix q z) hinv) (g.extensionMatrix_continuous z).continuousAt

/-- Ordinary zero-boundary cavity trees supply the boundary parameters. Their
compressed finite-core matrices converge to the physical reference matrix. -/
theorem dirichlet_extensionGreen_tendsto (g : DeficientGraph V d) (hd : 3≤d) (z : ℂ) (hz : 0<z.im) :
    Tendsto (fun n : ℕ => g.extensionGreen (cavityIterate z 0 n) z) atTop
      (𝓝 (g.extensionGreen (semicircleRoot z) z)) :=
  (g.extensionGreen_continuousAt hd (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le).tendsto.comp
    (cavityIterate_zero_tendsto_physical z hz)

theorem dirichlet_extensionGreen_entry_tendsto (g : DeficientGraph V d) (hd : 3≤d)
    (z : ℂ) (hz : 0<z.im) (i j : V) :
    Tendsto (fun n : ℕ => g.extensionGreen (cavityIterate z 0 n) z i j) atTop
      (𝓝 (g.extensionGreen (semicircleRoot z) z i j)) := by
  have heval : Continuous (fun M : Matrix V V ℂ => M i j) := by fun_prop
  exact heval.continuousAt.tendsto.comp (g.dirichlet_extensionGreen_tendsto hd z hz)

end DeficientGraph
end LocalLaw
