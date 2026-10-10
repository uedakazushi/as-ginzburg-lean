import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.Module.Submodule.Map

/-! A genuine linear equivalence transports an internal grading by
actual images of its homogeneous subspaces. -/
namespace ASGinzburg
open scoped DirectSum
universe u v w
variable {k : Type u} [Field k]
variable {M : Type v} [AddCommGroup M] [Module k M]
variable {N : Type w} [AddCommGroup N] [Module k N]

theorem homogeneousLinearEquivImage_isInternal
    (e : M ≃ₗ[k] N) (G : ℤ → Submodule k M) (hG : DirectSum.IsInternal G) :
    DirectSum.IsInternal (fun q => (G q).map e.toLinearMap) := by
  let f : Submodule k M ≃o Submodule k N := Submodule.orderIsoMapComap e
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · change iSupIndep (f ∘ G)
    exact hG.submodule_iSupIndep.map_orderIso f
  · change (⨆ q, f (G q)) = ⊤
    rw [← f.map_iSup,hG.submodule_iSup_eq_top]
    exact f.map_top

noncomputable def homogeneousLinearEquivImageDecomposition
    (e : M ≃ₗ[k] N) (G : ℤ → Submodule k M) [DirectSum.Decomposition G] :
    DirectSum.Decomposition (fun q => (G q).map e.toLinearMap) :=
  (homogeneousLinearEquivImage_isInternal e G
    (DirectSum.Decomposition.isInternal G)).chooseDecomposition

end ASGinzburg
