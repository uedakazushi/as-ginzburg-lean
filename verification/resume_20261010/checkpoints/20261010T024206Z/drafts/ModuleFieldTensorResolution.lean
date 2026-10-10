import work.ASGinzburgDraft.ModuleFieldRestrictionResolution
import work.ASGinzburgDraft.ModuleTensorBifunctor
import work.ASGinzburgDraft.BifunctorTotalResolution
import work.ASGinzburgDraft.NatTotalExists

/-! The underlying vector-space tensor total of two genuine ordinary
module resolutions contracts to the ordinary tensor of their endpoints. -/
namespace ASGinzburg
open CategoryTheory HomologicalComplex
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable {M : ModuleCat.{w} Rᵐᵒᵖ} {N : ModuleCat.{z} R}
variable (P : ProjectiveResolution M) (Q : ProjectiveResolution N)

noncomputable def moduleFieldTensorResolutionHomotopyEquiv :
    HomotopyEquiv
      (mapBifunctor (moduleFieldRestrictionResolution k Rᵐᵒᵖ P).complex
        (moduleFieldRestrictionResolution k R Q).complex (moduleTensorBifunctor k)
          (ComplexShape.down ℕ))
      ((ChainComplex.single₀ (ModuleCat.{max w z} k)).obj
        (((moduleTensorBifunctor k).obj
          ((ModuleCat.restrictScalars (algebraMap k Rᵐᵒᵖ)).obj M)).obj
            ((ModuleCat.restrictScalars (algebraMap k R)).obj N))) := by
  letI := moduleCatField_projective k
    ((ModuleCat.restrictScalars (algebraMap k Rᵐᵒᵖ)).obj M)
  letI := moduleCatField_projective k
    ((ModuleCat.restrictScalars (algebraMap k R)).obj N)
  exact bifunctorTotalResolutionHomotopyEquiv (moduleTensorBifunctor k)
    (moduleFieldRestrictionResolution k Rᵐᵒᵖ P) (moduleFieldRestrictionResolution k R Q)

theorem moduleFieldTensorResolutionHomotopyEquiv_quasiIso :
    QuasiIso (moduleFieldTensorResolutionHomotopyEquiv k R P Q).hom := by
  infer_instance

end ASGinzburg
