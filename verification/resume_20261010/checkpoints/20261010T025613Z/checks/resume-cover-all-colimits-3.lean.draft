import ASGinzburg.RightModuleAbelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! The genuine linear cover-module inclusion preserves every native-small
colimit, because it creates those colimits in the presheaf category. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable instance rightModuleInclusionPreservesColimits :
    PreservesColimitsOfSize.{v,v} A.rightModuleProperty.ι where
  preservesColimitsOfShape := {
    preservesColimit := fun {K} =>
      preservesColimit_of_createsColimit_and_hasColimit K A.rightModuleProperty.ι
  }

end ASGinzburg.ZAlgebra
