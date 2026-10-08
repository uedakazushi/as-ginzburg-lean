import ASGinzburg.Triangle333
import ASGinzburg.ASPeriodicity

/-! Proposition 5.1 for the concrete three-vertex three-arrow AS model.
The original quadratic resolution (5.1) still needs to be identified with
this model's actual finite coproduct resolution, rather than postulated. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def ASRegular.trianglePeriodIso (hAS : A.ASRegular triangle333) :
    A.PeriodIso 3 := hAS.periodIso A triangle333

theorem ASRegular.triangle_isPeriodic (hAS : A.ASRegular triangle333) :
    A.IsPeriodic 3 := ⟨hAS.trianglePeriodIso A⟩

noncomputable def ASRegular.triangleNegativePeriodIso (hAS : A.ASRegular triangle333) :
    A.PeriodIso (-3) := hAS.negativePeriodIso A triangle333

theorem ASRegular.triangle_isPeriodic_negative (hAS : A.ASRegular triangle333) :
    A.IsPeriodic (-3) := ⟨hAS.triangleNegativePeriodIso A⟩

end ASGinzburg.ZAlgebra
