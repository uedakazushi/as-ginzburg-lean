import ASGinzburg.FoundationEnoughProjectives
import ASGinzburg.ThreeTermProjectiveDimension

/-! Genuine foundation Ext vanishing follows from the proved projective
objects and the actual AS-restricted resolution; no Ext table is assumed. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def foundationRepresentableExtZeroEquiv (i : Q.Vertex)
    (M : A.FoundationRightModule Q) :
    Abelian.Ext.{v} (A.foundationRepresentable Q i) M 0 ≃+
      (A.foundationRightEvaluation Q i).obj M :=
  Abelian.Ext.addEquiv₀.trans (A.foundationRepresentableYonedaEquiv Q i M).toAddEquiv

theorem foundationRepresentable_higher_ext_eq_zero (i : Q.Vertex)
    (M : A.FoundationRightModule Q) (n : ℕ)
    (e : Abelian.Ext.{v} (A.foundationRepresentable Q i) M (n+1)) : e=0 :=
  Abelian.Ext.eq_zero_of_projective e

namespace ASResolution
variable {A Q} {j : Q.Vertex} (R : A.ASResolution Q (j,0))

include R in
theorem foundation_simple_ext_ge_three_eq_zero (M : A.FoundationRightModule Q)
    (n : ℕ) (hn : 3 ≤ n)
    (e : Abelian.Ext.{v}
      ((A.foundationRestriction Q).obj (A.simpleRightModule (Q.height (j,0)))) M n) : e=0 := by
  letI := R.foundation_simple_hasProjectiveDimensionLE_two
  exact e.eq_zero_of_hasProjectiveDimensionLT 3 hn

end ASResolution
end ASGinzburg.ZAlgebra
