import ASGinzburg.ASRegularIsomorphismClasses
import ASGinzburg.GinzburgRegularImpliesASRegular

/-! The genuine potential-to-algebra map has values in vertex-fixing AS
isomorphism classes. Its surjectivity is exactly the existence of a regular
potential recovering every AS algebra. Surjectivity and descent through
path-algebra automorphisms are not asserted here. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k] (Q : CutQuiver)

abbrev GinzburgRegularPotential := {φ : Q.Potential k // Q.GinzburgRegular k φ}

noncomputable def GinzburgRegularPotential.asRegularAlgebra
    (φ : GinzburgRegularPotential k Q) : ASRegularAlgebra.{u,u} k Q :=
  ⟨Q.unrolledJacobianZAlgebra k φ.val, φ.property.asRegular Q k φ.val⟩

noncomputable def GinzburgRegularPotential.asIsomorphismClass
    (φ : GinzburgRegularPotential k Q) : ASRegularIsomorphismClass.{u,u} k Q :=
  (φ.asRegularAlgebra k Q).isomorphismClass k Q

theorem GinzburgRegularPotential.asIsomorphismClass_eq_iff
    (φ ψ : GinzburgRegularPotential k Q) :
    φ.asIsomorphismClass k Q = ψ.asIsomorphismClass k Q ↔
      Nonempty (ZAlgebra.Isomorphism (Q.unrolledJacobianZAlgebra k φ.val)
        (Q.unrolledJacobianZAlgebra k ψ.val)) :=
  ASRegularAlgebra.isomorphismClass_eq_iff k Q _ _

theorem ginzburgRegularASClassMap_surjective_iff :
    Function.Surjective (GinzburgRegularPotential.asIsomorphismClass k Q) ↔
      ∀ A : ASRegularAlgebra.{u,u} k Q, ∃ φ : GinzburgRegularPotential k Q,
        Nonempty (ZAlgebra.Isomorphism (Q.unrolledJacobianZAlgebra k φ.val) A.val) := by
  constructor
  · intro h A
    obtain ⟨φ, hφ⟩ := h (A.isomorphismClass k Q)
    exact ⟨φ, Quotient.exact hφ⟩
  · intro h C
    refine Quotient.inductionOn C ?_
    intro A
    obtain ⟨φ, hφ⟩ := h A
    exact ⟨φ, Quotient.sound hφ⟩

end ASGinzburg
