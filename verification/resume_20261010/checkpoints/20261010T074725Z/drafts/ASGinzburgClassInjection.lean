import work.ASGinzburgDraft.ZeroCutIsomorphismTransposedAutomorphism
import ASGinzburg.PathAutomorphismJacobianDescent

/-! Actual native isomorphism lifting proves the injectivity part of
the source Theorem 3.2 class correspondence. Recovery of arbitrary AS
algebras remains a distinct outstanding theorem. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k] (Q : CutQuiver)

theorem asGinzburgClassInjection : ASGinzburgClassInjectionStatement k Q := by
  intro φ ψ h
  obtain ⟨F⟩ := (GinzburgRegularPotential.asIsomorphismClass_eq_iff k Q φ ψ).mp h
  apply (GinzburgRegularPotential.pathAutomorphismClass_eq_iff_smul k Q φ ψ).mpr
  exact φ.property.nativeJacobianIsomorphism_potentialOrbit Q k ψ.property F

theorem GinzburgRegularPotential.pathClass_eq_iff_asClass_eq
    (φ ψ : GinzburgRegularPotential k Q) :
    φ.pathAutomorphismClass k Q = ψ.pathAutomorphismClass k Q ↔
      φ.asIsomorphismClass k Q = ψ.asIsomorphismClass k Q :=
  ⟨asGinzburgClassDescent k Q φ ψ, asGinzburgClassInjection k Q φ ψ⟩

theorem ginzburgRegularPotentialASClassMap_injective :
    Function.Injective (ginzburgRegularPotentialASClassMap k Q) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro φ ψ h
  exact asGinzburgClassInjection k Q φ ψ h

end ASGinzburg
