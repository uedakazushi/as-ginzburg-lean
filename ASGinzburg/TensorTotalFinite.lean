import ASGinzburg.ModuleCatFiniteCoproduct
import ASGinzburg.AlgebraEnvelopingTensorTotal
import ASGinzburg.AlgebraEnvelopingTensorFinite

/-! Finite diagonal coproducts in genuine module-valued total complexes,
and finite generation of the right enveloping tensor total. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ModuleCat.Algebra
universe u v w z

section Generic
variable (S : Type u) [Ring S] {I₁ I₂ : Type} {J : Type*}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

theorem bicomplexTotal_finite
    (K : HomologicalComplex₂ (ModuleCat.{w} S) c₁ c₂) (c : ComplexShape J)
    [DecidableEq J] [TotalComplexShape c₁ c₂ c] [K.HasTotal c]
    [∀ i₁ i₂, Module.Finite S ((K.X i₁).X i₂)] (j : J)
    [Finite ((ComplexShape.π c₁ c₂ c) ⁻¹' {j})] :
    Module.Finite S ((K.total c).X j) := by
  change Module.Finite S
    ((∐ (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j)) : ModuleCat.{w} S)
  letI : ∀ i, Module.Finite S (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j i) :=
    fun i => inferInstanceAs (Module.Finite S ((K.X i.1.1).X i.1.2))
  exact moduleCatFiniteCoproduct_finite S _

end Generic

instance natTotalDiagonal_finite (n : ℕ) :
    Finite ((ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) ⁻¹' {n}) := by
  let f : ((ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) ⁻¹' {n}) → Fin (n + 1) := fun x =>
    ⟨x.1.1, by
      have hx : x.1.1 + x.1.2 = n := x.2
      omega⟩
  apply Finite.of_injective f
  intro x y h
  have hx : x.1.1 + x.1.2 = n := x.2
  have hy : y.1.1 + y.1.2 = n := y.2
  have hfst : x.1.1 = y.1.1 := congrArg Fin.val h
  apply Subtype.ext
  exact Prod.ext hfst (by omega)

section Enveloping
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
  (P : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ)
  (Q : ChainComplex (ModuleCat.{z} R) ℕ)

attribute [local instance] tensorRightEnvelopingModule

theorem tensorRightEnvelopingTotal_finite
    [∀ i, Module.Finite Rᵐᵒᵖ (P.X i)] [∀ i, Module.Finite R (Q.X i)]
    [HasMapBifunctor P Q (tensorRightEnvelopingBifunctor k R) (ComplexShape.down ℕ)]
    (n : ℕ) :
    Module.Finite (AlgebraEnvelopingRing k R)ᵐᵒᵖ
      ((tensorRightEnvelopingTotal k R P Q (ComplexShape.down ℕ)).X n) := by
  letI : ∀ i j, Module.Finite (AlgebraEnvelopingRing k R)ᵐᵒᵖ
      (((tensorRightEnvelopingBicomplex k R P Q).X i).X j) :=
    fun i j => tensorRightEnvelopingModule_finite k R (P.X i) (Q.X j)
  letI : (tensorRightEnvelopingBicomplex k R P Q).HasTotal (ComplexShape.down ℕ) := by
    change HasMapBifunctor P Q (tensorRightEnvelopingBifunctor k R) (ComplexShape.down ℕ)
    infer_instance
  exact bicomplexTotal_finite (AlgebraEnvelopingRing k R)ᵐᵒᵖ
    (tensorRightEnvelopingBicomplex k R P Q) (ComplexShape.down ℕ) n

end Enveloping
end ASGinzburg
