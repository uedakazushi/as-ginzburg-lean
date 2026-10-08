import ASGinzburg.ASResolution
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Finite-dimensional Hom spaces, keeping the actual linear right modules. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

/-- Precomposition with an epimorphism embeds the actual Hom space. -/
def rightModuleHomPrecomp {X Y : A.RightModule} (e : X ⟶ Y) (N : A.RightModule) :
    (Y ⟶ N) →ₗ[k] (X ⟶ N) where
  toFun f := e ≫ f
  map_add' f g := Preadditive.comp_add _ _ _ e f g
  map_smul' r f := Linear.comp_smul _ _ _ e r f

theorem rightModuleHomPrecomp_injective {X Y : A.RightModule} (e : X ⟶ Y) [Epi e]
    (N : A.RightModule) : Function.Injective (A.rightModuleHomPrecomp e N) := by
  intro f g h
  exact (cancel_epi e).mp h

theorem rightModuleHomFinite_of_epi {X Y : A.RightModule} (e : X ⟶ Y) [Epi e]
    (N : A.RightModule) [Module.Finite k (X ⟶ N)] : Module.Finite k (Y ⟶ N) :=
  Module.Finite.of_injective (A.rightModuleHomPrecomp e N)
    (A.rightModuleHomPrecomp_injective e N)

/-- A finite coproduct of representables has finite Hom into a target whose
relevant components are finite dimensional. -/
noncomputable def rightModuleCoproductHomLinearEquiv {β : Type*} (g : β → A.RightModule)
    [HasCoproduct g] (N : A.RightModule) :
    (∐ g ⟶ N) ≃ₗ[k] (∀ b, g b ⟶ N) where
  toFun f b := Sigma.ι g b ≫ f
  invFun f := Sigma.desc f
  left_inv f := by apply Sigma.hom_ext; intro b; simp
  right_inv f := by funext b; simp
  map_add' f h := by funext b; exact Preadditive.comp_add _ _ _ _ f h
  map_smul' r f := by funext b; exact Linear.comp_smul _ _ _ _ r f

theorem rightModuleCoproductHomFinite {β : Type*} [Finite β] (g : β → A.RightModule)
    [HasCoproduct g] (N : A.RightModule) [∀ b, Module.Finite k (g b ⟶ N)] :
    Module.Finite k (∐ g ⟶ N) :=
  Module.Finite.of_injective (A.rightModuleCoproductHomLinearEquiv g N).toLinearMap
    (A.rightModuleCoproductHomLinearEquiv g N).injective

theorem representableHomFinite (i : ℤ) (N : A.RightModule)
    [Module.Finite k ((A.rightModuleEvaluation i).obj N)] :
    Module.Finite k (A.representable i ⟶ N) :=
  Module.Finite.of_injective (A.representableYonedaEquiv i N).toLinearMap
    (A.representableYonedaEquiv i N).injective

theorem representableHomRepresentableFinite (i j : ℤ) :
    Module.Finite k (A.representable i ⟶ A.representable j) :=
  Module.Finite.of_injective (A.representableHomEquiv i j).symm.toLinearMap
    (A.representableHomEquiv i j).symm.injective

theorem asResolutionTerm₁HomFinite (Q : CutQuiver) (w : Q.LiftVertex) (i : ℤ) :
    Module.Finite k (A.asResolutionTerm₁ Q w ⟶ A.representable i) := by
  dsimp [asResolutionTerm₁]
  letI := fun a : Q.incomingArrows w =>
    A.representableHomRepresentableFinite (Q.height (Q.incomingSource w a)) i
  exact A.rightModuleCoproductHomFinite _ _

theorem asResolutionTerm₂HomFinite (Q : CutQuiver) (w : Q.LiftVertex) (i : ℤ) :
    Module.Finite k (A.asResolutionTerm₂ Q w ⟶ A.representable i) := by
  dsimp [asResolutionTerm₂]
  letI := fun a : Q.outgoingArrows (Q.tau.symm w) =>
    A.representableHomRepresentableFinite
      (Q.height (Q.outgoingTarget (Q.tau.symm w) a)) i
  exact A.rightModuleCoproductHomFinite _ _

end ASGinzburg.ZAlgebra
