import ASGinzburg.FiniteProjectiveHomColimits
import ASGinzburg.LeftModuleExtNaturalSequence
import ASGinzburg.LeftModuleHomology
import ASGinzburg.LeftModuleProjectives
import Mathlib.Algebra.Category.ModuleCat.Products

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v w w'
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

def leftModuleHomPrecomp {X Y : A.LeftModule} (e : X ⟶ Y) (N : A.LeftModule) :
    (Y ⟶ N) →ₗ[k] (X ⟶ N) where
  toFun f := e ≫ f
  map_add' f g := Preadditive.comp_add _ _ _ e f g
  map_smul' r f := Linear.comp_smul _ _ _ e r f

theorem leftModuleHomPrecomp_injective {X Y : A.LeftModule} (e : X ⟶ Y) [Epi e]
    (N : A.LeftModule) : Function.Injective (A.leftModuleHomPrecomp e N) := by
  intro f g h
  exact (cancel_epi e).mp h

noncomputable def leftModuleCoproductHomLinearEquiv {β : Type*} (g : β → A.LeftModule)
    [HasCoproduct g] (N : A.LeftModule) :
    (∐ g ⟶ N) ≃ₗ[k] (∀ b, g b ⟶ N) where
  toFun f b := Sigma.ι g b ≫ f
  invFun f := Sigma.desc f
  left_inv f := by apply Sigma.hom_ext; intro b; simp
  right_inv f := by funext b; simp
  map_add' f h := by funext b; exact Preadditive.comp_add _ _ _ _ f h
  map_smul' r f := by funext b; exact Linear.comp_smul _ _ _ _ r f
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v w w'
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def leftRepresentableHomEvaluationIso (i : ℤ) :
    (linearCoyoneda k A.LeftModule).obj (op (A.leftRepresentable i)) ≅
      A.leftModuleEvaluation i :=
  NatIso.ofComponents (fun M => (A.leftRepresentableYonedaEquiv i M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    ext g
    exact A.leftRepresentableYonedaEquiv_comp i g f)

noncomputable instance leftModuleEvaluationPreservesColimitsOfShape (i : ℤ)
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J (ModuleCat.{v} k)] :
    PreservesColimitsOfShape J (A.leftModuleEvaluation i) := by
  dsimp [leftModuleEvaluation]
  infer_instance

noncomputable instance leftRepresentableHomPreservesColimitsOfShape (i : ℤ)
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J (ModuleCat.{v} k)] :
    PreservesColimitsOfShape J
      ((linearCoyoneda k A.LeftModule).obj (op (A.leftRepresentable i))) :=
  preservesColimitsOfShape_of_natIso (A.leftRepresentableHomEvaluationIso i).symm

noncomputable def leftModuleExtZeroFunctorIso (M : A.LeftModule) :
    A.leftModuleExtCovariant M 0 ≅ (linearCoyoneda k A.LeftModule).obj (op M) :=
  NatIso.ofComponents (fun N => (A.leftModuleExtZeroLinearEquiv M N).toModuleIso) (by
    intro X Y f
    apply ModuleCat.hom_ext
    ext x
    apply (A.leftModuleExtZeroLinearEquiv M Y).symm.injective
    change (A.leftModuleExtZeroLinearEquiv M Y).symm
      ((A.leftModuleExtZeroLinearEquiv M Y)
        (x.comp (Abelian.Ext.mk₀ f) (by rfl))) =
      (A.leftModuleExtZeroLinearEquiv M Y).symm
        (A.leftModuleExtZeroLinearEquiv M X x ≫ f)
    rw [LinearEquiv.symm_apply_apply]
    change x.comp (Abelian.Ext.mk₀ f) (by rfl) =
      Abelian.Ext.mk₀ (A.leftModuleExtZeroLinearEquiv M X x ≫ f)
    rw [← Abelian.Ext.mk₀_comp_mk₀]
    congr 1
    exact (Abelian.Ext.mk₀_addEquiv₀_apply x).symm)
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v w w'
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

def leftModuleHomPrecompNat {M N : A.LeftModule} (f : M ⟶ N) :
    (linearCoyoneda k A.LeftModule).obj (op N) ⟶
      (linearCoyoneda k A.LeftModule).obj (op M) :=
  (linearCoyoneda k A.LeftModule).map f.op

theorem leftModuleHomPrecompNat_comp_zero {S : ShortComplex A.LeftModule} :
    A.leftModuleHomPrecompNat S.g ≫ A.leftModuleHomPrecompNat S.f = 0 := by
  apply NatTrans.ext
  funext N
  apply ModuleCat.hom_ext
  ext x
  change S.f ≫ (S.g ≫ x) = 0
  rw [← Category.assoc, S.zero, zero_comp]

def leftModuleHomShortComplex (S : ShortComplex A.LeftModule) :
    ShortComplex (A.LeftModule ⥤ ModuleCat.{v} k) :=
  ShortComplex.mk (A.leftModuleHomPrecompNat S.g) (A.leftModuleHomPrecompNat S.f)
    (A.leftModuleHomPrecompNat_comp_zero (S := S))

theorem leftModuleHomShortComplex_exact_component {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) (N : A.LeftModule) :
    ((A.leftModuleHomShortComplex S).map
      ((evaluation A.LeftModule (ModuleCat.{v} k)).obj N)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  change S.f ≫ x = 0 at hx
  obtain ⟨y, hy⟩ := CokernelCofork.IsColimit.desc' hS.gIsCokernel x hx
  exact ⟨y, hy⟩

instance leftModuleHomPrecompNatAppMono {M N : A.LeftModule} (f : M ⟶ N) [Epi f]
    (P : A.LeftModule) : Mono ((A.leftModuleHomPrecompNat f).app P) :=
  (ModuleCat.mono_iff_injective _).mpr (A.leftModuleHomPrecomp_injective f P)

instance leftModuleHomPrecompNatMono {M N : A.LeftModule} (f : M ⟶ N) [Epi f] :
    Mono (A.leftModuleHomPrecompNat f) := NatTrans.mono_of_mono_app _

noncomputable def leftModuleHomKernelForkIsLimit {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) :
    IsLimit (KernelFork.ofι (A.leftModuleHomPrecompNat S.g)
      (A.leftModuleHomPrecompNat_comp_zero (S := S))) := by
  apply evaluationJointlyReflectsLimits
  intro N
  refine (isLimitMapConeForkEquiv'
    ((evaluation A.LeftModule (ModuleCat.{v} k)).obj N)
    (A.leftModuleHomPrecompNat_comp_zero (S := S))).symm ?_
  letI : Epi S.g := hS.epi_g
  letI : Mono ((A.leftModuleHomShortComplex S).map
      ((evaluation A.LeftModule (ModuleCat.{v} k)).obj N)).f := by
    change Mono ((A.leftModuleHomPrecompNat S.g).app N)
    infer_instance
  exact (A.leftModuleHomShortComplex_exact_component hS N).fIsKernel

noncomputable def leftModuleHomKernelNatIso {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) :
    (linearCoyoneda k A.LeftModule).obj (op S.X₃) ≅
      kernel (A.leftModuleHomPrecompNat S.f) :=
  IsLimit.conePointUniqueUpToIso (A.leftModuleHomKernelForkIsLimit hS) (limit.isLimit _)

@[reassoc] theorem leftModuleHomKernelNatIso_hom_ι {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) :
    (A.leftModuleHomKernelNatIso hS).hom ≫ kernel.ι (A.leftModuleHomPrecompNat S.f) =
      A.leftModuleHomPrecompNat S.g :=
  IsLimit.conePointUniqueUpToIso_hom_comp (A.leftModuleHomKernelForkIsLimit hS)
    (limit.isLimit _) .zero

/-- Left exactness and exact colimits transfer exchange from the two middle Hom functors. -/
noncomputable def leftModuleHomPreservesExactColimits {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) (J : Type w) [Category.{w'} J]
    [HasColimitsOfShape J (ModuleCat.{v} k)]
    [HasExactColimitsOfShape J (ModuleCat.{v} k)]
    [PreservesColimitsOfShape J ((linearCoyoneda k A.LeftModule).obj (op S.X₁))]
    [PreservesColimitsOfShape J ((linearCoyoneda k A.LeftModule).obj (op S.X₂))] :
    PreservesColimitsOfShape J ((linearCoyoneda k A.LeftModule).obj (op S.X₃)) := by
  letI := kernelFunctorPreservesExactColimits (J := J) (A.leftModuleHomPrecompNat S.f)
  exact preservesColimitsOfShape_of_natIso (A.leftModuleHomKernelNatIso hS).symm
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v w w'
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

def leftModuleHomDiagram {I : Type} (g : I → A.LeftModule) :
    A.LeftModule ⥤ (Discrete I ⥤ ModuleCat.{v} k) where
  obj N := Discrete.functor (fun i => ModuleCat.of k (g i ⟶ N))
  map f := Discrete.natTrans (fun i =>
    ((linearCoyoneda k A.LeftModule).obj (op (g i.as))).map f)
  map_id N := by
    apply NatTrans.ext
    funext i
    exact ((linearCoyoneda k A.LeftModule).obj (op (g i.as))).map_id N
  map_comp f h := by
    apply NatTrans.ext
    funext i
    exact ((linearCoyoneda k A.LeftModule).obj (op (g i.as))).map_comp f h

noncomputable def leftModuleCoproductHomLimitComponentIso {I : Type}
    (g : I → A.LeftModule) (N : A.LeftModule) :
    ModuleCat.of k (∐ g ⟶ N) ≅ limit ((A.leftModuleHomDiagram g).obj N) :=
  (A.leftModuleCoproductHomLinearEquiv g N).toModuleIso ≪≫
    (ModuleCat.piIsoPi (fun i => ModuleCat.of k (g i ⟶ N))).symm ≪≫
    Pi.isoLimit ((A.leftModuleHomDiagram g).obj N)

@[reassoc] theorem leftModuleCoproductHomLimitComponentIso_hom_π {I : Type}
    (g : I → A.LeftModule) (N : A.LeftModule) (i : I) :
    (A.leftModuleCoproductHomLimitComponentIso g N).hom ≫
      limit.π ((A.leftModuleHomDiagram g).obj N) ⟨i⟩ =
      ModuleCat.ofHom (A.leftModuleHomPrecomp (Sigma.ι g i) N) := by
  simp only [leftModuleCoproductHomLimitComponentIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Pi.isoLimit_hom_π]
  change (A.leftModuleCoproductHomLinearEquiv g N).toModuleIso.hom ≫
    (ModuleCat.piIsoPi (fun j => ModuleCat.of k (g j ⟶ N))).inv ≫
      Pi.π (fun j => ModuleCat.of k (g j ⟶ N)) i = _
  rw [ModuleCat.piIsoPi_inv_kernel_ι]
  rfl

noncomputable def leftModuleCoproductHomLimitIso {I : Type} (g : I → A.LeftModule) :
    (linearCoyoneda k A.LeftModule).obj (op (∐ g)) ≅ A.leftModuleHomDiagram g ⋙ lim :=
  NatIso.ofComponents (A.leftModuleCoproductHomLimitComponentIso g) (by
    intro X Y f
    apply limit.hom_ext
    intro i
    rcases i with ⟨i⟩
    simp only [Functor.comp_map, lim_map, Category.assoc, limMap_π,
      leftModuleCoproductHomLimitComponentIso_hom_π,
      leftModuleCoproductHomLimitComponentIso_hom_π_assoc]
    apply ModuleCat.hom_ext
    ext h
    exact (Category.assoc (Sigma.ι g i) h f).symm)

noncomputable instance leftModuleHomDiagramPreservesColimitsOfShape {I : Type}
    (g : I → A.LeftModule) (J : Type w) [Category.{w'} J]
    [HasColimitsOfShape J (ModuleCat.{v} k)]
    [∀ i, PreservesColimitsOfShape J ((linearCoyoneda k A.LeftModule).obj (op (g i)))] :
    PreservesColimitsOfShape J (A.leftModuleHomDiagram g) := by
  apply preservesColimitsOfShape_of_evaluation
  intro i
  exact inferInstanceAs
    (PreservesColimitsOfShape J ((linearCoyoneda k A.LeftModule).obj (op (g i.as))))

noncomputable instance leftFiniteCoproductHomPreservesColimitsOfShape {I : Type} [Finite I]
    (g : I → A.LeftModule) (J : Type w) [Category.{w'} J]
    [HasColimitsOfShape J (ModuleCat.{v} k)]
    [∀ i, PreservesColimitsOfShape J ((linearCoyoneda k A.LeftModule).obj (op (g i)))] :
    PreservesColimitsOfShape J ((linearCoyoneda k A.LeftModule).obj (op (∐ g))) :=
  preservesColimitsOfShape_of_natIso (A.leftModuleCoproductHomLimitIso g).symm

/-- Closure applied to actual representables, with no Hom exchange hypothesis. -/
noncomputable instance leftFiniteRepresentableCoproductHomPreservesColimitsOfShape
    {I : Type} [Finite I] (indices : I → ℤ) (J : Type w) [Category.{w'} J]
    [HasColimitsOfShape J (ModuleCat.{v} k)] :
    PreservesColimitsOfShape J ((linearCoyoneda k A.LeftModule).obj
      (op (∐ fun i => A.leftRepresentable (indices i)))) := inferInstance
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v w w'
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def leftFiniteProjectiveHomPreservesColimits {P : A.LeftModule}
    (hP : A.leftFiniteProjectiveProperty P) (J : Type w) [Category.{w'} J]
    [HasColimitsOfShape J A.LeftModule] [HasColimitsOfShape J (ModuleCat.{v} k)] :
    PreservesColimitsOfShape J ((linearCoyoneda k A.LeftModule).obj (op P)) := by
  obtain ⟨n,i,⟨r⟩⟩ := hP
  exact ASGinzburg.preservesColimitsOfShape_of_functor_retract
    (r.op.map (linearCoyoneda k A.LeftModule))
end ASGinzburg.ZAlgebra
