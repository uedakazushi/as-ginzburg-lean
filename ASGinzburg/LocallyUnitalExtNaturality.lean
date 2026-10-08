import ASGinzburg.ExactEquivalenceExt
import ASGinzburg.LocallyUnitalExtComparison

/-! The derived Ext comparisons commute with precomposition and
postcomposition by degree-zero morphisms. The linear and additive versions
agree, and both concrete locally unital comparisons satisfy these identities. -/

namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe w w₁ w₂ v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive] [HasExt.{w} C] [HasExt.{w} D]
theorem exactEquivalenceExtAddEquiv_hom (X Y : C) (n : ℕ) (α : Abelian.Ext.{w} X Y n) :
    (exactEquivalenceExtAddEquiv e X Y n α).hom =
      ((exactDerivedSingleIso e 0).app X).inv ≫
        (e.functor.mapDerivedCategory.map α.hom ≫
          (e.functor.mapDerivedCategory.commShiftIso (n : ℤ)).hom.app
            ((DerivedCategory.singleFunctor C 0).obj Y)) ≫
        (shiftFunctor (DerivedCategory D) (n : ℤ)).map ((exactDerivedSingleIso e 0).app Y).hom := by
  change Abelian.Ext.homAddEquiv (Abelian.Ext.homAddEquiv.symm _) = _
  exact Abelian.Ext.homAddEquiv.apply_symm_apply _

theorem exactEquivalenceExtAddEquiv_precomp {X' X Y : C} (f : X' ⟶ X) (n : ℕ)
    (α : Abelian.Ext.{w} X Y n) :
    exactEquivalenceExtAddEquiv e X' Y n ((Abelian.Ext.mk₀ f).comp α (zero_add n)) =
      (Abelian.Ext.mk₀ (e.functor.map f)).comp (exactEquivalenceExtAddEquiv e X Y n α) (zero_add n) := by
  apply Abelian.Ext.ext
  simp only [exactEquivalenceExtAddEquiv_hom, Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom,
    ShiftedHom.mk₀_comp, Functor.map_comp, Category.assoc]
  have h := (exactDerivedSingleIso e 0).inv.naturality f
  change (DerivedCategory.singleFunctor D 0).map (e.functor.map f) ≫
      ((exactDerivedSingleIso e 0).app X).inv =
    ((exactDerivedSingleIso e 0).app X').inv ≫
      e.functor.mapDerivedCategory.map ((DerivedCategory.singleFunctor C 0).map f) at h
  simpa only [Category.assoc] using congrArg
    (fun t => t ≫ e.functor.mapDerivedCategory.map α.hom ≫
      (e.functor.mapDerivedCategory.commShiftIso (n : ℤ)).hom.app
        ((DerivedCategory.singleFunctor C 0).obj Y) ≫
      (shiftFunctor (DerivedCategory D) (n : ℤ)).map ((exactDerivedSingleIso e 0).app Y).hom) h.symm

theorem exactEquivalenceExtAddEquiv_postcomp {X Y Y' : C} (f : Y ⟶ Y') (n : ℕ)
    (α : Abelian.Ext.{w} X Y n) :
    exactEquivalenceExtAddEquiv e X Y' n (α.comp (Abelian.Ext.mk₀ f) (add_zero n)) =
      (exactEquivalenceExtAddEquiv e X Y n α).comp (Abelian.Ext.mk₀ (e.functor.map f)) (add_zero n) := by
  apply Abelian.Ext.ext
  simp only [exactEquivalenceExtAddEquiv_hom, Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom,
    ShiftedHom.comp_mk₀, Functor.map_comp, Category.assoc]
  have hc := (e.functor.mapDerivedCategory.commShiftIso (n : ℤ)).hom.naturality
    ((DerivedCategory.singleFunctor C 0).map f)
  change e.functor.mapDerivedCategory.map
      ((shiftFunctor (DerivedCategory C) (n : ℤ)).map ((DerivedCategory.singleFunctor C 0).map f)) ≫
      (e.functor.mapDerivedCategory.commShiftIso (n : ℤ)).hom.app
        ((DerivedCategory.singleFunctor C 0).obj Y') =
    (e.functor.mapDerivedCategory.commShiftIso (n : ℤ)).hom.app
      ((DerivedCategory.singleFunctor C 0).obj Y) ≫
      (shiftFunctor (DerivedCategory D) (n : ℤ)).map
        (e.functor.mapDerivedCategory.map ((DerivedCategory.singleFunctor C 0).map f)) at hc
  have hs := (exactDerivedSingleIso e 0).hom.naturality f
  change e.functor.mapDerivedCategory.map ((DerivedCategory.singleFunctor C 0).map f) ≫
      ((exactDerivedSingleIso e 0).app Y').hom =
    ((exactDerivedSingleIso e 0).app Y).hom ≫
      (DerivedCategory.singleFunctor D 0).map (e.functor.map f) at hs
  have hshift := congrArg (shiftFunctor (DerivedCategory D) (n : ℤ)).map hs
  rw [Functor.map_comp, Functor.map_comp] at hshift
  have ht := congrArg (fun t => t ≫
      (shiftFunctor (DerivedCategory D) (n : ℤ)).map ((exactDerivedSingleIso e 0).app Y').hom) hc
  dsimp only at ht
  simp only [Category.assoc] at ht
  rw [hshift] at ht
  simpa only [Category.assoc] using congrArg
    (fun t => ((exactDerivedSingleIso e 0).app X).inv ≫
      e.functor.mapDerivedCategory.map α.hom ≫ t) ht

theorem exactEquivalenceExtLinearEquiv_toAddEquiv (R : Type*) [Field R]
    [Linear R C] [Linear R D] [e.functor.Linear R] (X Y : C) (n : ℕ) :
    letI := exactExtModule R X Y n
    letI := exactExtModule R (e.functor.obj X) (e.functor.obj Y) n
    (exactEquivalenceExtLinearEquiv e R X Y n).toAddEquiv =
      exactEquivalenceExtAddEquiv e X Y n := rfl

end ASGinzburg

namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem leftLocallyUnitalExtLinearEquiv_toAddEquiv (M N : A.LeftModule) (n : ℕ) :
    (A.leftLocallyUnitalExtLinearEquiv M N n).toAddEquiv =
      A.leftLocallyUnitalExtAddEquiv M N n := by
  letI := HasDerivedCategory.standard A.LeftModule
  letI := HasDerivedCategory.standard A.LeftLocallyUnitalModule
  letI : A.leftLocallyUnitalEquivalence.functor.Additive := A.leftTotalLocallyUnitalFunctorAdditive
  letI : A.leftLocallyUnitalEquivalence.inverse.Additive := A.leftLocallyUnitalComponentFunctorAdditive
  letI : A.leftLocallyUnitalEquivalence.functor.Linear k := A.leftTotalLocallyUnitalFunctorLinear
  exact ASGinzburg.exactEquivalenceExtLinearEquiv_toAddEquiv A.leftLocallyUnitalEquivalence k M N n

theorem leftLocallyUnitalExtLinearEquiv_precomp {M' M N : A.LeftModule}
    (f : M' ⟶ M) (n : ℕ) (α : Abelian.Ext.{v} M N n) :
    A.leftLocallyUnitalExtLinearEquiv M' N n ((Abelian.Ext.mk₀ f).comp α (zero_add n)) =
      (Abelian.Ext.mk₀ (A.leftTotalLocallyUnitalFunctor.map f)).comp
        (A.leftLocallyUnitalExtLinearEquiv M N n α) (zero_add n) := by
  letI := HasDerivedCategory.standard A.LeftModule
  letI := HasDerivedCategory.standard A.LeftLocallyUnitalModule
  letI : A.leftLocallyUnitalEquivalence.functor.Additive := A.leftTotalLocallyUnitalFunctorAdditive
  letI : A.leftLocallyUnitalEquivalence.inverse.Additive := A.leftLocallyUnitalComponentFunctorAdditive
  change (A.leftLocallyUnitalExtLinearEquiv M' N n).toAddEquiv
      ((Abelian.Ext.mk₀ f).comp α (zero_add n)) =
    (Abelian.Ext.mk₀ (A.leftTotalLocallyUnitalFunctor.map f)).comp
      ((A.leftLocallyUnitalExtLinearEquiv M N n).toAddEquiv α) (zero_add n)
  rw [A.leftLocallyUnitalExtLinearEquiv_toAddEquiv, A.leftLocallyUnitalExtLinearEquiv_toAddEquiv]
  exact ASGinzburg.exactEquivalenceExtAddEquiv_precomp A.leftLocallyUnitalEquivalence f n α

theorem leftLocallyUnitalExtLinearEquiv_postcomp {M N N' : A.LeftModule}
    (f : N ⟶ N') (n : ℕ) (α : Abelian.Ext.{v} M N n) :
    A.leftLocallyUnitalExtLinearEquiv M N' n (α.comp (Abelian.Ext.mk₀ f) (add_zero n)) =
      (A.leftLocallyUnitalExtLinearEquiv M N n α).comp
        (Abelian.Ext.mk₀ (A.leftTotalLocallyUnitalFunctor.map f)) (add_zero n) := by
  letI := HasDerivedCategory.standard A.LeftModule
  letI := HasDerivedCategory.standard A.LeftLocallyUnitalModule
  letI : A.leftLocallyUnitalEquivalence.functor.Additive := A.leftTotalLocallyUnitalFunctorAdditive
  letI : A.leftLocallyUnitalEquivalence.inverse.Additive := A.leftLocallyUnitalComponentFunctorAdditive
  change (A.leftLocallyUnitalExtLinearEquiv M N' n).toAddEquiv
      (α.comp (Abelian.Ext.mk₀ f) (add_zero n)) =
    ((A.leftLocallyUnitalExtLinearEquiv M N n).toAddEquiv α).comp
      (Abelian.Ext.mk₀ (A.leftTotalLocallyUnitalFunctor.map f)) (add_zero n)
  rw [A.leftLocallyUnitalExtLinearEquiv_toAddEquiv, A.leftLocallyUnitalExtLinearEquiv_toAddEquiv]
  exact ASGinzburg.exactEquivalenceExtAddEquiv_postcomp A.leftLocallyUnitalEquivalence f n α

theorem rightLocallyUnitalExtLinearEquiv_toAddEquiv (M N : A.RightModule) (n : ℕ) :
    (A.rightLocallyUnitalExtLinearEquiv M N n).toAddEquiv =
      A.rightLocallyUnitalExtAddEquiv M N n := by
  letI := HasDerivedCategory.standard A.RightModule
  letI := HasDerivedCategory.standard A.RightLocallyUnitalModule
  letI : A.rightLocallyUnitalEquivalence.functor.Additive := A.rightTotalLocallyUnitalFunctorAdditive
  letI : A.rightLocallyUnitalEquivalence.inverse.Additive := A.rightLocallyUnitalComponentFunctorAdditive
  letI : A.rightLocallyUnitalEquivalence.functor.Linear k := A.rightTotalLocallyUnitalFunctorLinear
  exact ASGinzburg.exactEquivalenceExtLinearEquiv_toAddEquiv A.rightLocallyUnitalEquivalence k M N n

theorem rightLocallyUnitalExtLinearEquiv_precomp {M' M N : A.RightModule}
    (f : M' ⟶ M) (n : ℕ) (α : Abelian.Ext.{v} M N n) :
    A.rightLocallyUnitalExtLinearEquiv M' N n ((Abelian.Ext.mk₀ f).comp α (zero_add n)) =
      (Abelian.Ext.mk₀ (A.rightTotalLocallyUnitalFunctor.map f)).comp
        (A.rightLocallyUnitalExtLinearEquiv M N n α) (zero_add n) := by
  letI := HasDerivedCategory.standard A.RightModule
  letI := HasDerivedCategory.standard A.RightLocallyUnitalModule
  letI : A.rightLocallyUnitalEquivalence.functor.Additive := A.rightTotalLocallyUnitalFunctorAdditive
  letI : A.rightLocallyUnitalEquivalence.inverse.Additive := A.rightLocallyUnitalComponentFunctorAdditive
  change (A.rightLocallyUnitalExtLinearEquiv M' N n).toAddEquiv
      ((Abelian.Ext.mk₀ f).comp α (zero_add n)) =
    (Abelian.Ext.mk₀ (A.rightTotalLocallyUnitalFunctor.map f)).comp
      ((A.rightLocallyUnitalExtLinearEquiv M N n).toAddEquiv α) (zero_add n)
  rw [A.rightLocallyUnitalExtLinearEquiv_toAddEquiv, A.rightLocallyUnitalExtLinearEquiv_toAddEquiv]
  exact ASGinzburg.exactEquivalenceExtAddEquiv_precomp A.rightLocallyUnitalEquivalence f n α

theorem rightLocallyUnitalExtLinearEquiv_postcomp {M N N' : A.RightModule}
    (f : N ⟶ N') (n : ℕ) (α : Abelian.Ext.{v} M N n) :
    A.rightLocallyUnitalExtLinearEquiv M N' n (α.comp (Abelian.Ext.mk₀ f) (add_zero n)) =
      (A.rightLocallyUnitalExtLinearEquiv M N n α).comp
        (Abelian.Ext.mk₀ (A.rightTotalLocallyUnitalFunctor.map f)) (add_zero n) := by
  letI := HasDerivedCategory.standard A.RightModule
  letI := HasDerivedCategory.standard A.RightLocallyUnitalModule
  letI : A.rightLocallyUnitalEquivalence.functor.Additive := A.rightTotalLocallyUnitalFunctorAdditive
  letI : A.rightLocallyUnitalEquivalence.inverse.Additive := A.rightLocallyUnitalComponentFunctorAdditive
  change (A.rightLocallyUnitalExtLinearEquiv M N' n).toAddEquiv
      (α.comp (Abelian.Ext.mk₀ f) (add_zero n)) =
    ((A.rightLocallyUnitalExtLinearEquiv M N n).toAddEquiv α).comp
      (Abelian.Ext.mk₀ (A.rightTotalLocallyUnitalFunctor.map f)) (add_zero n)
  rw [A.rightLocallyUnitalExtLinearEquiv_toAddEquiv, A.rightLocallyUnitalExtLinearEquiv_toAddEquiv]
  exact ASGinzburg.exactEquivalenceExtAddEquiv_postcomp A.rightLocallyUnitalEquivalence f n α

end ASGinzburg.ZAlgebra
