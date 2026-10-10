import ASGinzburg.FiniteDimensionalExtConcentration
import ASGinzburg.ExtComponentShortExact

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem rightFiniteDimensional_ext_three_shortExact (hAS : A.ASRegular Q)
    {S : ShortComplex A.RightModule} (hS : S.ShortExact)
    (h₁ : A.rightFiniteDimensionalProperty S.X₁)
    (h₃ : A.rightFiniteDimensionalProperty S.X₃) :
    (A.rightModuleExtLeftShortComplex S 3).ShortExact :=
  A.rightModuleExtLeftShortComplex_three_shortExact hS
    (fun i => A.rightFiniteDimensional_ext_other_eq_zero Q hAS S.X₁ h₁ i 2 (by decide))
    (fun i => A.rightFiniteDimensional_ext_other_eq_zero Q hAS S.X₃ h₃ i 4 (by decide))

theorem rightVertexFiltration_ext_three_finite (hAS : A.ASRegular Q)
    {M : A.RightModule} (F : A.RightVertexFiltration M) :
    A.leftFiniteDimensionalProperty (A.rightModuleExtLeft M 3) := by
  induction F with
  | zero hM => exact A.leftFiniteDimensional_of_isZero (A.rightModuleExtLeft_isZero_of_isZero hM 3)
  | @step M i f hf tail ih =>
    letI := hf
    let S : ShortComplex A.RightModule :=
      ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
    have hT : (A.rightModuleExtLeftShortComplex S 3).ShortExact :=
      A.rightModuleExtLeftShortComplex_three_shortExact hS
        (fun j => A.rightFiniteDimensional_ext_other_eq_zero Q hAS (A.simpleRightModule i)
          (A.rightFiniteDimensional_simple i) j 2 (by decide))
        (fun j => A.rightVertexFiltration_ext_other_eq_zero Q hAS tail j 4 (by decide))
    have hs : A.leftFiniteDimensionalProperty (A.rightModuleExtLeft (A.simpleRightModule i) 3) := by
      obtain ⟨w,rfl⟩ := Q.height_bijective.surjective i
      exact A.leftFiniteDimensional_of_mono (hAS.extLeftThreeIsoSimple A Q w).hom
        (A.leftFiniteDimensional_simple _)
    exact A.leftFiniteDimensional_of_shortExact hT ih hs

theorem rightFiniteDimensional_ext_three_finite (hAS : A.ASRegular Q)
    (M : A.RightModule) (hM : A.rightFiniteDimensionalProperty M) :
    A.leftFiniteDimensionalProperty (A.rightModuleExtLeft M 3) :=
  A.rightVertexFiltration_ext_three_finite Q hAS (A.rightFiniteDimensionalVertexFiltration M hM)
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem leftFiniteDimensional_ext_three_shortExact (hAS : A.ASRegular Q)
    {S : ShortComplex A.LeftModule} (hS : S.ShortExact)
    (h₁ : A.leftFiniteDimensionalProperty S.X₁)
    (h₃ : A.leftFiniteDimensionalProperty S.X₃) :
    (A.leftModuleExtRightShortComplex S 3).ShortExact :=
  A.leftModuleExtRightShortComplex_three_shortExact hS
    (fun i => A.leftFiniteDimensional_ext_other_eq_zero Q hAS S.X₁ h₁ i 2 (by decide))
    (fun i => A.leftFiniteDimensional_ext_other_eq_zero Q hAS S.X₃ h₃ i 4 (by decide))

theorem leftVertexFiltration_ext_three_finite (hAS : A.ASRegular Q)
    {M : A.LeftModule} (F : A.LeftVertexFiltration M) :
    A.rightFiniteDimensionalProperty (A.leftModuleExtRight M 3) := by
  induction F with
  | zero hM => exact A.rightFiniteDimensional_of_isZero (A.leftModuleExtRight_isZero_of_isZero hM 3)
  | @step M i f hf tail ih =>
    letI := hf
    let S : ShortComplex A.LeftModule :=
      ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
    have hT : (A.leftModuleExtRightShortComplex S 3).ShortExact :=
      A.leftModuleExtRightShortComplex_three_shortExact hS
        (fun j => A.leftFiniteDimensional_ext_other_eq_zero Q hAS (A.simpleLeftModule i)
          (A.leftFiniteDimensional_simple i) j 2 (by decide))
        (fun j => A.leftVertexFiltration_ext_other_eq_zero Q hAS tail j 4 (by decide))
    have hs : A.rightFiniteDimensionalProperty (A.leftModuleExtRight (A.simpleLeftModule i) 3) := by
      obtain ⟨w,rfl⟩ := Q.height_bijective.surjective i
      exact A.rightFiniteDimensional_of_mono (hAS.leftExtThreeIsoSimple A Q w).hom
        (A.rightFiniteDimensional_simple _)
    exact A.rightFiniteDimensional_of_shortExact hT ih hs

theorem leftFiniteDimensional_ext_three_finite (hAS : A.ASRegular Q)
    (M : A.LeftModule) (hM : A.leftFiniteDimensionalProperty M) :
    A.rightFiniteDimensionalProperty (A.leftModuleExtRight M 3) :=
  A.leftVertexFiltration_ext_three_finite Q hAS (A.leftFiniteDimensionalVertexFiltration M hM)
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

abbrev RightFiniteDimensional := A.rightFiniteDimensionalProperty.FullSubcategory
abbrev LeftFiniteDimensional := A.leftFiniteDimensionalProperty.FullSubcategory

instance rightFiniteDimensionalOppositeLinear : Linear k A.RightFiniteDimensionalᵒᵖ :=
  ASGinzburg.oppositeLinear _
instance leftFiniteDimensionalOppositeLinear : Linear k A.LeftFiniteDimensionalᵒᵖ :=
  ASGinzburg.oppositeLinear _

noncomputable def rightFiniteDimensionalExtThreeFunctor (hAS : A.ASRegular Q) :
    A.RightFiniteDimensionalᵒᵖ ⥤ A.LeftFiniteDimensional where
  obj M := ⟨A.rightModuleExtLeft M.unop.obj 3,
    A.rightFiniteDimensional_ext_three_finite Q hAS M.unop.obj M.unop.property⟩
  map f := ObjectProperty.homMk (A.rightModuleExtPrecompLeft f.unop.hom 3)
  map_id M := by
    apply ObjectProperty.hom_ext
    exact (A.rightModuleExtLeftFunctor 3).map_id (op M.unop.obj)
  map_comp {M N P} f g := by
    let fb : op M.unop.obj ⟶ op N.unop.obj :=
      (show N.unop.obj ⟶ M.unop.obj from f.unop.hom).op
    let gb : op N.unop.obj ⟶ op P.unop.obj :=
      (show P.unop.obj ⟶ N.unop.obj from g.unop.hom).op
    apply ObjectProperty.hom_ext
    exact (A.rightModuleExtLeftFunctor 3).map_comp fb gb

noncomputable def leftFiniteDimensionalExtThreeFunctor (hAS : A.ASRegular Q) :
    A.LeftFiniteDimensionalᵒᵖ ⥤ A.RightFiniteDimensional where
  obj M := ⟨A.leftModuleExtRight M.unop.obj 3,
    A.leftFiniteDimensional_ext_three_finite Q hAS M.unop.obj M.unop.property⟩
  map f := ObjectProperty.homMk (A.leftModuleExtPrecompRight f.unop.hom 3)
  map_id M := by
    apply ObjectProperty.hom_ext
    exact (A.leftModuleExtRightFunctor 3).map_id (op M.unop.obj)
  map_comp {M N P} f g := by
    let fb : op M.unop.obj ⟶ op N.unop.obj :=
      (show N.unop.obj ⟶ M.unop.obj from f.unop.hom).op
    let gb : op N.unop.obj ⟶ op P.unop.obj :=
      (show P.unop.obj ⟶ N.unop.obj from g.unop.hom).op
    apply ObjectProperty.hom_ext
    exact (A.leftModuleExtRightFunctor 3).map_comp fb gb

instance rightFiniteDimensionalExtThreeFunctorAdditive (hAS : A.ASRegular Q) :
    (A.rightFiniteDimensionalExtThreeFunctor Q hAS).Additive where
  map_add := by
    intro M N f g
    let fb : op M.unop.obj ⟶ op N.unop.obj :=
      (show N.unop.obj ⟶ M.unop.obj from f.unop.hom).op
    let gb : op M.unop.obj ⟶ op N.unop.obj :=
      (show N.unop.obj ⟶ M.unop.obj from g.unop.hom).op
    apply ObjectProperty.hom_ext
    exact (A.rightModuleExtLeftFunctor 3).map_add (f := fb) (g := gb)

instance leftFiniteDimensionalExtThreeFunctorAdditive (hAS : A.ASRegular Q) :
    (A.leftFiniteDimensionalExtThreeFunctor Q hAS).Additive where
  map_add := by
    intro M N f g
    let fb : op M.unop.obj ⟶ op N.unop.obj :=
      (show N.unop.obj ⟶ M.unop.obj from f.unop.hom).op
    let gb : op M.unop.obj ⟶ op N.unop.obj :=
      (show N.unop.obj ⟶ M.unop.obj from g.unop.hom).op
    apply ObjectProperty.hom_ext
    exact (A.leftModuleExtRightFunctor 3).map_add (f := fb) (g := gb)

instance rightFiniteDimensionalExtThreeFunctorLinear (hAS : A.ASRegular Q) :
    (A.rightFiniteDimensionalExtThreeFunctor Q hAS).Linear k where
  map_smul := by
    intro M N f r
    let fb : op M.unop.obj ⟶ op N.unop.obj :=
      (show N.unop.obj ⟶ M.unop.obj from f.unop.hom).op
    apply ObjectProperty.hom_ext
    exact (A.rightModuleExtLeftFunctor 3).map_smul (f := fb) r

instance leftFiniteDimensionalExtThreeFunctorLinear (hAS : A.ASRegular Q) :
    (A.leftFiniteDimensionalExtThreeFunctor Q hAS).Linear k where
  map_smul := by
    intro M N f r
    let fb : op M.unop.obj ⟶ op N.unop.obj :=
      (show N.unop.obj ⟶ M.unop.obj from f.unop.hom).op
    apply ObjectProperty.hom_ext
    exact (A.leftModuleExtRightFunctor 3).map_smul (f := fb) r
end ASGinzburg.ZAlgebra
