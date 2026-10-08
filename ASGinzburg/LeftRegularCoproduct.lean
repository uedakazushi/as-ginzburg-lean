import ASGinzburg.LeftHomColimits
import ASGinzburg.RegularCoproductActions
import ASGinzburg.LeftModuleADual

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def leftRegularCoproduct : A.LeftModule := ∐ fun i : ℤ => A.leftRepresentable i

noncomputable def leftRegularCoproductComponentIso (j : ℤ) :
    (A.leftModuleEvaluation j).obj A.leftRegularCoproduct ≅
      ModuleCat.of k (⨁ i : ℤ, A.Hom i j) :=
  PreservesCoproduct.iso (A.leftModuleEvaluation j) (fun i : ℤ => A.leftRepresentable i) ≪≫
    ModuleCat.coprodIsoDirectSum _

noncomputable def leftRegularCoproductProjection (i : ℤ) :
    A.leftRegularCoproduct ⟶ A.leftRepresentable i :=
  Sigma.desc (fun j : ℤ => if h : j=i then eqToHom (congrArg A.leftRepresentable h) else 0)

@[reassoc (attr := simp)] theorem leftRegularCoproduct_inclusion_projection (i : ℤ) :
    Sigma.ι (fun j : ℤ => A.leftRepresentable j) i ≫ A.leftRegularCoproductProjection i = 𝟙 _ := by
  simp [leftRegularCoproductProjection]

@[reassoc] theorem leftRegularCoproduct_inclusion_projection_off (i j : ℤ) (hji : j ≠ i) :
    Sigma.ι (fun l : ℤ => A.leftRepresentable l) j ≫ A.leftRegularCoproductProjection i = 0 := by
  simp [leftRegularCoproductProjection,hji]

/-- Actual right multiplication on the regular left-module coproduct. -/
noncomputable def leftRegularCoproductAction {i j : ℤ} (a : A.Hom i j) :
    A.leftRegularCoproduct ⟶ A.leftRegularCoproduct :=
  A.leftRegularCoproductProjection j ≫
    A.leftRepresentableFunctor.map (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from a).op ≫
      Sigma.ι (fun l : ℤ => A.leftRepresentable l) i

@[reassoc (attr := simp)] theorem leftRegularCoproduct_inclusion_action {i j : ℤ} (a : A.Hom i j) :
    Sigma.ι (fun l : ℤ => A.leftRepresentable l) j ≫ A.leftRegularCoproductAction a =
      A.leftRepresentableFunctor.map (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from a).op ≫
        Sigma.ι (fun l : ℤ => A.leftRepresentable l) i := by
  simp [leftRegularCoproductAction]

@[reassoc] theorem leftRegularCoproduct_inclusion_action_off {i j : ℤ}
    (a : A.Hom i j) (l : ℤ) (hlj : l ≠ j) :
    Sigma.ι (fun t : ℤ => A.leftRepresentable t) l ≫ A.leftRegularCoproductAction a = 0 := by
  rw [leftRegularCoproductAction,
    leftRegularCoproduct_inclusion_projection_off_assoc _ _ _ hlj,zero_comp]

theorem leftRegularCoproductAction_add {i j : ℤ} (a b : A.Hom i j) :
    A.leftRegularCoproductAction (a+b) =
      A.leftRegularCoproductAction a + A.leftRegularCoproductAction b := by
  have hm := A.leftRepresentableFunctor.map_add
    (f := (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from a).op)
    (g := (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from b).op)
  dsimp [leftRegularCoproductAction]
  erw [hm]
  rw [Preadditive.add_comp,Preadditive.comp_add]

theorem leftRegularCoproductAction_smul {i j : ℤ} (r : k) (a : A.Hom i j) :
    A.leftRegularCoproductAction (r • a) = r • A.leftRegularCoproductAction a := by
  have hm := A.leftRepresentableFunctor.map_smul r (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from a).op
  dsimp [leftRegularCoproductAction]
  erw [hm]
  rw [Linear.smul_comp,Linear.comp_smul]

theorem leftRegularCoproductAction_comp {i j l : ℤ} (a : A.Hom i j) (b : A.Hom j l) :
    A.leftRegularCoproductAction b ≫ A.leftRegularCoproductAction a =
      A.leftRegularCoproductAction (A.comp b a) := by
  simp only [leftRegularCoproductAction,Category.assoc,
    leftRegularCoproduct_inclusion_projection_assoc]
  change A.leftRegularCoproductProjection l ≫
    A.leftRepresentableFunctor.map (show (op (⟨l⟩ : A.Obj)) ⟶ op ⟨j⟩ from
      (show (⟨j⟩ : A.Obj) ⟶ ⟨l⟩ from b).op) ≫
      A.leftRepresentableFunctor.map (show (op (⟨j⟩ : A.Obj)) ⟶ op ⟨i⟩ from
        (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from a).op) ≫ _ = _
  rw [← Functor.map_comp_assoc]
  rfl

theorem leftRegularCoproductAction_id (i : ℤ) :
    A.leftRegularCoproductAction (A.id i) =
      A.leftRegularCoproductProjection i ≫ Sigma.ι (fun l : ℤ => A.leftRepresentable l) i := by
  change A.leftRegularCoproductProjection i ≫
    A.leftRepresentableFunctor.map (𝟙 (op (⟨i⟩ : A.Obj))) ≫
      Sigma.ι (fun l : ℤ => A.leftRepresentable l) i = _
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem leftRegularCoproductAction_comp_off {i j p q : ℤ}
    (a : A.Hom i j) (b : A.Hom p q) (hjp : j ≠ p) :
    A.leftRegularCoproductAction b ≫ A.leftRegularCoproductAction a = 0 := by
  simp only [leftRegularCoproductAction,Category.assoc]
  rw [A.leftRegularCoproduct_inclusion_projection_off_assoc j p (Ne.symm hjp)]
  simp

end ASGinzburg.ZAlgebra
