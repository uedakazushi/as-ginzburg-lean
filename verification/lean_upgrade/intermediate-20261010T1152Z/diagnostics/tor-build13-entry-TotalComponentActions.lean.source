import ASGinzburg.TotalAlgebra

/-! The concrete left and right total-space actions respect addition, scalars,
connected composition, and the zero product of disconnected components. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem leftModuleTotalAction_add (M : A.LeftModule) {i j : ℤ} (a b : A.Hom i j) :
    A.leftModuleTotalAction M (a + b) =
      A.leftModuleTotalAction M a + A.leftModuleTotalAction M b := by
  letI := M.property.1
  have hm := M.obj.map_add
    (f := (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from a))
    (g := (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from b))
  dsimp [leftModuleTotalAction]
  erw [hm]
  rw [ModuleCat.hom_add, LinearMap.add_comp, LinearMap.comp_add]

theorem leftModuleTotalAction_smul (M : A.LeftModule) {i j : ℤ} (r : k) (a : A.Hom i j) :
    A.leftModuleTotalAction M (r • a) = r • A.leftModuleTotalAction M a := by
  letI := M.property.2
  have hm := M.obj.map_smul r (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from a)
  dsimp [leftModuleTotalAction]
  erw [hm]
  rw [ModuleCat.hom_smul, LinearMap.smul_comp, LinearMap.comp_smul]

theorem leftModuleTotalAction_comp (M : A.LeftModule) {i j l : ℤ}
    (a : A.Hom i j) (b : A.Hom j l) :
    (A.leftModuleTotalAction M b).comp (A.leftModuleTotalAction M a) =
      A.leftModuleTotalAction M (A.comp b a) := by
  apply DFinsupp.lhom_ext
  intro p x
  change A.leftModuleTotalAction M b
    (A.leftModuleTotalAction M a (DirectSum.lof k ℤ _ p x)) =
      A.leftModuleTotalAction M (A.comp b a) (DirectSum.lof k ℤ _ p x)
  by_cases hp : p = i
  · subst p
    rw [A.leftModuleTotalAction_lof, A.leftModuleTotalAction_lof,
      A.leftModuleTotalAction_lof]
    have hmap := M.obj.map_comp (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from a)
      (show (⟨j⟩ : A.Obj) ⟶ ⟨l⟩ from b)
    erw [hmap]
    rfl
  · rw [A.leftModuleTotalAction_lof_off M a p hp, map_zero,
      A.leftModuleTotalAction_lof_off M (A.comp b a) p hp]

theorem leftModuleTotalAction_comp_off (M : A.LeftModule) {i j p q : ℤ}
    (a : A.Hom i j) (b : A.Hom p q) (hjp : j ≠ p) :
    (A.leftModuleTotalAction M b).comp (A.leftModuleTotalAction M a) = 0 := by
  apply DFinsupp.lhom_ext
  intro l x
  change A.leftModuleTotalAction M b
    (A.leftModuleTotalAction M a (DirectSum.lof k ℤ _ l x)) = 0
  by_cases hli : l = i
  · subst l
    rw [A.leftModuleTotalAction_lof, A.leftModuleTotalAction_lof_off M b j hjp]
  · rw [A.leftModuleTotalAction_lof_off M a l hli, map_zero]

theorem rightModuleTotalAction_add (M : A.RightModule) {i j : ℤ} (a b : A.Hom i j) :
    A.rightModuleTotalAction M (a + b) =
      A.rightModuleTotalAction M a + A.rightModuleTotalAction M b := by
  letI := M.property.1
  have hm := M.obj.map_add
    (f := (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from a).op)
    (g := (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from b).op)
  dsimp [rightModuleTotalAction]
  erw [hm]
  rw [ModuleCat.hom_add, LinearMap.add_comp, LinearMap.comp_add]

theorem rightModuleTotalAction_smul (M : A.RightModule) {i j : ℤ} (r : k) (a : A.Hom i j) :
    A.rightModuleTotalAction M (r • a) = r • A.rightModuleTotalAction M a := by
  letI := M.property.2
  have hm := M.obj.map_smul r (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from a).op
  dsimp [rightModuleTotalAction]
  erw [hm]
  rw [ModuleCat.hom_smul, LinearMap.smul_comp, LinearMap.comp_smul]

theorem rightModuleTotalAction_comp (M : A.RightModule) {i j l : ℤ}
    (a : A.Hom i j) (b : A.Hom j l) :
    (A.rightModuleTotalAction M a).comp (A.rightModuleTotalAction M b) =
      A.rightModuleTotalAction M (A.comp b a) := by
  apply DFinsupp.lhom_ext
  intro p x
  change A.rightModuleTotalAction M a
    (A.rightModuleTotalAction M b (DirectSum.lof k ℤ _ p x)) =
      A.rightModuleTotalAction M (A.comp b a) (DirectSum.lof k ℤ _ p x)
  by_cases hp : p = l
  · subst p
    rw [A.rightModuleTotalAction_lof, A.rightModuleTotalAction_lof,
      A.rightModuleTotalAction_lof]
    have hmap := M.obj.map_comp (show (⟨j⟩ : A.Obj) ⟶ ⟨l⟩ from b).op
      (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from a).op
    erw [hmap]
    rfl
  · rw [A.rightModuleTotalAction_lof_off M b p hp, map_zero,
      A.rightModuleTotalAction_lof_off M (A.comp b a) p hp]

theorem rightModuleTotalAction_comp_off (M : A.RightModule) {i j p q : ℤ}
    (a : A.Hom i j) (b : A.Hom p q) (hjp : j ≠ p) :
    (A.rightModuleTotalAction M a).comp (A.rightModuleTotalAction M b) = 0 := by
  apply DFinsupp.lhom_ext
  intro l x
  change A.rightModuleTotalAction M a
    (A.rightModuleTotalAction M b (DirectSum.lof k ℤ _ l x)) = 0
  by_cases hlq : l = q
  · subst l
    rw [A.rightModuleTotalAction_lof, A.rightModuleTotalAction_lof_off M a p (Ne.symm hjp)]
  · rw [A.rightModuleTotalAction_lof_off M b l hlq, map_zero]

noncomputable def leftTotalComponentRepresentation (M : A.LeftModule) (i j : ℤ) :
    A.Hom i j →ₗ[k] Module.End k (A.leftModuleTotalSpace M) where
  toFun := A.leftModuleTotalAction M
  map_add' := A.leftModuleTotalAction_add M
  map_smul' r a := A.leftModuleTotalAction_smul M r a

noncomputable def rightTotalComponentRepresentation (M : A.RightModule) (i j : ℤ) :
    A.Hom i j →ₗ[k] Module.End k (A.rightModuleTotalSpace M) where
  toFun := A.rightModuleTotalAction M
  map_add' := A.rightModuleTotalAction_add M
  map_smul' r a := A.rightModuleTotalAction_smul M r a

end ASGinzburg.ZAlgebra
