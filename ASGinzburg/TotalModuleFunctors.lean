import ASGinzburg.LocallyUnitalModules

/-!
Natural transformations act componentwise on the total spaces and commute with
the genuine total algebra actions. They therefore give module maps over the
unitization. The resulting left and right functors are faithful; fullness and
essential surjectivity are proved separately.
-/
namespace ASGinzburg.ZAlgebra
open CategoryTheory Opposite
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def leftTotalLinearMap {M N : A.LeftModule} (f : M ⟶ N) :
    A.leftModuleTotalSpace M →ₗ[k] A.leftModuleTotalSpace N :=
  DFinsupp.mapRange.linearMap (fun i => (f.app (⟨i⟩ : A.Obj)).hom)

noncomputable def rightTotalLinearMap {M N : A.RightModule} (f : M ⟶ N) :
    A.rightModuleTotalSpace M →ₗ[k] A.rightModuleTotalSpace N :=
  DFinsupp.mapRange.linearMap (fun i => (f.app (op (⟨i⟩ : A.Obj))).hom)

@[simp] theorem leftTotalLinearMap_lof {M N : A.LeftModule} (f : M ⟶ N) (i : ℤ)
    (x : (A.leftModuleEvaluation i).obj M) :
    A.leftTotalLinearMap f (DirectSum.lof k ℤ _ i x) =
      DirectSum.lof k ℤ _ i ((f.app (⟨i⟩ : A.Obj)).hom x) := by
  exact DFinsupp.mapRange_single (hf := fun i => (f.app (⟨i⟩ : A.Obj)).hom.map_zero)

@[simp] theorem rightTotalLinearMap_lof {M N : A.RightModule} (f : M ⟶ N) (i : ℤ)
    (x : (A.rightModuleEvaluation i).obj M) :
    A.rightTotalLinearMap f (DirectSum.lof k ℤ _ i x) =
      DirectSum.lof k ℤ _ i ((f.app (op (⟨i⟩ : A.Obj))).hom x) := by
  exact DFinsupp.mapRange_single (hf := fun i => (f.app (op (⟨i⟩ : A.Obj))).hom.map_zero)

theorem leftTotalLinearMap_action {M N : A.LeftModule} (f : M ⟶ N) {i j : ℤ}
    (a : A.Hom i j) :
    (A.leftTotalLinearMap f).comp (A.leftModuleTotalAction M a) =
      (A.leftModuleTotalAction N a).comp (A.leftTotalLinearMap f) := by
  apply DFinsupp.lhom_ext
  intro l x
  change A.leftTotalLinearMap f
    (A.leftModuleTotalAction M a (DirectSum.lof k ℤ _ l x)) =
      A.leftModuleTotalAction N a (A.leftTotalLinearMap f (DirectSum.lof k ℤ _ l x))
  by_cases hli : l = i
  · subst l
    rw [A.leftModuleTotalAction_lof, A.leftTotalLinearMap_lof,
      A.leftTotalLinearMap_lof, A.leftModuleTotalAction_lof]
    apply congrArg (DirectSum.lof k ℤ (fun l => (A.leftModuleEvaluation l).obj N) j)
    exact congrArg (fun h => h.hom x) (f.naturality (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from a))
  · rw [A.leftModuleTotalAction_lof_off M a l hli, map_zero,
      A.leftTotalLinearMap_lof, A.leftModuleTotalAction_lof_off N a l hli]

theorem rightTotalLinearMap_action {M N : A.RightModule} (f : M ⟶ N) {i j : ℤ}
    (a : A.Hom i j) :
    (A.rightTotalLinearMap f).comp (A.rightModuleTotalAction M a) =
      (A.rightModuleTotalAction N a).comp (A.rightTotalLinearMap f) := by
  apply DFinsupp.lhom_ext
  intro l x
  change A.rightTotalLinearMap f
    (A.rightModuleTotalAction M a (DirectSum.lof k ℤ _ l x)) =
      A.rightModuleTotalAction N a (A.rightTotalLinearMap f (DirectSum.lof k ℤ _ l x))
  by_cases hlj : l = j
  · subst l
    rw [A.rightModuleTotalAction_lof, A.rightTotalLinearMap_lof,
      A.rightTotalLinearMap_lof, A.rightModuleTotalAction_lof]
    apply congrArg (DirectSum.lof k ℤ (fun l => (A.rightModuleEvaluation l).obj N) i)
    exact congrArg (fun h => h.hom x)
      (f.naturality (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from a).op)
  · rw [A.rightModuleTotalAction_lof_off M a l hlj, map_zero,
      A.rightTotalLinearMap_lof, A.rightModuleTotalAction_lof_off N a l hlj]


theorem leftTotalLinearMap_representation {M N : A.LeftModule} (f : M ⟶ N)
    (a : A.totalAlgebra) :
    (A.leftTotalLinearMap f).comp (A.leftTotalRepresentation M a) =
      (A.leftTotalRepresentation N a).comp (A.leftTotalLinearMap f) := by
  obtain ⟨a,rfl⟩ := A.totalAlgebraEquiv.surjective a
  induction a using DFinsupp.induction with
  | h0 => simp
  | ha p b a _ _ ih =>
    rw [A.totalAlgebraEquiv.map_add,
      (A.leftTotalRepresentation M).map_add,
      (A.leftTotalRepresentation N).map_add,
      LinearMap.comp_add, LinearMap.add_comp, ih]
    congr 1
    change (A.leftTotalLinearMap f).comp (A.leftTotalRepresentation M (A.totalAlgebraComponent b)) =
      (A.leftTotalRepresentation N (A.totalAlgebraComponent b)).comp (A.leftTotalLinearMap f)
    rw [A.leftTotalRepresentation_component, A.leftTotalRepresentation_component]
    exact A.leftTotalLinearMap_action f b

theorem rightTotalLinearMap_representation {M N : A.RightModule} (f : M ⟶ N)
    (a : A.totalAlgebra) :
    (A.rightTotalLinearMap f).comp (A.rightTotalRepresentation M a).unop =
      (A.rightTotalRepresentation N a).unop.comp (A.rightTotalLinearMap f) := by
  obtain ⟨a,rfl⟩ := A.totalAlgebraEquiv.surjective a
  induction a using DFinsupp.induction with
  | h0 => simp
  | ha p b a _ _ ih =>
    rw [A.totalAlgebraEquiv.map_add,
      (A.rightTotalRepresentation M).map_add,
      (A.rightTotalRepresentation N).map_add, MulOpposite.unop_add, MulOpposite.unop_add,
      LinearMap.comp_add, LinearMap.add_comp, ih]
    congr 1
    change (A.rightTotalLinearMap f).comp
      (A.rightTotalRepresentation M (A.totalAlgebraComponent b)).unop =
      (A.rightTotalRepresentation N (A.totalAlgebraComponent b)).unop.comp (A.rightTotalLinearMap f)
    rw [A.rightTotalRepresentation_component, A.rightTotalRepresentation_component]
    exact A.rightTotalLinearMap_action f b

noncomputable def leftTotalModuleMap {M N : A.LeftModule} (f : M ⟶ N) :
    A.leftTotalModule M ⟶ A.leftTotalModule N := by
  letI := A.leftTotalUnitizationModule M
  letI := A.leftTotalUnitizationModule N
  exact ModuleCat.ofHom
    { toFun := fun x : A.leftTotalModule M => (A.leftTotalLinearMap f x : A.leftTotalModule N)
      map_add' := (A.leftTotalLinearMap f).map_add
      map_smul' := by
        intro r x
        change A.leftTotalLinearMap f
          (r.fst • x + A.leftTotalRepresentation M r.snd x) =
            r.fst • A.leftTotalLinearMap f x + A.leftTotalRepresentation N r.snd (A.leftTotalLinearMap f x)
        rw [map_add, map_smul]
        exact congrArg (r.fst • A.leftTotalLinearMap f x + ·)
          (LinearMap.congr_fun (A.leftTotalLinearMap_representation f r.snd) x) }

noncomputable def rightTotalModuleMap {M N : A.RightModule} (f : M ⟶ N) :
    A.rightTotalModule M ⟶ A.rightTotalModule N := by
  letI := A.rightTotalUnitizationModule M
  letI := A.rightTotalUnitizationModule N
  exact ModuleCat.ofHom
    { toFun := fun x : A.rightTotalModule M => (A.rightTotalLinearMap f x : A.rightTotalModule N)
      map_add' := (A.rightTotalLinearMap f).map_add
      map_smul' := by
        intro r x
        change A.rightTotalLinearMap f
          (r.unop.fst • x + (A.rightTotalRepresentation M r.unop.snd).unop x) =
            r.unop.fst • A.rightTotalLinearMap f x +
              (A.rightTotalRepresentation N r.unop.snd).unop (A.rightTotalLinearMap f x)
        rw [map_add, map_smul]
        exact congrArg (r.unop.fst • A.rightTotalLinearMap f x + ·)
          (LinearMap.congr_fun (A.rightTotalLinearMap_representation f r.unop.snd) x) }


noncomputable def leftTotalLocallyUnitalFunctor : A.LeftModule ⥤ A.LeftLocallyUnitalModule where
  obj := A.leftTotalLocallyUnitalModule
  map f := A.leftTotalModuleMap f
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro i
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro i
    rfl

noncomputable def rightTotalLocallyUnitalFunctor : A.RightModule ⥤ A.RightLocallyUnitalModule where
  obj := A.rightTotalLocallyUnitalModule
  map f := A.rightTotalModuleMap f
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro i
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro i
    rfl

instance leftTotalLocallyUnitalFunctorFaithful : A.leftTotalLocallyUnitalFunctor.Faithful where
  map_injective := by
    intro M N f g h
    apply NatTrans.ext
    funext X
    rcases X with ⟨i⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have he := congrArg (fun t => t.hom (DirectSum.lof k ℤ
      (fun l => (A.leftModuleEvaluation l).obj M) i x)) h
    change A.leftTotalLinearMap f (DirectSum.lof k ℤ _ i x) =
      A.leftTotalLinearMap g (DirectSum.lof k ℤ _ i x) at he
    rw [A.leftTotalLinearMap_lof, A.leftTotalLinearMap_lof] at he
    simpa only [DirectSum.lof_apply] using congrArg (fun z => z i) he

instance rightTotalLocallyUnitalFunctorFaithful : A.rightTotalLocallyUnitalFunctor.Faithful where
  map_injective := by
    intro M N f g h
    apply NatTrans.ext
    funext X
    cases X using Opposite.rec
    rename_i X
    rcases X with ⟨i⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have he := congrArg (fun t => t.hom (DirectSum.lof k ℤ
      (fun l => (A.rightModuleEvaluation l).obj M) i x)) h
    change A.rightTotalLinearMap f (DirectSum.lof k ℤ _ i x) =
      A.rightTotalLinearMap g (DirectSum.lof k ℤ _ i x) at he
    rw [A.rightTotalLinearMap_lof, A.rightTotalLinearMap_lof] at he
    simpa only [DirectSum.lof_apply] using congrArg (fun z => z i) he

end ASGinzburg.ZAlgebra
