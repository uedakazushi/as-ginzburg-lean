import ASGinzburg.TotalModuleRepresentations

/-!
The coproduct of the original right representables has the finite-support total
algebra as its total space. The explicit equivalence sends inclusions to matrix
components and intertwines the original right action with right multiplication.
-/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def rightRegularTotalComponentsEquiv :
    A.rightModuleTotalSpace A.rightRegularCoproduct ≃ₗ[k] A.totalAlgebraSpace :=
  (DFinsupp.mapRange.linearEquiv
    (fun i => (A.rightRegularCoproductComponentIso i).toLinearEquiv)).trans
      ((DFinsupp.sigmaCurryLEquiv (R := k) (M := fun i j : ℤ => A.Hom i j)).symm.trans
        (DFinsupp.domLCongr (R := k) (Equiv.sigmaEquivProd ℤ ℤ)))

noncomputable def rightRegularTotalAlgebraEquiv :
    A.rightModuleTotalSpace A.rightRegularCoproduct ≃ₗ[k] A.totalAlgebra :=
  A.rightRegularTotalComponentsEquiv.trans A.totalAlgebraEquiv

theorem rightRegularComponentIso_lof_inv (i j : ℤ) (a : A.Hom i j) :
    (A.rightRegularCoproductComponentIso i).inv.hom (DirectSum.lof k ℤ _ j a) =
      ((Sigma.ι (fun l : ℤ => A.representable l) j).app (op (⟨i⟩ : A.Obj))).hom a := by
  have h : ModuleCat.ofHom (DirectSum.lof k ℤ (fun l => A.Hom i l) j) ≫
      (A.rightRegularCoproductComponentIso i).inv =
      (A.rightModuleEvaluation i).map (Sigma.ι (fun l : ℤ => A.representable l) j) := by
    dsimp only [rightRegularCoproductComponentIso, Iso.trans_inv]
    rw [← Category.assoc]
    erw [ModuleCat.lof_coprodIsoDirectSum_inv
      (fun l : ℤ => (A.rightModuleEvaluation i).obj (A.representable l)) j]
    rw [PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]
  exact congrArg (fun f => f.hom a) h

theorem rightRegularComponentIso_inclusion (i j : ℤ) (a : A.Hom i j) :
    (A.rightRegularCoproductComponentIso i).hom.hom
      (((Sigma.ι (fun l : ℤ => A.representable l) j).app (op (⟨i⟩ : A.Obj))).hom a) =
      DirectSum.lof k ℤ _ j a := by
  rw [← A.rightRegularComponentIso_lof_inv i j a]
  exact (A.rightRegularCoproductComponentIso i).toLinearEquiv.apply_symm_apply _

noncomputable def rightRegularMatrixElement {i j : ℤ} (a : A.Hom i j) :
    A.rightModuleTotalSpace A.rightRegularCoproduct :=
  DirectSum.lof k ℤ _ i
    (((Sigma.ι (fun l : ℤ => A.representable l) j).app (op (⟨i⟩ : A.Obj))).hom a)

theorem rightRegularTotalComponentsEquiv_matrixElement {i j : ℤ} (a : A.Hom i j) :
    A.rightRegularTotalComponentsEquiv (A.rightRegularMatrixElement a) =
      DFinsupp.single (i,j) a := by
  simp only [rightRegularTotalComponentsEquiv, rightRegularMatrixElement,
    LinearEquiv.trans_apply]
  change DFinsupp.domLCongr (R := k) (Equiv.sigmaEquivProd ℤ ℤ)
    (DFinsupp.sigmaUncurry (DFinsupp.mapRange
      (fun t x => (A.rightRegularCoproductComponentIso t).toLinearEquiv x)
      (fun t => (A.rightRegularCoproductComponentIso t).toLinearEquiv.map_zero)
      (DFinsupp.single i
        (((Sigma.ι (fun l : ℤ => A.representable l) j).app (op (⟨i⟩ : A.Obj))).hom a)))) = _
  erw [DFinsupp.mapRange_single]
  change DFinsupp.domLCongr (R := k) (M := fun p : Σ _ : ℤ, ℤ => A.Hom p.1 p.2) (Equiv.sigmaEquivProd ℤ ℤ)
    (DFinsupp.sigmaUncurry (α := fun _ : ℤ => ℤ) (δ := fun i j : ℤ => A.Hom i j) (DFinsupp.single i
      ((A.rightRegularCoproductComponentIso i).hom.hom
        (((Sigma.ι (fun l : ℤ => A.representable l) j).app (op (⟨i⟩ : A.Obj))).hom a)))) = _
  rw [A.rightRegularComponentIso_inclusion]
  erw [DFinsupp.sigmaUncurry_single]
  apply DFinsupp.ext
  rintro ⟨p,q⟩
  change (DFinsupp.single (β := fun p : Σ _ : ℤ, ℤ => A.Hom p.1 p.2) ⟨i,j⟩ a) ⟨p,q⟩ =
    (DFinsupp.single (β := fun p : ℤ × ℤ => A.Hom p.1 p.2) (i,j) a) (p,q)
  rcases eq_or_ne p i with rfl | hp <;> rcases eq_or_ne q j with rfl | hq
  all_goals simp_all [DFinsupp.single_apply, eq_comm]

@[simp] theorem rightRegularTotalAlgebraEquiv_matrixElement {i j : ℤ} (a : A.Hom i j) :
    A.rightRegularTotalAlgebraEquiv (A.rightRegularMatrixElement a) = A.totalAlgebraComponent a := by
  change A.totalAlgebraEquiv (A.rightRegularTotalComponentsEquiv (A.rightRegularMatrixElement a)) = _
  rw [A.rightRegularTotalComponentsEquiv_matrixElement]
  rfl

theorem rightRegularTotalComponentsEquiv_symm_single {i j : ℤ} (a : A.Hom i j) :
    A.rightRegularTotalComponentsEquiv.symm (DFinsupp.single (i,j) a) =
      A.rightRegularMatrixElement a := by
  apply A.rightRegularTotalComponentsEquiv.injective
  rw [LinearEquiv.apply_symm_apply, A.rightRegularTotalComponentsEquiv_matrixElement]

theorem rightRegularMatrixElement_action {i j l : ℤ} (a : A.Hom i j) (b : A.Hom j l) :
    A.rightModuleTotalAction A.rightRegularCoproduct a (A.rightRegularMatrixElement b) =
      A.rightRegularMatrixElement (A.comp b a) := by
  change A.rightModuleTotalAction A.rightRegularCoproduct a
    (DirectSum.lof k ℤ _ j
      (((Sigma.ι (fun t : ℤ => A.representable t) l).app (op (⟨j⟩ : A.Obj))).hom b)) = _
  rw [A.rightModuleTotalAction_lof]
  apply congrArg (DirectSum.lof k ℤ (fun t => (A.rightModuleEvaluation t).obj A.rightRegularCoproduct) i)
  exact (congrArg (fun f => f.hom b)
    ((Sigma.ι (fun t : ℤ => A.representable t) l).naturality
      (show op (⟨j⟩ : A.Obj) ⟶ op (⟨i⟩ : A.Obj) from
        (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from a).op))).symm

theorem rightRegularMatrixElement_action_off {i j p q : ℤ} (a : A.Hom i j)
    (b : A.Hom p q) (hpj : p ≠ j) :
    A.rightModuleTotalAction A.rightRegularCoproduct a (A.rightRegularMatrixElement b) = 0 :=
  A.rightModuleTotalAction_lof_off A.rightRegularCoproduct a p hpj _

theorem rightRegularTotalAlgebraEquiv_action {i j : ℤ} (a : A.Hom i j)
    (x : A.rightModuleTotalSpace A.rightRegularCoproduct) :
    A.rightRegularTotalAlgebraEquiv (A.rightModuleTotalAction A.rightRegularCoproduct a x) =
      A.rightRegularTotalAlgebraEquiv x * A.totalAlgebraComponent a := by
  obtain ⟨x,rfl⟩ := A.rightRegularTotalComponentsEquiv.symm.surjective x
  induction x using DFinsupp.induction with
  | h0 => simp
  | ha p b x _ _ ih =>
    rw [map_add, map_add, map_add, map_add, add_mul, ih]
    congr 1
    rcases p with ⟨l,m⟩
    rw [A.rightRegularTotalComponentsEquiv_symm_single]
    by_cases hl : l = j
    · subst l
      rw [A.rightRegularMatrixElement_action, A.rightRegularTotalAlgebraEquiv_matrixElement,
        A.rightRegularTotalAlgebraEquiv_matrixElement, A.totalAlgebraComponent_mul]
    · rw [A.rightRegularMatrixElement_action_off a b hl, map_zero,
        A.rightRegularTotalAlgebraEquiv_matrixElement,
        A.totalAlgebraComponent_mul_off a b (Ne.symm hl)]

theorem rightRegularTotalAlgebraEquiv_representation (a : A.totalAlgebra)
    (x : A.rightModuleTotalSpace A.rightRegularCoproduct) :
    A.rightRegularTotalAlgebraEquiv ((A.rightTotalRepresentation A.rightRegularCoproduct a).unop x) =
      A.rightRegularTotalAlgebraEquiv x * a := by
  obtain ⟨a,rfl⟩ := A.totalAlgebraEquiv.surjective a
  induction a using DFinsupp.induction with
  | h0 =>
    rw [map_zero, map_zero, MulOpposite.unop_zero, LinearMap.zero_apply, map_zero, mul_zero]
  | ha p b a _ _ ih =>
    rw [A.totalAlgebraEquiv.map_add,
      (A.rightTotalRepresentation A.rightRegularCoproduct).map_add,
      MulOpposite.unop_add, LinearMap.add_apply, map_add, mul_add, ih]
    congr 1
    change A.rightRegularTotalAlgebraEquiv
      ((A.rightTotalRepresentation A.rightRegularCoproduct (A.totalAlgebraComponent b)).unop x) = _
    rw [A.rightTotalRepresentation_component]
    exact A.rightRegularTotalAlgebraEquiv_action b x

end ASGinzburg.ZAlgebra
