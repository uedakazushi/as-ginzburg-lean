import ASGinzburg.LeftRegularCoproduct
import ASGinzburg.RegularTotalAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def leftRegularTotalComponentsEquiv :
    A.leftModuleTotalSpace A.leftRegularCoproduct ≃ₗ[k] A.totalAlgebraSpace :=
  (DFinsupp.mapRange.linearEquiv (fun j => (A.leftRegularCoproductComponentIso j).toLinearEquiv)).trans
    ((DFinsupp.sigmaCurryLEquiv (R := k) (M := fun j i : ℤ => A.Hom i j)).symm.trans
      (DFinsupp.domLCongr (R := k)
        ((Equiv.sigmaEquivProd ℤ ℤ).trans (Equiv.prodComm ℤ ℤ))))

noncomputable def leftRegularTotalAlgebraEquiv :
    A.leftModuleTotalSpace A.leftRegularCoproduct ≃ₗ[k] A.totalAlgebra :=
  A.leftRegularTotalComponentsEquiv.trans A.totalAlgebraEquiv

theorem leftRegularComponentIso_lof_inv (i j : ℤ) (a : A.Hom i j) :
    (A.leftRegularCoproductComponentIso j).inv.hom (DirectSum.lof k ℤ _ i a) =
      ((Sigma.ι (fun l : ℤ => A.leftRepresentable l) i).hom.app (⟨j⟩ : A.Obj)).hom a := by
  have h : ModuleCat.ofHom (DirectSum.lof k ℤ (fun l => A.Hom l j) i) ≫
      (A.leftRegularCoproductComponentIso j).inv =
      (A.leftModuleEvaluation j).map (Sigma.ι (fun l : ℤ => A.leftRepresentable l) i) := by
    dsimp only [leftRegularCoproductComponentIso,Iso.trans_inv]
    rw [← Category.assoc]
    erw [ModuleCat.lof_coprodIsoDirectSum_inv
      (fun l : ℤ => (A.leftModuleEvaluation j).obj (A.leftRepresentable l)) i]
    rw [PreservesCoproduct.inv_hom,ι_comp_sigmaComparison]
  exact congrArg (fun f => f.hom a) h

theorem leftRegularComponentIso_inclusion (i j : ℤ) (a : A.Hom i j) :
    (A.leftRegularCoproductComponentIso j).hom.hom
      (((Sigma.ι (fun l : ℤ => A.leftRepresentable l) i).hom.app (⟨j⟩ : A.Obj)).hom a) =
      DirectSum.lof k ℤ _ i a := by
  rw [← A.leftRegularComponentIso_lof_inv i j a]
  exact (A.leftRegularCoproductComponentIso j).toLinearEquiv.apply_symm_apply _

noncomputable def leftRegularMatrixElement {i j : ℤ} (a : A.Hom i j) :
    A.leftModuleTotalSpace A.leftRegularCoproduct :=
  DirectSum.lof k ℤ _ j
    (((Sigma.ι (fun l : ℤ => A.leftRepresentable l) i).hom.app (⟨j⟩ : A.Obj)).hom a)

theorem leftRegularTotalComponentsEquiv_matrixElement {i j : ℤ} (a : A.Hom i j) :
    A.leftRegularTotalComponentsEquiv (A.leftRegularMatrixElement a) = DFinsupp.single (i,j) a := by
  simp only [leftRegularTotalComponentsEquiv,leftRegularMatrixElement,LinearEquiv.trans_apply]
  change DFinsupp.domLCongr (R := k)
    ((Equiv.sigmaEquivProd ℤ ℤ).trans (Equiv.prodComm ℤ ℤ))
      (DFinsupp.sigmaUncurry (DFinsupp.mapRange
        (fun t x => (A.leftRegularCoproductComponentIso t).toLinearEquiv x)
        (fun t => (A.leftRegularCoproductComponentIso t).toLinearEquiv.map_zero)
        (DFinsupp.single j
          (((Sigma.ι (fun l : ℤ => A.leftRepresentable l) i).hom.app (⟨j⟩ : A.Obj)).hom a)))) = _
  erw [DFinsupp.mapRange_single]
  change DFinsupp.domLCongr (R := k) (M := fun p : Σ _ : ℤ, ℤ => A.Hom p.2 p.1)
    ((Equiv.sigmaEquivProd ℤ ℤ).trans (Equiv.prodComm ℤ ℤ))
      (DFinsupp.sigmaUncurry (α := fun _ : ℤ => ℤ) (δ := fun j i : ℤ => A.Hom i j)
        (DFinsupp.single j ((A.leftRegularCoproductComponentIso j).hom.hom
          (((Sigma.ι (fun l : ℤ => A.leftRepresentable l) i).hom.app (⟨j⟩ : A.Obj)).hom a)))) = _
  rw [A.leftRegularComponentIso_inclusion]
  erw [DFinsupp.sigmaUncurry_single]
  apply DFinsupp.ext
  rintro ⟨p,q⟩
  change (DFinsupp.single (β := fun p : Σ _ : ℤ, ℤ => A.Hom p.2 p.1) ⟨j,i⟩ a) ⟨q,p⟩ =
    (DFinsupp.single (β := fun p : ℤ × ℤ => A.Hom p.1 p.2) (i,j) a) (p,q)
  rcases eq_or_ne p i with rfl | hp <;> rcases eq_or_ne q j with rfl | hq
  all_goals simp_all [DFinsupp.single_apply,eq_comm]

@[simp] theorem leftRegularTotalAlgebraEquiv_matrixElement {i j : ℤ} (a : A.Hom i j) :
    A.leftRegularTotalAlgebraEquiv (A.leftRegularMatrixElement a) = A.totalAlgebraComponent a := by
  change A.totalAlgebraEquiv (A.leftRegularTotalComponentsEquiv (A.leftRegularMatrixElement a)) = _
  rw [A.leftRegularTotalComponentsEquiv_matrixElement]
  rfl

theorem leftRegularTotalComponentsEquiv_symm_single {i j : ℤ} (a : A.Hom i j) :
    A.leftRegularTotalComponentsEquiv.symm (DFinsupp.single (i,j) a) = A.leftRegularMatrixElement a := by
  apply A.leftRegularTotalComponentsEquiv.injective
  rw [LinearEquiv.apply_symm_apply,A.leftRegularTotalComponentsEquiv_matrixElement]

theorem leftRegularMatrixElement_action {i j p : ℤ} (a : A.Hom i j) (b : A.Hom p i) :
    A.leftModuleTotalAction A.leftRegularCoproduct a (A.leftRegularMatrixElement b) =
      A.leftRegularMatrixElement (A.comp a b) := by
  change A.leftModuleTotalAction A.leftRegularCoproduct a
    (DirectSum.lof k ℤ _ i
      (((Sigma.ι (fun t : ℤ => A.leftRepresentable t) p).hom.app (⟨i⟩ : A.Obj)).hom b)) = _
  rw [A.leftModuleTotalAction_lof]
  apply congrArg (DirectSum.lof k ℤ (fun t => (A.leftModuleEvaluation t).obj A.leftRegularCoproduct) j)
  exact (congrArg (fun f => f.hom b)
    ((Sigma.ι (fun t : ℤ => A.leftRepresentable t) p).hom.naturality
      (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from a))).symm

theorem leftRegularMatrixElement_action_off {i j p q : ℤ} (a : A.Hom i j)
    (b : A.Hom p q) (hqi : q ≠ i) :
    A.leftModuleTotalAction A.leftRegularCoproduct a (A.leftRegularMatrixElement b) = 0 :=
  A.leftModuleTotalAction_lof_off A.leftRegularCoproduct a q hqi _

theorem leftRegularTotalAlgebraEquiv_action {i j : ℤ} (a : A.Hom i j)
    (x : A.leftModuleTotalSpace A.leftRegularCoproduct) :
    A.leftRegularTotalAlgebraEquiv (A.leftModuleTotalAction A.leftRegularCoproduct a x) =
      A.totalAlgebraComponent a * A.leftRegularTotalAlgebraEquiv x := by
  obtain ⟨x,rfl⟩ := A.leftRegularTotalComponentsEquiv.symm.surjective x
  induction x using DFinsupp.induction with
  | h0 => simp
  | ha p b x _ _ ih =>
    rw [map_add,map_add,map_add,map_add,mul_add,ih]
    congr 1
    rcases p with ⟨l,m⟩
    rw [A.leftRegularTotalComponentsEquiv_symm_single]
    by_cases hm : m=i
    · subst m
      rw [A.leftRegularMatrixElement_action,A.leftRegularTotalAlgebraEquiv_matrixElement,
        A.leftRegularTotalAlgebraEquiv_matrixElement,A.totalAlgebraComponent_mul]
    · rw [A.leftRegularMatrixElement_action_off a b hm,map_zero,
        A.leftRegularTotalAlgebraEquiv_matrixElement,A.totalAlgebraComponent_mul_off b a hm]

theorem leftRegularTotalAlgebraEquiv_representation (a : A.totalAlgebra)
    (x : A.leftModuleTotalSpace A.leftRegularCoproduct) :
    A.leftRegularTotalAlgebraEquiv (A.leftTotalRepresentation A.leftRegularCoproduct a x) =
      a * A.leftRegularTotalAlgebraEquiv x := by
  obtain ⟨a,rfl⟩ := A.totalAlgebraEquiv.surjective a
  induction a using DFinsupp.induction with
  | h0 => rw [map_zero,map_zero,LinearMap.zero_apply,map_zero,zero_mul]
  | ha p b a _ _ ih =>
    rw [A.totalAlgebraEquiv.map_add,(A.leftTotalRepresentation A.leftRegularCoproduct).map_add,
      LinearMap.add_apply,map_add,add_mul,ih]
    congr 1
    change A.leftRegularTotalAlgebraEquiv
      (A.leftTotalRepresentation A.leftRegularCoproduct (A.totalAlgebraComponent b) x) = _
    rw [A.leftTotalRepresentation_component]
    exact A.leftRegularTotalAlgebraEquiv_action b x

end ASGinzburg.ZAlgebra
