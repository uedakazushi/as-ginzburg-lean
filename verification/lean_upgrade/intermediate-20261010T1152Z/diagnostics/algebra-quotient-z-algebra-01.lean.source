import ASGinzburg.LinearIdealProducts

/-! Actual quotient component algebras by two-sided linear ideals. -/
namespace ASGinzburg.ZAlgebra.LinearIdeal
universe u v
variable {k : Type u} [Field k] {B : ZAlgebra.{u,v} k} (I : B.LinearIdeal)

abbrev QuotientComponent (i j : ℤ) := B.Hom i j ⧸ I.hom i j

noncomputable def quotientCompRight {i j l : ℤ} (g : B.Hom j l) :
    I.QuotientComponent i j →ₗ[k] I.QuotientComponent i l :=
  (I.hom i j).liftQ (((I.hom i l).mkQ).comp (B.comp g)) (by
    intro f hf
    change (I.hom i l).mkQ (B.comp g f)=0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (I.comp_left hf g))

@[simp] theorem quotientCompRight_mk {i j l : ℤ} (g : B.Hom j l) (f : B.Hom i j) :
    I.quotientCompRight g (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (B.comp g f) := rfl

noncomputable def quotientCompPre {i j l : ℤ} :
    B.Hom j l →ₗ[k] I.QuotientComponent i j →ₗ[k] I.QuotientComponent i l where
  toFun := I.quotientCompRight
  map_add' := by
    intro g h
    apply LinearMap.ext
    intro x
    obtain ⟨f,rfl⟩ := (I.hom i j).mkQ_surjective x
    simp [LinearMap.add_apply]
  map_smul' := by
    intro a g
    apply LinearMap.ext
    intro x
    obtain ⟨f,rfl⟩ := (I.hom i j).mkQ_surjective x
    simp [LinearMap.smul_apply]

noncomputable def quotientComp {i j l : ℤ} :
    I.QuotientComponent j l →ₗ[k] I.QuotientComponent i j →ₗ[k]
      I.QuotientComponent i l :=
  (I.hom j l).liftQ I.quotientCompPre (by
    intro g hg
    apply LinearMap.ext
    intro x
    obtain ⟨f,rfl⟩ := (I.hom i j).mkQ_surjective x
    change Submodule.Quotient.mk (B.comp g f)=0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (I.comp_right hg f))

@[simp] theorem quotientComp_mk {i j l : ℤ} (f : B.Hom i j) (g : B.Hom j l) :
    I.quotientComp (Submodule.Quotient.mk g) (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (B.comp g f) := rfl

noncomputable def quotient (hdiag : ∀ i, I.hom i i=⊥) : ZAlgebra.{u,v} k where
  Hom := I.QuotientComponent
  id i := Submodule.Quotient.mk (B.id i)
  comp := I.quotientComp
  comp_id := by
    intro i j x
    obtain ⟨f,rfl⟩ := (I.hom i j).mkQ_surjective x
    simp [B.comp_id]
  id_comp := by
    intro i j x
    obtain ⟨f,rfl⟩ := (I.hom i j).mkQ_surjective x
    simp [B.id_comp]
  comp_assoc := by
    intro i j l m x y z
    obtain ⟨f,rfl⟩ := (I.hom i j).mkQ_surjective x
    obtain ⟨g,rfl⟩ := (I.hom j l).mkQ_surjective y
    obtain ⟨h,rfl⟩ := (I.hom l m).mkQ_surjective z
    simp [B.comp_assoc]
  positive := by
    intro i j hij x
    obtain ⟨f,rfl⟩ := (I.hom i j).mkQ_surjective x
    rw [B.positive hij f]
    exact Submodule.Quotient.mk_zero _
  connected := by
    intro i x
    obtain ⟨f,rfl⟩ := (I.hom i i).mkQ_surjective x
    obtain ⟨a,rfl⟩ := B.connected i f
    exact ⟨a,Submodule.Quotient.mk_smul _ _ _⟩
  id_nonzero := by
    intro i h
    have hi := (Submodule.Quotient.mk_eq_zero (I.hom i i)).mp h
    rw [hdiag i] at hi
    exact B.id_nonzero i hi
  finite := by intro i j; infer_instance

noncomputable def quotientMap (hdiag : ∀ i, I.hom i i=⊥) :
    Homomorphism B (I.quotient hdiag) where
  map := fun i j => (I.hom i j).mkQ
  map_id := by intro i; rfl
  map_comp := by intro i j l f g; rfl

theorem quotientMap_surjective (hdiag : ∀ i, I.hom i i=⊥) (i j : ℤ) :
    Function.Surjective ((I.quotientMap hdiag).map i j) := (I.hom i j).mkQ_surjective

theorem quotientMap_kernel (hdiag : ∀ i, I.hom i i=⊥) (i j : ℤ) :
    (I.quotientMap hdiag).kernel.hom i j=I.hom i j := (I.hom i j).ker_mkQ

end ASGinzburg.ZAlgebra.LinearIdeal
