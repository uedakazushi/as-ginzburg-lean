import ASGinzburg.PathLinearIdeals

/-! Actual bilinear products on quotient path components of arbitrary
genuine two-sided path ideals. -/
namespace ASGinzburg.CutQuiver.PathLinearIdeal
universe u
variable {k : Type u} [Field k] {Q : CutQuiver} (I : Q.PathLinearIdeal k)

abbrev QuotientComponent (i j : Q.Vertex) := Q.PathComponent k i j ⧸ I.hom i j

noncomputable def quotientCompRight {i j l : Q.Vertex} (g : Q.PathComponent k j l) :
    I.QuotientComponent i j →ₗ[k] I.QuotientComponent i l :=
  (I.hom i j).liftQ (((I.hom i l).mkQ).comp (Q.pathComp k g)) (by
    intro f hf
    change (I.hom i l).mkQ (Q.pathComp k g f)=0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (I.comp_left hf g))

@[simp] theorem quotientCompRight_mk {i j l : Q.Vertex} (g : Q.PathComponent k j l) (f : Q.PathComponent k i j) :
    I.quotientCompRight g (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (Q.pathComp k g f) := rfl

noncomputable def quotientCompPre {i j l : Q.Vertex} :
    Q.PathComponent k j l →ₗ[k] I.QuotientComponent i j →ₗ[k] I.QuotientComponent i l where
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

noncomputable def quotientComp {i j l : Q.Vertex} :
    I.QuotientComponent j l →ₗ[k] I.QuotientComponent i j →ₗ[k]
      I.QuotientComponent i l :=
  (I.hom j l).liftQ I.quotientCompPre (by
    intro g hg
    apply LinearMap.ext
    intro x
    obtain ⟨f,rfl⟩ := (I.hom i j).mkQ_surjective x
    change Submodule.Quotient.mk (Q.pathComp k g f)=0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (I.comp_right hg f))

@[simp] theorem quotientComp_mk {i j l : Q.Vertex} (f : Q.PathComponent k i j) (g : Q.PathComponent k j l) :
    I.quotientComp (Submodule.Quotient.mk g) (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (Q.pathComp k g f) := rfl

theorem quotientComp_id {u v : Q.Vertex} (x : I.QuotientComponent u v) :
    I.quotientComp (Submodule.Quotient.mk (Q.pathId k v)) x=x := by
  obtain ⟨f,rfl⟩ := (I.hom u v).mkQ_surjective x
  simp [Q.pathComp_id]

theorem id_quotientComp {u v : Q.Vertex} (x : I.QuotientComponent u v) :
    I.quotientComp x (Submodule.Quotient.mk (Q.pathId k u))=x := by
  obtain ⟨f,rfl⟩ := (I.hom u v).mkQ_surjective x
  simp [Q.id_pathComp]

theorem quotientComp_assoc {u v w x : Q.Vertex}
    (f : I.QuotientComponent u v) (g : I.QuotientComponent v w)
    (h : I.QuotientComponent w x) :
    I.quotientComp h (I.quotientComp g f)=I.quotientComp (I.quotientComp h g) f := by
  obtain ⟨f,rfl⟩ := (I.hom u v).mkQ_surjective f
  obtain ⟨g,rfl⟩ := (I.hom v w).mkQ_surjective g
  obtain ⟨h,rfl⟩ := (I.hom w x).mkQ_surjective h
  simp [Q.pathComp_assoc]

end ASGinzburg.CutQuiver.PathLinearIdeal
