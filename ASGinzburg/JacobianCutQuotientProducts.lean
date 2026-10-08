import ASGinzburg.BetweenSheetJacobianIdeals

/-! Genuine bilinear products on homogeneous Jacobian quotient
components, indexed by arbitrary endpoint sheets. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def pathCutCompBetweenLinear {u v w : Q.LiftVertex} :
    Q.pathCutComponent k v.1 w.1 (w.2-v.2) →ₗ[k]
      Q.pathCutComponent k u.1 v.1 (v.2-u.2) →ₗ[k]
        Q.pathCutComponent k u.1 w.1 (w.2-u.2) where
  toFun g := ((Q.pathComp k g.val).comp
    (Q.pathCutComponent k u.1 v.1 (v.2-u.2)).subtype).codRestrict
      _ (fun f => (Q.pathCutCompBetween k g f).property)
  map_add' := by
    intro g h
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact LinearMap.congr_fun (map_add (Q.pathComp k) g.val h.val) f.val
  map_smul' := by
    intro a g
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact LinearMap.congr_fun (map_smul (Q.pathComp k) a g.val) f.val

abbrev PathCutJacobianQuotient (φ : Q.Potential k) (u v : Q.LiftVertex) :=
  Q.pathCutComponent k u.1 v.1 (v.2-u.2) ⧸
    Q.pathJacobianCutIdeal k φ u.1 v.1 (v.2-u.2)

noncomputable def cutJacobianQuotientCompRight (φ : Q.Potential k) {u v w : Q.LiftVertex}
    (g : Q.pathCutComponent k v.1 w.1 (w.2-v.2)) :
    Q.PathCutJacobianQuotient k φ u v →ₗ[k] Q.PathCutJacobianQuotient k φ u w :=
  (Q.pathJacobianCutIdeal k φ u.1 v.1 (v.2-u.2)).liftQ
    ((Q.pathJacobianCutIdeal k φ u.1 w.1 (w.2-u.2)).mkQ.comp
      (Q.pathCutCompBetweenLinear k g)) (by
        intro f hf
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        change Q.pathComp k g.val f.val ∈ (Q.pathJacobianIdeal k φ).hom u.1 w.1
        exact (Q.pathJacobianIdeal k φ).comp_left hf g.val)

@[simp] theorem cutJacobianQuotientCompRight_mk (φ : Q.Potential k) {u v w : Q.LiftVertex}
    (g : Q.pathCutComponent k v.1 w.1 (w.2-v.2))
    (f : Q.pathCutComponent k u.1 v.1 (v.2-u.2)) :
    Q.cutJacobianQuotientCompRight k φ g (Submodule.Quotient.mk f)=
      Submodule.Quotient.mk (Q.pathCutCompBetweenLinear k g f) := rfl

noncomputable def cutJacobianQuotientCompPre (φ : Q.Potential k) {u v w : Q.LiftVertex} :
    Q.pathCutComponent k v.1 w.1 (w.2-v.2) →ₗ[k]
      Q.PathCutJacobianQuotient k φ u v →ₗ[k] Q.PathCutJacobianQuotient k φ u w where
  toFun := Q.cutJacobianQuotientCompRight k φ
  map_add' := by
    intro g h
    apply LinearMap.ext
    intro x
    obtain ⟨f,rfl⟩ := (Q.pathJacobianCutIdeal k φ u.1 v.1 (v.2-u.2)).mkQ_surjective x
    simp [LinearMap.add_apply]
  map_smul' := by
    intro a g
    apply LinearMap.ext
    intro x
    obtain ⟨f,rfl⟩ := (Q.pathJacobianCutIdeal k φ u.1 v.1 (v.2-u.2)).mkQ_surjective x
    simp [LinearMap.smul_apply]

noncomputable def cutJacobianQuotientComp (φ : Q.Potential k) {u v w : Q.LiftVertex} :
    Q.PathCutJacobianQuotient k φ v w →ₗ[k]
      Q.PathCutJacobianQuotient k φ u v →ₗ[k] Q.PathCutJacobianQuotient k φ u w :=
  (Q.pathJacobianCutIdeal k φ v.1 w.1 (w.2-v.2)).liftQ
    (Q.cutJacobianQuotientCompPre k φ) (by
      intro g hg
      apply LinearMap.ext
      intro x
      obtain ⟨f,rfl⟩ := (Q.pathJacobianCutIdeal k φ u.1 v.1 (v.2-u.2)).mkQ_surjective x
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      change Q.pathComp k g.val f.val ∈ (Q.pathJacobianIdeal k φ).hom u.1 w.1
      exact (Q.pathJacobianIdeal k φ).comp_right hg f.val)

@[simp] theorem cutJacobianQuotientComp_mk (φ : Q.Potential k) {u v w : Q.LiftVertex}
    (g : Q.pathCutComponent k v.1 w.1 (w.2-v.2))
    (f : Q.pathCutComponent k u.1 v.1 (v.2-u.2)) :
    Q.cutJacobianQuotientComp k φ (Submodule.Quotient.mk g) (Submodule.Quotient.mk f)=
      Submodule.Quotient.mk (Q.pathCutCompBetweenLinear k g f) := rfl

end ASGinzburg.CutQuiver
