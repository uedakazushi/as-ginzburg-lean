import ASGinzburg.GinzburgCutZeroQuotientProducts

/-! Products on actual mathlib H-zero induced by the genuine Ginzburg
cycle product and differential boundaries, without a Jacobian definition. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgCutHomologyZeroComp (φ : Q.Potential k) {u v w : Q.LiftVertex} :
    Q.ginzburgCutHomology k φ v.1 w.1 (w.2-v.2) 0 →ₗ[k]
      Q.ginzburgCutHomology k φ u.1 v.1 (v.2-u.2) 0 →ₗ[k] Q.ginzburgCutHomology k φ u.1 w.1 (w.2-u.2) 0 :=
  ((Q.ginzburgCutZeroQuotientComp k φ).compl₁₂
    (Q.ginzburgCutHomologyZeroQuotientIso k φ v.1 w.1 (w.2-v.2)).hom.hom
    (Q.ginzburgCutHomologyZeroQuotientIso k φ u.1 v.1 (v.2-u.2)).hom.hom).compr₂
      (Q.ginzburgCutHomologyZeroQuotientIso k φ u.1 w.1 (w.2-u.2)).inv.hom

noncomputable def ginzburgCutZeroHomologyClass (φ : Q.Potential k) (u v : Q.LiftVertex) :
    Q.ginzburgCutCohomologicalComponent k u.1 v.1 0 (v.2-u.2) →ₗ[k] Q.ginzburgCutHomology k φ u.1 v.1 (v.2-u.2) 0 :=
  (Q.ginzburgCutHomologyZeroQuotientIso k φ u.1 v.1 (v.2-u.2)).inv.hom.comp
    (LinearMap.range (Q.ginzburgCutNegativeOneDifferential k φ u.1 v.1 (v.2-u.2))).mkQ

@[simp] theorem ginzburgCutHomologyZeroQuotientIso_class (φ : Q.Potential k)
    {u v : Q.LiftVertex} (f : Q.ginzburgCutCohomologicalComponent k u.1 v.1 0 (v.2-u.2)) :
    (Q.ginzburgCutHomologyZeroQuotientIso k φ u.1 v.1 (v.2-u.2)).hom
      (Q.ginzburgCutZeroHomologyClass k φ u v f)=Submodule.Quotient.mk f := by
  change (Q.ginzburgCutHomologyZeroQuotientIso k φ u.1 v.1 (v.2-u.2)).hom
    ((Q.ginzburgCutHomologyZeroQuotientIso k φ u.1 v.1 (v.2-u.2)).inv (Submodule.Quotient.mk f))=_
  simp

theorem ginzburgCutZeroHomologyClass_surjective (φ : Q.Potential k) (u v : Q.LiftVertex) :
    Function.Surjective (Q.ginzburgCutZeroHomologyClass k φ u v) :=
  (ModuleCat.epi_iff_surjective _).mp (inferInstance :
    CategoryTheory.Epi (Q.ginzburgCutHomologyZeroQuotientIso k φ u.1 v.1 (v.2-u.2)).inv) |>.comp
      (LinearMap.range (Q.ginzburgCutNegativeOneDifferential k φ u.1 v.1 (v.2-u.2))).mkQ_surjective

theorem ginzburgCutHomologyZeroComp_class (φ : Q.Potential k) {u v w : Q.LiftVertex}
    (f : Q.ginzburgCutCohomologicalComponent k u.1 v.1 0 (v.2-u.2))
    (g : Q.ginzburgCutCohomologicalComponent k v.1 w.1 0 (w.2-v.2)) :
    Q.ginzburgCutHomologyZeroComp k φ (Q.ginzburgCutZeroHomologyClass k φ v w g)
      (Q.ginzburgCutZeroHomologyClass k φ u v f)=
        Q.ginzburgCutZeroHomologyClass k φ u w (Q.ginzburgCutZeroComp k g f) := by
  simp [ginzburgCutHomologyZeroComp,LinearMap.compl₁₂_apply,LinearMap.compr₂_apply,
    ginzburgCutZeroHomologyClass,LinearMap.comp_apply]

theorem ginzburgCutHomologyZeroQuotientIso_comp (φ : Q.Potential k) {u v w : Q.LiftVertex}
    (f : Q.ginzburgCutHomology k φ u.1 v.1 (v.2-u.2) 0) (g : Q.ginzburgCutHomology k φ v.1 w.1 (w.2-v.2) 0) :
    (Q.ginzburgCutHomologyZeroQuotientIso k φ u.1 w.1 (w.2-u.2)).hom (Q.ginzburgCutHomologyZeroComp k φ g f)=
      Q.ginzburgCutZeroQuotientComp k φ
        ((Q.ginzburgCutHomologyZeroQuotientIso k φ v.1 w.1 (w.2-v.2)).hom g)
        ((Q.ginzburgCutHomologyZeroQuotientIso k φ u.1 v.1 (v.2-u.2)).hom f) := by
  change (Q.ginzburgCutHomologyZeroQuotientIso k φ u.1 w.1 (w.2-u.2)).hom
    ((Q.ginzburgCutHomologyZeroQuotientIso k φ u.1 w.1 (w.2-u.2)).inv _) = _
  simp

end ASGinzburg.CutQuiver
