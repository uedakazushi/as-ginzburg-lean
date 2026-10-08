import ASGinzburg.GinzburgZeroQuotientProducts

/-! Products on actual mathlib H-zero induced by the genuine Ginzburg
cycle product and differential boundaries, without a Jacobian definition. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgHomologyZeroComp (φ : Q.Potential k) {u v w : Q.Vertex} :
    Q.ginzburgHomology k φ v w 0 →ₗ[k]
      Q.ginzburgHomology k φ u v 0 →ₗ[k] Q.ginzburgHomology k φ u w 0 :=
  ((Q.ginzburgZeroQuotientComp k φ).compl₁₂
    (Q.ginzburgHomologyZeroQuotientIso k φ v w).hom.hom
    (Q.ginzburgHomologyZeroQuotientIso k φ u v).hom.hom).compr₂
      (Q.ginzburgHomologyZeroQuotientIso k φ u w).inv.hom

noncomputable def ginzburgZeroHomologyClass (φ : Q.Potential k) (u v : Q.Vertex) :
    Q.ginzburgCohomologicalComponent k u v 0 →ₗ[k] Q.ginzburgHomology k φ u v 0 :=
  (Q.ginzburgHomologyZeroQuotientIso k φ u v).inv.hom.comp
    (LinearMap.range (Q.ginzburgNegativeOneDifferential k φ u v)).mkQ

@[simp] theorem ginzburgHomologyZeroQuotientIso_class (φ : Q.Potential k)
    {u v : Q.Vertex} (f : Q.ginzburgCohomologicalComponent k u v 0) :
    (Q.ginzburgHomologyZeroQuotientIso k φ u v).hom
      (Q.ginzburgZeroHomologyClass k φ u v f)=Submodule.Quotient.mk f := by
  change (Q.ginzburgHomologyZeroQuotientIso k φ u v).hom
    ((Q.ginzburgHomologyZeroQuotientIso k φ u v).inv (Submodule.Quotient.mk f))=_
  simp

theorem ginzburgZeroHomologyClass_surjective (φ : Q.Potential k) (u v : Q.Vertex) :
    Function.Surjective (Q.ginzburgZeroHomologyClass k φ u v) :=
  (ModuleCat.epi_iff_surjective _).mp (inferInstance :
    CategoryTheory.Epi (Q.ginzburgHomologyZeroQuotientIso k φ u v).inv) |>.comp
      (LinearMap.range (Q.ginzburgNegativeOneDifferential k φ u v)).mkQ_surjective

theorem ginzburgHomologyZeroComp_class (φ : Q.Potential k) {u v w : Q.Vertex}
    (f : Q.ginzburgCohomologicalComponent k u v 0)
    (g : Q.ginzburgCohomologicalComponent k v w 0) :
    Q.ginzburgHomologyZeroComp k φ (Q.ginzburgZeroHomologyClass k φ v w g)
      (Q.ginzburgZeroHomologyClass k φ u v f)=
        Q.ginzburgZeroHomologyClass k φ u w (Q.ginzburgZeroComp k g f) := by
  simp [ginzburgHomologyZeroComp,LinearMap.compl₁₂_apply,LinearMap.compr₂_apply,
    ginzburgZeroHomologyClass,LinearMap.comp_apply]

theorem ginzburgHomologyZeroQuotientIso_comp (φ : Q.Potential k) {u v w : Q.Vertex}
    (f : Q.ginzburgHomology k φ u v 0) (g : Q.ginzburgHomology k φ v w 0) :
    (Q.ginzburgHomologyZeroQuotientIso k φ u w).hom (Q.ginzburgHomologyZeroComp k φ g f)=
      Q.ginzburgZeroQuotientComp k φ
        ((Q.ginzburgHomologyZeroQuotientIso k φ v w).hom g)
        ((Q.ginzburgHomologyZeroQuotientIso k φ u v).hom f) := by
  change (Q.ginzburgHomologyZeroQuotientIso k φ u w).hom
    ((Q.ginzburgHomologyZeroQuotientIso k φ u w).inv _) = _
  simp

end ASGinzburg.CutQuiver
