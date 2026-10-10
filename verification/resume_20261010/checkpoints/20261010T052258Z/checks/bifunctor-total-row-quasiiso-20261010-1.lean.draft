import work.ASGinzburgDraft.BicomplexTotalRowQuasiIso
import Mathlib.Algebra.Homology.Bifunctor

/-! Degreewise epimorphic quasi-isomorphisms in the second variable induce
quasi-isomorphisms on actual bifunctor totals when the row functors preserve homology. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Category HomologicalComplex HomologicalComplex₂

universe u w u₁ u₂ v₁ v₂
variable {k : Type u} [Ring k]
variable {C₁ : Type u₁} {C₂ : Type u₂} [Category.{v₁} C₁] [Category.{v₂} C₂]
variable [Preadditive C₁] [Abelian C₂]
variable (F : C₁ ⥤ C₂ ⥤ ModuleCat.{w} k) [F.Additive] [∀ X, (F.obj X).Additive]
variable (P : ChainComplex C₁ ℕ) {Q Q' : ChainComplex C₂ ℕ} (f : Q ⟶ Q')
variable [QuasiIso f] [∀ n, Epi (f.f n)]
variable [∀ i, (F.obj (P.X i)).PreservesHomology]
variable [∀ i, (F.obj (P.X i)).PreservesEpimorphisms]

theorem bifunctorTotal_quasiIso_of_row_quasiIso :
    QuasiIso (mapBifunctorMap (𝟙 P) f F (ComplexShape.down ℕ)) := by
  unfold mapBifunctorMap
  apply bicomplexTotal_quasiIso_of_row_quasiIso
  · intro i j
    change Epi ((F.map (𝟙 (P.X i))).app (Q.X j) ≫ (F.obj (P.X i)).map (f.f j))
    simp only [Functor.map_id, NatTrans.id_app, id_comp]
    infer_instance
  · intro i
    have hrow :
        ((((F.mapBifunctorHomologicalComplex (ComplexShape.down ℕ) (ComplexShape.down ℕ)).map
          (𝟙 P)).app Q ≫
          ((F.mapBifunctorHomologicalComplex (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj P).map f).f i) =
          ((F.obj (P.X i)).mapHomologicalComplex (ComplexShape.down ℕ)).map f := by
      ext j
      change (F.map (𝟙 (P.X i))).app (Q.X j) ≫ (F.obj (P.X i)).map (f.f j) = _
      simp only [Functor.map_id, NatTrans.id_app, id_comp]
      rfl
    rw [hrow]
    infer_instance

end ASGinzburg
