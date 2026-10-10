import work.ASGinzburgDraft.OrdinaryModuleRingDualDerived

/-! The genuine right-derived ring-dual comparison intertwines actual
module maps with precomposition on projective-resolution cochains. -/
namespace ASGinzburg
open CategoryTheory Opposite
universe v
variable (R : Type v) [Ring R]

theorem ordinaryProjectiveResolutionOpposite_ι_f_zero {M : ModuleCat.{v} R}
    (P : ProjectiveResolution M) :
    (ordinaryProjectiveResolutionOpposite R P).ι.f 0 = (P.π.f 0).op := by
  simp only [ordinaryProjectiveResolutionOpposite, HomologicalComplex.comp_f,
    ordinarySingleZeroOppositeIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
    HomologicalComplex.opFunctor_map_f, Quiver.Hom.unop_op]
  change 𝟙 (op M) ≫ (P.π.f 0).op = (P.π.f 0).op
  exact Category.id_comp _

theorem ordinaryRingDualResolutionHomologyIso_hom_naturality
    {M N : ModuleCat.{v} R} (f₀ : M ⟶ N)
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (f : P.complex ⟶ Q.complex)
    (hf : f.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f₀) (n : ℕ) :
    (ordinaryRingDualExtFunctor R n).map f₀.op ≫
        (ordinaryRingDualResolutionHomologyIso R P n).hom =
      (ordinaryRingDualResolutionHomologyIso R Q n).hom ≫
        HomologicalComplex.homologyMap
          (((ordinaryRingDualFunctor R).mapHomologicalComplex (ComplexShape.up ℕ)).map
            ((HomologicalComplex.opFunctor (ModuleCat.{v} R) (ComplexShape.down ℕ)).map
              f.op)) n := by
  apply InjectiveResolution.isoRightDerivedObj_hom_naturality f₀.op
    (ordinaryProjectiveResolutionOpposite R Q) (ordinaryProjectiveResolutionOpposite R P)
    ((HomologicalComplex.opFunctor (ModuleCat.{v} R) (ComplexShape.down ℕ)).map f.op)
  rw [ordinaryProjectiveResolutionOpposite_ι_f_zero,
    ordinaryProjectiveResolutionOpposite_ι_f_zero]
  change (Q.π.f 0).op ≫ (f.f 0).op = f₀.op ≫ (P.π.f 0).op
  rw [← op_comp, ← op_comp, hf]

theorem ordinaryRingDualResolutionHomologyIso_inv_naturality
    {M N : ModuleCat.{v} R} (f₀ : M ⟶ N)
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (f : P.complex ⟶ Q.complex)
    (hf : f.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f₀) (n : ℕ) :
    (ordinaryRingDualResolutionHomologyIso R Q n).inv ≫
        (ordinaryRingDualExtFunctor R n).map f₀.op =
      HomologicalComplex.homologyMap
        (((ordinaryRingDualFunctor R).mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((HomologicalComplex.opFunctor (ModuleCat.{v} R) (ComplexShape.down ℕ)).map
            f.op)) n ≫
        (ordinaryRingDualResolutionHomologyIso R P n).inv := by
  rw [← cancel_mono (ordinaryRingDualResolutionHomologyIso R P n).hom,
    Category.assoc, Category.assoc,
    ordinaryRingDualResolutionHomologyIso_hom_naturality R f₀ P Q f hf n,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end ASGinzburg
