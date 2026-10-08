import ASGinzburg.ResolutionExtBoundaryNaturality

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) {M N : A.RightModule}
  (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
  (hP₄ : IsZero (P.complex.X 4)) (hQ₄ : IsZero (Q.complex.X 4))
  (hP : ∀ n, n<4 → A.rightFiniteProjectiveProperty (P.complex.X n))
  (hQ : ∀ n, n<4 → A.rightFiniteProjectiveProperty (Q.complex.X n))
  (hM : ∀ i n, n<3 → ∀ e : Abelian.Ext.{v} M (A.representable i) n, e=0)
  (hN : ∀ i n, n<3 → ∀ e : Abelian.Ext.{v} N (A.representable i) n, e=0)
  (F : P.complex ⟶ Q.complex)

noncomputable def rightResolutionDualTermMap : ∀ n,
    (A.rightResolutionDualFourTerm Q hQ₄ hQ hN).term n ⟶
      (A.rightResolutionDualFourTerm P hP₄ hP hM).term n
  | 0 => A.rightModuleADualMap (F.f 3)
  | 1 => A.rightModuleADualMap (F.f 2)
  | 2 => A.rightModuleADualMap (F.f 1)
  | 3 => A.rightModuleADualMap (F.f 0)
  | _+4 => 0

theorem rightResolutionDualTermMap_comm (n : ℕ) :
    A.rightResolutionDualTermMap P Q hP₄ hQ₄ hP hQ hM hN F (n+1) ≫
      (A.rightResolutionDualFourTerm P hP₄ hP hM).differential n =
    (A.rightResolutionDualFourTerm Q hQ₄ hQ hN).differential n ≫
      A.rightResolutionDualTermMap P Q hP₄ hQ₄ hP hQ hM hN F n := by
  rcases n with _ | _ | _ | n
  · change A.rightModuleADualFunctor.map (F.f 2).op ≫
      A.rightModuleADualFunctor.map (P.complex.d 3 2).op =
      A.rightModuleADualFunctor.map (Q.complex.d 3 2).op ≫ A.rightModuleADualFunctor.map (F.f 3).op
    rw [← A.rightModuleADualFunctor.map_comp,← A.rightModuleADualFunctor.map_comp,
      ← op_comp,← op_comp,F.comm 3 2]
  · change A.rightModuleADualFunctor.map (F.f 1).op ≫
      A.rightModuleADualFunctor.map (P.complex.d 2 1).op =
      A.rightModuleADualFunctor.map (Q.complex.d 2 1).op ≫ A.rightModuleADualFunctor.map (F.f 2).op
    rw [← A.rightModuleADualFunctor.map_comp,← A.rightModuleADualFunctor.map_comp,
      ← op_comp,← op_comp,F.comm 2 1]
  · change A.rightModuleADualFunctor.map (F.f 0).op ≫
      A.rightModuleADualFunctor.map (P.complex.d 1 0).op =
      A.rightModuleADualFunctor.map (Q.complex.d 1 0).op ≫ A.rightModuleADualFunctor.map (F.f 1).op
    rw [← A.rightModuleADualFunctor.map_comp,← A.rightModuleADualFunctor.map_comp,
      ← op_comp,← op_comp,F.comm 1 0]
  · simp [rightResolutionDualTermMap,ASGinzburg.FourTermProjectiveResolution.differential]

noncomputable def rightResolutionDualComplexMap :
    (A.rightResolutionDualFourTerm Q hQ₄ hQ hN).complex ⟶
      (A.rightResolutionDualFourTerm P hP₄ hP hM).complex :=
  ChainComplex.ofHom _ _ _ _ _ _
    (A.rightResolutionDualTermMap P Q hP₄ hQ₄ hP hQ hM hN F)
    (A.rightResolutionDualTermMap_comm P Q hP₄ hQ₄ hP hQ hM hN F)

theorem rightResolutionDualComplexMap_augmentation (f : M ⟶ N)
    (hπ : F.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f) :
    (A.rightResolutionDualComplexMap P Q hP₄ hQ₄ hP hQ hM hN F).f 0 ≫
      (A.rightResolutionDualFourTerm P hP₄ hP hM).toProjectiveResolution.π.f 0 =
    (A.rightResolutionDualFourTerm Q hQ₄ hQ hN).toProjectiveResolution.π.f 0 ≫
      A.rightModuleExtPrecompLeft f 3 := by
  change A.rightModuleADualMap (F.f 3) ≫ A.rightResolutionExtTopProjection P hP₄ =
    A.rightResolutionExtTopProjection Q hQ₄ ≫ A.rightModuleExtPrecompLeft f 3
  exact A.rightResolutionExtTopProjection_natural P Q hP₄ hQ₄ F f hπ
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) {M N : A.LeftModule}
  (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
  (hP₄ : IsZero (P.complex.X 4)) (hQ₄ : IsZero (Q.complex.X 4))
  (hP : ∀ n, n<4 → A.leftFiniteProjectiveProperty (P.complex.X n))
  (hQ : ∀ n, n<4 → A.leftFiniteProjectiveProperty (Q.complex.X n))
  (hM : ∀ i n, n<3 → ∀ e : Abelian.Ext.{v} M (A.leftRepresentable i) n, e=0)
  (hN : ∀ i n, n<3 → ∀ e : Abelian.Ext.{v} N (A.leftRepresentable i) n, e=0)
  (F : P.complex ⟶ Q.complex)

noncomputable def leftResolutionDualTermMap : ∀ n,
    (A.leftResolutionDualFourTerm Q hQ₄ hQ hN).term n ⟶
      (A.leftResolutionDualFourTerm P hP₄ hP hM).term n
  | 0 => A.leftModuleADualMap (F.f 3)
  | 1 => A.leftModuleADualMap (F.f 2)
  | 2 => A.leftModuleADualMap (F.f 1)
  | 3 => A.leftModuleADualMap (F.f 0)
  | _+4 => 0

theorem leftResolutionDualTermMap_comm (n : ℕ) :
    A.leftResolutionDualTermMap P Q hP₄ hQ₄ hP hQ hM hN F (n+1) ≫
      (A.leftResolutionDualFourTerm P hP₄ hP hM).differential n =
    (A.leftResolutionDualFourTerm Q hQ₄ hQ hN).differential n ≫
      A.leftResolutionDualTermMap P Q hP₄ hQ₄ hP hQ hM hN F n := by
  rcases n with _ | _ | _ | n
  · change A.leftModuleADualFunctor.map (F.f 2).op ≫
      A.leftModuleADualFunctor.map (P.complex.d 3 2).op =
      A.leftModuleADualFunctor.map (Q.complex.d 3 2).op ≫ A.leftModuleADualFunctor.map (F.f 3).op
    rw [← A.leftModuleADualFunctor.map_comp,← A.leftModuleADualFunctor.map_comp,
      ← op_comp,← op_comp,F.comm 3 2]
  · change A.leftModuleADualFunctor.map (F.f 1).op ≫
      A.leftModuleADualFunctor.map (P.complex.d 2 1).op =
      A.leftModuleADualFunctor.map (Q.complex.d 2 1).op ≫ A.leftModuleADualFunctor.map (F.f 2).op
    rw [← A.leftModuleADualFunctor.map_comp,← A.leftModuleADualFunctor.map_comp,
      ← op_comp,← op_comp,F.comm 2 1]
  · change A.leftModuleADualFunctor.map (F.f 0).op ≫
      A.leftModuleADualFunctor.map (P.complex.d 1 0).op =
      A.leftModuleADualFunctor.map (Q.complex.d 1 0).op ≫ A.leftModuleADualFunctor.map (F.f 1).op
    rw [← A.leftModuleADualFunctor.map_comp,← A.leftModuleADualFunctor.map_comp,
      ← op_comp,← op_comp,F.comm 1 0]
  · simp [leftResolutionDualTermMap,ASGinzburg.FourTermProjectiveResolution.differential]

noncomputable def leftResolutionDualComplexMap :
    (A.leftResolutionDualFourTerm Q hQ₄ hQ hN).complex ⟶
      (A.leftResolutionDualFourTerm P hP₄ hP hM).complex :=
  ChainComplex.ofHom _ _ _ _ _ _
    (A.leftResolutionDualTermMap P Q hP₄ hQ₄ hP hQ hM hN F)
    (A.leftResolutionDualTermMap_comm P Q hP₄ hQ₄ hP hQ hM hN F)

theorem leftResolutionDualComplexMap_augmentation (f : M ⟶ N)
    (hπ : F.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f) :
    (A.leftResolutionDualComplexMap P Q hP₄ hQ₄ hP hQ hM hN F).f 0 ≫
      (A.leftResolutionDualFourTerm P hP₄ hP hM).toProjectiveResolution.π.f 0 =
    (A.leftResolutionDualFourTerm Q hQ₄ hQ hN).toProjectiveResolution.π.f 0 ≫
      A.leftModuleExtPrecompRight f 3 := by
  change A.leftModuleADualMap (F.f 3) ≫ A.leftResolutionExtTopProjection P hP₄ =
    A.leftResolutionExtTopProjection Q hQ₄ ≫ A.leftModuleExtPrecompRight f 3
  exact A.leftResolutionExtTopProjection_natural P Q hP₄ hQ₄ F f hπ
end ASGinzburg.ZAlgebra
