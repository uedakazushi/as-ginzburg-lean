import ASGinzburg.ProjectiveResolutionSyzygies

namespace CategoryTheory.ProjectiveResolution
open CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] {M N : C}
  (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
  (F : P.complex ⟶ Q.complex) (f : M ⟶ N)
  (hπ : F.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f)

noncomputable def firstKernelMap : kernel (P.π.f 0) ⟶ kernel (Q.π.f 0) :=
  kernel.map (P.π.f 0) (Q.π.f 0) (F.f 0) f hπ.symm

@[reassoc] theorem firstKernelMap_ι :
    P.firstKernelMap Q F f hπ ≫ kernel.ι (Q.π.f 0) = kernel.ι (P.π.f 0) ≫ F.f 0 :=
  kernel.lift_ι _ _ _

@[reassoc] theorem firstCover_firstKernelMap :
    P.firstCover ≫ P.firstKernelMap Q F f hπ = F.f 1 ≫ Q.firstCover := by
  apply (cancel_mono (kernel.ι (Q.π.f 0))).mp
  rw [Category.assoc,P.firstKernelMap_ι,← Category.assoc,P.firstCover_ι,
    Category.assoc,Q.firstCover_ι]
  exact (F.comm 1 0).symm

noncomputable def secondKernelMap : kernel P.firstCover ⟶ kernel Q.firstCover :=
  kernel.map P.firstCover Q.firstCover (F.f 1) (P.firstKernelMap Q F f hπ)
    (P.firstCover_firstKernelMap Q F f hπ)

@[reassoc] theorem secondKernelMap_ι :
    P.secondKernelMap Q F f hπ ≫ kernel.ι Q.firstCover = kernel.ι P.firstCover ≫ F.f 1 :=
  kernel.lift_ι _ _ _

@[reassoc] theorem secondCover_secondKernelMap :
    P.secondCover ≫ P.secondKernelMap Q F f hπ = F.f 2 ≫ Q.secondCover := by
  apply (cancel_mono (kernel.ι Q.firstCover)).mp
  rw [Category.assoc,P.secondKernelMap_ι,← Category.assoc,P.secondCover_ι,
    Category.assoc,Q.secondCover_ι]
  exact (F.comm 2 1).symm

noncomputable def shortExact₀Hom :
    ShortComplex.mk (kernel.ι (P.π.f 0)) (P.π.f 0) (kernel.condition _) ⟶
      ShortComplex.mk (kernel.ι (Q.π.f 0)) (Q.π.f 0) (kernel.condition _) where
  τ₁ := P.firstKernelMap Q F f hπ
  τ₂ := F.f 0
  τ₃ := f
  comm₁₂ := P.firstKernelMap_ι Q F f hπ
  comm₂₃ := hπ

noncomputable def shortExact₁Hom :
    ShortComplex.mk (kernel.ι P.firstCover) P.firstCover (kernel.condition _) ⟶
      ShortComplex.mk (kernel.ι Q.firstCover) Q.firstCover (kernel.condition _) where
  τ₁ := P.secondKernelMap Q F f hπ
  τ₂ := F.f 1
  τ₃ := P.firstKernelMap Q F f hπ
  comm₁₂ := P.secondKernelMap_ι Q F f hπ
  comm₂₃ := (P.firstCover_firstKernelMap Q F f hπ).symm

noncomputable def shortExact₂Hom :
    ShortComplex.mk (P.complex.d 3 2) P.secondCover P.d₃_secondCover ⟶
      ShortComplex.mk (Q.complex.d 3 2) Q.secondCover Q.d₃_secondCover where
  τ₁ := F.f 3
  τ₂ := F.f 2
  τ₃ := P.secondKernelMap Q F f hπ
  comm₁₂ := F.comm 3 2
  comm₂₃ := (P.secondCover_secondKernelMap Q F f hπ).symm
end CategoryTheory.ProjectiveResolution
