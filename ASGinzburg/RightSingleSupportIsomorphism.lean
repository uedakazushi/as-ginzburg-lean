import ASGinzburg.FiniteProjectivePresentations

namespace ASGinzburg.ZAlgebra
open CategoryTheory Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def rightSingleSupportComponentIso (i : ℤ) (M N : A.RightModule)
    (hM : ∀ j, j ≠ i → Limits.IsZero ((A.rightModuleEvaluation j).obj M))
    (hN : ∀ j, j ≠ i → Limits.IsZero ((A.rightModuleEvaluation j).obj N))
    (e : (A.rightModuleEvaluation i).obj M ≅ (A.rightModuleEvaluation i).obj N) :
    ∀ X : A.Objᵒᵖ, M.obj.obj X ≅ N.obj.obj X := by
  intro X
  cases X using Opposite.rec
  rename_i X
  rcases X with ⟨j⟩
  by_cases h : j=i
  · subst j; exact e
  · exact (hM j h).iso (hN j h)

noncomputable def rightSingleSupportIso (i : ℤ) (M N : A.RightModule)
    (hM : ∀ j, j ≠ i → Limits.IsZero ((A.rightModuleEvaluation j).obj M))
    (hN : ∀ j, j ≠ i → Limits.IsZero ((A.rightModuleEvaluation j).obj N))
    (e : (A.rightModuleEvaluation i).obj M ≅ (A.rightModuleEvaluation i).obj N) : M ≅ N := by
  letI : M.obj.Linear k := M.property.2
  letI : N.obj.Linear k := N.property.2
  apply A.rightModuleProperty.isoMk
  refine NatIso.ofComponents (F := M.obj) (G := N.obj) (A.rightSingleSupportComponentIso i M N hM hN e) ?_
  intro X Y f
  cases X using Opposite.rec
  cases Y using Opposite.rec
  rename_i X Y
  rcases X with ⟨j⟩
  rcases Y with ⟨l⟩
  by_cases hj : j=i
  · by_cases hl : l=i
    · subst j; subst l
      obtain ⟨r,hr⟩ := (A.scalarEndEquiv i).surjective f.unop
      have hf : f = r • 𝟙 (op (⟨i⟩ : A.Obj)) := by
        apply Quiver.Hom.unop_inj
        change f.unop = r • A.id i
        exact hr.symm
      rw [hf,M.obj.map_smul,N.obj.map_smul,M.obj.map_id,N.obj.map_id]
      simp
    · exact (hN l hl).eq_of_tgt _ _
  · exact (hM j hj).eq_of_src _ _
end ASGinzburg.ZAlgebra
