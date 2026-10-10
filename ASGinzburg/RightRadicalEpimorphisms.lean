import ASGinzburg.RightModuleRadical

/-! Epimorphisms of the unchanged linear right modules map the actual
positive-action radical onto the actual target radical. This is needed
to recover minimal relations from an AS second-cover map. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem positiveActionSpan_map_of_epi {M N : A.RightModule} (f : M ⟶ N) [Epi f]
    (i : ℤ) :
    Submodule.map ((A.rightModuleEvaluation i).map f).hom (A.positiveActionSpan M i)=
      A.positiveActionSpan N i := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact A.positiveActionSpan_map_mem f i hx
  · apply Submodule.span_le.mpr
    rintro _ ⟨l,hil,z,a,rfl⟩
    obtain ⟨y,hy⟩ := (A.rightModule_epi_iff_surjective f).mp (by infer_instance) l z
    refine ⟨M.obj.map (show (⟨i⟩ : A.Obj) ⟶ ⟨l⟩ from a).op y,
      Submodule.subset_span ⟨l,hil,y,a,rfl⟩,?_⟩
    have h := congrArg (fun t => t.hom y)
      (f.hom.naturality (show (⟨i⟩ : A.Obj) ⟶ ⟨l⟩ from a).op)
    change f.hom.app (op ⟨i⟩)
      (M.obj.map (show (⟨i⟩ : A.Obj) ⟶ ⟨l⟩ from a).op y)=_
    change f.hom.app (op ⟨i⟩)
      (M.obj.map (show (⟨i⟩ : A.Obj) ⟶ ⟨l⟩ from a).op y)=
        N.obj.map (show (⟨i⟩ : A.Obj) ⟶ ⟨l⟩ from a).op (f.hom.app (op ⟨l⟩) y) at h
    change f.hom.app (op ⟨l⟩) y=z at hy
    rw [hy] at h
    exact h

end ASGinzburg.ZAlgebra
