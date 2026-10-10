import ASGinzburg.ZAlgebraHomomorphisms

/-! The product of genuine two-sided linear ideals is again a two-sided
linear ideal, using the span of actual composable products. -/
namespace ASGinzburg.ZAlgebra.LinearIdeal
universe u v
variable {k : Type u} [Field k] {B : ZAlgebra.{u,v} k}

def productGenerators (I J : B.LinearIdeal) (i l : ℤ) : Set (B.Hom i l) :=
  {x | ∃ j, ∃ f ∈ I.hom i j, ∃ g ∈ J.hom j l, B.comp g f = x}

def mul (I J : B.LinearIdeal) : B.LinearIdeal where
  hom i l := Submodule.span k (productGenerators I J i l)
  comp_left := by
    intro i l m f hf g
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j,f,hf,h,hh,rfl⟩ := hx
      apply Submodule.subset_span
      exact ⟨j,f,hf,B.comp g h,J.comp_left hh g,(B.comp_assoc f h g).symm⟩
    | zero => simp
    | add x y hx hy ihx ihy =>
      simpa only [map_add] using Submodule.add_mem _ ihx ihy
    | smul a x hx ih =>
      simpa only [map_smul] using Submodule.smul_mem _ a ih
  comp_right := by
    intro i j l g hg f
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m,h,hh,g,hg,rfl⟩ := hx
      apply Submodule.subset_span
      exact ⟨m,B.comp h f,I.comp_right hh f,g,hg,B.comp_assoc f h g⟩
    | zero => simp
    | add x y hx hy ihx ihy =>
      simpa only [map_add,LinearMap.add_apply] using Submodule.add_mem _ ihx ihy
    | smul a x hx ih =>
      simpa only [map_smul,LinearMap.smul_apply] using Submodule.smul_mem _ a ih

theorem comp_mem_mul (I J : B.LinearIdeal) {i j l : ℤ}
    {f : B.Hom i j} (hf : f ∈ I.hom i j)
    {g : B.Hom j l} (hg : g ∈ J.hom j l) : B.comp g f ∈ (I.mul J).hom i l :=
  Submodule.subset_span ⟨j,f,hf,g,hg,rfl⟩

end ASGinzburg.ZAlgebra.LinearIdeal
