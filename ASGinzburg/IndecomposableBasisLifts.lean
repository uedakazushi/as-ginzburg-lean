import ASGinzburg.ASGeneratorBasis

/-! Every actual basis of Hom modulo positive products has chosen
algebra-element lifts, and those lifts give the required decomposition. -/
namespace ASGinzburg.ZAlgebra
universe u v w
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def indecomposableBasisLift (i j : ℤ) {ι : Type w}
    (b : Module.Basis ι k (A.Hom i j ⧸ Submodule.span k (A.products i j)))
    (a : ι) : A.Hom i j :=
  Classical.choose ((Submodule.span k (A.products i j)).mkQ_surjective (b a))

theorem indecomposableBasisLift_mkQ (i j : ℤ) {ι : Type w}
    (b : Module.Basis ι k (A.Hom i j ⧸ Submodule.span k (A.products i j)))
    (a : ι) :
    (Submodule.span k (A.products i j)).mkQ (A.indecomposableBasisLift i j b a)=b a :=
  Classical.choose_spec ((Submodule.span k (A.products i j)).mkQ_surjective (b a))

theorem indecomposableBasisLift_decomposition (i j : ℤ) {ι : Type w}
    (b : Module.Basis ι k (A.Hom i j ⧸ Submodule.span k (A.products i j))) :
    Submodule.span k (Set.range (A.indecomposableBasisLift i j b)) ⊔
      Submodule.span k (A.products i j)=⊤ := by
  let p := Submodule.span k (A.products i j)
  have hm : Submodule.map p.mkQ
      (Submodule.span k (Set.range (A.indecomposableBasisLift i j b)))=⊤ := by
    rw [Submodule.map_span,←Set.range_comp]
    have hf : p.mkQ ∘ A.indecomposableBasisLift i j b=b := by
      funext a
      exact A.indecomposableBasisLift_mkQ i j b a
    rw [hf]
    exact b.span_eq
  have hs := (p.map_mkQ_eq_top _).mp hm
  simpa only [sup_comm] using hs

end ASGinzburg.ZAlgebra
