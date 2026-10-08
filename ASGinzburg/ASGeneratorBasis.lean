import ASGinzburg.ASGeneratorDimensions
import ASGinzburg.PeriodInverse
import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-! The actual coefficients of d₁ give a basis of each positive-degree
indecomposable component, rather than only a numerical equality. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {Q : CutQuiver}
namespace ASResolution
variable {w : Q.LiftVertex} (R : A.ASResolution Q w)

abbrev GeneratorIndex (i : ℤ) := {a : Q.incomingArrows w // Q.height (Q.incomingSource w a) = i}

noncomputable def incomingGenerator (i : ℤ) (a : GeneratorIndex (Q := Q) (w := w) i) :
    A.Hom i (Q.height w) :=
  A.homTransport _ _ i (Q.height w) a.property rfl (R.incomingElement a.val)

noncomputable def indecomposableGenerator (i : ℤ) (a : GeneratorIndex (Q := Q) (w := w) i) :
    A.Hom i (Q.height w) ⧸ Submodule.span k (A.products i (Q.height w)) :=
  Submodule.Quotient.mk (R.incomingGenerator i a)

theorem incomingMultiplication_diagonal_span (i : ℤ) (a : Q.incomingArrows w)
    (ha : Q.height (Q.incomingSource w a) = i) (x : A.Hom i (Q.height (Q.incomingSource w a))) :
    Submodule.Quotient.mk (A.comp (R.incomingElement a) x) ∈
      Submodule.span k (Set.range (R.indecomposableGenerator i)) := by
  subst i
  obtain ⟨c,rfl⟩ := A.connected (Q.height (Q.incomingSource w a)) x
  change (Submodule.span k (A.products _ (Q.height w))).mkQ
    (A.comp (R.incomingElement a) (c • A.id _)) ∈ _
  rw [map_smul,A.id_comp,map_smul]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨⟨a,rfl⟩,rfl⟩

include R in
theorem indecomposableGenerator_span (i : ℤ) (hi : i < Q.height w) :
    Submodule.span k (Set.range (R.indecomposableGenerator i)) = ⊤ := by
  apply top_unique
  intro y hy
  clear hy
  obtain ⟨y,rfl⟩ := (Submodule.span k (A.products i (Q.height w))).mkQ_surjective y
  obtain ⟨x,rfl⟩ := R.incomingMultiplication_surjective i hi y
  induction x using DirectSum.induction_on with
  | zero => simpa only [map_zero,Submodule.Quotient.mk_zero] using
      (Submodule.span k (Set.range (R.indecomposableGenerator i))).zero_mem
  | add x y hx hy =>
    change (Submodule.span k (A.products i (Q.height w))).mkQ
      (R.incomingMultiplication i (x+y)) ∈ _
    simpa only [map_add] using
      (Submodule.span k (Set.range (R.indecomposableGenerator i))).add_mem hx hy
  | of a x =>
    change Submodule.Quotient.mk (R.incomingMultiplication i (DirectSum.lof k (Q.incomingArrows w)
      (fun a => A.Hom i (Q.height (Q.incomingSource w a))) a x)) ∈ _
    simp only [incomingMultiplication,DirectSum.toModule_lof]
    rcases lt_trichotomy (Q.height (Q.incomingSource w a)) i with hlt | heq | hlt
    · rw [A.positive hlt x]
      simp
    · exact R.incomingMultiplication_diagonal_span i a heq x
    · have hmem : A.comp (R.incomingElement a) x ∈ Submodule.span k (A.products i (Q.height w)) :=
        Submodule.subset_span ⟨Q.height (Q.incomingSource w a),hlt,Q.incomingSource_height_lt w a,
          x,R.incomingElement a,rfl⟩
      have hz : (Submodule.Quotient.mk (A.comp (R.incomingElement a) x) :
          A.Hom i (Q.height w) ⧸ Submodule.span k (A.products i (Q.height w))) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr hmem
      rw [hz]
      exact Submodule.zero_mem _

noncomputable def indecomposableGeneratorBasis (i : ℤ) (hi : i < Q.height w) :
    Module.Basis (GeneratorIndex (Q := Q) (w := w) i) k
      (A.Hom i (Q.height w) ⧸ Submodule.span k (A.products i (Q.height w))) := by
  classical
  exact basisOfTopLeSpanOfCardEqFinrank (R.indecomposableGenerator i)
    (R.indecomposableGenerator_span i hi).ge
    (R.indecomposables_finrank i hi).symm

theorem indecomposableGeneratorBasis_apply (i : ℤ) (hi : i < Q.height w)
    (a : GeneratorIndex (Q := Q) (w := w) i) :
    R.indecomposableGeneratorBasis i hi a = R.indecomposableGenerator i a := by
  classical
  simp [indecomposableGeneratorBasis]

theorem incomingGenerator_decomposition (i : ℤ) (hi : i < Q.height w) :
    Submodule.span k (Set.range (R.incomingGenerator i)) ⊔
      Submodule.span k (A.products i (Q.height w)) = ⊤ := by
  let p := Submodule.span k (A.products i (Q.height w))
  have hm : Submodule.map p.mkQ (Submodule.span k (Set.range (R.incomingGenerator i))) = ⊤ := by
    rw [Submodule.map_span]
    change Submodule.span k (p.mkQ '' Set.range (R.incomingGenerator i)) = ⊤
    rw [← Set.range_comp]
    exact R.indecomposableGenerator_span i hi
  have h := (p.map_mkQ_eq_top (Submodule.span k (Set.range (R.incomingGenerator i)))).mp hm
  simpa only [sup_comm] using h

end ASResolution
end ASGinzburg.ZAlgebra
