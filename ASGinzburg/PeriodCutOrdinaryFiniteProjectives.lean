import ASGinzburg.PeriodCutOrdinaryProjectives
import ASGinzburg.PeriodCutFiniteProjectives

/-! Genuine finite sums and retracts of cover representables become
ordinary projective right R modules. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem cornerFiniteRepresentableSum_ring_projective (n : ℕ) (i : Fin n→ℤ) :
    Projective ((E.cornerModuleRingFunctor Q).obj
      (∐ fun j : Fin n => (E.cornerCoverZAlgebra Q).representable (i j))) := by
  letI : ∀ j : Fin n,Projective ((E.cornerModuleRingFunctor Q).obj
      ((E.cornerCoverZAlgebra Q).representable (i j))) :=
    fun j => E.cornerRepresentable_ring_projective Q (i j)
  let e := PreservesCoproduct.iso (E.cornerModuleRingFunctor Q)
    (fun j : Fin n => (E.cornerCoverZAlgebra Q).representable (i j))
  exact Projective.of_iso e.symm (ASGinzburg.coproduct_projective
    (fun j : Fin n => (E.cornerModuleRingFunctor Q).obj
      ((E.cornerCoverZAlgebra Q).representable (i j))))

theorem cornerFiniteProjective_ring_projective {P : (E.cornerCoverZAlgebra Q).RightModule}
    (hP : (E.cornerCoverZAlgebra Q).rightFiniteProjectiveProperty P) :
    Projective ((E.cornerModuleRingFunctor Q).obj P) := by
  obtain ⟨n,i,⟨r⟩⟩ := hP
  let F := E.cornerModuleRingFunctor Q
  letI := E.cornerFiniteRepresentableSum_ring_projective Q n i
  exact ASGinzburg.projective_of_retract (r.map F)

end ASGinzburg.ZAlgebra.PeriodIso
