import ASGinzburg.PeriodCutHomogeneousIdeals
import Mathlib.RingTheory.Jacobson.Ideal

/-! Maximal homogeneous left ideals are exactly the ordinary maximal
left ideals containing the positive-degree ideal. This is proved using
the actual degree-zero projection and nonnegative grading. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

def CutMaximalHomogeneousLeftIdeal
    (I : Ideal (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))) : Prop :=
  E.CutHomogeneousLeftIdeal Q I ∧ I≠⊤ ∧
    ∀ J : Ideal (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ))),
      E.CutHomogeneousLeftIdeal Q J → I < J → J=⊤

theorem cutMaximalHomogeneous_positive_le
    (I : Ideal (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ))))
    (hI : E.CutMaximalHomogeneousLeftIdeal Q I) : E.cutPositiveIdeal Q≤I := by
  by_cases h : I⊔E.cutPositiveIdeal Q=I
  · exact h ▸ (le_sup_right : E.cutPositiveIdeal Q≤I⊔E.cutPositiveIdeal Q)
  · have ht := hI.2.2 (I⊔E.cutPositiveIdeal Q)
      (E.cutHomogeneousLeftIdeal_sup Q _ _ hI.1 (E.cutPositiveIdeal_homogeneous Q))
      (lt_of_le_of_ne le_sup_left (Ne.symm h))
    exact (E.cutHomogeneous_sup_positive_ne_top Q I hI.1 hI.2.1 ht).elim

theorem cutMaximalHomogeneous_isMaximal
    (I : Ideal (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ))))
    (hI : E.CutMaximalHomogeneousLeftIdeal Q I) : I.IsMaximal := by
  apply Ideal.isMaximal_def.mpr
  refine ⟨hI.2.1,?_⟩
  intro J hIJ
  exact hI.2.2 J (E.cutHomogeneousLeftIdeal_of_positive_le Q J
    ((E.cutMaximalHomogeneous_positive_le Q I hI).trans hIJ.le)) hIJ

theorem cutMaximalHomogeneous_iff
    (I : Ideal (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))) :
    E.CutMaximalHomogeneousLeftIdeal Q I ↔ E.cutPositiveIdeal Q≤I ∧ I.IsMaximal := by
  constructor
  · intro hI
    exact ⟨E.cutMaximalHomogeneous_positive_le Q I hI,E.cutMaximalHomogeneous_isMaximal Q I hI⟩
  · rintro ⟨hPI,hM⟩
    have h := Ideal.isMaximal_def.mp hM
    exact ⟨E.cutHomogeneousLeftIdeal_of_positive_le Q I hPI,h.1,fun J hJ hIJ => h.2 J hIJ⟩

noncomputable def cutGradedJacobson : Ideal (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ))) :=
  sInf {I | E.CutMaximalHomogeneousLeftIdeal Q I}

theorem cutGradedJacobson_eq_positive_jacobson :
    E.cutGradedJacobson Q=(E.cutPositiveIdeal Q).jacobson := by
  unfold cutGradedJacobson Ideal.jacobson
  congr 1
  ext I
  exact E.cutMaximalHomogeneous_iff Q I

end ASGinzburg.ZAlgebra.PeriodIso
