import work.ASGinzburgDraft.PeriodCutGradedTensorNakayama
import ASGinzburg.BalancedTensorTorMinimalResolution
import ASGinzburg.FourTermProjectiveDimension

/-! A native bounded-below graded resolution term is detected by actual
Tor against the radical quotient. The criterion uses a genuine ordinary
projective resolution and an actual identification of its term grading. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem cutGradedJacobson_quotient_annihilated
    (r : E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))
    (hr : r ∈ E.cutGradedJacobson Q)
    (x : E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)) ⧸ E.cutGradedJacobson Q) :
    r • x = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk (E.cutGradedJacobson Q) (r*a) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ((E.cutGradedJacobson Q).mul_mem_right a hr)

set_option maxHeartbeats 600000 in
theorem cutMinimalProjectiveResolution_term_isZero_of_tor
    (M : ModuleCat.{v} (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))ᵐᵒᵖ)
    (P : ProjectiveResolution M) (n : ℕ)
    (T : E.CutGradedRightModule Q) (e : P.complex.X n ≅ T.ringModule)
    (b : ℤ) (hb : ∀ q : ℤ, q < b → T.grade q = ⊥)
    (hP : ∀ i j, ∀ x : P.complex.X i, P.complex.d i j x ∈ Submodule.span k
      {a : P.complex.X j | ∃ r ∈ (E.cutGradedJacobson Q : Set (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))),
        ∃ m : P.complex.X j, MulOpposite.op r • m = a})
    (hTor : IsZero ((balancedTensorTorLeftFunctor.{u,v,v,v} k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)) ⧸ E.cutGradedJacobson Q) n).obj M)) :
    IsZero (P.complex.X n) := by
  have hTensor := (balancedTensorTorMinimalResolution_isZero_iff.{u,v,v,v} k
    (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))
    (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)) ⧸ E.cutGradedJacobson Q)
    M P (E.cutGradedJacobson Q : Set _) (E.cutGradedJacobson_quotient_annihilated Q)
    (fun i j x => hP i j x) n).mp hTor
  have hTensorT := ((balancedTensorLeftFunctor.{u,v,v,v} k
    (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))
    (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)) ⧸ E.cutGradedJacobson Q)).mapIso e).isZero_iff.mp
      hTensor
  exact e.isZero_iff.mpr (T.ringModule_isZero_of_grade_lower_bound_tensor_functor b hb hTensorT)

theorem cutMinimalProjectiveResolution_hasProjectiveDimensionLE_of_tor_four
    (M : ModuleCat.{v} (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))ᵐᵒᵖ)
    (P : ProjectiveResolution M)
    (T : E.CutGradedRightModule Q) (e : P.complex.X 4 ≅ T.ringModule)
    (b : ℤ) (hb : ∀ q : ℤ, q < b → T.grade q = ⊥)
    (hP : ∀ i j, ∀ x : P.complex.X i, P.complex.d i j x ∈ Submodule.span k
      {a : P.complex.X j | ∃ r ∈ (E.cutGradedJacobson Q : Set (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))),
        ∃ m : P.complex.X j, MulOpposite.op r • m = a})
    (hTor : IsZero ((balancedTensorTorLeftFunctor.{u,v,v,v} k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))
      (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)) ⧸ E.cutGradedJacobson Q) 4).obj M)) :
    HasProjectiveDimensionLE M 3 :=
  fourTermProjectiveResolution_hasProjectiveDimensionLE P
    (E.cutMinimalProjectiveResolution_term_isZero_of_tor Q M P 4 T e b hb hP hTor)

end ASGinzburg.ZAlgebra.PeriodIso
