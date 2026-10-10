import ASGinzburg.PeriodCutEnvelopingRegularZeroGrading

/-! Every genuine unsigned enveloping homogeneous block acts on R by a
k-linear operator raising its internal degree by the sum of the two
factor degrees. This includes arbitrary tensor elements, not only pure
tensors. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open scoped TensorProduct
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

noncomputable def cutEnvelopingRegularHomogeneousOperator (d : ℕ × ℕ)
    (a : E.CutEnvelopingBlock (fun i : Q.Vertex => (i.val : ℤ)) d) :
    E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)) →ₗ[k]
      E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)) :=
  regularEnvelopingRepresentation k _
    (E.cutEnvelopingHomogeneousInclusion (fun i : Q.Vertex => (i.val : ℤ)) d a)

theorem cutEnvelopingRegularHomogeneousOperator_homogeneous (d : ℕ × ℕ)
    (a : E.CutEnvelopingBlock (fun i : Q.Vertex => (i.val : ℤ)) d)
    (q : ℤ) (x : E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))
    (hx : x ∈ E.cutIntegerHomogeneousSpace Q q) :
    E.cutEnvelopingRegularHomogeneousOperator Q d a x ∈
      E.cutIntegerHomogeneousSpace Q (q + ((d.1 + d.2 : ℕ) : ℤ)) := by
  rcases d with ⟨i,j⟩
  induction a using TensorProduct.induction_on with
  | zero =>
    have h : E.cutEnvelopingRegularHomogeneousOperator Q (i,j) 0 = 0 :=
      ((regularEnvelopingRepresentation k _).toLinearMap.comp
        (E.cutEnvelopingHomogeneousInclusion
          (fun t : Q.Vertex => (t.val : ℤ)) (i,j))).map_zero
    rw [h, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  | tmul a b =>
    change regularEnvelopingRepresentation k _
      (E.cutEnvelopingHomogeneousInclusion (fun t : Q.Vertex => (t.val : ℤ))
        (i,j) (a ⊗ₜ[k] b)) x ∈ _
    rw [E.cutEnvelopingHomogeneousInclusion_tmul,
      regularEnvelopingRepresentation_tmul]
    have hl := E.cutIntegerHomogeneousSpace_mul_left Q q x hx i a
    simpa only [Nat.cast_add, add_assoc] using
      E.cutIntegerHomogeneousSpace_mul_right Q (q+(i:ℤ)) _ hl j b
  | add a b ha hb =>
    have h : E.cutEnvelopingRegularHomogeneousOperator Q (i,j) (a+b) x =
        E.cutEnvelopingRegularHomogeneousOperator Q (i,j) a x +
          E.cutEnvelopingRegularHomogeneousOperator Q (i,j) b x :=
      LinearMap.congr_fun (((regularEnvelopingRepresentation k _).toLinearMap.comp
        (E.cutEnvelopingHomogeneousInclusion
          (fun t : Q.Vertex => (t.val : ℤ)) (i,j))).map_add a b) x
    exact h.symm ▸ Submodule.add_mem _ ha hb

attribute [local instance] cutEnvelopingZeroRegularModule

theorem cutEnvelopingRegularHomogeneousOperator_integerGrade (d : ℕ × ℕ)
    (a : E.CutEnvelopingBlock (fun i : Q.Vertex => (i.val : ℤ)) d)
    (q : ℤ) (x : E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))
    (hx : x ∈ E.cutEnvelopingRegularIntegerGrade Q q) :
    E.cutEnvelopingRegularHomogeneousOperator Q d a x ∈
      E.cutEnvelopingRegularIntegerGrade Q (q + ((d.1 + d.2 : ℕ) : ℤ)) :=
  E.cutEnvelopingRegularHomogeneousOperator_homogeneous Q d a q x hx

end ASGinzburg.ZAlgebra.PeriodIso
