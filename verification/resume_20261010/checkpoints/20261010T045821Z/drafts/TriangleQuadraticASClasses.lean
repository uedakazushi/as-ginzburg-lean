import work.ASGinzburgDraft.Corollary52QuotientEquivalence

/-! The proved comparison of the literal quadratic AS definition with
the triangle AS definition also identifies their actual vertex-fixing
isomorphism-class spaces. -/
namespace ASGinzburg
universe u v
variable (k : Type u) [Field k]

def quadraticTriangleASAlgebraEquiv :
    QuadraticASAlgebra.{u,v} k ≃ ASRegularAlgebra.{u,v} k triangle333 where
  toFun A := ⟨A.val, A.val.quadraticASRegular_iff_triangleASRegular.mp A.property⟩
  invFun A := ⟨A.val, A.val.quadraticASRegular_iff_triangleASRegular.mpr A.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

noncomputable def quadraticTriangleASClassEquiv :
    QuadraticASIsomorphismClass.{u,v} k ≃ ASRegularIsomorphismClass.{u,v} k triangle333 :=
  Quotient.congr (quadraticTriangleASAlgebraEquiv.{u,v} k) (fun _ _ => Iff.rfl)

theorem quadraticTriangleASClassEquiv_apply (A : QuadraticASAlgebra.{u,v} k) :
    quadraticTriangleASClassEquiv k (A.isomorphismClass k) =
      (quadraticTriangleASAlgebraEquiv k A).isomorphismClass k triangle333 := rfl

theorem quadraticTriangleASClassEquiv_tensor (w : GinzburgRegularTensor333 k) :
    quadraticTriangleASClassEquiv k (w.asQuadraticASClass k) =
      (ginzburgRegularTensorPotentialEquiv333 k w).asIsomorphismClass k triangle333 := rfl

theorem regularTensorQuadraticClass_eq_iff_potentialASClass
    (w w' : GinzburgRegularTensor333 k) :
    w.asQuadraticASClass k = w'.asQuadraticASClass k ↔
      (ginzburgRegularTensorPotentialEquiv333 k w).asIsomorphismClass k triangle333 =
        (ginzburgRegularTensorPotentialEquiv333 k w').asIsomorphismClass k triangle333 := by
  rw [← quadraticTriangleASClassEquiv_tensor, ← quadraticTriangleASClassEquiv_tensor]
  exact (quadraticTriangleASClassEquiv k).injective.eq_iff.symm

end ASGinzburg
