import ASGinzburg.ASGeneratorBasis

/-! On sheet zero the genuine indecomposable basis of the AS resolution
is indexed exactly by the non-cut arrows of the foundation quiver. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

abbrev FoundationArrow (i j : Q.Vertex) :=
  {a : Q.Arrow // Q.source a=i ∧ Q.target a=j ∧ Q.cut a=false}

theorem foundation_generator_noncut (i j : Q.Vertex)
    (a : ZAlgebra.ASResolution.GeneratorIndex (Q := Q) (w := (j,0)) (i.val : ℤ)) :
    Q.cut a.val.val=false := by
  have ha := a.property
  have hs := (Q.source a.val.val).isLt
  have hi := i.isLt
  cases hc : Q.cut a.val.val
  · rfl
  · simp [incomingSource,liftedSource,height,cutDegree,hc] at ha
    omega

def foundationGeneratorIndexEquiv (i j : Q.Vertex) :
    ZAlgebra.ASResolution.GeneratorIndex (Q := Q) (w := (j,0)) (i.val : ℤ) ≃
      Q.FoundationArrow i j where
  toFun a := ⟨a.val.val,by
    refine ⟨?_,a.val.property,Q.foundation_generator_noncut i j a⟩
    apply Fin.ext
    have ha := a.property
    have hc := Q.foundation_generator_noncut i j a
    simp [incomingSource,liftedSource,height,cutDegree,hc] at ha
    omega⟩
  invFun a := ⟨⟨a.val,a.property.2.1⟩,by
    simp [incomingSource,liftedSource,height,cutDegree,a.property.1,a.property.2.2]⟩
  left_inv a := by rfl
  right_inv a := by rfl

end ASGinzburg.CutQuiver

namespace ASGinzburg.ZAlgebra.ASResolution
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {Q : CutQuiver}

noncomputable def foundationArrowBasis (i j : Q.Vertex) (hij : i.val<j.val)
    (R : A.ASResolution Q (j,0)) :
    Module.Basis (Q.FoundationArrow i j) k
      (A.Hom (i.val : ℤ) (j.val : ℤ) ⧸
        Submodule.span k (A.products (i.val : ℤ) (j.val : ℤ))) := by
  have hi : (i.val : ℤ)<Q.height (j,0) := by simp [CutQuiver.height]; omega
  exact (R.indecomposableGeneratorBasis (i.val : ℤ) hi).reindex
    (Q.foundationGeneratorIndexEquiv i j)

end ASGinzburg.ZAlgebra.ASResolution
