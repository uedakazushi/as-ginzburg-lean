import ASGinzburg.GinzburgLoopArrowRepresentative
import ASGinzburg.GinzburgLoopPathCoefficients
import ASGinzburg.GinzburgFilteredPrefixCoefficients

/-! The full native dual prefix component of a differentiated loop
is exactly the actual original arrow, with its true cut degree. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgLoopOriginalArrowComponent (v : Q.Vertex)
    (b : Q.Arrow) (hb : Q.source b=v) :
    Q.ginzburgCutCohomologicalComponent k v (Q.target b) (-1-(-1))
      (1-(GinzburgArrow.dual b).cutDegree Q) := by
  refine ⟨Finsupp.single ((Q.originalGinzburgArrowPath b).transport Q hb rfl) 1,?_,?_⟩
  · apply Finsupp.single_mem_supported
    simp [GinzburgPath.cohomologicalDegree_transport,originalGinzburgArrowPath,
      GinzburgPath.cohomologicalDegree,GinzburgArrow.cohomologicalDegree]
  · apply Finsupp.single_mem_supported
    simp [originalGinzburgArrowPath,GinzburgPath.cutDegree,GinzburgArrow.cutDegree]

theorem ginzburgLoopArrowDualPrefix_eq (φ : Q.Potential k)
    (v : Q.Vertex) (b : Q.Arrow) (hb : Q.source b=v) :
    (((Q.ginzburgFilteredToPrefix k φ v v (-1) 1).f (-1)
      (Q.ginzburgLoopLayerDifferential k φ v v 1 (Q.ginzburgLoopArrowRepresentative k v)))
      ⟨.dual b,hb,rfl⟩)=Q.ginzburgLoopOriginalArrowComponent k v b hb := by
  let z := Q.ginzburgLoopLayerDifferential k φ v v 1 (Q.ginzburgLoopArrowRepresentative k v)
  apply (Q.ginzburgCutComponentBasisEquiv k v (Q.target b) (-1-(-1))
    (1-(GinzburgArrow.dual b).cutDegree Q)).injective
  apply Finsupp.ext
  intro p
  simp only [Q.ginzburgCutComponentBasisEquiv_apply]
  change _=(Finsupp.single ((Q.originalGinzburgArrowPath b).transport Q hb rfl) (1:k)) p.val
  exact (Q.ginzburgFilteredToPrefix_coefficient k φ v v (-1) (-1) 1 z
    ⟨.dual b,hb,rfl⟩ p).trans
      ((congrArg (fun f : Q.GinzburgPathComponent k v v =>
        f ((GinzburgLastGeneratorData.path Q) ⟨⟨.dual b,hb⟩,p.val⟩))
        (Q.ginzburgLoopArrowDifferential_val k φ v)).trans
          (Q.ginzburgLoopDifferential_dual_path_coeff k v b hb p.val))

end ASGinzburg.CutQuiver
