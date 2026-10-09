import ASGinzburg.GinzburgUnitGeneratorDifferentials

/-! At every integer sheet, each actual dual prefix of the unit-loop
differential is the original arrow from the corresponding shifted vertex. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgUnitLoopArrowComponent (v : Q.Vertex) (s : ℤ)
    (b : Q.Arrow) (hb : Q.source b=v) :
    Q.ginzburgCutCohomologicalComponent k v (Q.target b) (-1-(-1))
      ((s-(s-1))-(GinzburgArrow.dual b).cutDegree Q) := by
  refine ⟨(Q.ginzburgLoopOriginalArrowComponent k v b hb).val,
    (Q.ginzburgLoopOriginalArrowComponent k v b hb).property.1,?_⟩
  have hc : (s-(s-1))-(GinzburgArrow.dual b).cutDegree Q=
      1-(GinzburgArrow.dual b).cutDegree Q := by omega
  rw [hc]
  exact (Q.ginzburgLoopOriginalArrowComponent k v b hb).property.2

theorem ginzburgUnitLoopDualPrefix_eq (φ : Q.Potential k)
    (v : Q.Vertex) (s : ℤ) (b : Q.Arrow) (hb : Q.source b=v) :
    (((Q.ginzburgFilteredToPrefix k φ v v (-1) (s-(s-1))).f (-1)
      (Q.ginzburgLoopLayerDifferential k φ v v (s-(s-1))
        (Q.ginzburgGeneratorUnitRepresentative k (v,s) (-2)
          ⟨.loop v,rfl,rfl⟩))) ⟨.dual b,hb,rfl⟩)=
      Q.ginzburgUnitLoopArrowComponent k v s b hb := by
  let z := Q.ginzburgLoopLayerDifferential k φ v v (s-(s-1))
    (Q.ginzburgGeneratorUnitRepresentative k (v,s) (-2) ⟨.loop v,rfl,rfl⟩)
  apply (Q.ginzburgCutComponentBasisEquiv k v (Q.target b) (-1-(-1))
    ((s-(s-1))-(GinzburgArrow.dual b).cutDegree Q)).injective
  apply Finsupp.ext
  intro p
  simp only [Q.ginzburgCutComponentBasisEquiv_apply]
  change _=(Finsupp.single ((Q.originalGinzburgArrowPath b).transport Q hb rfl) (1:k)) p.val
  exact (Q.ginzburgFilteredToPrefix_coefficient k φ v v (-1) (-1) (s-(s-1)) z
    ⟨.dual b,hb,rfl⟩ p).trans
      ((congrArg (fun f : Q.GinzburgPathComponent k v v =>
        f ((GinzburgLastGeneratorData.path Q) ⟨⟨.dual b,hb⟩,p.val⟩))
        (Q.ginzburgUnitLoopDifferential_val k φ v s)).trans
          (Q.ginzburgLoopDifferential_dual_path_coeff k v b hb p.val))

end ASGinzburg.CutQuiver
