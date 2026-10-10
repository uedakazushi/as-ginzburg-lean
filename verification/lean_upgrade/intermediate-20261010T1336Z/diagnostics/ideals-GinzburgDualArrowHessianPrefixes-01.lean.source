import ASGinzburg.GinzburgDualArrowRepresentative
import ASGinzburg.GinzburgOriginalPrefixCoefficients
import ASGinzburg.GinzburgCyclicHessianCoefficients
import ASGinzburg.GinzburgPathHessianCut

/-! The actual upper prefix of the differential of a native dual
arrow has exactly the path-valued cyclic Hessian coefficients. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

theorem GinzburgLastGeneratorData.original_path {u v : Q.Vertex}
    (b : Q.Arrow) (hb : Q.target b=v) (p : Q.Path u (Q.source b)) :
    (GinzburgLastGeneratorData.path Q)
      ⟨⟨GinzburgArrow.original b,hb⟩,p.originalGinzburg Q⟩=
      ((Path.snoc p b rfl).transport rfl hb).originalGinzburg Q := by
  subst v
  simp [GinzburgLastGeneratorData.path,Path.transport,GinzburgPath.transport,
    Path.originalGinzburg]

universe u
variable (k : Type u) [Field k]

theorem ginzburgDualArrowHessianPrefix_coeff (φ : Q.Potential k)
    (a b : Q.Arrow) (hb : Q.target b=Q.source a)
    (p : Q.Path (Q.target a) (Q.source b))
    (hp : (p.cutDegree:ℤ)=(GinzburgArrow.dual a).cutDegree Q-
      (GinzburgArrow.original b).cutDegree Q) :
    (((Q.ginzburgOriginalFilteredToPrefix k φ (Q.target a) (Q.source a)
      ((GinzburgArrow.dual a).cutDegree Q)).f 0
        (Q.ginzburgDualLayerDifferential k φ (Q.target a) (Q.source a)
          ((GinzburgArrow.dual a).cutDegree Q) (Q.ginzburgDualArrowRepresentative k a)))
      ⟨.original b,hb,rfl⟩).val (p.originalGinzburg Q)=
      Q.pathCyclicHessian k a b φ p := by
  let pr : {p : Q.GinzburgPath (Q.target a) (Q.source b) //
      p.cohomologicalDegree=0-0 ∧ p.cutDegree=
        (GinzburgArrow.dual a).cutDegree Q-(GinzburgArrow.original b).cutDegree Q} :=
    ⟨p.originalGinzburg Q,by simp [p.originalGinzburg_cohomologicalDegree Q],by
      simpa only [p.originalGinzburg_cutDegree Q] using hp⟩
  have he := Q.ginzburgOriginalFilteredToPrefix_coefficient k φ (Q.target a)
    (Q.source a) ((GinzburgArrow.dual a).cutDegree Q)
    (Q.ginzburgDualLayerDifferential k φ (Q.target a) (Q.source a)
      ((GinzburgArrow.dual a).cutDegree Q) (Q.ginzburgDualArrowRepresentative k a))
    ⟨.original b,hb,rfl⟩ pr
  change _=Q.ginzburgDifferential k φ (Q.target a) (Q.source a)
    (Finsupp.single (Q.ginzburgArrowPath (.dual a)) 1)
    ((GinzburgLastGeneratorData.path Q) ⟨⟨.original b,hb⟩,p.originalGinzburg Q⟩) at he
  rw [GinzburgLastGeneratorData.original_path] at he
  exact he.trans (Q.ginzburgDifferential_dualArrow_snoc_coeff k a b φ p hb)

theorem ginzburgDualArrowHessianPrefix_coeff_all (φ : Q.Potential k)
    (a b : Q.Arrow) (hb : Q.target b=Q.source a)
    (p : Q.Path (Q.target a) (Q.source b)) :
    (((Q.ginzburgOriginalFilteredToPrefix k φ (Q.target a) (Q.source a)
      ((GinzburgArrow.dual a).cutDegree Q)).f 0
        (Q.ginzburgDualLayerDifferential k φ (Q.target a) (Q.source a)
          ((GinzburgArrow.dual a).cutDegree Q) (Q.ginzburgDualArrowRepresentative k a)))
      ⟨.original b,hb,rfl⟩).val (p.originalGinzburg Q)=
      Q.pathCyclicHessian k a b φ p := by
  by_cases hp : (p.cutDegree:ℤ)=(GinzburgArrow.dual a).cutDegree Q-
      (GinzburgArrow.original b).cutDegree Q
  · exact Q.ginzburgDualArrowHessianPrefix_coeff k φ a b hb p hp
  · let z := Q.ginzburgDualLayerDifferential k φ (Q.target a) (Q.source a)
      ((GinzburgArrow.dual a).cutDegree Q) (Q.ginzburgDualArrowRepresentative k a)
    let f := ((Q.ginzburgOriginalFilteredToPrefix k φ (Q.target a) (Q.source a)
      ((GinzburgArrow.dual a).cutDegree Q)).f 0 z) ⟨.original b,hb,rfl⟩
    change f.val (p.originalGinzburg Q)=_
    have hL : f.val (p.originalGinzburg Q)=0 := by
      apply (Finsupp.mem_supported' k _).mp f.property.2
      intro h
      apply hp
      simpa only [Set.mem_setOf_eq,p.originalGinzburg_cutDegree Q] using h
    have hR := (Finsupp.mem_supported' k _).mp
      (Q.pathCyclicHessian_ginzburg_cut k a b φ) p hp
    exact hL.trans hR.symm

end ASGinzburg.CutQuiver
