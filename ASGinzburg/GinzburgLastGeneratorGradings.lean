import ASGinzburg.GinzburgAugmentationBasis

/-! The free augmentation basis retains the genuine cohomological and
cut degrees, so its free summands have exactly the generator shifts. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

theorem GinzburgLastGeneratorData.path_cohomologicalDegree {u v : Q.Vertex}
    (d : Q.GinzburgLastGeneratorData u v) :
    (d.path Q).cohomologicalDegree=d.2.cohomologicalDegree+d.1.val.cohomologicalDegree Q := by
  obtain ⟨⟨a,ha⟩,p⟩ := d
  cases ha
  rfl

theorem GinzburgLastGeneratorData.path_cutDegree {u v : Q.Vertex}
    (d : Q.GinzburgLastGeneratorData u v) :
    (d.path Q).cutDegree=d.2.cutDegree+d.1.val.cutDegree Q := by
  obtain ⟨⟨a,ha⟩,p⟩ := d
  cases ha
  rfl

theorem GinzburgLastGeneratorData.path_cohomologicalDegree_iff {u v : Q.Vertex}
    (d : Q.GinzburgLastGeneratorData u v) (q : ℤ) :
    (d.path Q).cohomologicalDegree=q ↔
      d.2.cohomologicalDegree=q-d.1.val.cohomologicalDegree Q := by
  rw [d.path_cohomologicalDegree]
  omega

theorem GinzburgLastGeneratorData.path_cutDegree_iff {u v : Q.Vertex}
    (d : Q.GinzburgLastGeneratorData u v) (c : ℤ) :
    (d.path Q).cutDegree=c ↔ d.2.cutDegree=c-d.1.val.cutDegree Q := by
  rw [d.path_cutDegree]
  omega

def GinzburgLastGeneratorData.atDegreeEquiv (u v : Q.Vertex) (q c : ℤ) :
    {p : Q.GinzburgPath u v // 0<p.length ∧ p.cohomologicalDegree=q ∧ p.cutDegree=c} ≃
      {d : Q.GinzburgLastGeneratorData u v //
        d.2.cohomologicalDegree=q-d.1.val.cohomologicalDegree Q ∧
        d.2.cutDegree=c-d.1.val.cutDegree Q} where
  toFun p := ⟨p.val.lastGenerator Q p.property.1,by
    constructor
    · apply ((p.val.lastGenerator Q p.property.1).path_cohomologicalDegree_iff Q q).mp
      rw [p.val.lastGenerator_path]
      exact p.property.2.1
    · apply ((p.val.lastGenerator Q p.property.1).path_cutDegree_iff Q c).mp
      rw [p.val.lastGenerator_path]
      exact p.property.2.2⟩
  invFun d := ⟨d.val.path Q,by
    refine ⟨by rw [d.val.path_length]; omega,?_,?_⟩
    · exact (d.val.path_cohomologicalDegree_iff Q q).mpr d.property.1
    · exact (d.val.path_cutDegree_iff Q c).mpr d.property.2⟩
  left_inv p := Subtype.ext (p.val.lastGenerator_path Q p.property.1)
  right_inv d := Subtype.ext (d.val.path_lastGenerator Q)

end ASGinzburg.CutQuiver
