import ASGinzburg.GinzburgZeroProducts
import ASGinzburg.GinzburgCutHomologyZero

/-! Genuine degree-zero products at fixed endpoint sheets and stability
of the actual fixed-cut differential boundary images. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgCutZeroComp {u v w : Q.LiftVertex} :
    Q.ginzburgCutCohomologicalComponent k v.1 w.1 0 (w.2-v.2) →ₗ[k]
      Q.ginzburgCutCohomologicalComponent k u.1 v.1 0 (v.2-u.2) →ₗ[k]
        Q.ginzburgCutCohomologicalComponent k u.1 w.1 0 (w.2-u.2) where
  toFun g := ((Q.ginzburgPathComp k g.val).comp
    (Q.ginzburgCutCohomologicalComponent k u.1 v.1 0 (v.2-u.2)).subtype).codRestrict _ (fun f => by
      constructor
      · simpa only [zero_add] using
          Q.ginzburgCohomologicalComponent_comp k f.property.1 g.property.1
      · have h := Q.ginzburgCutComponent_comp k f.property.2 g.property.2
        simpa only [show v.2-u.2+(w.2-v.2)=w.2-u.2 by omega] using h)
  map_add' := by
    intro g h
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact LinearMap.congr_fun (map_add (Q.ginzburgPathComp k) g.val h.val) f.val
  map_smul' := by
    intro a g
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact LinearMap.congr_fun (map_smul (Q.ginzburgPathComp k) a g.val) f.val

theorem ginzburgCutZeroComp_boundary_left (φ : Q.Potential k) {u v w : Q.LiftVertex}
    {f : Q.ginzburgCutCohomologicalComponent k u.1 v.1 0 (v.2-u.2)}
    (hf : f ∈ LinearMap.range (Q.ginzburgCutNegativeOneDifferential k φ u.1 v.1 (v.2-u.2)))
    (g : Q.ginzburgCutCohomologicalComponent k v.1 w.1 0 (w.2-v.2)) :
    Q.ginzburgCutZeroComp k g f ∈ LinearMap.range
      (Q.ginzburgCutNegativeOneDifferential k φ u.1 w.1 (w.2-u.2)) := by
  obtain ⟨x,rfl⟩ := hf
  have hx : Q.ginzburgPathComp k g.val x.val ∈
      Q.ginzburgCutCohomologicalComponent k u.1 w.1 (-1) (w.2-u.2) := by
    constructor
    · simpa only [add_zero] using
        Q.ginzburgCohomologicalComponent_comp k x.property.1 g.property.1
    · have h := Q.ginzburgCutComponent_comp k x.property.2 g.property.2
      simpa only [show v.2-u.2+(w.2-v.2)=w.2-u.2 by omega] using h
  refine ⟨⟨Q.ginzburgPathComp k g.val x.val,hx⟩,?_⟩
  apply Subtype.ext
  change Q.ginzburgDifferential k φ u.1 w.1 (Q.ginzburgPathComp k g.val x.val)=
    Q.ginzburgPathComp k g.val (Q.ginzburgDifferential k φ u.1 v.1 x.val)
  rw [Q.ginzburgDifferential_comp,Q.ginzburgDifferential_degreeZero k φ g.property.1,
    Q.ginzburgSignMap_homogeneous k g.property.1,ginzburgSign_zero,one_smul]
  simp

theorem ginzburgCutZeroComp_boundary_right (φ : Q.Potential k) {u v w : Q.LiftVertex}
    {g : Q.ginzburgCutCohomologicalComponent k v.1 w.1 0 (w.2-v.2)}
    (hg : g ∈ LinearMap.range (Q.ginzburgCutNegativeOneDifferential k φ v.1 w.1 (w.2-v.2)))
    (f : Q.ginzburgCutCohomologicalComponent k u.1 v.1 0 (v.2-u.2)) :
    Q.ginzburgCutZeroComp k g f ∈ LinearMap.range
      (Q.ginzburgCutNegativeOneDifferential k φ u.1 w.1 (w.2-u.2)) := by
  obtain ⟨x,rfl⟩ := hg
  have hx : Q.ginzburgPathComp k x.val f.val ∈
      Q.ginzburgCutCohomologicalComponent k u.1 w.1 (-1) (w.2-u.2) := by
    constructor
    · simpa only [zero_add] using
        Q.ginzburgCohomologicalComponent_comp k f.property.1 x.property.1
    · have h := Q.ginzburgCutComponent_comp k f.property.2 x.property.2
      simpa only [show v.2-u.2+(w.2-v.2)=w.2-u.2 by omega] using h
  refine ⟨⟨Q.ginzburgPathComp k x.val f.val,hx⟩,?_⟩
  apply Subtype.ext
  change Q.ginzburgDifferential k φ u.1 w.1 (Q.ginzburgPathComp k x.val f.val)=
    Q.ginzburgPathComp k (Q.ginzburgDifferential k φ v.1 w.1 x.val) f.val
  rw [Q.ginzburgDifferential_comp,Q.ginzburgDifferential_degreeZero k φ f.property.1]
  simp

end ASGinzburg.CutQuiver
