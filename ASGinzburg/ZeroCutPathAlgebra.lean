import ASGinzburg.PathCutProducts
import ASGinzburg.FiniteComponentAlgebra

/-! The actual non-cut path spaces, with their original path
composition and zero-length paths, form a finite-dimensional ring. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def zeroCutPathId (i : Q.Vertex) : Q.pathCutComponent k i i 0 :=
  ⟨Q.pathId k i,Finsupp.single_mem_supported _ _ (by rfl)⟩

noncomputable def zeroCutPathComp {i j l : Q.Vertex} :
    Q.pathCutComponent k j l 0 →ₗ[k]
      Q.pathCutComponent k i j 0 →ₗ[k] Q.pathCutComponent k i l 0 where
  toFun g :=
    { toFun := fun f => ⟨Q.pathComp k g.val f.val,by
        simpa only [add_zero] using Q.pathCutComponent_comp k f.property g.property⟩
      map_add' := fun f h => Subtype.ext ((Q.pathComp k g.val).map_add f.val h.val)
      map_smul' := fun c f => Subtype.ext ((Q.pathComp k g.val).map_smul c f.val) }
  map_add' g h := by
    apply LinearMap.ext
    intro f
    exact Subtype.ext (LinearMap.congr_fun ((Q.pathComp k).map_add g.val h.val) f.val)
  map_smul' c g := by
    apply LinearMap.ext
    intro f
    exact Subtype.ext (LinearMap.congr_fun ((Q.pathComp k).map_smul c g.val) f.val)

noncomputable def zeroCutPathComponentAlgebra : LinearComponentAlgebra k Q.Vertex where
  Hom i j := Q.pathCutComponent k i j 0
  id := Q.zeroCutPathId k
  comp := Q.zeroCutPathComp k
  comp_id f := Subtype.ext (Q.pathComp_id k f.val)
  id_comp f := Subtype.ext (Q.id_pathComp k f.val)
  comp_assoc f g h := Subtype.ext (Q.pathComp_assoc k f.val g.val h.val)

noncomputable abbrev ZeroCutPathRing := (Q.zeroCutPathComponentAlgebra k).Total

noncomputable instance zeroCutPathRingFinite : Module.Finite k (Q.ZeroCutPathRing k) := by
  change Module.Finite k (∀ i j : Q.Vertex,Q.pathCutComponent k i j 0)
  infer_instance

end ASGinzburg.CutQuiver
