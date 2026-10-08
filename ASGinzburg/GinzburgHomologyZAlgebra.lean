import ASGinzburg.GinzburgCutHomologyUnits
import ASGinzburg.GinzburgCutHomologyFinite
import ASGinzburg.ZAlgebraIsomorphisms

/-! The actual fixed-cut mathlib H-zero forms a locally finite directed
Z-algebra, with its genuine induced multiplication, isomorphic to A(Phi). -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable abbrev GinzburgHomologyComponent (φ : Q.Potential k) (i j : ℤ) : Type u :=
  Q.ginzburgCutHomology k φ (Q.heightEquiv.symm i).1 (Q.heightEquiv.symm j).1
    ((Q.heightEquiv.symm j).2-(Q.heightEquiv.symm i).2) 0

noncomputable def ginzburgHomologyComponentJacobianEquiv (φ : Q.Potential k) (i j : ℤ) :
    Q.GinzburgHomologyComponent k φ i j ≃ₗ[k] (Q.unrolledJacobianZAlgebra k φ).Hom i j :=
    (Q.ginzburgCutHomologyZeroUnrolledIso k φ (Q.heightEquiv.symm i)
      (Q.heightEquiv.symm j)).toLinearEquiv.trans
        ((Q.unrolledJacobianZAlgebra k φ).homTransport _ _ i j
          (Q.height_heightEquiv_symm i) (Q.height_heightEquiv_symm j))

theorem ginzburgHomologyComponentJacobianEquiv_id (φ : Q.Potential k) (i : ℤ) :
    Q.ginzburgHomologyComponentJacobianEquiv k φ i i
      (Q.ginzburgCutHomologyZeroId k φ (Q.heightEquiv.symm i))=
        (Q.unrolledJacobianZAlgebra k φ).id i := by
  change (Q.unrolledJacobianZAlgebra k φ).homTransport _ _ i i _ _
    ((Q.ginzburgCutHomologyZeroUnrolledIso k φ _ _).hom
      (Q.ginzburgCutHomologyZeroId k φ _))=_
  rw [Q.ginzburgCutHomologyZeroUnrolledIso_id,ZAlgebra.homTransport_id]

theorem ginzburgHomologyComponentJacobianEquiv_comp (φ : Q.Potential k) {i j l : ℤ}
    (f : Q.GinzburgHomologyComponent k φ i j) (g : Q.GinzburgHomologyComponent k φ j l) :
    Q.ginzburgHomologyComponentJacobianEquiv k φ i l (Q.ginzburgCutHomologyZeroComp k φ g f)=
      (Q.unrolledJacobianZAlgebra k φ).comp
        (Q.ginzburgHomologyComponentJacobianEquiv k φ j l g)
        (Q.ginzburgHomologyComponentJacobianEquiv k φ i j f) := by
  change (Q.unrolledJacobianZAlgebra k φ).homTransport _ _ i l _ _
    ((Q.ginzburgCutHomologyZeroUnrolledIso k φ _ _).hom
      (Q.ginzburgCutHomologyZeroComp k φ g f))=_
  rw [Q.ginzburgCutHomologyZeroUnrolledIso_comp,ZAlgebra.homTransport_comp]
  rfl

noncomputable def ginzburgHomologyZAlgebra (φ : Q.Potential k) : ZAlgebra.{u,u} k where
  Hom := Q.GinzburgHomologyComponent k φ
  id i := Q.ginzburgCutHomologyZeroId k φ (Q.heightEquiv.symm i)
  comp := Q.ginzburgCutHomologyZeroComp k φ
  comp_id := Q.ginzburgCutHomologyZeroComp_id k φ
  id_comp := Q.id_ginzburgCutHomologyZeroComp k φ
  comp_assoc := Q.ginzburgCutHomologyZeroComp_assoc k φ
  positive := by
    intro i j hij f
    apply (Q.ginzburgHomologyComponentJacobianEquiv k φ i j).injective
    rw [map_zero]
    exact (Q.unrolledJacobianZAlgebra k φ).positive hij _
  connected := by
    intro i f
    obtain ⟨a,ha⟩ := (Q.unrolledJacobianZAlgebra k φ).connected i
      (Q.ginzburgHomologyComponentJacobianEquiv k φ i i f)
    refine ⟨a,?_⟩
    apply (Q.ginzburgHomologyComponentJacobianEquiv k φ i i).injective
    rw [map_smul,Q.ginzburgHomologyComponentJacobianEquiv_id]
    exact ha
  id_nonzero := by
    intro i h
    have he := congrArg (Q.ginzburgHomologyComponentJacobianEquiv k φ i i) h
    rw [Q.ginzburgHomologyComponentJacobianEquiv_id,map_zero] at he
    exact (Q.unrolledJacobianZAlgebra k φ).id_nonzero i he
  finite := by intro i j; infer_instance

noncomputable def ginzburgHomologyJacobianIsomorphism (φ : Q.Potential k) :
    ZAlgebra.Isomorphism (Q.ginzburgHomologyZAlgebra k φ) (Q.unrolledJacobianZAlgebra k φ) where
  map := Q.ginzburgHomologyComponentJacobianEquiv k φ
  map_id := Q.ginzburgHomologyComponentJacobianEquiv_id k φ
  map_comp := Q.ginzburgHomologyComponentJacobianEquiv_comp k φ

end ASGinzburg.CutQuiver
