import work.ASGinzburgDraft.TriangleTensorAction
import work.ASGinzburgDraft.TrianglePotentialCoordinates
import work.ASGinzburgDraft.TriangleQuadraticASRegular
import ASGinzburg.GinzburgRegularImpliesASRegular
import ASGinzburg.ZAlgebraIsomorphisms

/-! The actual assertion of source Corollary 5.2. The left side consists
of the literal quadratic resolutions (5.1) and Ext dimension condition
(5.2); the right side consists of actual XYZ tensors with vanishing
negative Ginzburg homology, modulo the actual GL(X) × GL(Y) × GL(Z)
action. The assertion is defined, not assumed or proved. Establishing
it as a theorem still requires the source correspondence proof. -/
namespace ASGinzburg
universe u v
variable (k : Type u) [Field k]

noncomputable def TriangleTensorGinzburgRegular (w : CubicTensor333 k) : Prop :=
  triangle333.GinzburgRegular k (triangleTensorPotentialEquiv k w)

noncomputable abbrev GinzburgRegularTensor333 :=
  {w : CubicTensor333 k // TriangleTensorGinzburgRegular k w}

noncomputable def ginzburgRegularTensorSetoid333 :
    Setoid (GinzburgRegularTensor333 k) :=
  Setoid.comap Subtype.val
    (MulAction.orbitRel (TriangleGL333 k) (CubicTensor333 k))

noncomputable abbrev GinzburgRegularTensorOrbit333 :=
  Quotient (ginzburgRegularTensorSetoid333 k)

noncomputable def GinzburgRegularTensor333.orbitClass
    (w : GinzburgRegularTensor333 k) : GinzburgRegularTensorOrbit333 k :=
  Quotient.mk _ w

theorem GinzburgRegularTensor333.orbitClass_eq_iff
    (w w' : GinzburgRegularTensor333 k) :
    w.orbitClass k = w'.orbitClass k ↔
      ∃ g : TriangleGL333 k, g • w.val = w'.val := by
  rw [GinzburgRegularTensor333.orbitClass,
    GinzburgRegularTensor333.orbitClass, Quotient.eq]
  change w.val ∈ MulAction.orbit (TriangleGL333 k) w'.val ↔ _
  rw [MulAction.mem_orbit_symm, MulAction.mem_orbit_iff]

abbrev QuadraticASAlgebra := {A : ZAlgebra.{u,v} k // A.QuadraticASRegular}

noncomputable def quadraticASIsomorphismSetoid :
    Setoid (QuadraticASAlgebra.{u,v} k) where
  r A B := Nonempty (ZAlgebra.Isomorphism A.val B.val)
  iseqv :=
    { refl := fun A => ⟨ZAlgebra.Isomorphism.refl A.val⟩
      symm := fun ⟨E⟩ => ⟨E.symm⟩
      trans := fun ⟨E⟩ ⟨F⟩ => ⟨E.trans F⟩ }

noncomputable abbrev QuadraticASIsomorphismClass :=
  Quotient (quadraticASIsomorphismSetoid.{u,v} k)

noncomputable def QuadraticASAlgebra.isomorphismClass
    (A : QuadraticASAlgebra.{u,v} k) : QuadraticASIsomorphismClass.{u,v} k :=
  Quotient.mk _ A

theorem QuadraticASAlgebra.isomorphismClass_eq_iff
    (A B : QuadraticASAlgebra.{u,v} k) :
    A.isomorphismClass k = B.isomorphismClass k ↔
      Nonempty (ZAlgebra.Isomorphism A.val B.val) :=
  Quotient.eq

noncomputable def GinzburgRegularTensor333.asQuadraticASAlgebra
    (w : GinzburgRegularTensor333 k) : QuadraticASAlgebra.{u,u} k :=
  ⟨triangle333.unrolledJacobianZAlgebra k (triangleTensorPotentialEquiv k w.val),
    (ZAlgebra.quadraticASRegular_iff_triangleASRegular _).mpr
      (w.property.asRegular triangle333 k (triangleTensorPotentialEquiv k w.val))⟩

noncomputable def GinzburgRegularTensor333.asQuadraticASClass
    (w : GinzburgRegularTensor333 k) : QuadraticASIsomorphismClass.{u,u} k :=
  (w.asQuadraticASAlgebra k).isomorphismClass k

/-- The tensor-to-algebra map identifies exactly the actual GL orbits. -/
noncomputable def Corollary52ClassStatement : Prop :=
  ∀ w w' : GinzburgRegularTensor333 k,
    w.orbitClass k = w'.orbitClass k ↔
      w.asQuadraticASClass k = w'.asQuadraticASClass k

/-- Every literal quadratic AS algebra is recovered from an actual
Ginzburg-regular tensor, up to an actual vertex-fixing isomorphism. -/
noncomputable def Corollary52TensorRecoveryStatement : Prop :=
  ∀ A : ZAlgebra.{u,v} k, A.QuadraticASRegular →
    ∃ w : GinzburgRegularTensor333 k,
      Nonempty (ZAlgebra.Isomorphism A
        (triangle333.unrolledJacobianZAlgebra k (triangleTensorPotentialEquiv k w.val)))

noncomputable def Corollary52Statement : Prop :=
  Corollary52ClassStatement k ∧ Corollary52TensorRecoveryStatement.{u,v} k

end ASGinzburg
