import ASGinzburg.BalancedTensorUniversal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Tensoring a genuine right module with a quotient ring gives its quotient
by the action of the ideal. This uses the actual balanced tensor quotient. -/
namespace ASGinzburg
universe u v w
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k Rᵐᵒᵖ M]
variable (I : Ideal R) [I.IsTwoSided]

def balancedTensorIdealAction : Submodule k M :=
  Submodule.span k (Set.range (fun p : I × M => MulOpposite.op (p.1 : R) • p.2))

omit [Algebra k R] [IsScalarTower k Rᵐᵒᵖ M] [I.IsTwoSided] in
theorem balancedTensorIdealAction_mem (r : R) (hr : r ∈ I) (m : M) :
    MulOpposite.op r • m ∈ balancedTensorIdealAction k R M I :=
  Submodule.subset_span ⟨(⟨r, hr⟩, m), rfl⟩

theorem balancedTensorIdealAction_smul_mem (r : R) {m : M}
    (hm : m ∈ balancedTensorIdealAction k R M I) :
    MulOpposite.op r • m ∈ balancedTensorIdealAction k R M I := by
  refine Submodule.span_induction
    (p := fun x _ => MulOpposite.op r • x ∈ balancedTensorIdealAction k R M I)
    ?_ ?_ ?_ ?_ hm
  · rintro x ⟨⟨i, y⟩, rfl⟩
    have h := balancedTensorIdealAction_mem k R M I ((i : R) * r)
      (I.mul_mem_right r i.property) y
    simpa only [MulOpposite.op_mul, mul_smul] using h
  · change MulOpposite.op r • (0 : M) ∈ balancedTensorIdealAction k R M I
    rw [smul_zero]
    exact (balancedTensorIdealAction k R M I).zero_mem
  · intro x y hx hy hfx hfy
    rw [smul_add]
    exact (balancedTensorIdealAction k R M I).add_mem hfx hfy
  · intro c x hx hfx
    rw [smul_comm]
    exact (balancedTensorIdealAction k R M I).smul_mem c hfx

abbrev BalancedTensorIdealQuotient := M ⧸ balancedTensorIdealAction k R M I

noncomputable def balancedTensorQuotientScalar (m : M) :
    R →ₗ[k] BalancedTensorIdealQuotient k R M I where
  toFun r := (balancedTensorIdealAction k R M I).mkQ (MulOpposite.op r • m)
  map_add' r s := by
    rw [MulOpposite.op_add, add_smul, map_add]
  map_smul' c r := by
    rw [MulOpposite.op_smul, smul_assoc, map_smul]
    rfl

noncomputable def balancedTensorQuotientCoefficient (m : M) :
    R ⧸ I →ₗ[k] BalancedTensorIdealQuotient k R M I :=
  (I.restrictScalars k).liftQ (balancedTensorQuotientScalar k R M I m) (by
    intro r hr
    apply (Submodule.Quotient.mk_eq_zero (balancedTensorIdealAction k R M I)).mpr
    exact balancedTensorIdealAction_mem k R M I r hr m)

@[simp] theorem balancedTensorQuotientCoefficient_mk (m : M) (r : R) :
    balancedTensorQuotientCoefficient k R M I m (Ideal.Quotient.mk I r) =
      (balancedTensorIdealAction k R M I).mkQ (MulOpposite.op r • m) := rfl

noncomputable def balancedTensorQuotientBilinear :
    M →ₗ[k] R ⧸ I →ₗ[k] BalancedTensorIdealQuotient k R M I where
  toFun := balancedTensorQuotientCoefficient k R M I
  map_add' x y := by
    apply LinearMap.ext
    intro q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp only [LinearMap.add_apply, balancedTensorQuotientCoefficient_mk, smul_add, map_add]
  map_smul' c x := by
    apply LinearMap.ext
    intro q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp only [LinearMap.smul_apply, balancedTensorQuotientCoefficient_mk]
    rw [smul_comm, map_smul]
    rfl

noncomputable def balancedTensorQuotientMap :
    BalancedTensorSpace k R M (R ⧸ I) →ₗ[k] BalancedTensorIdealQuotient k R M I :=
  balancedTensorLift k R M (R ⧸ I) (balancedTensorQuotientBilinear k R M I) (by
    intro s m q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    change (balancedTensorIdealAction k R M I).mkQ (MulOpposite.op r • MulOpposite.op s • m) =
      (balancedTensorIdealAction k R M I).mkQ (MulOpposite.op (s * r) • m)
    rw [MulOpposite.op_mul, mul_smul])

@[simp] theorem balancedTensorQuotientMap_tmul_mk (m : M) (r : R) :
    balancedTensorQuotientMap k R M I
        (balancedTensorTmul k R M (R ⧸ I) m (Ideal.Quotient.mk I r)) =
      (balancedTensorIdealAction k R M I).mkQ (MulOpposite.op r • m) := by
  rw [balancedTensorQuotientMap, balancedTensorLift_tmul]
  rfl

noncomputable def balancedTensorQuotientInverse :
    BalancedTensorIdealQuotient k R M I →ₗ[k] BalancedTensorSpace k R M (R ⧸ I) :=
  (balancedTensorIdealAction k R M I).liftQ
    ((balancedTensorBilinear k R M (R ⧸ I)).flip (Ideal.Quotient.mk I 1)) (by
      apply Submodule.span_le.mpr
      rintro a ⟨⟨i, m⟩, rfl⟩
      change balancedTensorTmul k R M (R ⧸ I)
        (MulOpposite.op (i : R) • m) (Ideal.Quotient.mk I 1) = 0
      rw [balancedTensorTmul_balance]
      have h : (i : R) • Ideal.Quotient.mk I 1 = 0 := by
        change Ideal.Quotient.mk I ((i : R) * 1) = 0
        rw [mul_one]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr i.property
      rw [h]
      exact (balancedTensorBilinear k R M (R ⧸ I) m).map_zero)

omit [IsScalarTower k Rᵐᵒᵖ M] in
@[simp] theorem balancedTensorQuotientInverse_mk (m : M) :
    balancedTensorQuotientInverse k R M I
        ((balancedTensorIdealAction k R M I).mkQ m) =
      balancedTensorTmul k R M (R ⧸ I) m (Ideal.Quotient.mk I 1) := rfl

noncomputable def balancedTensorQuotientEquiv :
    BalancedTensorSpace k R M (R ⧸ I) ≃ₗ[k] BalancedTensorIdealQuotient k R M I where
  toFun := balancedTensorQuotientMap k R M I
  invFun := balancedTensorQuotientInverse k R M I
  left_inv a := by
    have h : (balancedTensorQuotientInverse k R M I).comp (balancedTensorQuotientMap k R M I) =
        LinearMap.id := by
      apply balancedTensorSpace_linearMap_ext k R M (R ⧸ I)
      intro m q
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
      simp only [LinearMap.comp_apply, balancedTensorQuotientMap_tmul_mk,
        balancedTensorQuotientInverse_mk, LinearMap.id_apply]
      rw [balancedTensorTmul_balance]
      change balancedTensorTmul k R M (R ⧸ I) m (Ideal.Quotient.mk I (r * 1)) =
        balancedTensorTmul k R M (R ⧸ I) m (Ideal.Quotient.mk I r)
      rw [mul_one]
    exact LinearMap.congr_fun h a
  right_inv a := by
    obtain ⟨m, rfl⟩ := (balancedTensorIdealAction k R M I).mkQ_surjective a
    rw [balancedTensorQuotientInverse_mk, balancedTensorQuotientMap_tmul_mk]
    rw [MulOpposite.op_one, one_smul]
  map_add' := map_add (balancedTensorQuotientMap k R M I)
  map_smul' := map_smul (balancedTensorQuotientMap k R M I)

@[simp] theorem balancedTensorQuotientEquiv_tmul_mk (m : M) (r : R) :
    balancedTensorQuotientEquiv k R M I
        (balancedTensorTmul k R M (R ⧸ I) m (Ideal.Quotient.mk I r)) =
      (balancedTensorIdealAction k R M I).mkQ (MulOpposite.op r • m) :=
  balancedTensorQuotientMap_tmul_mk k R M I m r

@[simp] theorem balancedTensorQuotientEquiv_symm_mk (m : M) :
    (balancedTensorQuotientEquiv k R M I).symm
        ((balancedTensorIdealAction k R M I).mkQ m) =
      balancedTensorTmul k R M (R ⧸ I) m (Ideal.Quotient.mk I 1) :=
  balancedTensorQuotientInverse_mk k R M I m

end ASGinzburg
