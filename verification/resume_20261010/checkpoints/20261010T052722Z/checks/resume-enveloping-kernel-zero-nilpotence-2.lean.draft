import work.ASGinzburgDraft.PeriodCutEnvelopingAugmentationComparison
import work.ASGinzburgDraft.PeriodCutZeroEnvelopingNilpotence

/-! The actual full enveloping augmentation, restricted to its genuine
degree-zero subalgebra, has the nilpotent ideal needed for graded
Nakayama. This is the comap of the full kernel, not a separate radical
chosen independently of the augmentation. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))
attribute [local instance] cutZeroSelfScalarTower
attribute [local instance] cutZeroEnvelopingSelfSMul cutZeroEnvelopingSelfScalarTower

theorem cutEnvelopingKernel_zeroComap_eq :
    (E.cutEnvelopingAugmentationKernel Q).comap (E.cutEnvelopingZeroInclusion Q) =
      E.cutZeroEnvelopingAugmentationKernel Q :=
  E.cutEnvelopingAugmentationKernel_comap_zeroInclusion Q

theorem cutEnvelopingKernel_zeroComap_pow_eq_bot :
    ((E.cutEnvelopingAugmentationKernel Q).comap (E.cutEnvelopingZeroInclusion Q)) ^
      (2 * Q.vertices) = ⊥ := by
  rw [E.cutEnvelopingKernel_zeroComap_eq Q]
  exact E.cutZeroEnvelopingAugmentationKernel_pow_eq_bot Q

theorem cutEnvelopingKernel_zeroComap_isNilpotent :
    IsNilpotent ((E.cutEnvelopingAugmentationKernel Q).comap
      (E.cutEnvelopingZeroInclusion Q)) :=
  ⟨2 * Q.vertices, E.cutEnvelopingKernel_zeroComap_pow_eq_bot Q⟩

end ASGinzburg.ZAlgebra.PeriodIso
