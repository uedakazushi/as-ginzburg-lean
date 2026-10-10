import ASGinzburg.GinzburgAugmentationHeight
import ASGinzburg.GinzburgPrefixLengthSupport
import ASGinzburg.GinzburgPrefixFixedCoefficientClasses

/-! Genuine nonempty prefix coefficients vanish at or above their
fixed unrolled endpoint, as required for representable radical membership. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgCutComponent_eq_zero_of_nonempty_of_not_height_lt
    (x y : Q.LiftVertex) (q : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 q (y.2-x.2))
    (hf : f.val ∈ Q.ginzburgAugmentationSubmodule k x.1 y.1)
    (hxy : ¬Q.height x<Q.height y) : f=0 := by
  have hm : f.val ∈ Q.ginzburgAugmentationAtDegree k x.1 y.1 q (y.2-x.2) := by
    rw [Q.ginzburgAugmentationAtDegree_eq_inf]
    exact ⟨hf,f.property⟩
  rw [Q.ginzburgAugmentationAtDegree_eq_bot_of_not_height_lt k x y q hxy,
    Submodule.mem_bot] at hm
  exact Subtype.ext hm

theorem ginzburgLayerOriginalCoefficient_eq_zero_of_not_height_lt
    (x v : Q.LiftVertex)
    (f : Q.ginzburgGeneratorLayerAtDegree k x.1 v.1 0 0 (v.2-x.2))
    (hf : f.val ∈ Finsupp.supported k k
      {p : Q.GinzburgPath x.1 v.1 | 2 ≤ p.length})
    (a : {a : Q.GinzburgArrow // a.target Q=v.1 ∧ a.cohomologicalDegree Q=0})
    (ha : ¬Q.height x<Q.height (Q.ginzburgPrefixGeneratorEndpoint v a.val)) :
    Q.ginzburgGeneratorLayerFreeEquiv k x.1 v.1 0 0 (v.2-x.2) f a=0 := by
  let g := Q.ginzburgGeneratorLayerFreeEquiv k x.1 v.1 0 0 (v.2-x.2) f a
  have hgf : g.val ∈ Finsupp.supported k k
      {p : Q.GinzburgPath x.1 (a.val.source Q) | 1 ≤ p.length} :=
    Q.ginzburgGeneratorLayerFreeEquiv_supported_length k x.1 v.1 0 0 (v.2-x.2) 1 f hf a
  have hg : g.val ∈ Q.ginzburgAugmentationSubmodule k x.1 (a.val.source Q) :=
    Finsupp.supported_mono (fun p hp => by
      change 1 ≤ p.length at hp
      change 0<p.length
      omega) hgf
  have hzero : Q.ginzburgPrefixCoefficientZeroCutEquiv k x v a.val g=0 :=
    Q.ginzburgCutComponent_eq_zero_of_nonempty_of_not_height_lt k x
      (Q.ginzburgPrefixGeneratorEndpoint v a.val) 0
      (Q.ginzburgPrefixCoefficientZeroCutEquiv k x v a.val g)
      (by rw [Q.ginzburgPrefixCoefficientZeroCutEquiv_coe];exact hg) ha
  exact (Q.ginzburgPrefixCoefficientZeroCutEquiv k x v a.val).injective
    (by simpa only [map_zero] using hzero)

end ASGinzburg.CutQuiver
