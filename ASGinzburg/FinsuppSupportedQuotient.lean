import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Isomorphisms

/-! The quotient of two actual supported finite-function spaces is
the supported space on their set difference. -/
namespace ASGinzburg
universe u v
variable (k : Type u) [Field k] (α : Type v)

noncomputable def supportedDifferenceProjection (s t : Set α) :
    Finsupp.supported k k t →ₗ[k] Finsupp.supported k k (t\s) := by
  classical
  exact (Finsupp.restrictDom k k (t\s)).comp (Finsupp.supported k k t).subtype

theorem supportedDifferenceProjection_surjective (s t : Set α) :
    Function.Surjective (supportedDifferenceProjection k α s t) := by
  classical
  intro f
  refine ⟨⟨f.val,Finsupp.supported_mono (Set.diff_subset) f.property⟩,?_⟩
  apply Subtype.ext
  change f.val.filter (· ∈ t\s)=f.val
  rw [Finsupp.filter_eq_self_iff]
  intro p hp
  exact f.property ((Finsupp.mem_support_iff).mpr hp)

theorem supportedDifferenceProjection_ker (s t : Set α) :
    LinearMap.ker (supportedDifferenceProjection k α s t)=
      (Finsupp.supported k k s).comap (Finsupp.supported k k t).subtype := by
  classical
  ext f
  rw [LinearMap.mem_ker,Submodule.mem_comap]
  change supportedDifferenceProjection k α s t f=0 ↔ f.val ∈ Finsupp.supported k k s
  rw [Finsupp.mem_supported']
  constructor
  · intro hf p hp
    by_cases ht : p∈t
    · have he := congrArg (fun g : Finsupp.supported k k (t\s) => g.val p) hf
      simpa [supportedDifferenceProjection,Finsupp.restrictDom_apply,
        Finsupp.filter_apply,ht,hp] using he
    · exact (Finsupp.mem_supported' k f.val).mp f.property p ht
  · intro hf
    apply Subtype.ext
    change f.val.filter (· ∈ t\s)=0
    rw [Finsupp.filter_eq_zero_iff]
    intro p hp
    exact hf p hp.2

noncomputable def supportedQuotientDifferenceEquiv (s t : Set α) :
    (Finsupp.supported k k t ⧸
      (Finsupp.supported k k s).comap (Finsupp.supported k k t).subtype) ≃ₗ[k]
        Finsupp.supported k k (t\s) :=
  (Submodule.quotEquivOfEq _ _
    (supportedDifferenceProjection_ker k α s t).symm).trans
      ((supportedDifferenceProjection k α s t).quotKerEquivOfSurjective
        (supportedDifferenceProjection_surjective k α s t))

theorem supportedQuotientDifferenceEquiv_mk (s t : Set α)
    (f : Finsupp.supported k k t) :
    supportedQuotientDifferenceEquiv k α s t (Submodule.Quotient.mk f)=
      supportedDifferenceProjection k α s t f := rfl

end ASGinzburg
