import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic

/-!
# The top cohomology calculation used in Proposition 1.3

For a cochain complex supported in degrees 0,...,3, the third cohomology
is the cokernel of d². Here it is computed concretely as a quotient by
the range. No identification with an Ext group is assumed or asserted.
-/

namespace ASGinzburg

universe u v w

variable {k : Type u} [Field k]
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

abbrev TopCohomology (d : M →ₗ[k] N) := N ⧸ LinearMap.range d

theorem map_from_zero_domain_eq_zero [Subsingleton M] (d : M →ₗ[k] N) : d = 0 := by
  ext m
  have hm : m = 0 := Subsingleton.elim _ _
  simp [hm]

noncomputable def topCohomologyEquiv [Subsingleton M] (d : M →ₗ[k] N) :
    TopCohomology d ≃ₗ[k] N :=
  (LinearMap.range d).quotEquivOfEqBot (by
    rw [map_from_zero_domain_eq_zero d, LinearMap.range_zero])

theorem topCohomology_finrank [Subsingleton M] (d : M →ₗ[k] N) :
    Module.finrank k (TopCohomology d) = Module.finrank k N :=
  (topCohomologyEquiv d).finrank_eq

theorem topCohomology_field_finrank [Subsingleton M] (d : M →ₗ[k] k) :
    Module.finrank k (TopCohomology d) = 1 := by
  rw [topCohomology_finrank]
  exact Module.finrank_self k

end ASGinzburg
