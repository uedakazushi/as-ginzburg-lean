import ASGinzburg.TriangleQuadraticResolution
import ASGinzburg.ModuleCatFourTermEuler
import ASGinzburg.CoproductRadicals
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Evaluation of the genuine finite quadratic resolution gives its
Euler dimension identity. No dimension recurrence is an extra hypothesis. -/

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def quadraticTripleComponentEquiv (i j : ℤ) :
    (A.rightModuleEvaluation j).obj (A.quadraticTriple i) ≃ₗ[k] (Fin 3 → A.Hom j i) :=
  A.rightFiniteCoproductPiEquiv (fun _ : Fin 3 => A.representable i) j

theorem quadraticTripleComponentFinite (i j : ℤ) :
    Module.Finite k ((A.rightModuleEvaluation j).obj (A.quadraticTriple i)) :=
  Module.Finite.of_injective (A.quadraticTripleComponentEquiv i j).toLinearMap
    (A.quadraticTripleComponentEquiv i j).injective

theorem quadraticTripleComponent_finrank (i j : ℤ) :
    Module.finrank k ((A.rightModuleEvaluation j).obj (A.quadraticTriple i)) =
      3 * Module.finrank k (A.Hom j i) := by
  rw [(A.quadraticTripleComponentEquiv i j).finrank_eq, Module.finrank_pi_fintype]
  simp

theorem simpleRightModule_component_finrank (i j : ℤ) :
    Module.finrank k ((A.rightModuleEvaluation j).obj (A.simpleRightModule i)) =
      if j = i then 1 else 0 := by
  classical
  by_cases h : j = i
  · subst j
    simp [A.simpleRightModule_diagonal_finrank]
  · letI : Subsingleton ((A.rightModuleEvaluation j).obj (A.simpleRightModule i)) :=
      ModuleCat.isZero_iff_subsingleton.mp (A.simpleRightModule_off_diagonal i j h)
    rw [if_neg h]
    exact Module.finrank_zero_of_subsingleton

/-- Euler's identity for each evaluated actual exact resolution (5.1). -/
theorem QuadraticASResolution.component_euler {A : ZAlgebra.{u,v} k} {i : ℤ}
    (R : A.QuadraticASResolution i) (j : ℤ) :
    (Module.finrank k (A.Hom j i) : ℤ) - 3 * Module.finrank k (A.Hom j (i - 1)) +
      3 * Module.finrank k (A.Hom j (i - 2)) - Module.finrank k (A.Hom j (i - 3)) =
      if j = i then 1 else 0 := by
  let F := A.rightModuleEvaluation j
  haveI := A.quadraticTripleComponentFinite (i - 1) j
  haveI := A.quadraticTripleComponentFinite (i - 2) j
  haveI : Module.Finite k (F.obj (A.representable i)) := by
    change Module.Finite k (A.Hom j i)
    infer_instance
  haveI := R.mono_d₃
  have he := moduleCatFourTermEuler (F.map R.d₃) (F.map R.d₂) (F.map R.d₁)
    (F.map (A.simpleRightModuleπ i))
    (R.exact₂.map F).moduleCat_range_eq_ker
    (R.exact₁.map F).moduleCat_range_eq_ker
    (R.exact₀.map F).moduleCat_range_eq_ker
  change (Module.finrank k (A.Hom j i) : ℤ) -
    Module.finrank k ((A.rightModuleEvaluation j).obj (A.quadraticTriple (i - 1))) +
    Module.finrank k ((A.rightModuleEvaluation j).obj (A.quadraticTriple (i - 2))) -
    Module.finrank k (A.Hom j (i - 3)) =
    Module.finrank k ((A.rightModuleEvaluation j).obj (A.simpleRightModule i)) at he
  rw [A.quadraticTripleComponent_finrank, A.quadraticTripleComponent_finrank,
    A.simpleRightModule_component_finrank] at he
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using he

end ASGinzburg.ZAlgebra
