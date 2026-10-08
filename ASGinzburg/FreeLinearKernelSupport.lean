import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! A free linear evaluation can have relations only on the discarded basis
vectors when the remaining images are linearly independent. -/
namespace ASGinzburg
universe u v w
variable {k : Type u} [Field k] {I : Type v} {V : Type w}
  [AddCommGroup V] [Module k V]

theorem linearCombination_ker_le_supported (v : I → V) (S : Set I)
    (hzero : ∀ i ∈ S, v i=0) (hind : LinearIndepOn k v Sᶜ) :
    LinearMap.ker (Finsupp.linearCombination k v) ≤ Finsupp.supported k k S := by
  classical
  have hlong : Finsupp.supported k k S ≤ LinearMap.ker (Finsupp.linearCombination k v) := by
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro x ⟨i,hi,rfl⟩
    simp [hzero i hi]
  intro f hf
  let short := f.filter (fun i => i ∉ S)
  let long := f.filter (fun i => i ∈ S)
  have hshortmem : short ∈ Finsupp.supported k k Sᶜ := by
    apply (Finsupp.mem_supported' k _).mpr
    intro i hi
    have h : i ∈ S := by simpa using hi
    simp [short,h]
  have hlongmem : long ∈ Finsupp.supported k k S := by
    apply (Finsupp.mem_supported' k _).mpr
    intro i hi
    simp [long,hi]
  have hlongzero := hlong hlongmem
  have hsplit : short+long=f := by
    ext i
    by_cases hi : i∈S <;> simp [short,long,hi]
  have hshortzero : Finsupp.linearCombination k v short = 0 := by
    have H := congrArg (Finsupp.linearCombination k v) hsplit
    rw [map_add,hlongzero,add_zero,hf] at H
    exact H
  have hs : short=0 := (linearIndepOn_iff.mp hind) short hshortmem hshortzero
  apply (Finsupp.mem_supported' k _).mpr
  intro i hi
  have H := congrArg (fun f : I →₀ k => f i) hs
  simpa [short,hi] using H

end ASGinzburg
