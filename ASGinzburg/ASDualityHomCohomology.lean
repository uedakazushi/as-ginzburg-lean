import ASGinzburg.ASResolutionHomComplex
import ASGinzburg.ASDualityHomTerms

/-!
# Hom cohomology in the nonzero position used in Proposition 1.3

The actual Hom complex for the supplied resolution of s_(tau v) into P_v
has terms 0,0,0,k and zero afterwards. The resulting H^3 is k. The actual
derived Ext^3 calculation and its degree-three comparison are constructed
separately in ASDualityExt and ASDualityDimension.
-/

namespace ASGinzburg.ZAlgebra.ASResolution
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {Q : CutQuiver}

theorem homComplex_isZero_ge_four {v : Q.LiftVertex} (R : A.ASResolution Q v)
    (N : A.RightModule) (n : ℕ) : IsZero ((R.homComplex N).X (n + 4)) := by
  apply ModuleCat.isZero_of_iff_subsingleton.mpr
  exact ⟨fun f g => (R.complex_isZero_ge_four n).eq_of_src f g⟩

variable (v : Q.LiftVertex) (R : A.ASResolution Q (Q.tau v))

theorem homComplex_tau_representable_low_terms_isZero (n : ℕ) (hn : n < 3) :
    IsZero ((R.homComplex (A.representable (Q.height v))).X n) := by
  apply ModuleCat.isZero_of_iff_subsingleton.mpr
  constructor
  intro f g
  rcases n with _ | _ | _ | n
  · rw [A.asDualityHomTerm₀_zero Q v f, A.asDualityHomTerm₀_zero Q v g]
  · rw [A.asDualityHomTerm₁_zero Q v f, A.asDualityHomTerm₁_zero Q v g]
  · rw [A.asDualityHomTerm₂_zero Q v f, A.asDualityHomTerm₂_zero Q v g]
  · omega

noncomputable def homComplex_tau_representable_top_homologyLinearEquiv :
    (R.homComplex (A.representable (Q.height v))).homology 3 ≃ₗ[k] k := by
  let C := R.homComplex (A.representable (Q.height v))
  have hf : (C.sc' 2 3 4).f = 0 := by
    change C.d 2 3 = 0
    exact (R.homComplex_tau_representable_low_terms_isZero v 2 (by decide)).eq_of_src _ _
  have hg : (C.sc' 2 3 4).g = 0 := by
    change C.d 3 4 = 0
    exact (R.homComplex_isZero_ge_four (A.representable (Q.height v)) 0).eq_of_tgt _ _
  exact ((C.homologyIsoSc' 2 3 4 (by simp) (by simp)) ≪≫
    (ShortComplex.HomologyData.ofZeros (C.sc' 2 3 4) hf hg).left.homologyIso).toLinearEquiv.trans
      (A.asDualityHomTerm₃Equiv Q v)

theorem homComplex_tau_representable_low_homology_isZero (n : ℕ) (hn : n < 3) :
    IsZero ((R.homComplex (A.representable (Q.height v))).homology n) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    (R.homComplex_tau_representable_low_terms_isZero v n hn)

theorem homComplex_tau_representable_high_homology_isZero (n : ℕ) :
    IsZero ((R.homComplex (A.representable (Q.height v))).homology (n + 4)) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    (R.homComplex_isZero_ge_four (A.representable (Q.height v)) n)

theorem homComplex_tau_representable_top_homology_finrank :
    Module.finrank k ((R.homComplex (A.representable (Q.height v))).homology 3) = 1 :=
  (R.homComplex_tau_representable_top_homologyLinearEquiv v).finrank_eq.trans
    (Module.finrank_self k)

end ASGinzburg.ZAlgebra.ASResolution
