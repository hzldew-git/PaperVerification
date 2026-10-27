import Mathlib.RingTheory.LocalProperties.Submodule

/-!
# Recovering a submodule from its maximal localizations

O'Meara's local-to-global lattice arguments use the standard fact that two
global lattices are equal once their localizations agree at every finite prime.
This file records the algebraic core of that step with actual localized
modules.  It does not identify localization with completion; that comparison
is a separate theorem in the completed-lattice layer.
-/

noncomputable section

namespace NormEuclidean.LocalizationLatticeRecovery

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Two submodules are equal if their images in the localized module agree at
every maximal ideal. -/
theorem submodule_eq_of_maximal_localizations_eq
    {A B : Submodule R M}
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      A.localized' (Localization.AtPrime P) P.primeCompl
          (LocalizedModule.mkLinearMap P.primeCompl M) =
        B.localized' (Localization.AtPrime P) P.primeCompl
          (LocalizedModule.mkLinearMap P.primeCompl M)) :
    A = B := by
  exact Submodule.eq_of_localization_maximal
    (fun P => Localization.AtPrime P)
    (fun P => LocalizedModule P.primeCompl M)
    (fun P => LocalizedModule.mkLinearMap P.primeCompl M)
    h

end NormEuclidean.LocalizationLatticeRecovery
