import NormEuclidean.ChapterX.LocalLatticePatching
import NormEuclidean.ChapterX.ProjectedComplement

/-!
# The actual full finite module on a global complementary subspace

Intersecting a raw full finite integer-ring module with a field subspace
gives a full finite module on that subspace. Fractional quadratic values and
nonfree global modules are allowed. No small complementary module is supplied
as an assumption in the later contraction construction.
-/

noncomputable section

namespace NormEuclidean.ComplementIntersection

open IsDedekindDomain CompletedIntegralLattice

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]

/-- The literal intersection, regarded as a module on the field subspace. -/
def onSubspace (L : Submodule R V) (U : Submodule K V) : Submodule R U :=
  L.comap (U.subtype.restrictScalars R)

omit [IsFractionRing R K] in
/-- The intersection is finite even when the original global module is nonfree. -/
theorem onSubspace_fg (L : Submodule R V) (hL : L.FG) (U : Submodule K V) :
    (onSubspace R L U).FG := by
  let f := U.subtype.restrictScalars R
  have hmap : ((onSubspace R L U).map f).FG :=
    hL.of_le (Submodule.map_comap_le _ _)
  exact Submodule.fg_of_fg_map_injective f U.subtype_injective hmap

omit [IsDedekindDomain R] in
/-- Denominator clearing in the original module proves fullness of the actual
intersection, without choosing a lattice basis or assuming integral values. -/
theorem onSubspace_full (L : Submodule R V)
    (hL : Submodule.span K (L : Set V) = ⊤) (U : Submodule K V) :
    Submodule.span K (onSubspace R L U : Set U) = ⊤ := by
  apply LocalLatticePatching.full_of_denominators R
  intro x
  obtain ⟨d, hd, hdx⟩ := ScalarExtension.exists_denominator L hL (x : V)
  exact ⟨d, hd, hdx⟩

omit [IsDedekindDomain R] [IsFractionRing R K] in
/-- Inclusion of the actual intersection in the original module is literal. -/
theorem onSubspace_le (L : Submodule R V) (U : Submodule K V)
    (x : U) (hx : x ∈ onSubspace R L U) : (x : V) ∈ L := hx

omit [IsDedekindDomain R] [IsFractionRing R K] in
/-- Its image in the original space is exactly the ordinary module intersection. -/
theorem map_onSubspace (L : Submodule R V) (U : Submodule K V) :
    (onSubspace R L U).map (U.subtype.restrictScalars R) = L ⊓ U.restrictScalars R := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.property⟩
  · rintro ⟨hxL, hxU⟩
    exact ⟨⟨x, hxU⟩, hxL, rfl⟩

end NormEuclidean.ComplementIntersection
