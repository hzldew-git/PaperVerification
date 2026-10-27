/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.QuadraticSpace.RepresentationRange
import Bong.QuadraticSpace.FieldDiagonalization

/-!
# Orthogonal complement of a field-space representation

A represented nondegenerate space splits from its host by an actual
isometry. This field construction has no lattice or valuation input.
-/

namespace Bong.QuadraticSpace.Representation

universe u v w

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}

/-- The represented field subspace of the host. -/
def representedRange (f : Representation r q) : Submodule K V :=
  LinearMap.range f.toLinearMap

/-- Its orthogonal complement in the host. -/
def representedResidual (f : Representation r q) : Submodule K V :=
  q.bilin.orthogonal f.representedRange

omit [FiniteDimensional K W] in
theorem representedRange_isCompl_residual (f : Representation r q) :
    IsCompl f.representedRange f.representedResidual := by
  exact q.bilin.isCompl_orthogonal_of_restrict_nondegenerate
    q.isSymm.isRefl f.range_nondegenerate

noncomputable def representedSumLinearEquiv (f : Representation r q) :
    (f.representedRange × f.representedResidual) ≃ₗ[K] V :=
  f.representedRange.prodEquivOfIsCompl f.representedResidual
    f.representedRange_isCompl_residual

omit [FiniteDimensional K W] in
theorem representedResidual_nondegenerate (f : Representation r q) :
    (q.bilin.restrict f.representedResidual).Nondegenerate := by
  have horth : q.bilin.orthogonal f.representedResidual = f.representedRange :=
    q.bilin.orthogonal_orthogonal q.nondegenerate q.isSymm.isRefl
      f.representedRange
  rw [q.bilin.restrict_nondegenerate_iff_isCompl_orthogonal
    q.isSymm.isRefl, horth]
  exact f.representedRange_isCompl_residual.symm

/-- The nondegenerate residual quadratic space. -/
def representedResidualSpace (f : Representation r q) :
    QuadraticSpace K f.representedResidual :=
  q.restrict f.representedResidual f.representedResidual_nondegenerate

/-- The host is the target plus its orthogonal residual. -/
noncomputable def representedSumIsometry (f : Representation r q) :
    Isometry (r.orthogonalSum f.representedResidualSpace) q where
  toLinearEquiv :=
    (f.rangeEquiv.prodCongr (LinearEquiv.refl K f.representedResidual)).trans
      f.representedSumLinearEquiv
  map_bilin := by
    intro x y
    change q.bilin (f.toLinearMap x.1 + (x.2 : V))
        (f.toLinearMap y.1 + (y.2 : V)) =
      r.bilin x.1 y.1 + q.bilin (x.2 : V) (y.2 : V)
    simp only [map_add, LinearMap.add_apply]
    have hxy : q.bilin (f.toLinearMap x.1) (y.2 : V) = 0 :=
      y.2.property _ ⟨x.1, rfl⟩
    have hyx : q.bilin (x.2 : V) (f.toLinearMap y.1) = 0 := by
      rw [q.isSymm.eq]
      exact x.2.property _ ⟨y.1, rfl⟩
    rw [hxy, hyx, f.map_bilin]
    ring

theorem representedSum_finrank (f : Representation r q) :
    Module.finrank K W + Module.finrank K f.representedResidual =
      Module.finrank K V := by
  simpa only [Module.finrank_prod] using
    f.representedSumIsometry.toLinearEquiv.finrank_eq

end Bong.QuadraticSpace.Representation
