import NormEuclidean.ChapterX.DualVolume
import NormEuclidean.GeneralContent

/-!
# Coefficient and pairing ideals of an isotropic ray

The coefficient ideal of a nonzero vector and its actual pairing-image ideal
have product between the intrinsic volume and the integer ring. This follows
from the proved volume action on the literal integral dual. The ideal bounds
do not assume an integral basis, maximal lattice or hyperbolic splitting.
-/

noncomputable section

namespace NormEuclidean.IsotropicRayIdeals

open Module IntegralVolume
open scoped nonZeroDivisors

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]

/-- The actual fractional ideal of pairings with vectors of the source module. -/
def pairingIdeal (B : LinearMap.BilinForm K V) (L : Submodule (integerSubring K) V)
    (hfg : L.FG) (e : V) : FractionalIdeal (integerSubring K)⁰ K :=
  ⟨L.map ((B e).restrictScalars (integerSubring K)),
    FractionalIdeal.isFractional_of_fg (hfg.map _)⟩

theorem mem_pairingIdeal (B : LinearMap.BilinForm K V)
    (L : Submodule (integerSubring K) V) (hfg : L.FG) (e : V) (a : K) :
    a ∈ pairingIdeal B L hfg e ↔ ∃ u ∈ L, B e u = a := Iff.rfl

/-- A nonzero ray in a regular space has nonzero actual pairing ideal. -/
theorem pairingIdeal_ne_zero (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (L : Submodule (integerSubring K) V) (hfg : L.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤) (e : V) (he : e ≠ 0) :
    pairingIdeal B L hfg e ≠ 0 := by
  intro hzero
  have hmap : B e = 0 := by
    apply LinearMap.ext_on hfull
    intro y hy
    have hmem : B e y ∈ pairingIdeal B L hfg e := ⟨y, hy, rfl⟩
    rw [hzero, FractionalIdeal.mem_zero_iff] at hmem
    exact hmem
  exact he (hB.1 e (by intro y; rw [hmap]; rfl))

/-- Integral half-polar scale is literal integrality of every source pairing. -/
theorem pairing_mem_integer (Q : QuadraticForm K V) (L : Lattice (integerSubring K) Q)
    (hs : L.scaleIdeal ≤ 1) (x y : V) (hx : x ∈ L.carrier) (hy : y ∈ L.carrier) :
    halfPolar Q x y ∈ integerSubring K := by
  have h := hs (L.halfPolar_mem_scaleIdeal ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h
  rw [← hr]
  exact r.property

variable [FiniteDimensional K V]

/-- The actual product of ray coefficient and pairing ideals is bounded by
volume below and the integer ring above. The ray need not be isotropic yet. -/
theorem product_bounds (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice (integerSubring K) Q) (hs : L.scaleIdeal ≤ 1) (e : V) (he : e ≠ 0) :
    let I := GeneralContent.coefficientIdeal L.carrier L.finite e he
    let J := pairingIdeal (halfPolar Q) L.carrier L.finite e
    L.volumeIdeal ≤ I * J ∧ I * J ≤ 1 := by
  let I := GeneralContent.coefficientIdeal L.carrier L.finite e he
  let J := pairingIdeal (halfPolar Q) L.carrier L.finite e
  have hJ : J ≠ 0 := pairingIdeal_ne_zero (halfPolar Q)
    (SpinorBridge.quadraticSpace Q hQ).nondegenerate L.carrier L.finite L.full e he
  have hleft : L.volumeIdeal * J⁻¹ ≤ I := by
    apply FractionalIdeal.mul_le.mpr
    intro a ha b hb
    have hdual : b • e ∈ (halfPolar Q).dualSubmodule L.carrier := by
      intro y hy
      have hby := (FractionalIdeal.mem_inv_iff hJ).mp hb (halfPolar Q e y)
        ((mem_pairingIdeal _ _ _ _ _).mpr ⟨y, hy, rfl⟩)
      rw [LinearMap.BilinForm.smul_left]
      exact Submodule.mem_one.mpr ((FractionalIdeal.mem_one_iff _).mp hby)
    change (a * b) • e ∈ L.carrier
    rw [mul_smul]
    apply DualVolume.volume_smul_dual_mem (halfPolar Q) L.carrier
      (fun x hx y hy ↦ pairing_mem_integer Q L hs x y hx hy) a _ (b • e) hdual
    exact ha
  refine ⟨?_, ?_⟩
  · calc
      L.volumeIdeal = (L.volumeIdeal * J⁻¹) * J := by
        rw [mul_assoc, inv_mul_cancel₀ hJ, mul_one]
      _ ≤ I * J := mul_le_mul_left hleft J
  · apply FractionalIdeal.mul_le.mpr
    intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := (mem_pairingIdeal _ _ _ _ _).mp hb
    have hae : a • e ∈ L.carrier := ha
    have hint := pairing_mem_integer Q L hs (a • e) u hae hu
    rw [LinearMap.BilinForm.smul_left] at hint
    exact (FractionalIdeal.mem_one_iff _).mpr ⟨⟨_, hint⟩, rfl⟩

end NormEuclidean.IsotropicRayIdeals
