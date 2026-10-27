import NormEuclidean.Hyperbolic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Integral lattices without freeness

All main algebraic constructions apply to an arbitrary submodule. The
`Lattice` structure records finite generation and spanning explicitly,
but no theorem in the descent mechanism silently assumes a basis.
-/

namespace NormEuclidean

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (R : Subring K) (Q : QuadraticForm K V)

/-- A finitely generated, full integral lattice, with no freeness field. -/
structure Lattice where
  carrier : Submodule R V
  finite : carrier.FG
  full : Submodule.span K (carrier : Set V) = ⊤
  integral : ∀ v ∈ carrier, Q v ∈ R

namespace Hyperbolic

variable {R Q} (L : Submodule R V)

def Mem (z : Hyperbolic K V) : Prop := z.1 ∈ L ∧ z.2.1 ∈ R ∧ z.2.2 ∈ R

@[simp] theorem mem_e : Mem L (e : Hyperbolic K V) :=
  ⟨L.zero_mem, R.one_mem, R.zero_mem⟩

@[simp] theorem mem_f : Mem L (f : Hyperbolic K V) :=
  ⟨L.zero_mem, R.zero_mem, R.one_mem⟩

@[simp] theorem mem_swap (z : Hyperbolic K V) : Mem L (swap z) ↔ Mem L z := by
  simp only [Mem, swap]
  exact ⟨fun h => ⟨h.1, h.2.2, h.2.1⟩, fun h => ⟨h.1, h.2.2, h.2.1⟩⟩

theorem polar_mem (hQ : ∀ v ∈ L, Q v ∈ R) {u v : V} (hu : u ∈ L) (hv : v ∈ L) :
    polar Q u v ∈ R :=
  R.sub_mem (R.sub_mem (hQ _ (L.add_mem hu hv)) (hQ _ hu)) (hQ _ hv)

theorem mem_transvection (hQ : ∀ v ∈ L, Q v ∈ R) {u : V} (hu : u ∈ L)
    {z : Hyperbolic K V} (hz : Mem L z) : Mem L (transvection Q u z) := by
  rcases hz with ⟨hv, ha, hb⟩
  refine ⟨L.sub_mem hv ?_, ha, R.sub_mem (R.add_mem hb (polar_mem L hQ hv hu))
    (R.mul_mem ha (hQ _ hu))⟩
  exact L.smul_mem (⟨z.2.1, ha⟩ : R) hu

/-- An ambient linear isometry preserving the integral lattice in both directions. -/
structure Aut where
  toLinearEquiv : Hyperbolic K V ≃ₗ[K] Hyperbolic K V
  q_eq : ∀ z, q Q (toLinearEquiv z) = q Q z
  mem_iff : ∀ z, Mem L (toLinearEquiv z) ↔ Mem L z

namespace Aut

instance : CoeFun (Aut (Q := Q) L) (fun _ => Hyperbolic K V → Hyperbolic K V) :=
  ⟨fun g => g.toLinearEquiv⟩

@[simp] theorem coe_toLinearEquiv (g : Aut (Q := Q) L) (z : Hyperbolic K V) :
    g.toLinearEquiv z = g z := rfl

def refl : Aut (Q := Q) L where
  toLinearEquiv := LinearEquiv.refl K _
  q_eq := fun _ => rfl
  mem_iff := fun _ => Iff.rfl

def comp (g h : Aut (Q := Q) L) : Aut (Q := Q) L where
  toLinearEquiv := h.toLinearEquiv.trans g.toLinearEquiv
  q_eq := fun z => (g.q_eq (h z)).trans (h.q_eq z)
  mem_iff := fun z => (g.mem_iff (h z)).trans (h.mem_iff z)

@[simp] theorem refl_apply (z : Hyperbolic K V) : refl (Q := Q) L z = z := rfl
@[simp] theorem comp_apply (g h : Aut (Q := Q) L) (z : Hyperbolic K V) :
    comp L g h z = g (h z) := rfl

def symm (g : Aut (Q := Q) L) : Aut (Q := Q) L where
  toLinearEquiv := g.toLinearEquiv.symm
  q_eq := fun z => by
    have h := g.q_eq (g.toLinearEquiv.symm z)
    simpa using h.symm
  mem_iff := fun z => by
    have h := g.mem_iff (g.toLinearEquiv.symm z)
    simpa using h.symm

@[simp] theorem symm_apply_apply (g : Aut (Q := Q) L) (z : Hyperbolic K V) :
    symm L g (g z) = z := g.toLinearEquiv.symm_apply_apply z

@[simp] theorem apply_symm_apply (g : Aut (Q := Q) L) (z : Hyperbolic K V) :
    g (symm L g z) = z := g.toLinearEquiv.apply_symm_apply z

@[simp] theorem map_zero (g : Aut (Q := Q) L) : g 0 = 0 := g.toLinearEquiv.map_zero
@[simp] theorem map_smul (g : Aut (Q := Q) L) (a : K) (z : Hyperbolic K V) :
    g (a • z) = a • g z := g.toLinearEquiv.map_smul a z

theorem injective (g : Aut (Q := Q) L) : Function.Injective g := g.toLinearEquiv.injective

def swap : Aut (Q := Q) L where
  toLinearEquiv := swapEquiv
  q_eq := q_swap Q
  mem_iff := mem_swap L

@[simp] theorem swap_apply (z : Hyperbolic K V) :
    swap (Q := Q) L z = Hyperbolic.swap z := rfl

def transvection (hQ : ∀ v ∈ L, Q v ∈ R) (u : V) (hu : u ∈ L) : Aut (Q := Q) L where
  toLinearEquiv := transvectionEquiv Q u
  q_eq := q_transvection Q u
  mem_iff := fun z => by
    constructor
    · intro hz
      change Mem L (Hyperbolic.transvection Q u z) at hz
      have h := mem_transvection L hQ (L.neg_mem hu) hz
      simpa using h
    · exact mem_transvection L hQ hu

@[simp] theorem transvection_apply (hQ : ∀ v ∈ L, Q v ∈ R) (u : V) (hu : u ∈ L)
    (z : Hyperbolic K V) : transvection L hQ u hu z = Hyperbolic.transvection Q u z := rfl

end Aut

/-- The coefficient set, which does not require a chosen lattice basis. -/
def coefficientSet (z : Hyperbolic K V) : Set K := {a | Mem L (a • z)}

theorem coefficientSet_aut (g : Aut (Q := Q) L) (z : Hyperbolic K V) :
    coefficientSet L (g z) = coefficientSet L z := by
  ext a
  simp only [coefficientSet, Set.mem_setOf_eq, ← Aut.map_smul]
  exact g.mem_iff (a • z)

@[simp] theorem coefficientSet_smul_e (c : K) :
    coefficientSet L (c • (e : Hyperbolic K V)) = {a | a * c ∈ R} := by
  ext a
  simp [coefficientSet, Mem, e]

end Hyperbolic
end NormEuclidean
