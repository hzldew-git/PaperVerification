import NormEuclidean.Descent

/-!
# Hyperbolic cancellation without a freeness assumption

The purely algebraic cancellation argument is separated from the norm descent:
primitive isotropic orbit transitivity is the only input to the theorem below.
Both lattices are arbitrary submodules of their ambient quadratic spaces.
-/

namespace NormEuclidean

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable {R : Subring K} {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
variable {L : Submodule R V} {L' : Submodule R W}

/-- An isometry of ambient quadratic spaces identifying the two integral lattices. -/
structure LatticeIsometry (Q : QuadraticForm K V) (Q' : QuadraticForm K W)
    (L : Submodule R V) (L' : Submodule R W) where
  toLinearEquiv : V ≃ₗ[K] W
  q_eq : ∀ v, Q' (toLinearEquiv v) = Q v
  mem_iff : ∀ v, toLinearEquiv v ∈ L' ↔ v ∈ L

namespace LatticeIsometry

/-- The induced integral isometry, expressed as an `R`-linear equivalence
of the lattice subtypes. This is the module-level isometry in the manuscript. -/
def toModuleEquiv (φ : LatticeIsometry Q Q' L L') : L ≃ₗ[R] L' where
  toFun := fun v => ⟨φ.toLinearEquiv v, (φ.mem_iff v).2 v.property⟩
  invFun := fun w => ⟨φ.toLinearEquiv.symm w,
    (φ.mem_iff (φ.toLinearEquiv.symm w)).1 (by
      rw [φ.toLinearEquiv.apply_symm_apply]
      exact w.property)⟩
  left_inv := fun v => by
    apply Subtype.ext
    exact φ.toLinearEquiv.symm_apply_apply v
  right_inv := fun w => by
    apply Subtype.ext
    exact φ.toLinearEquiv.apply_symm_apply w
  map_add' := fun v w => by
    apply Subtype.ext
    exact φ.toLinearEquiv.map_add v w
  map_smul' := fun a v => by
    apply Subtype.ext
    exact φ.toLinearEquiv.map_smul (a : K) (v : V)

@[simp] theorem toModuleEquiv_apply (φ : LatticeIsometry Q Q' L L') (v : L) :
    (φ.toModuleEquiv v : W) = φ.toLinearEquiv (v : V) := rfl

/-- The induced integral module equivalence preserves the quadratic form. -/
@[simp] theorem toModuleEquiv_q (φ : LatticeIsometry Q Q' L L') (v : L) :
    Q' (φ.toModuleEquiv v : W) = Q (v : V) := φ.q_eq v

end LatticeIsometry

namespace Hyperbolic

/-- An isometry between two possibly different hyperbolic lattice extensions. -/
structure Isometry (Q : QuadraticForm K V) (Q' : QuadraticForm K W)
    (L : Submodule R V) (L' : Submodule R W) where
  toLinearEquiv : Hyperbolic K V ≃ₗ[K] Hyperbolic K W
  q_eq : ∀ z, q Q' (toLinearEquiv z) = q Q z
  mem_iff : ∀ z, Mem L' (toLinearEquiv z) ↔ Mem L z

namespace Isometry

instance : CoeFun (Isometry Q Q' L L')
    (fun _ => Hyperbolic K V → Hyperbolic K W) := ⟨fun φ => φ.toLinearEquiv⟩

@[simp] theorem map_add (φ : Isometry Q Q' L L') (x y : Hyperbolic K V) :
    φ (x + y) = φ x + φ y := φ.toLinearEquiv.map_add x y

@[simp] theorem map_smul (φ : Isometry Q Q' L L') (a : K) (x : Hyperbolic K V) :
    φ (a • x) = a • φ x := φ.toLinearEquiv.map_smul a x

def symm (φ : Isometry Q Q' L L') : Isometry Q' Q L' L where
  toLinearEquiv := φ.toLinearEquiv.symm
  q_eq := fun z => by
    have h := φ.q_eq (φ.toLinearEquiv.symm z)
    simpa using h.symm
  mem_iff := fun z => by
    have h := φ.mem_iff (φ.toLinearEquiv.symm z)
    simpa using h.symm

@[simp] theorem symm_apply_apply (φ : Isometry Q Q' L L') (z : Hyperbolic K V) :
    φ.symm (φ z) = z := φ.toLinearEquiv.symm_apply_apply z

@[simp] theorem apply_symm_apply (φ : Isometry Q Q' L L') (z : Hyperbolic K W) :
    φ (φ.symm z) = z := φ.toLinearEquiv.apply_symm_apply z

/-- Postcompose a lattice isometry with an integral automorphism of its target. -/
def postcomp (φ : Isometry Q Q' L L') (g : Aut (Q := Q') L') :
    Isometry Q Q' L L' where
  toLinearEquiv := φ.toLinearEquiv.trans g.toLinearEquiv
  q_eq := fun z => (g.q_eq (φ z)).trans (φ.q_eq z)
  mem_iff := fun z => (g.mem_iff (φ z)).trans (φ.mem_iff z)

@[simp] theorem postcomp_apply (φ : Isometry Q Q' L L') (g : Aut (Q := Q') L')
    (z : Hyperbolic K V) : φ.postcomp g z = g (φ z) := rfl

theorem coefficientSet_eq (φ : Isometry Q Q' L L') (z : Hyperbolic K V) :
    coefficientSet L' (φ z) = coefficientSet L z := by
  ext a
  change Mem L' (a • φ z) ↔ Mem L (a • z)
  rw [← φ.map_smul]
  exact φ.mem_iff _

end Isometry

/-- Polarization without division by two. -/
def pairing (Q : QuadraticForm K V) (x y : Hyperbolic K V) : K :=
  q Q (x + y) - q Q x - q Q y

@[simp] theorem q_e : q Q (e : Hyperbolic K V) = 0 := by simp [q, e]
@[simp] theorem q_f : q Q (f : Hyperbolic K V) = 0 := by simp [q, f]

@[simp] theorem pairing_e (z : Hyperbolic K V) : pairing Q z e = z.2.2 := by
  simp [pairing, q, e]
  ring

@[simp] theorem pairing_f (z : Hyperbolic K V) : pairing Q z f = z.2.1 := by
  simp [pairing, q, f]
  ring

theorem Isometry.pairing_eq (φ : Isometry Q Q' L L') (x y : Hyperbolic K V) :
    pairing Q' (φ x) (φ y) = pairing Q x y := by
  unfold pairing
  rw [← φ.map_add, φ.q_eq, φ.q_eq, φ.q_eq]

theorem Isometry.map_b (φ : Isometry Q Q' L L') (he : φ e = e)
    (z : Hyperbolic K V) : (φ z).2.2 = z.2.2 := by
  have h := φ.pairing_eq z e
  simpa only [he, pairing_e] using h

theorem Isometry.map_a (φ : Isometry Q Q' L L') (hf : φ f = f)
    (z : Hyperbolic K V) : (φ z).2.1 = z.2.1 := by
  have h := φ.pairing_eq z f
  simpa only [hf, pairing_f] using h

/-- The integral orthogonal complement is exactly the original lattice. -/
theorem integral_orthogonal_complement (z : Hyperbolic K V) :
    (Mem L z ∧ pairing Q z e = 0 ∧ pairing Q z f = 0) ↔
      ∃ v ∈ L, z = (v, 0, 0) := by
  simp only [pairing_e, pairing_f]
  constructor
  · rintro ⟨hz, hb, ha⟩
    exact ⟨z.1, hz.1, Prod.ext rfl (Prod.ext ha hb)⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨hv, R.zero_mem, R.zero_mem⟩, rfl, rfl⟩

/-- Inclusion of the original quadratic space in its hyperbolic extension. -/
def embed (v : V) : Hyperbolic K V := (v, 0, 0)

omit [Module K V] in
@[simp] theorem embed_add (v w : V) :
    (embed (v + w) : Hyperbolic K V) = embed v + embed w := by simp [embed]

@[simp] theorem embed_smul (a : K) (v : V) :
    (embed (a • v) : Hyperbolic K V) = a • embed v := by simp [embed]

@[simp] theorem q_embed (v : V) : q Q (embed v) = Q v := by simp [q, embed]

@[simp] theorem mem_embed (v : V) : Mem L (embed v) ↔ v ∈ L := by simp [Mem, embed]

namespace Isometry

theorem map_embed (φ : Isometry Q Q' L L') (he : φ e = e) (hf : φ f = f)
    (v : V) : φ (embed v) = embed (φ (embed v)).1 := by
  apply Prod.ext
  · rfl
  · exact Prod.ext (φ.map_a hf (embed v)) (φ.map_b he (embed v))

theorem symm_e (φ : Isometry Q Q' L L') (he : φ e = e) : φ.symm e = e := by
  rw [← he, symm_apply_apply]

theorem symm_f (φ : Isometry Q Q' L L') (hf : φ f = f) : φ.symm f = f := by
  rw [← hf, symm_apply_apply]

/-- Restrict an isometry fixing the hyperbolic basis to the original spaces. -/
def restrict (φ : Isometry Q Q' L L') (he : φ e = e) (hf : φ f = f) :
    LatticeIsometry Q Q' L L' where
  toLinearEquiv := {
    toFun := fun v => (φ (embed v)).1
    invFun := fun w => (φ.symm (embed w)).1
    left_inv := fun v => by
      have h := φ.symm_apply_apply (embed v)
      rw [φ.map_embed he hf v] at h
      exact congrArg Prod.fst h
    right_inv := fun w => by
      have h := φ.apply_symm_apply (embed w)
      rw [φ.symm.map_embed (φ.symm_e he) (φ.symm_f hf) w] at h
      exact congrArg Prod.fst h
    map_add' := fun v w => by
      rw [embed_add, map_add]
      rfl
    map_smul' := fun a v => by
      rw [embed_smul, map_smul]
      rfl }
  q_eq := fun v => by
    have h := φ.q_eq (embed v)
    rw [φ.map_embed he hf v, q_embed, q_embed] at h
    exact h
  mem_iff := fun v => by
    have h := φ.mem_iff (embed v)
    rw [φ.map_embed he hf v, mem_embed, mem_embed] at h
    exact h

/-- Once `e` is fixed, an integral transvection fixes `f` as well. -/
theorem normalize_partner (φ : Isometry Q Q' L L')
    (hQ' : ∀ w ∈ L', Q' w ∈ R) (he : φ e = e) :
    ∃ g : Aut (Q := Q') L', g (φ e) = e ∧ g (φ f) = f := by
  let w : W := (φ f).1
  have hw : w ∈ L' := ((φ.mem_iff f).2 (mem_f L)).1
  have hb : (φ f).2.2 = 1 := φ.map_b he f
  have hq : Q' w + (φ f).2.1 = 0 := by
    have h := φ.q_eq f
    rw [q_f] at h
    simpa only [q, hb, mul_one] using h
  have ha : (φ f).2.1 = -Q' w := by
    linear_combination hq
  have hpartner : φ f = (w, -Q' w, 1) :=
    Prod.ext rfl (Prod.ext ha hb)
  let s := Aut.swap (Q := Q') L'
  let t := Aut.transvection L' hQ' w hw
  let g := Aut.comp L' s (Aut.comp L' t s)
  refine ⟨g, ?_, ?_⟩
  · change swap (transvection Q' w (swap (φ e))) = e
    rw [he, conjugate_fixes_e]
  · change swap (transvection Q' w (swap (φ f))) = f
    rw [hpartner, conjugate_normalizes_partner]

end Isometry

/-- Pure algebraic cancellation from transitivity on primitive isotropic vectors.
No finite generation, basis, or freeness assumption is needed for this step. -/
theorem cancellation_of_primitive_orbits
    (hQ' : ∀ w ∈ L', Q' w ∈ R)
    (horbit : ∀ z : Hyperbolic K W, Mem L' z → z ≠ 0 → q Q' z = 0 →
      coefficientSet L' z = (R : Set K) →
      ∃ g : Aut (Q := Q') L', g z = e)
    (φ : Isometry Q Q' L L') : Nonempty (LatticeIsometry Q Q' L L') := by
  have hmem : Mem L' (φ e) := (φ.mem_iff e).2 (mem_e L)
  have hiso : q Q' (φ e) = 0 := (φ.q_eq e).trans q_e
  have hprim : coefficientSet L' (φ e) = (R : Set K) := by
    rw [φ.coefficientSet_eq]
    ext a
    simp [coefficientSet, Mem, e]
  have hne : φ e ≠ 0 := by
    intro hz
    have he0 : (e : Hyperbolic K V) = 0 :=
      φ.toLinearEquiv.injective (by simpa using hz)
    have hone : (1 : K) = 0 := congrArg (fun z : Hyperbolic K V => z.2.1) he0
    exact one_ne_zero hone
  obtain ⟨g, hg⟩ := horbit (φ e) hmem hne hiso hprim
  let ψ := φ.postcomp g
  have he : ψ e = e := hg
  obtain ⟨η, hηe, hηf⟩ := ψ.normalize_partner hQ' he
  exact ⟨(ψ.postcomp η).restrict hηe hηf⟩

/-- Lemma 3.1 (reference manuscript): an anisotropic norm-Euclidean integral lattice cancels
from an isometry after adjoining one hyperbolic plane. The two lattices
need not be free modules. -/
theorem norm_euclidean_cancellation (N : IntegralNorm R)
    (hQ' : ∀ w ∈ L', Q' w ∈ R) (hA' : Q'.Anisotropic)
    (hE' : IsNormEuclidean N Q' L')
    (φ : Isometry Q Q' L L') : Nonempty (LatticeIsometry Q Q' L L') := by
  apply cancellation_of_primitive_orbits hQ' _ φ
  intro z hz hz0 hiso hprimitive
  exact primitive_orbit_transitivity Q' L' N hQ' hA' hE' hz hz0 hiso hprimitive

end Hyperbolic
end NormEuclidean
