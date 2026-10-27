import NormEuclidean.Cancellation

/-!
# The hyperbolic extension as an actual quadratic module

These adapters package the coordinate predicates as the standard mathlib
objects used in the scalar-extension bridge. They do not add mathematical
hypotheses or change the coordinate formulas.
-/

namespace NormEuclidean.Hyperbolic

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K} (Q : QuadraticForm K V) (L : Submodule R V)

/-- The coordinate quadratic expression bundled as a quadratic form. -/
def form : QuadraticForm K (Hyperbolic K V) :=
  Q.comp (LinearMap.fst K V (K × K)) +
    QuadraticMap.linMulLin
      ((LinearMap.fst K K K).comp (LinearMap.snd K V (K × K)))
      ((LinearMap.snd K K K).comp (LinearMap.snd K V (K × K)))

@[simp] theorem form_apply (z : Hyperbolic K V) : form Q z = q Q z := rfl

/-- The integral hyperbolic extension as an actual submodule. -/
def submodule : Submodule R (Hyperbolic K V) where
  carrier := Mem L
  zero_mem' := ⟨L.zero_mem, R.zero_mem, R.zero_mem⟩
  add_mem' := fun hx hy =>
    ⟨L.add_mem hx.1 hy.1, R.add_mem hx.2.1 hy.2.1, R.add_mem hx.2.2 hy.2.2⟩
  smul_mem' := fun r _ hz =>
    ⟨L.smul_mem r hz.1, R.mul_mem r.property hz.2.1, R.mul_mem r.property hz.2.2⟩

@[simp] theorem mem_submodule (z : Hyperbolic K V) : z ∈ submodule L ↔ Mem L z := Iff.rfl

theorem submodule_integral (hQ : ∀ v ∈ L, Q v ∈ R) :
    ∀ z ∈ submodule L, form Q z ∈ R := by
  intro z hz
  exact R.add_mem (hQ _ hz.1) (R.mul_mem hz.2.1 hz.2.2)

/-- Adjoining the standard hyperbolic plane preserves full ambient span. -/
theorem submodule_full (hL : Submodule.span K (L : Set V) = ⊤) :
    Submodule.span K (submodule L : Set (Hyperbolic K V)) = ⊤ := by
  let P := Submodule.span K (submodule L : Set (Hyperbolic K V))
  have he : (e : Hyperbolic K V) ∈ P := Submodule.subset_span (mem_e L)
  have hf : (f : Hyperbolic K V) ∈ P := Submodule.subset_span (mem_f L)
  have hv : ∀ v : V, embed v ∈ P := by
    intro v
    have hvfull : v ∈ Submodule.span K (L : Set V) := by rw [hL]; trivial
    induction hvfull using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ((mem_embed x).2 hx)
    | zero => change (0 : Hyperbolic K V) ∈ P; exact P.zero_mem
    | add x y _ _ hx hy => simpa only [embed_add] using P.add_mem hx hy
    | smul a x _ hx => simpa only [embed_smul] using P.smul_mem a hx
  apply top_unique
  intro z _
  have h := P.add_mem (P.add_mem (hv z.1) (P.smul_mem z.2.1 he))
    (P.smul_mem z.2.2 hf)
  have hz : embed z.1 + z.2.1 • (e : Hyperbolic K V) + z.2.2 • f = z := by
    ext <;> simp [embed, e, f]
  exact hz ▸ h

/-- The integral hyperbolic module is the ordinary product `L × R × R`. -/
def moduleEquivProduct : submodule L ≃ₗ[R] L × R × R where
  toFun := fun z => (⟨z.val.1, z.property.1⟩,
    ⟨z.val.2.1, z.property.2.1⟩, ⟨z.val.2.2, z.property.2.2⟩)
  invFun := fun z => ⟨((z.1 : V), (z.2.1 : K), (z.2.2 : K)),
    z.1.property, z.2.1.property, z.2.2.property⟩
  left_inv := by intro z; rfl
  right_inv := by intro z; rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro a z; rfl

/-- The quadratic form on the integral product coordinates. -/
def productQ (z : L × R × R) : K := Q (z.1 : V) + (z.2.1 : K) * (z.2.2 : K)

@[simp] theorem productQ_moduleEquivProduct (z : submodule L) :
    productQ Q L (moduleEquivProduct L z) = form Q (z : Hyperbolic K V) := rfl

@[simp] theorem form_moduleEquivProduct_symm (z : L × R × R) :
    form Q ((moduleEquivProduct L).symm z : Hyperbolic K V) = productQ Q L z := rfl

end NormEuclidean.Hyperbolic
