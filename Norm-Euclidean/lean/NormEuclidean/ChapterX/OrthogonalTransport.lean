import NormEuclidean.ChapterX.CommutatorSquares

/-!
# Actual orthogonal groups under a field isometry

Conjugation preserves properness, the actual Wall spinor norm and ambient
commutator membership. Reflection-word induction proves norm compatibility.
-/

noncomputable section

namespace NormEuclidean.OrthogonalTransport

open ProperSpinor SpinorBaseChange CommutatorGeneration

variable {F E W : Type*} [Field F] [CharZero F]
  [AddCommGroup E] [Module F E] [AddCommGroup W] [Module F W]
variable (Q : QuadraticForm F E) (P : QuadraticForm F W)
  (e : E ≃ₗ[F] W) (he : ∀ x, P (e x) = Q x)

include he

/-- The actual conjugation homomorphism on ambient orthogonal transformations. -/
def ambientMap : ambientGroup Q →* ambientGroup P where
  toFun g := ⟨(e.symm.trans g.1).trans e, fun z ↦ by
    change P (e (g.1 (e.symm z))) = P z
    rw [he, g.2, ← he, e.apply_symm_apply]⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    exact e.apply_symm_apply z
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    change e (g.1 (h.1 (e.symm z))) = e (g.1 (e.symm (e (h.1 (e.symm z)))))
    rw [e.symm_apply_apply]

@[simp] theorem ambientMap_apply (g : ambientGroup Q) (z : W) :
    (ambientMap Q P e he g).1 z = e (g.1 (e.symm z)) := rfl

theorem inverse_value (z : W) : Q (e.symm z) = P z := by
  rw [← he, e.apply_symm_apply]

/-- The actual multiplicative equivalence induced by an isometry. -/
def ambientEquiv : ambientGroup Q ≃* ambientGroup P where
  toFun := ambientMap Q P e he
  invFun := ambientMap P Q e.symm (inverse_value Q P e he)
  left_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    simp only [ambientMap_apply, LinearEquiv.symm_symm, e.symm_apply_apply]
  right_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    simp only [ambientMap_apply, LinearEquiv.symm_symm, e.apply_symm_apply]
  map_mul' := (ambientMap Q P e he).map_mul

theorem polar_map (x y : E) : QuadraticMap.polar P (e x) (e y) =
    QuadraticMap.polar Q x y := by
  simp only [QuadraticMap.polar, ← e.map_add, he]

/-- Isometric conjugation transports actual reflections. -/
theorem reflection_map (x : E) (hx : Q x ≠ 0) :
    ambientMap Q P e he (ambientReflection Q x hx) =
      ambientReflection P (e x) ((he x).trans_ne hx) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  change e (IntegralReflection.linearEquiv Q x hx (e.symm z)) =
    IntegralReflection.linearEquiv P (e x) ((he x).trans_ne hx) z
  rw [IntegralReflection.linearEquiv_apply, IntegralReflection.linearEquiv_apply,
    map_sub, map_smul, e.apply_symm_apply, he]
  have hp := polar_map Q P e he x (e.symm z)
  rw [e.apply_symm_apply] at hp
  rw [hp]

variable [FiniteDimensional F E] [FiniteDimensional F W]

/-- Properness is preserved by the actual linear conjugation, including different spaces. -/
def properMap (g : properGroup Q) : properGroup P :=
  ⟨ambientMap Q P e he g.1, by
    change LinearEquiv.det ((e.symm.trans g.1.1).trans e) = 1
    rw [LinearEquiv.det_conj]
    exact g.2⟩

/-- Actual Wall spinor norms are compatible with the field isometry. -/
theorem spinorNorm_map (hQ : Q.polarBilin.Nondegenerate) (hP : P.polarBilin.Nondegenerate)
    (g : ambientGroup Q) :
    ambientSpinorNormHom P hP (ambientMap Q P e he g) = ambientSpinorNormHom Q hQ g := by
  apply ambient_induction Q hQ
    (fun g ↦ ambientSpinorNormHom P hP (ambientMap Q P e he g) = ambientSpinorNormHom Q hQ g)
  · simp only [map_one]
  · intro g h hg hh
    simp only [map_mul, hg, hh]
  · intro x hx
    rw [reflection_map, ambientReflection_spinorNorm, ambientReflection_spinorNorm]
    congr 1
    exact Units.ext (he x)

theorem proper_spinorNorm_map (hQ : Q.polarBilin.Nondegenerate)
    (hP : P.polarBilin.Nondegenerate) (g : properGroup Q) :
    properAmbientSpinorNormHom P hP (properMap Q P e he g) =
      properAmbientSpinorNormHom Q hQ g := spinorNorm_map Q P e he hQ hP g.1

/-- Every conjugation homomorphism sends the actual derived group to the derived group. -/
theorem commutator_map (g : ambientGroup Q) (hg : g ∈ commutator (ambientGroup Q)) :
    ambientMap Q P e he g ∈ commutator (ambientGroup P) := by
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  exact Abelianization.commutator_subset_ker
    (Abelianization.of.comp (ambientMap Q P e he)) hg

/-- Actual ambient commutator membership is invariant under the isometry. -/
theorem commutator_map_iff (g : ambientGroup Q) :
    ambientMap Q P e he g ∈ commutator (ambientGroup P) ↔
      g ∈ commutator (ambientGroup Q) := by
  constructor
  · intro hg
    have hh := commutator_map P Q e.symm (inverse_value Q P e he)
      (ambientMap Q P e he g) hg
    have heq : ambientMap P Q e.symm (inverse_value Q P e he)
        (ambientMap Q P e he g) = g := (ambientEquiv Q P e he).left_inv g
    rwa [heq] at hh
  · exact commutator_map Q P e he g

end NormEuclidean.OrthogonalTransport
