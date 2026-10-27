import NormEuclidean.FiniteIdele
import NormEuclidean.HyperbolicSpinor
import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# The actual idelic scalar obstruction for a hyperbolic enlargement

At a finite place, lift the squareclass-valued proper integral spinor image
back to the local multiplicative group. The intersection of these conditions
inside the actual finite idele group is the local spinor subgroup. The full
idele version additionally uses the proper ambient image at infinite places.

Over a PID every idele is a principal factor times such local spinor factors.
The resulting scalar obstruction quotients are trivial. These quotients are
not identified here with spinor genera or global integral classes: that
geometric comparison and strong approximation remain unproved.
-/

noncomputable section

namespace NormEuclidean.AdelicSpinor

open IsDedekindDomain CompletedIntegralLattice ProperSpinor

variable {K V : Type*} [Field K] [CharZero K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]

/-- Ideles whose finite components lie in the lifted proper integral spinor images. -/
def finiteSpinorIdeles (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice R Q) : Subgroup (FiniteAdeleRing R K)ˣ :=
  ⨅ v : HeightOneSpectrum R,
    (properSpinorImage (form R v Q) (form_polarBilin_nondegenerate R v Q hQ)
      (carrier R v L.carrier)).comap
      ((QuotientGroup.mk' (Subgroup.square (LocalField R v)ˣ)).comp
        (FiniteIdele.componentUnit v))

theorem mem_finiteSpinorIdeles_iff (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (L : Lattice R Q) (a : (FiniteAdeleRing R K)ˣ) :
    a ∈ finiteSpinorIdeles R Q hQ L ↔
      ∀ v : HeightOneSpectrum R,
        Bong.Dyadic.squareClass (LocalField R v) (FiniteIdele.componentUnit v a) ∈
          properSpinorImage (form R v Q) (form_polarBilin_nondegenerate R v Q hQ)
            (carrier R v L.carrier) := by
  simp only [finiteSpinorIdeles, Subgroup.mem_iInf, Subgroup.mem_comap,
    MonoidHom.comp_apply, Bong.Dyadic.squareClass]

/-- The finite idelic denominator uses the full diagonal field group and the
lifted proper integral spinor groups. -/
def finiteDenominator (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice R Q) : Subgroup (FiniteAdeleRing R K)ˣ :=
  (FiniteAdeleRing.unitEmbedding R K).range ⊔ finiteSpinorIdeles R Q hQ L

/-- The scalar obstruction, without any assumed identification with genus classes. -/
abbrev FiniteObstruction (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice R Q) :=
  (FiniteAdeleRing R K)ˣ ⧸ finiteDenominator R Q hQ L

/-- Every local-unit idele belongs to the lifted stabilizer spinor subgroup
of the completed hyperbolic enlargement, at all finite places. -/
theorem hyperbolic_localUnits_le_finiteSpinorIdeles (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (L : Lattice R Q) :
    FiniteIdele.localUnitSubgroup ≤
      finiteSpinorIdeles R (Hyperbolic.form Q)
        (Hyperbolic.form_polarBilin_nondegenerate Q hQ) L.hyperbolic := by
  intro a ha
  rw [mem_finiteSpinorIdeles_iff]
  intro v
  obtain ⟨u, hu⟩ := FiniteIdele.exists_localIntegerUnit ha v
  have hmem : unitSquareClassHom (LocalRing R v) u ∈
      unitSquareClasses (LocalRing R v) := ⟨u, rfl⟩
  have hs := hyperbolic_unitSquareClasses_le_properSpinorImage R v Q hQ L hmem
  have hu' : Units.map (LocalRing R v).subtype.toMonoidHom u =
      FiniteIdele.componentUnit v a := hu
  rw [unitSquareClassHom_apply, hu'] at hs
  exact hs

/-- PID arithmetic kills the finite scalar obstruction, using actual ideles
and proved local proper integral isometries. -/
theorem hyperbolic_finiteDenominator_eq_top [IsPrincipalIdealRing R]
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (L : Lattice R Q) :
    finiteDenominator R (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ) L.hyperbolic = ⊤ := by
  apply (Subgroup.eq_top_iff' _).mpr
  intro a
  obtain ⟨k, u, hu⟩ := FiniteIdele.exists_diagonal_mul_localUnit a
  rw [hu]
  exact Subgroup.mul_mem_sup ⟨k, rfl⟩
    (hyperbolic_localUnits_le_finiteSpinorIdeles R Q hQ L u.2)

theorem hyperbolic_finiteObstruction_subsingleton [IsPrincipalIdealRing R]
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (L : Lattice R Q) :
    Subsingleton (FiniteObstruction R (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ) L.hyperbolic) :=
  QuotientGroup.subsingleton_iff.mpr (hyperbolic_finiteDenominator_eq_top R Q hQ L)

/-- Projection of an actual full idele to its finite components. -/
def finiteProjection : (NumberField.AdeleRing R K)ˣ →* (FiniteAdeleRing R K)ˣ :=
  Units.map (RingHom.snd (NumberField.InfiniteAdeleRing K)
    (FiniteAdeleRing R K)).toMonoidHom

/-- Evaluation at an actual infinite completion. -/
def infiniteComponentUnit (v : NumberField.InfinitePlace K) :
    (NumberField.AdeleRing R K)ˣ →* v.Completionˣ :=
  Units.map ((Pi.evalRingHom (fun w : NumberField.InfinitePlace K ↦ w.Completion) v).comp
    (RingHom.fst (NumberField.InfiniteAdeleRing K) (FiniteAdeleRing R K))).toMonoidHom

/-- All finite integral and infinite ambient spinor conditions in the full idele group. -/
def spinorIdeles (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice R Q) : Subgroup (NumberField.AdeleRing R K)ˣ :=
  (finiteSpinorIdeles R Q hQ L).comap (finiteProjection R) ⊓
    ⨅ v : NumberField.InfinitePlace K,
      (properAmbientSpinorNormHom (ArchimedeanComparison.form v Q)
        (archimedean_form_polarBilin_nondegenerate v hQ)).range.comap
        ((QuotientGroup.mk' (Subgroup.square v.Completionˣ)).comp (infiniteComponentUnit R v))

/-- For the hyperbolic enlargement the infinite conditions impose no
restriction, including no positivity restriction at real places. -/
theorem hyperbolic_spinorIdeles_eq_comap (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (L : Lattice R Q) :
    spinorIdeles R (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ) L.hyperbolic =
        (finiteSpinorIdeles R (Hyperbolic.form Q)
          (Hyperbolic.form_polarBilin_nondegenerate Q hQ) L.hyperbolic).comap
            (finiteProjection R) := by
  simp only [spinorIdeles, archimedean_hyperbolic_properSpinorImage_eq_top _ Q hQ,
    Subgroup.comap_top, iInf_top, inf_top_eq]

/-- Full principal ideles, with the same field unit in every completion. -/
def diagonal : Kˣ →* (NumberField.AdeleRing R K)ˣ :=
  Units.map (algebraMap K (NumberField.AdeleRing R K))

omit [CharZero K] [Invertible (2 : K)] in
@[simp] theorem finiteProjection_diagonal (k : Kˣ) :
    finiteProjection R (diagonal R k) = FiniteAdeleRing.unitEmbedding R K k := by
  apply Units.ext
  rfl

/-- The full idelic denominator for the scalar spinor obstruction. -/
def denominator (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice R Q) : Subgroup (NumberField.AdeleRing R K)ˣ :=
  (diagonal R).range ⊔ spinorIdeles R Q hQ L

abbrev Obstruction (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice R Q) :=
  (NumberField.AdeleRing R K)ˣ ⧸ denominator R Q hQ L

/-- Every full idele over a PID is a principal idele times the full lifted
local spinor subgroup of the hyperbolic enlargement. -/
theorem hyperbolic_exists_diagonal_mul_spinorIdele [IsPrincipalIdealRing R]
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (L : Lattice R Q)
    (a : (NumberField.AdeleRing R K)ˣ) :
    ∃ k : Kˣ, ∃ b : spinorIdeles R (Hyperbolic.form Q)
        (Hyperbolic.form_polarBilin_nondegenerate Q hQ) L.hyperbolic,
      a = diagonal R k * b.1 := by
  obtain ⟨k, u, hu⟩ := FiniteIdele.exists_diagonal_mul_localUnit (finiteProjection R a)
  let b := (diagonal R k)⁻¹ * a
  have hb : b ∈ spinorIdeles R (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ) L.hyperbolic := by
    rw [hyperbolic_spinorIdeles_eq_comap R Q hQ L]
    change finiteProjection R b ∈ finiteSpinorIdeles R (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ) L.hyperbolic
    have hp : finiteProjection R b = u.1 := by
      simp only [b, map_mul, map_inv, finiteProjection_diagonal, hu]
      simp
    rw [hp]
    exact hyperbolic_localUnits_le_finiteSpinorIdeles R Q hQ L u.2
  exact ⟨k, ⟨b, hb⟩, by dsimp [b]; simp⟩

theorem hyperbolic_denominator_eq_top [IsPrincipalIdealRing R]
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (L : Lattice R Q) :
    denominator R (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ) L.hyperbolic = ⊤ := by
  apply (Subgroup.eq_top_iff' _).mpr
  intro a
  obtain ⟨k, b, hb⟩ := hyperbolic_exists_diagonal_mul_spinorIdele R Q hQ L a
  rw [hb]
  exact Subgroup.mul_mem_sup ⟨k, rfl⟩ b.2

theorem hyperbolic_obstruction_subsingleton [IsPrincipalIdealRing R]
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (L : Lattice R Q) :
    Subsingleton (Obstruction R (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ) L.hyperbolic) :=
  QuotientGroup.subsingleton_iff.mpr (hyperbolic_denominator_eq_top R Q hQ L)

end NormEuclidean.AdelicSpinor

namespace NormEuclidean

open scoped NumberField

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

/-- From the original rank, anisotropy and norm approximation hypotheses,
derive triviality of the actual full idelic scalar obstruction. This is not
yet a theorem about the cardinality of the genus class set. -/
theorem hyperbolic_idelic_obstruction_trivial_of_rank_ge_three
    (L : Lattice (integerSubring K) Q) (hdim : 3 ≤ Module.finrank K V)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier) :
    letI := L.finiteDimensional
    Subsingleton (AdelicSpinor.Obstruction (integerSubring K) (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q
        (quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA)) L.hyperbolic) := by
  letI := L.finiteDimensional
  letI := isPrincipalIdealRing_of_rank_ge_three L hdim hA hE
  exact AdelicSpinor.hyperbolic_obstruction_subsingleton (integerSubring K) Q
    (quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA) L

end NormEuclidean
