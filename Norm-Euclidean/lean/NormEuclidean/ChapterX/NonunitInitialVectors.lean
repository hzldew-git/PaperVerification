import NormEuclidean.ChapterX.BinaryUnitRepresentation

/-!
# Initial vectors from a binary unit frame in the actual complement

At a non-dyadic denominator divisor, a binary unit frame in the completed
complement constructs a nonzero initial residual with beta zero. Existence
of the frame from unimodularity is a separate geometric step, not assumed
as a local representation law or asserted to have been proved here.
-/

noncomputable section

namespace NormEuclidean.NonunitInitialVectors

open IsDedekindDomain CompletedIntegralLattice QuadraticMap

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E]
variable (v : HeightOneSpectrum (integerSubring K))
  [Module (LocalField (integerSubring K) v) E]

/-- A binary unit diagonal frame in an actual completed module represents
every unit. Odd residue characteristic is supplied by the explicit unit two. -/
theorem represents_unit_of_binary_frame
    (Q : QuadraticForm (LocalField (integerSubring K) v) E)
    (N : Submodule (LocalRing (integerSubring K) v) E)
    (htwo : IsUnit (2 : LocalRing (integerSubring K) v))
    (e f : E) (he : e ∈ N) (hf : f ∈ N)
    (a b : (LocalRing (integerSubring K) v)ˣ)
    (heQ : Q e = ((a : LocalRing (integerSubring K) v) : LocalField (integerSubring K) v))
    (hfQ : Q f = ((b : LocalRing (integerSubring K) v) : LocalField (integerSubring K) v))
    (hef : Q.polarBilin e f = 0) (t : (LocalRing (integerSubring K) v)ˣ) :
    ∃ z ∈ N, Q z = ((t : LocalRing (integerSubring K) v) : LocalField (integerSubring K) v) := by
  let F := LocalField (integerSubring K) v
  let S := LocalRing (integerSubring K) v
  letI := CompletionHensel.henselian_completed_integers v
  letI := CompletionHensel.finite_residue_field v
  obtain ⟨x, y, hxy⟩ := BinaryUnitRepresentation.henselian_binary_represents_unit htwo a b t
  have hortho : Q.IsOrtho ((x : F) • e) ((y : F) • f) :=
    Q.isOrtho_polarBilin.mp (by simp [hef])
  rw [isOrtho_def] at hortho
  refine ⟨x • e + y • f, N.add_mem (N.smul_mem x he) (N.smul_mem y hf), ?_⟩
  change Q ((x : F) • e + (y : F) • f) = (t : S)
  rw [hortho, Q.map_smul, Q.map_smul, heQ, hfQ]
  have hfield := congrArg (fun s : S ↦ (s : F)) hxy
  simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_pow] at hfield
  simp only [smul_eq_mul]
  linear_combination hfield

/-- The nonunit-denominator initial vector is constructed from the binary
frame, with beta zero and nonzero value. The denominator itself is arbitrary. -/
theorem exists_initial_vector_of_binary_frame
    (Q : QuadraticForm (LocalField (integerSubring K) v) E)
    (N : Submodule (LocalRing (integerSubring K) v) E)
    (htwo : IsUnit (2 : LocalRing (integerSubring K) v))
    (e f : E) (he : e ∈ N) (hf : f ∈ N)
    (a b : (LocalRing (integerSubring K) v)ˣ)
    (heQ : Q e = ((a : LocalRing (integerSubring K) v) : LocalField (integerSubring K) v))
    (hfQ : Q f = ((b : LocalRing (integerSubring K) v) : LocalField (integerSubring K) v))
    (hef : Q.polarBilin e f = 0) (t : (LocalRing (integerSubring K) v)ˣ)
    (c : LocalField (integerSubring K) v) :
    ∃ β : LocalRing (integerSubring K) v, ∃ z ∈ N, Q z ≠ 0 ∧
      Q z = ((t : LocalRing (integerSubring K) v) : LocalField (integerSubring K) v) *
        (1 - c ^ 2 * (β : LocalField (integerSubring K) v) ^ 2) := by
  obtain ⟨z, hz, hzQ⟩ := represents_unit_of_binary_frame v Q N htwo e f he hf a b heQ hfQ hef t
  have ht0 := (t.isUnit.map (LocalRing (integerSubring K) v).subtype).ne_zero
  refine ⟨0, z, hz, hzQ.trans_ne ht0, ?_⟩
  simpa only [Subring.coe_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, mul_one]
    using hzQ

end NormEuclidean.NonunitInitialVectors
