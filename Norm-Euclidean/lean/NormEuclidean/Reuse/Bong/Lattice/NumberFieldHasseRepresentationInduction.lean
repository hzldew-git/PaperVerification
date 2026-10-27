import NormEuclidean.ChapterX.HasseRepresentationInterface
import Bong.QuadraticSpace.LineOrthogonalSplit

/-!
# O'Meara 66:3 reduced to its rank-one Hasse case

This file formalizes the induction in O'Meara, Theorem 66:3.  The only
arithmetic input left explicit is the theorem's rank-one case, which O'Meara
derives from the Hasse isotropy theorem 66:1.
-/

namespace Bong.HeADCV5.Global

open scoped NumberField TensorProduct

namespace NumberFieldLattice

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- O'Meara 66:3 in rank one, uniformly for every regular host space. -/
def HasAllPlaceRankOneHasseRepresentation (K : Type u)
    [Field K] [NumberField K] : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (q : Bong.QuadraticSpace K V),
    HasAllPlaceHasseRepresentationAtRank.{u, u, u} q 1

private def orthogonalSumRepresentation
    {S₁ T₁ S₂ T₂ : Type u}
    [AddCommGroup S₁] [Module K S₁]
    [AddCommGroup T₁] [Module K T₁]
    [AddCommGroup S₂] [Module K S₂]
    [AddCommGroup T₂] [Module K T₂]
    {q₁ : Bong.QuadraticSpace K S₁} {r₁ : Bong.QuadraticSpace K T₁}
    {q₂ : Bong.QuadraticSpace K S₂} {r₂ : Bong.QuadraticSpace K T₂}
    (f : Bong.QuadraticSpace.Representation q₁ r₁)
    (g : Bong.QuadraticSpace.Representation q₂ r₂) :
    Bong.QuadraticSpace.Representation
      (q₁.orthogonalSum q₂) (r₁.orthogonalSum r₂) where
  toLinearMap :=
    { toFun := fun z ↦ (f.toLinearMap z.1, g.toLinearMap z.2)
      map_add' := by intro z z'; ext <;> simp
      map_smul' := by intro c z; ext <;> simp }
  injective := by
    intro z z' h
    apply Prod.ext
    · exact f.injective (congrArg Prod.fst h)
    · exact g.injective (congrArg Prod.snd h)
  map_bilin := by
    intro z z'
    change r₁.bilin (f.toLinearMap z.1) (f.toLinearMap z'.1) +
        r₂.bilin (g.toLinearMap z.2) (g.toLinearMap z'.2) =
      q₁.bilin z.1 z'.1 + q₂.bilin z.2 z'.2
    rw [f.map_bilin, g.map_bilin]

private def orthogonalSumInrRepresentation
    {T₁ T₂ : Type u} [AddCommGroup T₁] [Module K T₁]
    [AddCommGroup T₂] [Module K T₂]
    (q₁ : Bong.QuadraticSpace K T₁) (q₂ : Bong.QuadraticSpace K T₂) :
    Bong.QuadraticSpace.Representation q₂ (q₁.orthogonalSum q₂) where
  toLinearMap :=
    { toFun := fun z ↦ (0, z)
      map_add' := by intro z z'; simp
      map_smul' := by intro c z; simp }
  injective := by
    intro z z' h
    exact congrArg Prod.snd h
  map_bilin := by
    intro z z'
    simp

private def emptyDiagonalRepresentation
    {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (q : Bong.QuadraticSpace K V) :
    Bong.QuadraticSpace.Representation
      (Bong.QuadraticSpace.finiteDiagonal
        (fun i : Fin 0 ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)) q where
  toLinearMap := 0
  injective := by
    intro z z' _
    exact Subsingleton.elim z z'
  map_bilin := by
    intro z z'
    simp [Bong.QuadraticSpace.finiteDiagonal_bilin_apply]

/-- Cancellation of a globally split common line after an arbitrary scalar
extension.  This is the local Witt-cancellation step in O'Meara 66:3. -/
private theorem scalarExtension_complement_represents
    {E : Type u} [Field E] [CharZero E] [Algebra K E]
    {V T : Type u} [AddCommGroup V] [Module K V]
    [AddCommGroup T] [Module K T]
    [FiniteDimensional K V] [FiniteDimensional K T]
    (q : Bong.QuadraticSpace K V) (r : Bong.QuadraticSpace K T)
    (a : Kˣ)
    {C D : Type u} [AddCommGroup C] [Module K C]
    [AddCommGroup D] [Module K D]
    [FiniteDimensional K C] [FiniteDimensional K D]
    (c : Bong.QuadraticSpace K C) (d : Bong.QuadraticSpace K D)
    (hostSplit : Bong.QuadraticSpace.Isometry
      ((Bong.QuadraticSpace.scaledLine a).orthogonalSum c) q)
    (sourceSplit : Bong.QuadraticSpace.Isometry
      ((Bong.QuadraticSpace.scaledLine a).orthogonalSum d) r)
    (hrep : (q.scalarExtension (E := E)).Represents
      (r.scalarExtension (E := E))) :
    (c.scalarExtension (E := E)).Represents
      (d.scalarExtension (E := E)) := by
  let lineE := (Bong.QuadraticSpace.scaledLine a).scalarExtension (E := E)
  let cE := c.scalarExtension (E := E)
  let dE := d.scalarExtension (E := E)
  let hostSplitE : Bong.QuadraticSpace.Isometry
      (lineE.orthogonalSum cE) (q.scalarExtension (E := E)) :=
    (Bong.QuadraticSpace.scalarExtensionOrthogonalSumIsometry
      (E := E) (Bong.QuadraticSpace.scaledLine a) c).symm.trans
        hostSplit.scalarExtension
  let sourceSplitE : Bong.QuadraticSpace.Isometry
      (lineE.orthogonalSum dE) (r.scalarExtension (E := E)) :=
    (Bong.QuadraticSpace.scalarExtensionOrthogonalSumIsometry
      (E := E) (Bong.QuadraticSpace.scaledLine a) d).symm.trans
        sourceSplit.scalarExtension
  rcases hrep with ⟨total⟩
  apply Bong.QuadraticSpace.fieldOrthogonalSumLeftCancelRepresents
    lineE dE cE
  exact ⟨hostSplitE.symm.toRepresentation.trans <|
    total.trans sourceSplitE.toRepresentation⟩

/-- The finite-diagonal induction in O'Meara 66:3. -/
private theorem finiteDiagonalHasseRepresentation
    (hline : HasAllPlaceRankOneHasseRepresentation K)
    {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (q : Bong.QuadraticSpace K V) {n : Nat}
    (A : Fin n → K) (hA : ∀ i, A i ≠ 0)
    (hFinite : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (q.scalarExtension (E := p.adicCompletion K)).Represents
        ((Bong.QuadraticSpace.finiteDiagonal A hA).scalarExtension
          (E := p.adicCompletion K)))
    (hInfinite : ∀ p : NumberField.InfinitePlace K,
      (q.scalarExtension (E := p.Completion)).Represents
        ((Bong.QuadraticSpace.finiteDiagonal A hA).scalarExtension
          (E := p.Completion))) :
    q.Represents (Bong.QuadraticSpace.finiteDiagonal A hA) := by
  induction n generalizing V with
  | zero =>
      exact ⟨emptyDiagonalRepresentation q⟩
  | succ n ih =>
      let tail : Fin n → K := Fin.init A
      have htail : ∀ i, tail i ≠ 0 := fun i ↦ hA i.castSucc
      let a : Kˣ := Units.mk0 (A (Fin.last n)) (hA (Fin.last n))
      let tailSpace := Bong.QuadraticSpace.finiteDiagonal tail htail
      let lineSpace := Bong.QuadraticSpace.scaledLine a
      have hcoeff : Fin.snoc tail (a : K) = A := by
        change Fin.snoc (Fin.init A) (A (Fin.last n)) = A
        exact Fin.snoc_init_self A
      have sourceSplit : Bong.QuadraticSpace.Isometry
          (tailSpace.orthogonalSum lineSpace)
          (Bong.QuadraticSpace.finiteDiagonal A hA) := by
        let raw := Bong.QuadraticSpace.fieldFiniteDiagonalScaledLineSnocIsometry
          tail htail a
        simpa only [tailSpace, lineSpace, hcoeff] using raw
      let sourceSplitSwapped : Bong.QuadraticSpace.Isometry
          (lineSpace.orthogonalSum tailSpace)
          (Bong.QuadraticSpace.finiteDiagonal A hA) :=
        (Bong.QuadraticSpace.fieldOrthogonalSumSwap
          lineSpace tailSpace).trans sourceSplit
      let lineIntoSource : Bong.QuadraticSpace.Representation lineSpace
          (Bong.QuadraticSpace.finiteDiagonal A hA) :=
        sourceSplit.toRepresentation.trans
          (orthogonalSumInrRepresentation tailSpace lineSpace)
      have hLineFinite : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          (q.scalarExtension (E := p.adicCompletion K)).Represents
            (lineSpace.scalarExtension (E := p.adicCompletion K)) := by
        intro p
        rcases hFinite p with ⟨total⟩
        exact ⟨total.trans lineIntoSource.scalarExtension⟩
      have hLineInfinite : ∀ p : NumberField.InfinitePlace K,
          InfinitePlaceRepresents p q lineSpace := by
        intro p
        rcases hInfinite p with ⟨total⟩
        exact ⟨total.trans lineIntoSource.scalarExtension⟩
      have hLineGlobal : q.Represents lineSpace :=
        hline q lineSpace (by simp) hLineFinite hLineInfinite
      rcases hLineGlobal with ⟨lineRepresentation⟩
      let z : V := lineRepresentation.toLinearMap 1
      have hzValue : q.quadratic z = (a : K) := by
        change q.quadratic (lineRepresentation.toLinearMap 1) = (a : K)
        rw [lineRepresentation.map_quadratic,
          Bong.QuadraticSpace.scaledLine_quadratic_apply]
        simp
      have hz : q.IsAnisotropic z := by
        rw [Bong.QuadraticSpace.IsAnisotropic, hzValue]
        exact Units.ne_zero a
      let complement := q.orthogonalSpace z hz
      let hostSplit := Bong.QuadraticSpace.scaledLineOrthogonalIsometry
        q z a hz hzValue
      have hTailFinite : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          (complement.scalarExtension (E := p.adicCompletion K)).Represents
            (tailSpace.scalarExtension (E := p.adicCompletion K)) := by
        intro p
        letI : CharZero (p.adicCompletion K) :=
          Algebra.charZero_of_charZero K (p.adicCompletion K)
        exact scalarExtension_complement_represents q
          (Bong.QuadraticSpace.finiteDiagonal A hA) a complement tailSpace
          hostSplit sourceSplitSwapped (hFinite p)
      have hTailInfinite : ∀ p : NumberField.InfinitePlace K,
          (complement.scalarExtension (E := p.Completion)).Represents
            (tailSpace.scalarExtension (E := p.Completion)) := by
        intro p
        letI : CharZero p.Completion :=
          Algebra.charZero_of_charZero K p.Completion
        exact scalarExtension_complement_represents q
          (Bong.QuadraticSpace.finiteDiagonal A hA) a complement tailSpace
          hostSplit sourceSplitSwapped (hInfinite p)
      have hTailGlobal : complement.Represents tailSpace :=
        ih complement tail htail hTailFinite hTailInfinite
      rcases hTailGlobal with ⟨tailRepresentation⟩
      exact ⟨hostSplit.toRepresentation.trans <|
        (orthogonalSumRepresentation
          (Bong.QuadraticSpace.Representation.refl lineSpace)
          tailRepresentation).trans sourceSplitSwapped.symm.toRepresentation⟩

/-- O'Meara 66:3 for every rank follows from its uniform rank-one case.
This is the complete induction printed in the source. -/
theorem hasAllPlaceHasseRepresentationAtRank_of_rankOne
    (hline : HasAllPlaceRankOneHasseRepresentation K)
    {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (q : Bong.QuadraticSpace K V) (n : Nat) :
    HasAllPlaceHasseRepresentationAtRank.{u, u, u} q n := by
  intro W _ _ _ r _ hFinite hInfinite
  have hDiagFinite : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (q.scalarExtension (E := p.adicCompletion K)).Represents
        (r.fieldDiagonalModel.scalarExtension
          (E := p.adicCompletion K)) := by
    intro p
    rcases hFinite p with ⟨total⟩
    exact ⟨total.trans
      r.fieldDiagonalizationIsometry.symm.toRepresentation.scalarExtension⟩
  have hDiagInfinite : ∀ p : NumberField.InfinitePlace K,
      (q.scalarExtension (E := p.Completion)).Represents
        (r.fieldDiagonalModel.scalarExtension (E := p.Completion)) := by
    intro p
    rcases hInfinite p with ⟨total⟩
    exact ⟨total.trans
      r.fieldDiagonalizationIsometry.symm.toRepresentation.scalarExtension⟩
  have hDiagGlobal : q.Represents r.fieldDiagonalModel :=
    finiteDiagonalHasseRepresentation hline q
      r.fieldDiagonalCoefficients r.fieldDiagonalCoefficients_ne_zero
      hDiagFinite hDiagInfinite
  rcases hDiagGlobal with ⟨diagonalRepresentation⟩
  exact ⟨diagonalRepresentation.trans
    r.fieldDiagonalizationIsometry.toRepresentation⟩

end NumberFieldLattice

end Bong.HeADCV5.Global
