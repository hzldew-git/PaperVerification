import NormEuclidean.ChapterX.OddNormObstruction

/-!
# The two square classes of odd local units

Finite-field Euler criteria and simple-root Hensel lifting prove the unit
square-class dichotomy. This supplies the ramified odd-place calculation
without a local norm-index premise.
-/

noncomputable section

namespace NormEuclidean.OddSquareClasses

/-- A product of two nonsquares in an odd finite field is a square. -/
theorem finite_field_nonsquare_product {F : Type*} [Field F] [Finite F]
    (htwo : (2 : F) ≠ 0) (a b : F) (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) :
    IsSquare (a * b) := by
  classical
  letI := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := by
    intro h
    exact htwo ((ringChar.spec F 2).mpr (by rw [h]))
  have ha0 : a ≠ 0 := fun h ↦ ha (h ▸ IsSquare.zero)
  have hb0 : b ≠ 0 := fun h ↦ hb (h ▸ IsSquare.zero)
  have hap : a ^ (Fintype.card F / 2) = -1 :=
    (FiniteField.pow_dichotomy hchar ha0).resolve_left
      (fun h ↦ ha ((FiniteField.isSquare_iff hchar ha0).mpr h))
  have hbp : b ^ (Fintype.card F / 2) = -1 :=
    (FiniteField.pow_dichotomy hchar hb0).resolve_left
      (fun h ↦ hb ((FiniteField.isSquare_iff hchar hb0).mpr h))
  apply (FiniteField.isSquare_iff hchar (mul_ne_zero ha0 hb0)).mpr
  rw [mul_pow, hap, hbp, neg_one_mul, neg_neg]

/-- A square residue of a unit lifts to a square in the unit group. -/
theorem henselian_square_of_square_residue {S : Type*} [CommRing S] [IsLocalRing S]
    [HenselianRing S (IsLocalRing.maximalIdeal S)] (htwo : IsUnit (2 : S))
    (a : Sˣ) (ha : IsSquare (IsLocalRing.residue S a.val)) : IsSquare a := by
  obtain ⟨r, hr⟩ := ha
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective (R := S) r
  have hres : IsLocalRing.residue S (x ^ 2 - a.val) = 0 := by
    rw [map_sub, map_pow, hx, hr, pow_two, sub_self]
  obtain ⟨z, hz⟩ := OddNormObstruction.henselian_square_of_residue_square htwo a x hres
  refine ⟨z, Units.ext ?_⟩
  exact hz.symm.trans (pow_two z.val)

/-- Every unit is a square or becomes a square after multiplication by a
fixed unit having nonsquare residue. -/
theorem henselian_square_or_twist {S : Type*} [CommRing S] [IsLocalRing S]
    [Finite (IsLocalRing.ResidueField S)]
    [HenselianRing S (IsLocalRing.maximalIdeal S)] (htwo : IsUnit (2 : S))
    (d a : Sˣ) (hd : ¬ IsSquare (IsLocalRing.residue S d.val)) :
    IsSquare a ∨ IsSquare (a * d) := by
  classical
  by_cases ha : IsSquare (IsLocalRing.residue S a.val)
  · exact Or.inl (henselian_square_of_square_residue htwo a ha)
  right
  apply henselian_square_of_square_residue htwo
  have htwoR : (2 : IsLocalRing.ResidueField S) ≠ 0 := by
    simpa only [map_ofNat] using (htwo.map (IsLocalRing.residue S)).ne_zero
  simpa only [Units.val_mul, map_mul] using
    finite_field_nonsquare_product htwoR _ _ ha hd

/-- A unit with nonsquare residue exists in every local ring with finite
odd residue field. No square-class choice is supplied as a premise. -/
theorem exists_nonsquare_residue_unit {S : Type*} [CommRing S] [IsLocalRing S]
    [Finite (IsLocalRing.ResidueField S)] (htwo : IsUnit (2 : S)) :
    ∃ d : Sˣ, ¬ IsSquare (IsLocalRing.residue S d.val) := by
  have htwoR : (2 : IsLocalRing.ResidueField S) ≠ 0 := by
    simpa only [map_ofNat] using (htwo.map (IsLocalRing.residue S)).ne_zero
  have hchar : ringChar (IsLocalRing.ResidueField S) ≠ 2 := by
    intro h
    exact htwoR ((ringChar.spec _ 2).mpr (by rw [h]))
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective (R := S) a
  have hxunit : IsUnit x := (IsLocalRing.residue_ne_zero_iff_isUnit x).mp (by
    rw [hx]
    exact fun h ↦ ha (h ▸ IsSquare.zero))
  exact ⟨hxunit.unit, by simpa only [hxunit.unit_spec, hx] using ha⟩

end NormEuclidean.OddSquareClasses
