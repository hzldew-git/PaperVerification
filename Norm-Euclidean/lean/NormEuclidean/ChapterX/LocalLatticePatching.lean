import NormEuclidean.ChapterX.UnitDenominator
import NormEuclidean.ChapterX.FixedValueVectors
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Patching full modules at finitely many finite places

The construction uses actual localized submodules of the common fraction-field
space. Local constraints are contracted to the global space and intersected
inside a finite upper module. Distinct prime localizations impose no additional
constraint on one another. No integral basis of a global module is assumed.
-/

noncomputable section

namespace NormEuclidean.LocalLatticePatching

open IsDedekindDomain CompletedIntegralLattice

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]

/-- The actual localization, inside the original fraction-field vector space. -/
abbrev localizationAt (v : HeightOneSpectrum R) (M : Submodule R V) :
    Submodule (v.valuation K).valuationSubring V :=
  M.localized' (v.valuation K).valuationSubring v.asIdeal.primeCompl LinearMap.id

/-- Contract a local module to the global coefficient ring. -/
def saturation (v : HeightOneSpectrum R) (M : Submodule R V) : Submodule R V :=
  (localizationAt R v M).restrictScalars R

theorem le_saturation (v : HeightOneSpectrum R) (M : Submodule R V) :
    M ≤ saturation R v M := by
  intro x hx
  exact ⟨x, hx, 1, by simp⟩

@[simp] theorem local_saturation_self (v : HeightOneSpectrum R) (M : Submodule R V) :
    localizationAt R v (saturation R v M) = localizationAt R v M := by
  simp only [localizationAt, Submodule.localized'_eq_span, LinearMap.id_coe, Set.image_id]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    change x ∈ localizationAt R v M at hx
    simp only [localizationAt, Submodule.localized'_eq_span, LinearMap.id_coe,
      Set.image_id] at hx
    change x ∈ Submodule.span (v.valuation K).valuationSubring (M : Set V) at hx
    change x ∈ Submodule.span (v.valuation K).valuationSubring (M : Set V)
    exact hx
  · apply Submodule.span_mono
    exact le_saturation R v M

omit [IsFractionRing R K] in
/-- A scalar can have any required divisibility at one prime while avoiding
a different prime. This includes zero divisibility exponents. -/
theorem exists_avoiding_with_valuation_le (v w : HeightOneSpectrum R) (hvw : v ≠ w)
    (a : R) (ha : a ≠ 0) :
    ∃ c : R, c ∉ w.asIdeal ∧ v.intValuation c ≤ v.intValuation a := by
  let n := multiplicity v.asIdeal (Ideal.span {a})
  have hnot : ¬ v.asIdeal ^ n ≤ w.asIdeal := by
    intro h
    have hle : v.asIdeal ≤ w.asIdeal := Ideal.IsPrime.le_of_pow_le h
    have heq := (inferInstance : v.asIdeal.IsMaximal).eq_of_le w.isPrime.ne_top hle
    exact hvw (HeightOneSpectrum.ext_iff.mpr heq)
  obtain ⟨c, hc, hcw⟩ := Set.not_subset.mp hnot
  refine ⟨c, hcw, ?_⟩
  rw [v.intValuation_eq_exp_neg_multiplicity ha]
  exact (v.intValuation_le_pow_iff_mem c n).mpr hc

/-- Localizing a full module first at one prime and then at a distinct prime
gives the entire ambient space. The module need not be finitely generated. -/
theorem local_saturation_of_ne (v w : HeightOneSpectrum R) (hvw : v ≠ w)
    (M : Submodule R V) (hM : Submodule.span K (M : Set V) = ⊤) :
    localizationAt R w (saturation R v M) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a, ha, hax⟩ := ScalarExtension.exists_denominator M hM x
  obtain ⟨c, hcw, hca⟩ := exists_avoiding_with_valuation_le R v w hvw a ha
  have haK : (a : K) ≠ 0 := by exact_mod_cast ha
  have hval : v.valuation K ((c : K) / (a : K)) ≤ 1 := by
    change v.valuation K (algebraMap R K c / algebraMap R K a) ≤ 1
    rw [map_div₀, v.valuation_of_algebraMap, v.valuation_of_algebraMap]
    exact (div_le_one₀ ((v.intValuation_ne_zero a ha).bot_lt)).mpr hca
  have hcx : c • x ∈ saturation R v M := by
    change (c : K) • x ∈ localizationAt R v M
    have h := (localizationAt R v M).smul_mem
      (⟨(c : K) / (a : K), hval⟩ : (v.valuation K).valuationSubring)
      (le_saturation R v M hax)
    change ((c : K) / (a : K)) • ((a : K) • x) ∈ localizationAt R v M at h
    simpa only [smul_smul, div_mul_cancel₀ _ haK] using h
  refine ⟨c • x, hcx, ⟨c, hcw⟩, ?_⟩
  apply IsLocalizedModule.mk'_eq_iff.mpr
  simp only [LinearMap.id_apply, Submonoid.smul_def]

/-- Localization preserves the finite intersection of global submodules. -/
theorem local_finset_inf {ι : Type*} (v : HeightOneSpectrum R) (s : Finset ι)
    (M : ι → Submodule R V) :
    localizationAt R v (s.inf M) = s.inf (fun i ↦ localizationAt R v (M i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [localizationAt]
  | @insert i s hi ih =>
    simp only [Finset.inf_insert, localizationAt, Submodule.localized'_inf] at ih ⊢
    rw [ih]

/-- Equality of actual localizations also gives equality of their completed
integral spans. This is the forward base-change direction of descent. -/
theorem carrier_eq_of_localization_eq (v : HeightOneSpectrum R) {L M : Submodule R V}
    (h : localizationAt R v L = localizationAt R v M) : carrier R v L = carrier R v M := by
  simp only [localizationAt, Submodule.localized'_eq_span, LinearMap.id_coe,
    Set.image_id] at h
  simpa only [CompletionDescent.map_baseChange_span_eq_carrier] using
    congrArg (fun N : Submodule (v.valuation K).valuationSubring V ↦
      (N.baseChange (v.adicCompletionIntegers K)).map
        (CompletionDescent.integralTensorToCompletedSpace v)) h

/-- A denominator avoiding a prime gives containment at its actual localization. -/
theorem localization_le_of_scaled_le (v : HeightOneSpectrum R) (L M : Submodule R V)
    (a : R) (ha : a ∉ v.asIdeal) (h : ∀ x ∈ L, a • x ∈ M) :
    localizationAt R v L ≤ localizationAt R v M := by
  rw [localizationAt, Submodule.localized'_eq_span]
  apply Submodule.span_le.mpr
  rintro x ⟨y, hy, rfl⟩
  refine ⟨a • y, h y hy, ⟨a, ha⟩, ?_⟩
  apply IsLocalizedModule.mk'_eq_iff.mpr
  simp only [LinearMap.id_apply, Submonoid.smul_def]

omit [IsDedekindDomain R] [IsFractionRing R K] in
/-- Clearing a nonzero denominator for every vector proves fullness. -/
theorem full_of_denominators (M : Submodule R V)
    (h : ∀ x : V, ∃ a : R, a ≠ 0 ∧ (a : K) • x ∈ M) :
    Submodule.span K (M : Set V) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a, ha, hax⟩ := h x
  have haK : (a : K) ≠ 0 := by exact_mod_cast ha
  have hmem := (Submodule.span K (M : Set V)).smul_mem (a : K)⁻¹
    (Submodule.subset_span hax)
  simpa only [smul_smul, inv_mul_cancel₀ haK, one_smul] using hmem

omit [IsDedekindDomain R] in
/-- Finite intersections of full global modules remain full, without freeness. -/
theorem full_inf (L M : Submodule R V)
    (hL : Submodule.span K (L : Set V) = ⊤)
    (hM : Submodule.span K (M : Set V) = ⊤) :
    Submodule.span K ((L ⊓ M : Submodule R V) : Set V) = ⊤ := by
  apply full_of_denominators R
  intro x
  obtain ⟨a, ha, hax⟩ := ScalarExtension.exists_denominator L hL x
  obtain ⟨b, hb, hbx⟩ := ScalarExtension.exists_denominator M hM x
  refine ⟨a * b, mul_ne_zero ha hb, ?_, ?_⟩
  · change ((a : K) * (b : K)) • x ∈ L
    rw [mul_comm, mul_smul]
    exact L.smul_mem b hax
  · change ((a : K) * (b : K)) • x ∈ M
    rw [mul_smul]
    exact M.smul_mem a hbx

omit [IsDedekindDomain R] in
theorem full_finset_inf {ι : Type*} (s : Finset ι) (M : ι → Submodule R V)
    (h : ∀ i ∈ s, Submodule.span K (M i : Set V) = ⊤) :
    Submodule.span K ((s.inf M : Submodule R V) : Set V) = ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.inf_insert]
    exact full_inf R _ _ (h i (Finset.mem_insert_self i s))
      (ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj)))

/-- Patch finite full global modules at a finite set of primes. The resulting
finite full module has exactly the prescribed completed carriers there, and
exactly the base completed carrier at every other finite prime. -/
theorem exists_patched_module (L : Submodule R V) (hLfg : L.FG)
    (hL : Submodule.span K (L : Set V) = ⊤) (T : Finset (HeightOneSpectrum R))
    (M : HeightOneSpectrum R → Submodule R V) (hMfg : ∀ v ∈ T, (M v).FG)
    (hM : ∀ v ∈ T, Submodule.span K (M v : Set V) = ⊤) :
    ∃ P : Submodule R V, P.FG ∧ Submodule.span K (P : Set V) = ⊤ ∧
      (∀ v ∈ T, carrier R v P = carrier R v (M v)) ∧
      ∀ v ∉ T, carrier R v P = carrier R v L := by
  classical
  let U := L ⊔ T.sup M
  have hUfg : U.FG := hLfg.sup (Submodule.fg_finset_sup T M hMfg)
  have hLU : L ≤ U := le_sup_left
  have hU : Submodule.span K (U : Set V) = ⊤ :=
    top_unique (hL ▸ Submodule.span_mono hLU)
  obtain ⟨a, ha0, ha⟩ := exists_lattice_denominator U L hUfg hL
  let S := T ∪ (finite_primes_containing (K := K) R a ha0).toFinset
  let N := fun v : HeightOneSpectrum R ↦ if v ∈ T then M v else L
  have hNU : ∀ v, N v ≤ U := by
    intro v
    dsimp only [N]
    split_ifs with hv
    · exact (Finset.le_sup hv).trans le_sup_right
    · exact hLU
  have hN : ∀ v, Submodule.span K (N v : Set V) = ⊤ := by
    intro v
    dsimp only [N]
    split_ifs with hv
    · exact hM v hv
    · exact hL
  let P := U ⊓ S.inf (fun v ↦ saturation R v (N v))
  have hPfg : P.FG := hUfg.of_le inf_le_left
  have hP : Submodule.span K (P : Set V) = ⊤ := by
    have hlower := full_inf R U (S.inf N) hU (full_finset_inf R S N (fun v _ ↦ hN v))
    have hle : U ⊓ S.inf N ≤ P :=
      inf_le_inf le_rfl (Finset.inf_mono_fun (fun v _ ↦ le_saturation R v (N v)))
    exact top_unique (hlower ▸ Submodule.span_mono hle)
  have hlocal : ∀ v ∈ S, localizationAt R v P = localizationAt R v (N v) := by
    intro v hv
    rw [show P = U ⊓ S.inf (fun w ↦ saturation R w (N w)) from rfl,
      localizationAt, Submodule.localized'_inf]
    change localizationAt R v U ⊓ localizationAt R v
      (S.inf (fun w ↦ saturation R w (N w))) = localizationAt R v (N v)
    rw [local_finset_inf]
    apply le_antisymm
    · exact inf_le_right.trans ((Finset.inf_le hv).trans (local_saturation_self R v (N v)).le)
    · apply le_inf
      · exact (Submodule.localized'gi _ _ _).gc.monotone_l (hNU v)
      · apply Finset.le_inf
        intro w _
        by_cases hw : w = v
        · subst w
          exact (local_saturation_self R v (N v)).ge
        · rw [local_saturation_of_ne R w v hw (N w) (hN w)]
          exact le_top
  have hout : ∀ v ∉ S, localizationAt R v P = localizationAt R v L := by
    intro v hv
    have hav : a ∉ v.asIdeal := by
      intro hav
      apply hv
      exact Finset.mem_union_right T (by simpa using hav)
    have hUL : localizationAt R v U = localizationAt R v L := by
      apply le_antisymm
      · exact localization_le_of_scaled_le R v U L a hav ha
      · exact (Submodule.localized'gi _ _ _).gc.monotone_l hLU
    rw [show P = U ⊓ S.inf (fun w ↦ saturation R w (N w)) from rfl,
      localizationAt, Submodule.localized'_inf]
    change localizationAt R v U ⊓ localizationAt R v
      (S.inf (fun w ↦ saturation R w (N w))) = localizationAt R v L
    rw [local_finset_inf, hUL]
    have hall : S.inf (fun w ↦ localizationAt R v (saturation R w (N w))) = ⊤ := by
      apply top_unique
      apply Finset.le_inf
      intro w hw
      exact (local_saturation_of_ne R w v (fun heq ↦ hv (heq ▸ hw)) (N w) (hN w)).ge
    rw [hall, inf_top_eq]
  refine ⟨P, hPfg, hP, ?_, ?_⟩
  · intro v hv
    simpa only [N, if_pos hv] using
      carrier_eq_of_localization_eq R v (hlocal v (Finset.mem_union_left _ hv))
  · intro v hvT
    by_cases hv : v ∈ S
    · simpa only [N, if_neg hvT] using carrier_eq_of_localization_eq R v (hlocal v hv)
    · exact carrier_eq_of_localization_eq R v (hout v hv)

variable [Invertible (2 : K)]

/-- Patching norm-integral lattices gives an actual norm-integral lattice.
Integrality is recovered from the completed values at every finite prime. -/
theorem exists_patched_lattice (Q : QuadraticForm K V) (L : Lattice R Q)
    (T : Finset (HeightOneSpectrum R)) (M : HeightOneSpectrum R → Lattice R Q) :
    ∃ P : Lattice R Q,
      (∀ v ∈ T, carrier R v P.carrier = carrier R v (M v).carrier) ∧
      ∀ v ∉ T, carrier R v P.carrier = carrier R v L.carrier := by
  obtain ⟨N, hNfg, hN, hin, hout⟩ := exists_patched_module R L.carrier L.finite L.full T
    (fun v ↦ (M v).carrier) (fun v _ ↦ (M v).finite) (fun v _ ↦ (M v).full)
  have hint : ∀ x ∈ N, Q x ∈ R := by
    intro x hx
    apply mem_of_forall_finite_integral R
    intro v
    rw [← form_inclusion R v Q x]
    have hinc := inclusion_mem R v N hx
    by_cases hv : v ∈ T
    · rw [hin v hv] at hinc
      exact carrier_integral R v Q (M v).carrier (M v).integral _ hinc
    · rw [hout v hv] at hinc
      exact carrier_integral R v Q L.carrier L.integral _ hinc
  exact ⟨⟨N, hNfg, hN, hint⟩, hin, hout⟩

omit [Invertible (2 : K)] in
/-- The prescribed completed carriers determine the patched global module
uniquely over a non-field Dedekind coefficient ring. -/
theorem patched_module_unique (hR : ¬ IsField R) (T : Finset (HeightOneSpectrum R))
    {P P' L : Submodule R V} {M : HeightOneSpectrum R → Submodule R V}
    (hin : ∀ v ∈ T, carrier R v P = carrier R v (M v))
    (hout : ∀ v ∉ T, carrier R v P = carrier R v L)
    (hin' : ∀ v ∈ T, carrier R v P' = carrier R v (M v))
    (hout' : ∀ v ∉ T, carrier R v P' = carrier R v L) : P = P' := by
  apply CompletionDescent.submodule_eq_of_completed_carriers_eq R hR
  intro v
  by_cases hv : v ∈ T
  · exact (hin v hv).trans (hin' v hv).symm
  · exact (hout v hv).trans (hout' v hv).symm

/-- The local inclusion part of O'Meara 102:5 is recovered globally after
patching. The represented submodule may have smaller rank than the ambient lattice. -/
theorem exists_patched_lattice_containing (hR : ¬ IsField R) (Q : QuadraticForm K V)
    (L : Lattice R Q) (A : Submodule R V) (T : Finset (HeightOneSpectrum R))
    (M : HeightOneSpectrum R → Lattice R Q)
    (hin : ∀ v ∈ T, carrier R v A ≤ carrier R v (M v).carrier)
    (hout : ∀ v ∉ T, carrier R v A ≤ carrier R v L.carrier) :
    ∃ P : Lattice R Q, A ≤ P.carrier ∧
      (∀ v ∈ T, carrier R v P.carrier = carrier R v (M v).carrier) ∧
      ∀ v ∉ T, carrier R v P.carrier = carrier R v L.carrier := by
  obtain ⟨P, hPin, hPout⟩ := exists_patched_lattice R Q L T M
  refine ⟨P, ?_, hPin, hPout⟩
  intro x hx
  apply FixedValueVectors.mem_of_all_completed R hR P.carrier
  intro v
  by_cases hv : v ∈ T
  · rw [hPin v hv]
    exact hin v hv (inclusion_mem R v A hx)
  · rw [hPout v hv]
    exact hout v hv (inclusion_mem R v A hx)

end NormEuclidean.LocalLatticePatching
