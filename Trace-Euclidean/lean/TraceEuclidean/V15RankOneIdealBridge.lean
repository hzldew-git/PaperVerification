import TraceEuclidean.V15GeneralBinaryRadius
import TraceEuclidean.V15RankOneIntegral
import TraceEuclidean.V15IdealCoordinates
import TraceEuclidean.V15IdealNormQuotient

/-!
Every abstract rank-one lattice presentation in the formal project is an
actual fractional-ideal lattice after choosing its one field coordinate.
The theorem retains the lattice, quadratic form, positivity, integrality,
and strict trace-Euclidean condition rather than just their numerical data.
-/

namespace TraceEuclidean

open scoped NumberField nonZeroDivisors

noncomputable section

namespace GlobalLatticePresentation

private def rankOneCoordinate (P : GlobalLatticePresentation) :
    Fin P.rank → P.field.1 := fun _ ↦ 1

private def rankOneMap (P : GlobalLatticePresentation) :
    P.L →ₗ[𝓞 P.field.1] P.field.1 :=
  (LinearMap.proj (R := 𝓞 P.field.1)
    (φ := fun _ : Fin P.rank ↦ P.field.1) ⟨0, P.rankPositive⟩).comp P.L.subtype

/-- The first coordinate of a full lattice, viewed as a fractional ideal. -/
def rankOneFractionalIdeal (P : GlobalLatticePresentation) :
    FractionalIdeal (nonZeroDivisors (𝓞 P.field.1)) P.field.1 := by
  letI : P.L.IsLattice P.field.1 := P.full
  exact ⟨(rankOneMap P).range,
    FractionalIdeal.isFractional_of_fg (Submodule.fg_range (rankOneMap P))⟩

@[simp] private theorem rankOneFractionalIdeal_coe (P : GlobalLatticePresentation) :
    (P.rankOneFractionalIdeal).coeToSubmodule = (rankOneMap P).range := rfl

private theorem rankOneFractionalIdeal_ne_zero (P : GlobalLatticePresentation) :
    P.rankOneFractionalIdeal ≠ 0 := by
  rw [← FractionalIdeal.coeToSubmodule_ne_bot,
    rankOneFractionalIdeal_coe]
  intro hrange
  have hzero : ∀ x : P.L, rankOneMap P x = 0 := by
    intro x
    have hx : rankOneMap P x ∈ (rankOneMap P).range :=
      LinearMap.mem_range_self (rankOneMap P) x
    rw [hrange] at hx
    simpa using hx
  let p : (Fin P.rank → P.field.1) →ₗ[P.field.1] P.field.1 :=
    LinearMap.proj (R := P.field.1)
      (φ := fun _ : Fin P.rank ↦ P.field.1) ⟨0, P.rankPositive⟩
  have hle : Submodule.span P.field.1
      (P.L : Set (Fin P.rank → P.field.1)) ≤ p.ker := by
    apply Submodule.span_le.mpr
    intro x hx
    change p x = 0
    exact hzero ⟨x, hx⟩
  have htop : (⊤ : Submodule P.field.1 (Fin P.rank → P.field.1)) ≤ p.ker := by
    simpa only [P.full.span_eq_top] using hle
  have hbasis : Pi.basisFun P.field.1 (Fin P.rank) ⟨0, P.rankPositive⟩ ∈ p.ker :=
    htop Submodule.mem_top
  simp [p, Pi.basisFun_apply] at hbasis

private theorem rankOneCoordinate_unique (P : GlobalLatticePresentation)
    (hrank : P.rank = 1) (x : Fin P.rank → P.field.1) :
    x = x ⟨0, P.rankPositive⟩ • P.rankOneCoordinate := by
  funext i
  have hi : i = (⟨0, P.rankPositive⟩ : Fin P.rank) := by
    apply Fin.ext
    have hlt := i.isLt
    omega
  subst i
  simp [rankOneCoordinate, smul_eq_mul]

private theorem rankOneFractionalIdeal_mem (P : GlobalLatticePresentation)
    (hrank : P.rank = 1) (x : Fin P.rank → P.field.1) :
    x ∈ P.L ↔ x ⟨0, P.rankPositive⟩ ∈ P.rankOneFractionalIdeal := by
  rw [← FractionalIdeal.mem_coe, rankOneFractionalIdeal_coe]
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, hy⟩
    have hxy : x = y.1 := by
      funext i
      have hi : i = (⟨0, P.rankPositive⟩ : Fin P.rank) := by
        apply Fin.ext
        have hlt := i.isLt
        omega
      subst i
      exact hy.symm
    simpa only [hxy] using y.2

private theorem rankOneQuadratic_formula (P : GlobalLatticePresentation)
    (hrank : P.rank = 1) (x : Fin P.rank → P.field.1) :
    P.Q x = P.Q P.rankOneCoordinate *
      (x ⟨0, P.rankPositive⟩) ^ 2 := by
  calc
    P.Q x = P.Q (x ⟨0, P.rankPositive⟩ • P.rankOneCoordinate) := by
      rw [← P.rankOneCoordinate_unique hrank x]
    _ = (x ⟨0, P.rankPositive⟩) ^ 2 * P.Q P.rankOneCoordinate := by
      rw [QuadraticMap.map_smul]
      simp only [smul_eq_mul, pow_two]
    _ = P.Q P.rankOneCoordinate * (x ⟨0, P.rankPositive⟩) ^ 2 := by ring

private theorem rankOneCoefficient_positive (P : GlobalLatticePresentation) :
    ∀ σ : P.field.1 →+* ℝ, 0 < σ (P.Q P.rankOneCoordinate) := by
  have he : P.rankOneCoordinate ≠ 0 := by
    intro h
    have h0 := congrArg (fun x : Fin P.rank → P.field.1 ↦
      x ⟨0, P.rankPositive⟩) h
    simp [rankOneCoordinate] at h0
  exact P.positiveDefinite P.rankOneCoordinate he

private theorem rankOneValue_integral (P : GlobalLatticePresentation)
    (hrank : P.rank = 1) :
    ∀ x : P.rankOneFractionalIdeal,
      IsIntegral ℤ
        (P.Q P.rankOneCoordinate * (x : P.field.1) ^ 2) := by
  intro x
  have hx : (x : P.field.1) ∈ (rankOneMap P).range := by
    have hx' : (x : P.field.1) ∈
        (P.rankOneFractionalIdeal).coeToSubmodule :=
      FractionalIdeal.mem_coe.mpr x.2
    simpa only [rankOneFractionalIdeal_coe] using hx'
  obtain ⟨y, hy⟩ := hx
  have hQ := P.integral y
  rw [rankOneQuadratic_formula P hrank] at hQ
  change y.1 ⟨0, P.rankPositive⟩ = (x : P.field.1) at hy
  simpa only [hy] using hQ

private theorem rankOneIdeal_integral (P : GlobalLatticePresentation)
    (hrank : P.rank = 1) :
    v15ValueFractionalIdeal P.rankOneFractionalIdeal
      (P.Q P.rankOneCoordinate) ≤ 1 := by
  let I := P.rankOneFractionalIdeal
  let α := P.Q P.rankOneCoordinate
  have hvalues : ∀ x : I, IsIntegral ℤ (α * (x : P.field.1) ^ 2) :=
    P.rankOneValue_integral hrank
  have hclassic := v15_ideal_classic_of_integral I α hvalues
  change FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 P.field.1)) α * I ^ 2 ≤ 1
  rw [pow_two, ← mul_assoc, FractionalIdeal.mul_le]
  intro w hw y hy
  obtain ⟨x, hx, hwx⟩ := (FractionalIdeal.mem_singleton_mul).mp hw
  rw [hwx]
  have hxy : IsIntegral ℤ (α * x * y) := hclassic ⟨x, hx⟩ ⟨y, hy⟩
  exact (FractionalIdeal.mem_one_iff _).mpr ⟨⟨_, hxy⟩, rfl⟩

/-- The ideal trace condition at an arbitrary real threshold. -/
def V15IdealTraceEuclideanAt
    {F : Type*} [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (α : F) (t : ℝ) : Prop :=
  ∀ x : F, ∃ y : I,
    ((Algebra.trace ℚ F (α * (x - (y : F)) ^ 2) : ℚ) : ℝ) < t

/-- Every positive integral rank-one global lattice is an actual fractional
ideal with a totally positive quadratic coefficient; the trace-Euclidean
condition at any real threshold is equivalent under this presentation. -/
theorem rankOne_ideal_bridge_at (P : GlobalLatticePresentation)
    (hrank : P.rank = 1) (t : ℝ) :
    ∃ (I : FractionalIdeal (nonZeroDivisors (𝓞 P.field.1)) P.field.1)
      (α : P.field.1),
      I ≠ 0 ∧
      (∀ x : Fin P.rank → P.field.1,
        x ∈ P.L ↔ x ⟨0, P.rankPositive⟩ ∈ I) ∧
      (∀ x : Fin P.rank → P.field.1,
        P.Q x = α * (x ⟨0, P.rankPositive⟩) ^ 2) ∧
      (∀ σ : P.field.1 →+* ℝ, 0 < σ α) ∧
      v15ValueFractionalIdeal I α ≤ 1 ∧
      (P.IsTraceEuclidean t ↔ V15IdealTraceEuclideanAt I α t) := by
  let I := P.rankOneFractionalIdeal
  let α := P.Q P.rankOneCoordinate
  refine ⟨I, α, P.rankOneFractionalIdeal_ne_zero,
    P.rankOneFractionalIdeal_mem hrank,
    P.rankOneQuadratic_formula hrank,
    P.rankOneCoefficient_positive,
    P.rankOneIdeal_integral hrank, ?_⟩
  constructor
  · intro h x
    let u : Fin P.rank → P.field.1 := fun _ ↦ x
    obtain ⟨y, hy⟩ := h u
    let z : I := ⟨y.1 ⟨0, P.rankPositive⟩,
      (P.rankOneFractionalIdeal_mem hrank y.1).mp y.2⟩
    refine ⟨z, ?_⟩
    have hform := P.rankOneQuadratic_formula hrank (u - y.1)
    have heq : P.Q (u - y.1) = α * (x - (z : P.field.1)) ^ 2 := by
      simpa [u, z, Pi.sub_apply] using hform
    rw [heq] at hy
    exact hy
  · intro h x
    obtain ⟨z, hz⟩ := h (x ⟨0, P.rankPositive⟩)
    let y : P.L := ⟨(fun _ ↦ (z : P.field.1)),
      (P.rankOneFractionalIdeal_mem hrank _).mpr z.2⟩
    refine ⟨y, ?_⟩
    have hform := P.rankOneQuadratic_formula hrank (x - y.1)
    have heq : P.Q (x - y.1) =
        α * (x ⟨0, P.rankPositive⟩ - (z : P.field.1)) ^ 2 := by
      simpa [y, Pi.sub_apply] using hform
    rw [heq]
    exact hz

/-- For a rank-one lattice, the ideal presentation respects the manuscript's
threshold equal to the degree of its ground field. -/
theorem rankOne_ideal_bridge_degree (P : GlobalLatticePresentation)
    (hrank : P.rank = 1) :
    ∃ (I : FractionalIdeal (nonZeroDivisors (𝓞 P.field.1)) P.field.1)
      (α : P.field.1),
      I ≠ 0 ∧
      (∀ x : Fin P.rank → P.field.1,
        x ∈ P.L ↔ x ⟨0, P.rankPositive⟩ ∈ I) ∧
      (∀ x : Fin P.rank → P.field.1,
        P.Q x = α * (x ⟨0, P.rankPositive⟩) ^ 2) ∧
      (∀ σ : P.field.1 →+* ℝ, 0 < σ α) ∧
      v15ValueFractionalIdeal I α ≤ 1 ∧
      (P.IsTraceEuclidean (P.degree : ℝ) ↔
        V15IdealTraceEuclideanAt I α (P.degree : ℝ)) :=
  P.rankOne_ideal_bridge_at hrank P.degree

/-- The quadratic specialization used by the six-class classification. -/
theorem rankOne_ideal_bridge (P : GlobalLatticePresentation)
    (hrank : P.rank = 1) :
    ∃ (I : FractionalIdeal (nonZeroDivisors (𝓞 P.field.1)) P.field.1)
      (α : P.field.1),
      I ≠ 0 ∧
      (∀ x : Fin P.rank → P.field.1,
        x ∈ P.L ↔ x ⟨0, P.rankPositive⟩ ∈ I) ∧
      (∀ x : Fin P.rank → P.field.1,
        P.Q x = α * (x ⟨0, P.rankPositive⟩) ^ 2) ∧
      (∀ σ : P.field.1 →+* ℝ, 0 < σ α) ∧
      v15ValueFractionalIdeal I α ≤ 1 ∧
      (P.IsTraceEuclidean 2 ↔ V15IdealTraceEuclidean I α) := by
  obtain ⟨I, α, hI, hmem, hQ, hpos, hint, heq⟩ :=
    P.rankOne_ideal_bridge_at hrank 2
  refine ⟨I, α, hI, hmem, hQ, hpos, hint, ?_⟩
  rw [heq]
  constructor
  · intro h x
    obtain ⟨y, hy⟩ := h x
    exact ⟨y, by exact_mod_cast hy⟩
  · intro h x
    obtain ⟨y, hy⟩ := h x
    exact ⟨y, by exact_mod_cast hy⟩

end GlobalLatticePresentation

end

end TraceEuclidean
