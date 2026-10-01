import TraceEuclidean.DegreeSevenRows200To299ExceptionalDiscriminant
import TraceEuclidean.FiniteFieldIrreducibilityCertificate
import TraceEuclidean.CriticalFieldBridge
import TraceEuclidean.VoightIntegralBasisCertificate
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers.CertifyAdjoinRootCore
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers.MaximalAPI
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers.CertificateDedekind
import Mathlib.Tactic

set_option linter.all false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

namespace TraceEuclidean
namespace DegreeSevenRows200To299ExceptionalMaximalOrder

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1222840301, [-1, -5, -2, 13, 7, -9, -3, 1], 1⟩
local notation "l" => [-1, -5, -2, 13, 7, -9, -3, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
def irreducibilityCertificate :
    RabinIrreducibilityCertificate :=
  ⟨7,
    [[0, 1], [1, 5, 2, 1, 0, 2, 3], [6, 5, 5, 4, 1, 5, 6], [6, 5, 4, 1, 4, 3, 2], [0, 5, 5, 5, 1, 0, 3], [5, 0, 2, 3, 5, 4, 2], [6, 0, 3, 0, 3, 0, 5], [0, 1]],
    [[1], [5, 1, 4, 5, 2, 6, 6, 1, 5, 1, 6, 5, 4, 6, 2, 6, 3, 3, 3, 0, 0, 2, 2, 2, 6, 2, 0, 1, 6, 1, 4, 0, 5, 5, 2, 3], [0, 5, 0, 5, 2, 4, 5, 1, 4, 3, 2, 2, 5, 5, 4, 5, 4, 1, 1, 6, 6, 4, 2, 3, 5, 1, 4, 5, 6, 2, 1, 0, 3, 3, 4, 6], [1, 0, 3, 3, 1, 5, 5, 3, 4, 3, 6, 6, 2, 2, 3, 4, 1, 3, 3, 3, 3, 6, 5, 2, 4, 1, 2, 1, 1, 3, 5, 0, 1, 1, 6, 2], [5, 3, 5, 2, 3, 5, 4, 4, 0, 2, 4, 5, 6, 4, 0, 0, 4, 6, 4, 0, 4, 5, 6, 4, 6, 1, 6, 2, 4, 1, 4, 0, 5, 5, 2, 3], [1, 2, 5, 5, 1, 6, 3, 6, 5, 4, 3, 5, 6, 2, 3, 4, 6, 5, 5, 2, 2, 6, 3, 1, 4, 5, 6, 4, 2, 3, 5, 0, 1, 1, 6, 2], [1, 3, 4, 1, 5, 2, 5, 6, 3, 1, 0, 5, 5, 2, 2, 2, 3, 3, 5, 3, 6, 5, 3, 2, 3, 4, 3, 1, 2, 4, 2, 0, 6, 6, 1, 5]],
    [[], [2, 6, 6, 5, 1, 4], [], [], [], [], []],
    [[], [3, 4, 4, 1, 0, 3, 1], [], [], [], [], []]⟩

lemma irreducibilityCertificate_checked :
    irreducibilityCertificate.check 7 row = true := by
  decide

lemma T_irreducible : Irreducible T :=
  RabinIrreducibilityCertificate.irreducible_of_check_eq_true
    irreducibilityCertificate_checked
lemma T_monic : Monic T := by
  rw [← T_ofList]
  exact monic_ofList l rfl

abbrev K := AdjoinRoot (map (algebraMap ℤ ℚ) T)
instance hirr : Fact (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map T_monic).1
    T_irreducible
instance KField : Field K := AdjoinRoot.instField
instance : Algebra ℤ K := Ring.toIntAlgebra K
instance : IsScalarTower ℤ ℚ K :=
  IsScalarTower.of_algebraMap_eq' (by ext; simp)
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
  AdjoinRoot.isAdjoinRoot _
local notation "θ" => Adj.root

def basisDenominator : ℤ := 1
def basisNumerator : Fin 7 → Fin 7 → ℤ := ![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 7 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![1, 5, 2, -13, -7, 9, 3]], ![![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![1, 5, 2, -13, -7, 9, 3], ![3, 16, 11, -37, -34, 20, 18]], ![![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![1, 5, 2, -13, -7, 9, 3], ![3, 16, 11, -37, -34, 20, 18], ![18, 93, 52, -223, -163, 128, 74]], ![![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![1, 5, 2, -13, -7, 9, 3], ![3, 16, 11, -37, -34, 20, 18], ![18, 93, 52, -223, -163, 128, 74], ![74, 388, 241, -910, -741, 503, 350]], ![![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![1, 5, 2, -13, -7, 9, 3], ![3, 16, 11, -37, -34, 20, 18], ![18, 93, 52, -223, -163, 128, 74], ![74, 388, 241, -910, -741, 503, 350], ![350, 1824, 1088, -4309, -3360, 2409, 1553]], ![![0, 0, 0, 0, 0, 0, 1], ![1, 5, 2, -13, -7, 9, 3], ![3, 16, 11, -37, -34, 20, 18], ![18, 93, 52, -223, -163, 128, 74], ![74, 388, 241, -910, -741, 503, 350], ![350, 1824, 1088, -4309, -3360, 2409, 1553], ![1553, 8115, 4930, -19101, -15180, 10617, 7068]]]
  s := ![![[], [], [], [], [], [], []], ![[], [], [], [], [], [], [-1]], ![[], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [-1], [-3, -1], [-18, -3, -1]], ![[], [], [], [-1], [-3, -1], [-18, -3, -1], [-74, -18, -3, -1]], ![[], [], [-1], [-3, -1], [-18, -3, -1], [-74, -18, -3, -1], [-350, -74, -18, -3, -1]], ![[], [-1], [-3, -1], [-18, -3, -1], [-74, -18, -3, -1], [-350, -74, -18, -3, -1], [-1553, -350, -74, -18, -3, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 7 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 7) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 7) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 7) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 7 → Fin 7 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [1, 5, 2, -13, -7, 9, 3]], ![[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [1, 5, 2, -13, -7, 9, 3], [3, 16, 11, -37, -34, 20, 18]], ![[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [1, 5, 2, -13, -7, 9, 3], [3, 16, 11, -37, -34, 20, 18], [18, 93, 52, -223, -163, 128, 74]], ![[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [1, 5, 2, -13, -7, 9, 3], [3, 16, 11, -37, -34, 20, 18], [18, 93, 52, -223, -163, 128, 74], [74, 388, 241, -910, -741, 503, 350]], ![[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [1, 5, 2, -13, -7, 9, 3], [3, 16, 11, -37, -34, 20, 18], [18, 93, 52, -223, -163, 128, 74], [74, 388, 241, -910, -741, 503, 350], [350, 1824, 1088, -4309, -3360, 2409, 1553]], ![[0, 0, 0, 0, 0, 0, 1], [1, 5, 2, -13, -7, 9, 3], [3, 16, 11, -37, -34, 20, 18], [18, 93, 52, -223, -163, 128, 74], [74, 388, 241, -910, -741, 503, 350], [350, 1824, 1088, -4309, -3360, 2409, 1553], [1553, 8115, 4930, -19101, -15180, 10617, 7068]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0] [] (by decide)

instance hp73 : Fact (Nat.Prime 73) := fact_iff.2 (by norm_num)
instance hp229469 : Fact (Nat.Prime 229469) := fact_iff.2 (by norm_num)

def CD73 : CertificateDedekindCriterionLists l 73 where
  n := 3
  a' := [15, 23, 32, 70]
  b' := [23, 16, 52, 14, 59]
  k := [9, 21, 56, 42, 37, 21, 29, 2, 1]
  f := [1, 9, 32, 49, 30, 16, 1]
  g := [4, 26, 63, 37, 24, 1]
  h := [18, 46, 1]
  a := [39, 63, 23, 26, 68]
  b := [27, 13, 71, 15, 7, 5]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD229469 : CertificateDedekindCriterionLists l 229469 where
  n := 2
  a' := [53242, 28093, 143887, 224988, 176624]
  b' := [110328, 204380, 166545, 77473, 57932, 123542]
  k := [186523, 221771, 140641, 63651, 178276, 1]
  f := [20424, 4531, 2063, 6479, 5221, 22740, 1]
  g := [183109, 40615, 18494, 58086, 46806, 203871, 1]
  h := [25595, 1]
  a := [114355, 142364, 169435, 80059, 54045, 219357]
  b := [154467, 36109, 12088, 132337, 200310, 10112]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![73, 229469]
  exp := ![1, 1]
  pdgood := [73, 229469]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp73.out
    exact hp229469.out
  a := [181357173, -297778452, -738870511, 601568734, 365981793, -120792574]
  b := [-39621682, -90104137, 136043875, 175668007, -126921031, -59678577, 17256082]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 73 T_ofList CD73
    exact satisfiesDedekindCriterion_of_certificate_lists T l 229469 T_ofList CD229469

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ []
  · fin_cases hbad
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 7) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 7 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 7
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 7 := T_degree

noncomputable def bQ : Basis (Fin 7) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 7) (Fin 7) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 7) :
    bQ i = Adj.root ^ (i : ℕ) := by
  rw [show bQ i = pb.basis ((finCongr pb_dim).symm i) by
    exact Basis.reindex_apply pb.basis (finCongr pb_dim) i]
  rw [pb.basis_eq_pow, pb_gen]
  congr 1

lemma bOm_cast_eq_vecMul :
    (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) =
      Matrix.vecMul bQ (P.map (algebraMap ℚ K)) := by
  funext j
  change (timesTableO.basis j).val = _
  rw [timesTableO_basis_apply]
  rw [ofList_eq_sum']
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X]
  rw [_root_.map_mul, _root_.map_sum]
  rw [← IsAdjoinRoot.algebraMap_apply Adj]
  have hdist :
      (algebraMap ℚ K) ((algebraMap ℤ ℚ) basisDenominator)⁻¹ *
          (∑ x : Fin 7,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 7,
          (algebraMap ℚ K) ((algebraMap ℤ ℚ) basisDenominator)⁻¹ *
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ)) := by
    exact Finset.mul_sum Finset.univ _ _
  rw [hdist]
  rw [Matrix.vecMul_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [_root_.map_mul, ← IsAdjoinRoot.algebraMap_apply Adj,
    _root_.map_pow, IsAdjoinRoot.map_X Adj]
  rw [bQ_apply]
  simp [P, div_eq_mul_inv, mul_comm, mul_left_comm]

lemma bQ_discr : Algebra.discr ℚ bQ = (T.discr : ℚ) := by
  calc
    Algebra.discr ℚ bQ = Algebra.discr ℚ pb.basis := by
      simpa [bQ] using
        Algebra.discr_reindex ℚ pb.basis (finCongr pb_dim)
    _ = (minpoly ℚ pb.gen).discr :=
      powerBasis_discr_eq_minpoly_discr pb
    _ = (map (algebraMap ℤ ℚ) T).discr := by
      have hqmonic : (map (algebraMap ℤ ℚ) T).Monic :=
        T_monic.map (algebraMap ℤ ℚ)
      rw [show minpoly ℚ pb.gen = map (algebraMap ℤ ℚ) T by
        rw [pb_gen]
        calc
          minpoly ℚ Adj.root =
              map (algebraMap ℤ ℚ) T *
                C (map (algebraMap ℤ ℚ) T).leadingCoeff⁻¹ :=
            AdjoinRoot.minpoly_root hirr.out.ne_zero
          _ = map (algebraMap ℤ ℚ) T := by
            rw [hqmonic.leadingCoeff]
            simp]
    _ = (T.discr : ℚ) := by
      exact (intCast_discr_eq_discr_map T T_monic
        (T_degree ▸ by norm_num)).symm

lemma P_det_index_sq :
    P.det ^ 2 * (row.index : ℚ) ^ 2 = 1 := by
  have hP : P = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P, basisNumerator, basisDenominator]
  rw [hP]
  norm_num [row]


theorem field_discriminant_eq_recorded :
    NumberField.discr K = (row.fieldDiscriminant : ℤ) := by
  apply Rat.intCast_injective
  have hbOmCast :
      ((NumberField.discr K : ℤ) : ℚ) =
        Algebra.discr ℚ
          (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) := by
    rw [← bOm_discr]
    exact discr_ringOfIntegers_cast K bOm
  have hrecorded :
      T.discr = (row.index : ℤ) ^ 2 *
        (row.fieldDiscriminant : ℤ) := by
    simpa [T, row,
      DegreeSevenRows200To299ExceptionalDiscriminantCase006.row] using
      DegreeSevenRows200To299ExceptionalDiscriminantCase006.polynomial_discr
  have hrecordedQ :
      (T.discr : ℚ) = (row.index : ℚ) ^ 2 *
        (row.fieldDiscriminant : ℚ) := by
    exact_mod_cast hrecorded
  calc
    ((NumberField.discr K : ℤ) : ℚ) =
        Algebra.discr ℚ
          (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) :=
      hbOmCast
    _ = Algebra.discr ℚ
        (Matrix.vecMul bQ (P.map (algebraMap ℚ K))) := by
      rw [bOm_cast_eq_vecMul]
    _ = P.det ^ 2 * Algebra.discr ℚ bQ :=
      Algebra.discr_of_matrix_vecMul bQ P
    _ = P.det ^ 2 * (T.discr : ℚ) := by rw [bQ_discr]
    _ = P.det ^ 2 *
        ((row.index : ℚ) ^ 2 *
          (row.fieldDiscriminant : ℚ)) := by rw [hrecordedQ]
    _ = (P.det ^ 2 * (row.index : ℚ) ^ 2) *
        (row.fieldDiscriminant : ℚ) := by ring
    _ = (row.fieldDiscriminant : ℚ) := by
      rw [P_det_index_sq, one_mul]


/-- The exceptional polynomial generates only fields with its exact model
discriminant, because Dedekind's criterion proves that its power order is
already the full ring of integers. -/
theorem fieldDiscriminant_lowerBound
    {K' : Type*} [Field K'] [NumberField K']
    {f : ℤ[X]} (hfield : HunterFieldPolynomialCandidate K' 7 194 f)
    (hcoefficients : [-1, -5, -2, 13, 7, -9, -3, 1] =
      [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
        f.coeff 4, f.coeff 5, f.coeff 6, 1]) :
    20134393 ≤ (NumberField.discr K').natAbs := by
  have hf :
      f = polynomialOfCoefficients
        [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
          f.coeff 4, f.coeff 5, f.coeff 6, 1] :=
    degreeSeven_eq_polynomialOfCoefficients
      hfield.1.1 hfield.1.2.2.1
  have hT : T = f := by
    calc
      T = polynomialOfCoefficients [-1, -5, -2, 13, 7, -9, -3, 1] := by rfl
      _ = polynomialOfCoefficients
          [f.coeff 0, f.coeff 1, f.coeff 2, f.coeff 3,
            f.coeff 4, f.coeff 5, f.coeff 6, 1] := by rw [hcoefficients]
      _ = f := hf.symm
  rcases hfield.2 with ⟨a, hgen, hminpoly, index, hindex, hrelation⟩
  have hexact : NumberField.discr K' = (1222840301 : ℤ) :=
    numberField_discr_eq_of_adjoinRoot_model
      field_discriminant_eq_recorded a (hT.trans hminpoly) hgen
  rw [hexact]
  norm_num

def lowerBoundCertificate :
    DegreeSevenFieldDiscriminantLowerBoundCertificate :=
  { coefficients := [-1, -5, -2, 13, 7, -9, -3, 1]
    lowerBound := fun hfield hcoefficients =>
      fieldDiscriminant_lowerBound hfield hcoefficients }

end

end DegreeSevenRows200To299ExceptionalMaximalOrder
end TraceEuclidean
