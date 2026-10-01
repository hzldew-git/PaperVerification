import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk128
import TraceEuclidean.VoightAllIrreducible
import TraceEuclidean.VoightIntegralBasisCertificate
import TraceEuclidean.VoightPolynomialBridge
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers.CertifyAdjoinRootCore
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers.MaximalAPI
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers.CertificateDedekind
import Mathlib.Tactic

set_option linter.all false
set_option maxHeartbeats 5000000

namespace TraceEuclidean

namespace VoightMaximalOrderD7R47

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨81437164, [-1, -4, 2, 12, -1, -7, 0, 1], 1⟩
local notation "l" => [-1, -4, 2, 12, -1, -7, 0, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSeven := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSeven_irreducible row row_mem
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
  a := ![![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![1, 4, -2, -12, 1, 7, 0]], ![![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![1, 4, -2, -12, 1, 7, 0], ![0, 1, 4, -2, -12, 1, 7]], ![![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![1, 4, -2, -12, 1, 7, 0], ![0, 1, 4, -2, -12, 1, 7], ![7, 28, -13, -80, 5, 37, 1]], ![![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![1, 4, -2, -12, 1, 7, 0], ![0, 1, 4, -2, -12, 1, 7], ![7, 28, -13, -80, 5, 37, 1], ![1, 11, 26, -25, -79, 12, 37]], ![![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![1, 4, -2, -12, 1, 7, 0], ![0, 1, 4, -2, -12, 1, 7], ![7, 28, -13, -80, 5, 37, 1], ![1, 11, 26, -25, -79, 12, 37], ![37, 149, -63, -418, 12, 180, 12]], ![![0, 0, 0, 0, 0, 0, 1], ![1, 4, -2, -12, 1, 7, 0], ![0, 1, 4, -2, -12, 1, 7], ![7, 28, -13, -80, 5, 37, 1], ![1, 11, 26, -25, -79, 12, 37], ![37, 149, -63, -418, 12, 180, 12], ![12, 85, 125, -207, -406, 96, 180]]]
  s := ![![[], [], [], [], [], [], []], ![[], [], [], [], [], [], [-1]], ![[], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [-1], [0, -1], [-7, 0, -1]], ![[], [], [], [-1], [0, -1], [-7, 0, -1], [-1, -7, 0, -1]], ![[], [], [-1], [0, -1], [-7, 0, -1], [-1, -7, 0, -1], [-37, -1, -7, 0, -1]], ![[], [-1], [0, -1], [-7, 0, -1], [-1, -7, 0, -1], [-37, -1, -7, 0, -1], [-12, -37, -1, -7, 0, -1]]]
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
def Table : Fin 7 → Fin 7 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [1, 4, -2, -12, 1, 7, 0]], ![[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [1, 4, -2, -12, 1, 7, 0], [0, 1, 4, -2, -12, 1, 7]], ![[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [1, 4, -2, -12, 1, 7, 0], [0, 1, 4, -2, -12, 1, 7], [7, 28, -13, -80, 5, 37, 1]], ![[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [1, 4, -2, -12, 1, 7, 0], [0, 1, 4, -2, -12, 1, 7], [7, 28, -13, -80, 5, 37, 1], [1, 11, 26, -25, -79, 12, 37]], ![[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [1, 4, -2, -12, 1, 7, 0], [0, 1, 4, -2, -12, 1, 7], [7, 28, -13, -80, 5, 37, 1], [1, 11, 26, -25, -79, 12, 37], [37, 149, -63, -418, 12, 180, 12]], ![[0, 0, 0, 0, 0, 0, 1], [1, 4, -2, -12, 1, 7, 0], [0, 1, 4, -2, -12, 1, 7], [7, 28, -13, -80, 5, 37, 1], [1, 11, 26, -25, -79, 12, 37], [37, 149, -63, -418, 12, 180, 12], [12, 85, 125, -207, -406, 96, 180]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp1787 : Fact (Nat.Prime 1787) := fact_iff.2 (by norm_num)
instance hp11393 : Fact (Nat.Prime 11393) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 1]
  b' := [0, 1, 0, 1, 1]
  k := [1, 0, 1, 0, 0, 1]
  f := [1, 3, 0, -5, 1, 4, 1]
  g := [1, 1, 1, 1, 0, 1, 1]
  h := [1, 1]
  a := [1, 0, 1, 1, 1, 1]
  b := [0, 1, 0, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1787 : CertificateDedekindCriterionLists l 1787 where
  n := 2
  a' := [1548, 271, 472, 1413, 598]
  b' := [258, 674, 1254, 669, 660, 496]
  k := [1667, 322, 1349, 1646, 1470, 1]
  f := [375, 519, 349, 788, 321, 433, 1]
  g := [637, 881, 592, 1338, 544, 735, 1]
  h := [1052, 1]
  a := [257, 1187, 1609, 1345, 648, 1378]
  b := [3, 625, 1454, 267, 924, 409]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11393 : CertificateDedekindCriterionLists l 11393 where
  n := 2
  a' := [10325, 9187, 3176, 9144, 6823]
  b' := [10018, 5855, 2919, 1770, 4290, 8357]
  k := [6822, 3244, 6273, 3956, 1373, 1]
  f := [4667, 639, 3993, 886, 578, 2807, 1]
  g := [10613, 1451, 9080, 2013, 1314, 6383, 1]
  h := [5010, 1]
  a := [3879, 5744, 1587, 1382, 6850, 10906]
  b := [7376, 2701, 6767, 6159, 6160, 487]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 1787, 11393]
  exp := ![1, 1, 1]
  pdgood := [2, 1787, 11393]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp1787.out
    exact hp11393.out
  a := [87407402, -382428564, -97849024, 429159472, 32089414, -90727959]
  b := [-32031496, -23831757, 138479300, 17592063, -87230770, -4584202, 12961137]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1787 T_ofList CD1787
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11393 T_ofList CD11393

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
  have htriangular : P.BlockTriangular id := by
    have hcheck :
        (List.ofFn fun i : Fin 7 =>
          (List.ofFn fun j : Fin 7 =>
            decide ((j : ℕ) < (i : ℕ) -> P i j = 0)).all id).all id =
          true := by native_decide
    simp only [List.all_eq_true, List.forall_mem_ofFn_iff, id_eq,
      decide_eq_true_eq] at hcheck
    intro i j hji
    exact hcheck i j hji
  rw [Matrix.det_of_upperTriangular htriangular]
  native_decide

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
    simpa [T] using
      (voightPolynomialDiscriminantInput 7 row row_mem)
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

end

end VoightMaximalOrderD7R47

namespace VoightMaximalOrderD7R57

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨89211436, [2, 0, -11, 1, 12, -3, -3, 1], 1⟩
local notation "l" => [2, 0, -11, 1, 12, -3, -3, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSeven := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSeven_irreducible row row_mem
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
  a := ![![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-2, 0, 11, -1, -12, 3, 3]], ![![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-2, 0, 11, -1, -12, 3, 3], ![-6, -2, 33, 8, -37, -3, 12]], ![![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-2, 0, 11, -1, -12, 3, 3], ![-6, -2, 33, 8, -37, -3, 12], ![-24, -6, 130, 21, -136, -1, 33]], ![![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-2, 0, 11, -1, -12, 3, 3], ![-6, -2, 33, 8, -37, -3, 12], ![-24, -6, 130, 21, -136, -1, 33], ![-66, -24, 357, 97, -375, -37, 98]], ![![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-2, 0, 11, -1, -12, 3, 3], ![-6, -2, 33, 8, -37, -3, 12], ![-24, -6, 130, 21, -136, -1, 33], ![-66, -24, 357, 97, -375, -37, 98], ![-196, -66, 1054, 259, -1079, -81, 257]], ![![0, 0, 0, 0, 0, 0, 1], ![-2, 0, 11, -1, -12, 3, 3], ![-6, -2, 33, 8, -37, -3, 12], ![-24, -6, 130, 21, -136, -1, 33], ![-66, -24, 357, 97, -375, -37, 98], ![-196, -66, 1054, 259, -1079, -81, 257], ![-514, -196, 2761, 797, -2825, -308, 690]]]
  s := ![![[], [], [], [], [], [], []], ![[], [], [], [], [], [], [-1]], ![[], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [-1], [-3, -1], [-12, -3, -1]], ![[], [], [], [-1], [-3, -1], [-12, -3, -1], [-33, -12, -3, -1]], ![[], [], [-1], [-3, -1], [-12, -3, -1], [-33, -12, -3, -1], [-98, -33, -12, -3, -1]], ![[], [-1], [-3, -1], [-12, -3, -1], [-33, -12, -3, -1], [-98, -33, -12, -3, -1], [-257, -98, -33, -12, -3, -1]]]
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
def Table : Fin 7 → Fin 7 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-2, 0, 11, -1, -12, 3, 3]], ![[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-2, 0, 11, -1, -12, 3, 3], [-6, -2, 33, 8, -37, -3, 12]], ![[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-2, 0, 11, -1, -12, 3, 3], [-6, -2, 33, 8, -37, -3, 12], [-24, -6, 130, 21, -136, -1, 33]], ![[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-2, 0, 11, -1, -12, 3, 3], [-6, -2, 33, 8, -37, -3, 12], [-24, -6, 130, 21, -136, -1, 33], [-66, -24, 357, 97, -375, -37, 98]], ![[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-2, 0, 11, -1, -12, 3, 3], [-6, -2, 33, 8, -37, -3, 12], [-24, -6, 130, 21, -136, -1, 33], [-66, -24, 357, 97, -375, -37, 98], [-196, -66, 1054, 259, -1079, -81, 257]], ![[0, 0, 0, 0, 0, 0, 1], [-2, 0, 11, -1, -12, 3, 3], [-6, -2, 33, 8, -37, -3, 12], [-24, -6, 130, 21, -136, -1, 33], [-66, -24, 357, 97, -375, -37, 98], [-196, -66, 1054, 259, -1079, -81, 257], [-514, -196, 2761, 797, -2825, -308, 690]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp22302859 : Fact (Nat.Prime 22302859) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1]
  b' := [1, 1, 1]
  k := [1, 1, 0, 1, 1, 1]
  f := [-1, 0, 6, 0, -6, 2, 2]
  g := [0, 1, 1, 0, 1, 1, 1]
  h := [0, 1]
  a := [1]
  b := []
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD22302859 : CertificateDedekindCriterionLists l 22302859 where
  n := 2
  a' := [2896278, 15309115, 9102805, 20109998, 4462699]
  b' := [18965456, 21290797, 19128239, 20618443, 21922791, 2973360]
  k := [17486256, 7209003, 15437286, 16796729, 18276844, 1]
  f := [448726, 434736, 226182, 1520897, 1358037, 1831317, 1]
  g := [4971606, 4816603, 2505954, 16850595, 15046200, 20289850, 1]
  h := [2013006, 1]
  a := [12601408, 1811555, 18861599, 1339163, 3784323, 9503803]
  b := [14347980, 8420198, 10384429, 19023356, 19954775, 12799056]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![2, 22302859]
  exp := ![1, 1]
  pdgood := [2, 22302859]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp22302859.out
  a := [22302859, -10268005, -167586487, 74132375, 78517419, -34862583]
  b := [-933455, -26513854, 7234921, 46404277, -15540608, -13351218, 4980369]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 22302859 T_ofList CD22302859

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
  have htriangular : P.BlockTriangular id := by
    have hcheck :
        (List.ofFn fun i : Fin 7 =>
          (List.ofFn fun j : Fin 7 =>
            decide ((j : ℕ) < (i : ℕ) -> P i j = 0)).all id).all id =
          true := by native_decide
    simp only [List.all_eq_true, List.forall_mem_ofFn_iff, id_eq,
      decide_eq_true_eq] at hcheck
    intro i j hji
    exact hcheck i j hji
  rw [Matrix.det_of_upperTriangular htriangular]
  native_decide

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
    simpa [T] using
      (voightPolynomialDiscriminantInput 7 row row_mem)
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

end

end VoightMaximalOrderD7R57

namespace VoightMaximalOrderD7R59

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨89916129, [1, -1, -10, 15, 6, -8, -1, 1], 1⟩
local notation "l" => [1, -1, -10, 15, 6, -8, -1, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSeven := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSeven_irreducible row row_mem
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
  a := ![![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-1, 1, 10, -15, -6, 8, 1]], ![![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-1, 1, 10, -15, -6, 8, 1], ![-1, 0, 11, -5, -21, 2, 9]], ![![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-1, 1, 10, -15, -6, 8, 1], ![-1, 0, 11, -5, -21, 2, 9], ![-9, 8, 90, -124, -59, 51, 11]], ![![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-1, 1, 10, -15, -6, 8, 1], ![-1, 0, 11, -5, -21, 2, 9], ![-9, 8, 90, -124, -59, 51, 11], ![-11, 2, 118, -75, -190, 29, 62]], ![![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-1, 1, 10, -15, -6, 8, 1], ![-1, 0, 11, -5, -21, 2, 9], ![-9, 8, 90, -124, -59, 51, 11], ![-11, 2, 118, -75, -190, 29, 62], ![-62, 51, 622, -812, -447, 306, 91]], ![![0, 0, 0, 0, 0, 0, 1], ![-1, 1, 10, -15, -6, 8, 1], ![-1, 0, 11, -5, -21, 2, 9], ![-9, 8, 90, -124, -59, 51, 11], ![-11, 2, 118, -75, -190, 29, 62], ![-62, 51, 622, -812, -447, 306, 91], ![-91, 29, 961, -743, -1358, 281, 397]]]
  s := ![![[], [], [], [], [], [], []], ![[], [], [], [], [], [], [-1]], ![[], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [-1], [-1, -1], [-9, -1, -1]], ![[], [], [], [-1], [-1, -1], [-9, -1, -1], [-11, -9, -1, -1]], ![[], [], [-1], [-1, -1], [-9, -1, -1], [-11, -9, -1, -1], [-62, -11, -9, -1, -1]], ![[], [-1], [-1, -1], [-9, -1, -1], [-11, -9, -1, -1], [-62, -11, -9, -1, -1], [-91, -62, -11, -9, -1, -1]]]
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
def Table : Fin 7 → Fin 7 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-1, 1, 10, -15, -6, 8, 1]], ![[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-1, 1, 10, -15, -6, 8, 1], [-1, 0, 11, -5, -21, 2, 9]], ![[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-1, 1, 10, -15, -6, 8, 1], [-1, 0, 11, -5, -21, 2, 9], [-9, 8, 90, -124, -59, 51, 11]], ![[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-1, 1, 10, -15, -6, 8, 1], [-1, 0, 11, -5, -21, 2, 9], [-9, 8, 90, -124, -59, 51, 11], [-11, 2, 118, -75, -190, 29, 62]], ![[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-1, 1, 10, -15, -6, 8, 1], [-1, 0, 11, -5, -21, 2, 9], [-9, 8, 90, -124, -59, 51, 11], [-11, 2, 118, -75, -190, 29, 62], [-62, 51, 622, -812, -447, 306, 91]], ![[0, 0, 0, 0, 0, 0, 1], [-1, 1, 10, -15, -6, 8, 1], [-1, 0, 11, -5, -21, 2, 9], [-9, 8, 90, -124, -59, 51, 11], [-11, 2, 118, -75, -190, 29, 62], [-62, 51, 622, -812, -447, 306, 91], [-91, 29, 961, -743, -1358, 281, 397]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp3330227 : Fact (Nat.Prime 3330227) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 3
  a' := [1, 2, 2, 2]
  b' := [0, 0, 2, 0, 2]
  k := [1, 1, 2, 1, 0, 0, 0, 1, 1]
  f := [0, 1, 4, -4, -1, 4, 1]
  g := [1, 1, 0, 2, 1, 1]
  h := [1, 1, 1]
  a := [0, 2, 2, 0, 1]
  b := [1, 2, 2, 1, 0, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3330227 : CertificateDedekindCriterionLists l 3330227 where
  n := 2
  a' := [2930232, 2920490, 1482668, 1244976, 3248482]
  b' := [533149, 2208807, 3257657, 184376, 724948, 568662]
  k := [661008, 1810520, 1638930, 1744148, 2016843, 1]
  f := [2249797, 1932965, 319366, 350642, 1718847, 703063, 1]
  g := [3226944, 2772502, 458074, 502935, 2465388, 1008421, 1]
  h := [2321805, 1]
  a := [2302701, 2828110, 2480013, 3125649, 2572794, 887364]
  b := [731469, 1826201, 843613, 156544, 533890, 2442863]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![3, 3330227]
  exp := ![1, 1]
  pdgood := [3, 3330227]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp3330227.out
  a := [-47028807, -1257272052, -132211204, 1101811264, 74092869, -187091086]
  b := [-57019488, -69853485, 426541658, 58603186, -220253207, -14402881, 26727298]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3330227 T_ofList CD3330227

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
  have htriangular : P.BlockTriangular id := by
    have hcheck :
        (List.ofFn fun i : Fin 7 =>
          (List.ofFn fun j : Fin 7 =>
            decide ((j : ℕ) < (i : ℕ) -> P i j = 0)).all id).all id =
          true := by native_decide
    simp only [List.all_eq_true, List.forall_mem_ofFn_iff, id_eq,
      decide_eq_true_eq] at hcheck
    intro i j hji
    exact hcheck i j hji
  rw [Matrix.det_of_upperTriangular htriangular]
  native_decide

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
    simpa [T] using
      (voightPolynomialDiscriminantInput 7 row row_mem)
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

end

end VoightMaximalOrderD7R59

namespace VoightMaximalOrderD7R67

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨97212489, [-1, -7, -5, 14, 5, -7, -1, 1], 1⟩
local notation "l" => [-1, -7, -5, 14, 5, -7, -1, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSeven := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSeven_irreducible row row_mem
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
  a := ![![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![1, 7, 5, -14, -5, 7, 1]], ![![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![1, 7, 5, -14, -5, 7, 1], ![1, 8, 12, -9, -19, 2, 8]], ![![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![1, 7, 5, -14, -5, 7, 1], ![1, 8, 12, -9, -19, 2, 8], ![8, 57, 48, -100, -49, 37, 10]], ![![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![1, 7, 5, -14, -5, 7, 1], ![1, 8, 12, -9, -19, 2, 8], ![8, 57, 48, -100, -49, 37, 10], ![10, 78, 107, -92, -150, 21, 47]], ![![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![1, 7, 5, -14, -5, 7, 1], ![1, 8, 12, -9, -19, 2, 8], ![8, 57, 48, -100, -49, 37, 10], ![10, 78, 107, -92, -150, 21, 47], ![47, 339, 313, -551, -327, 179, 68]], ![![0, 0, 0, 0, 0, 0, 1], ![1, 7, 5, -14, -5, 7, 1], ![1, 8, 12, -9, -19, 2, 8], ![8, 57, 48, -100, -49, 37, 10], ![10, 78, 107, -92, -150, 21, 47], ![47, 339, 313, -551, -327, 179, 68], ![68, 523, 679, -639, -891, 149, 247]]]
  s := ![![[], [], [], [], [], [], []], ![[], [], [], [], [], [], [-1]], ![[], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [-1], [-1, -1], [-8, -1, -1]], ![[], [], [], [-1], [-1, -1], [-8, -1, -1], [-10, -8, -1, -1]], ![[], [], [-1], [-1, -1], [-8, -1, -1], [-10, -8, -1, -1], [-47, -10, -8, -1, -1]], ![[], [-1], [-1, -1], [-8, -1, -1], [-10, -8, -1, -1], [-47, -10, -8, -1, -1], [-68, -47, -10, -8, -1, -1]]]
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
def Table : Fin 7 → Fin 7 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [1, 7, 5, -14, -5, 7, 1]], ![[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [1, 7, 5, -14, -5, 7, 1], [1, 8, 12, -9, -19, 2, 8]], ![[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [1, 7, 5, -14, -5, 7, 1], [1, 8, 12, -9, -19, 2, 8], [8, 57, 48, -100, -49, 37, 10]], ![[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [1, 7, 5, -14, -5, 7, 1], [1, 8, 12, -9, -19, 2, 8], [8, 57, 48, -100, -49, 37, 10], [10, 78, 107, -92, -150, 21, 47]], ![[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [1, 7, 5, -14, -5, 7, 1], [1, 8, 12, -9, -19, 2, 8], [8, 57, 48, -100, -49, 37, 10], [10, 78, 107, -92, -150, 21, 47], [47, 339, 313, -551, -327, 179, 68]], ![[0, 0, 0, 0, 0, 0, 1], [1, 7, 5, -14, -5, 7, 1], [1, 8, 12, -9, -19, 2, 8], [8, 57, 48, -100, -49, 37, 10], [10, 78, 107, -92, -150, 21, 47], [47, 339, 313, -551, -327, 179, 68], [68, 523, 679, -639, -891, 149, 247]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp267803 : Fact (Nat.Prime 267803) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 2
  a' := [2, 2, 0, 2]
  b' := [1, 2, 0, 2, 1, 2]
  k := [2, 1, 0, 1, 0, 1]
  f := [1, 3, 2, -4, -1, 3, 1]
  g := [2, 0, 1, 1, 1, 1, 1]
  h := [1, 1]
  a := [0, 2, 0, 1, 1]
  b := [2, 2, 2, 0, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [10, 0, 1, 3]
  b' := [6, 3, 4, 6, 6]
  k := [6, 10, 4, 1]
  f := [3, 9, 5, 6, 7, 4, 1]
  g := [4, 10, 2, 8, 7, 1]
  h := [8, 3, 1]
  a := [7, 5, 2, 5, 2]
  b := [6, 4, 4, 6, 1, 9]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD267803 : CertificateDedekindCriterionLists l 267803 where
  n := 2
  a' := [219372, 190512, 98572, 183416, 81537]
  b' := [29689, 20138, 228187, 50853, 212565, 120312]
  k := [79879, 6723, 72735, 111044, 237921, 1]
  f := [131129, 129298, 51866, 47816, 48145, 66117, 1]
  g := [235933, 232637, 93318, 86032, 86624, 118960, 1]
  h := [148842, 1]
  a := [106155, 80659, 66183, 252619, 189205, 72891]
  b := [151594, 92869, 6712, 115235, 47162, 194912]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![3, 11, 267803]
  exp := ![1, 1, 1]
  pdgood := [3, 11, 267803]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp11.out
    exact hp267803.out
  a := [18769192, -33667224, -30650097, 37000648, 8823277, -8341018]
  b := [-3943813, -8325570, 12870037, 7343467, -7634795, -1430693, 1191574]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 267803 T_ofList CD267803

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
  have htriangular : P.BlockTriangular id := by
    have hcheck :
        (List.ofFn fun i : Fin 7 =>
          (List.ofFn fun j : Fin 7 =>
            decide ((j : ℕ) < (i : ℕ) -> P i j = 0)).all id).all id =
          true := by native_decide
    simp only [List.all_eq_true, List.forall_mem_ofFn_iff, id_eq,
      decide_eq_true_eq] at hcheck
    intro i j hji
    exact hcheck i j hji
  rw [Matrix.det_of_upperTriangular htriangular]
  native_decide

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
    simpa [T] using
      (voightPolynomialDiscriminantInput 7 row row_mem)
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

end

end VoightMaximalOrderD7R67

end TraceEuclidean
