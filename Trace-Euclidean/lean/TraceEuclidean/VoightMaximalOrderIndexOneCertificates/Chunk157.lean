import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk153
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

namespace VoightMaximalOrderD8R99

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1879038125, [5, -5, -31, -4, 28, 5, -9, -1, 1], 1⟩
local notation "l" => [5, -5, -31, -4, 28, 5, -9, -1, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsEight := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsEight_irreducible row row_mem
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
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 31, 4, -28, -5, 9, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 31, 4, -28, -5, 9, 1], ![-5, 0, 36, 35, -24, -33, 4, 10]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 31, 4, -28, -5, 9, 1], ![-5, 0, 36, 35, -24, -33, 4, 10], ![-50, 45, 310, 76, -245, -74, 57, 14]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 31, 4, -28, -5, 9, 1], ![-5, 0, 36, 35, -24, -33, 4, 10], ![-50, 45, 310, 76, -245, -74, 57, 14], ![-70, 20, 479, 366, -316, -315, 52, 71]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 31, 4, -28, -5, 9, 1], ![-5, 0, 36, 35, -24, -33, 4, 10], ![-50, 45, 310, 76, -245, -74, 57, 14], ![-70, 20, 479, 366, -316, -315, 52, 71], ![-355, 285, 2221, 763, -1622, -671, 324, 123]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 31, 4, -28, -5, 9, 1], ![-5, 0, 36, 35, -24, -33, 4, 10], ![-50, 45, 310, 76, -245, -74, 57, 14], ![-70, 20, 479, 366, -316, -315, 52, 71], ![-355, 285, 2221, 763, -1622, -671, 324, 123], ![-615, 260, 4098, 2713, -2681, -2237, 436, 447]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 31, 4, -28, -5, 9, 1], ![-5, 0, 36, 35, -24, -33, 4, 10], ![-50, 45, 310, 76, -245, -74, 57, 14], ![-70, 20, 479, 366, -316, -315, 52, 71], ![-355, 285, 2221, 763, -1622, -671, 324, 123], ![-615, 260, 4098, 2713, -2681, -2237, 436, 447], ![-2235, 1620, 14117, 5886, -9803, -4916, 1786, 883]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-10, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-10, -1, -1], [-14, -10, -1, -1]], ![[], [], [], [-1], [-1, -1], [-10, -1, -1], [-14, -10, -1, -1], [-71, -14, -10, -1, -1]], ![[], [], [-1], [-1, -1], [-10, -1, -1], [-14, -10, -1, -1], [-71, -14, -10, -1, -1], [-123, -71, -14, -10, -1, -1]], ![[], [-1], [-1, -1], [-10, -1, -1], [-14, -10, -1, -1], [-71, -14, -10, -1, -1], [-123, -71, -14, -10, -1, -1], [-447, -123, -71, -14, -10, -1, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 8 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 8) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 8) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 8) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 31, 4, -28, -5, 9, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 31, 4, -28, -5, 9, 1], [-5, 0, 36, 35, -24, -33, 4, 10]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 31, 4, -28, -5, 9, 1], [-5, 0, 36, 35, -24, -33, 4, 10], [-50, 45, 310, 76, -245, -74, 57, 14]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 31, 4, -28, -5, 9, 1], [-5, 0, 36, 35, -24, -33, 4, 10], [-50, 45, 310, 76, -245, -74, 57, 14], [-70, 20, 479, 366, -316, -315, 52, 71]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 31, 4, -28, -5, 9, 1], [-5, 0, 36, 35, -24, -33, 4, 10], [-50, 45, 310, 76, -245, -74, 57, 14], [-70, 20, 479, 366, -316, -315, 52, 71], [-355, 285, 2221, 763, -1622, -671, 324, 123]], ![[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 31, 4, -28, -5, 9, 1], [-5, 0, 36, 35, -24, -33, 4, 10], [-50, 45, 310, 76, -245, -74, 57, 14], [-70, 20, 479, 366, -316, -315, 52, 71], [-355, 285, 2221, 763, -1622, -671, 324, 123], [-615, 260, 4098, 2713, -2681, -2237, 436, 447]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 31, 4, -28, -5, 9, 1], [-5, 0, 36, 35, -24, -33, 4, 10], [-50, 45, 310, 76, -245, -74, 57, 14], [-70, 20, 479, 366, -316, -315, 52, 71], [-355, 285, 2221, 763, -1622, -671, 324, 123], [-615, 260, 4098, 2713, -2681, -2237, 436, 447], [-2235, 1620, 14117, 5886, -9803, -4916, 1786, 883]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp3006461 : Fact (Nat.Prime 3006461) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 1]
  b' := [2, 0, 1]
  k := [1]
  f := [-1, 1, 8, 2, -3, 1, 3, 1]
  g := [0, 3, 1, 2, 1]
  h := [0, 3, 1, 2, 1]
  a := [4, 3, 3, 2]
  b := [3, 0, 2, 0, 3, 0, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3006461 : CertificateDedekindCriterionLists l 3006461 where
  n := 2
  a' := [2676527, 66504, 672960, 1660302, 2517185, 592978]
  b' := [1290881, 2438138, 2366577, 2872471, 2171772, 435258, 2062761]
  k := [2560952, 2635729, 410590, 1661844, 833931, 398096, 1]
  f := [359077, 1138364, 1278796, 751826, 73178, 743891, 738437, 1]
  g := [827761, 2624209, 2947938, 1733142, 168692, 1714852, 1702278, 1]
  h := [1304182, 1]
  a := [1818776, 2306284, 20410, 80703, 1399891, 2926641, 1744540]
  b := [1387157, 1620118, 1668364, 2936334, 399271, 2743419, 1261921]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 3006461]
  exp := ![1, 1]
  pdgood := [5, 3006461]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp3006461.out
  a := [11898821, 104197332, -66071676, -154223302, 72264240, 46045488, -20687488]
  b := [8892360, -17966753, -42595625, 26800680, 31315066, -14414762, -6078928, 2585936]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3006461 T_ofList CD3006461

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

noncomputable def bOm : Basis (Fin 8) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 8 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 8
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 8 := T_degree

noncomputable def bQ : Basis (Fin 8) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 8) (Fin 8) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 8) :
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
          (∑ x : Fin 8,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 8,
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
        (List.ofFn fun i : Fin 8 =>
          (List.ofFn fun j : Fin 8 =>
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
      (voightPolynomialDiscriminantInput 8 row row_mem)
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

end VoightMaximalOrderD8R99

namespace VoightMaximalOrderD8R100

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1882030625, [-1, -1, 19, -27, -5, 21, -5, -3, 1], 1⟩
local notation "l" => [-1, -1, 19, -27, -5, 21, -5, -3, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsEight := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsEight_irreducible row row_mem
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
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -19, 27, 5, -21, 5, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -19, 27, 5, -21, 5, 3], ![3, 4, -56, 62, 42, -58, -6, 14]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -19, 27, 5, -21, 5, 3], ![3, 4, -56, 62, 42, -58, -6, 14], ![14, 17, -262, 322, 132, -252, 12, 36]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -19, 27, 5, -21, 5, 3], ![3, 4, -56, 62, 42, -58, -6, 14], ![14, 17, -262, 322, 132, -252, 12, 36], ![36, 50, -667, 710, 502, -624, -72, 120]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -19, 27, 5, -21, 5, 3], ![3, 4, -56, 62, 42, -58, -6, 14], ![14, 17, -262, 322, 132, -252, 12, 36], ![36, 50, -667, 710, 502, -624, -72, 120], ![120, 156, -2230, 2573, 1310, -2018, -24, 288]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -19, 27, 5, -21, 5, 3], ![3, 4, -56, 62, 42, -58, -6, 14], ![14, 17, -262, 322, 132, -252, 12, 36], ![36, 50, -667, 710, 502, -624, -72, 120], ![120, 156, -2230, 2573, 1310, -2018, -24, 288], ![288, 408, -5316, 5546, 4013, -4738, -578, 840]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, -19, 27, 5, -21, 5, 3], ![3, 4, -56, 62, 42, -58, -6, 14], ![14, 17, -262, 322, 132, -252, 12, 36], ![36, 50, -667, 710, 502, -624, -72, 120], ![120, 156, -2230, 2573, 1310, -2018, -24, 288], ![288, 408, -5316, 5546, 4013, -4738, -578, 840], ![840, 1128, -15552, 17364, 9746, -13627, -538, 1942]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-14, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-14, -3, -1], [-36, -14, -3, -1]], ![[], [], [], [-1], [-3, -1], [-14, -3, -1], [-36, -14, -3, -1], [-120, -36, -14, -3, -1]], ![[], [], [-1], [-3, -1], [-14, -3, -1], [-36, -14, -3, -1], [-120, -36, -14, -3, -1], [-288, -120, -36, -14, -3, -1]], ![[], [-1], [-3, -1], [-14, -3, -1], [-36, -14, -3, -1], [-120, -36, -14, -3, -1], [-288, -120, -36, -14, -3, -1], [-840, -288, -120, -36, -14, -3, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 8 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 8) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 8) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 8) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -19, 27, 5, -21, 5, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -19, 27, 5, -21, 5, 3], [3, 4, -56, 62, 42, -58, -6, 14]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -19, 27, 5, -21, 5, 3], [3, 4, -56, 62, 42, -58, -6, 14], [14, 17, -262, 322, 132, -252, 12, 36]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -19, 27, 5, -21, 5, 3], [3, 4, -56, 62, 42, -58, -6, 14], [14, 17, -262, 322, 132, -252, 12, 36], [36, 50, -667, 710, 502, -624, -72, 120]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -19, 27, 5, -21, 5, 3], [3, 4, -56, 62, 42, -58, -6, 14], [14, 17, -262, 322, 132, -252, 12, 36], [36, 50, -667, 710, 502, -624, -72, 120], [120, 156, -2230, 2573, 1310, -2018, -24, 288]], ![[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -19, 27, 5, -21, 5, 3], [3, 4, -56, 62, 42, -58, -6, 14], [14, 17, -262, 322, 132, -252, 12, 36], [36, 50, -667, 710, 502, -624, -72, 120], [120, 156, -2230, 2573, 1310, -2018, -24, 288], [288, 408, -5316, 5546, 4013, -4738, -578, 840]], ![[0, 0, 0, 0, 0, 0, 0, 1], [1, 1, -19, 27, 5, -21, 5, 3], [3, 4, -56, 62, 42, -58, -6, 14], [14, 17, -262, 322, 132, -252, 12, 36], [36, 50, -667, 710, 502, -624, -72, 120], [120, 156, -2230, 2573, 1310, -2018, -24, 288], [288, 408, -5316, 5546, 4013, -4738, -578, 840], [840, 1128, -15552, 17364, 9746, -13627, -538, 1942]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp389 : Fact (Nat.Prime 389) := fact_iff.2 (by norm_num)
instance hp7741 : Fact (Nat.Prime 7741) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 3, 1]
  b' := [1, 0, 2, 1]
  k := [1]
  f := [1, 1, -2, 7, 3, -3, 2, 1]
  g := [2, 1, 2, 1, 1]
  h := [2, 1, 2, 1, 1]
  a := [1, 3, 3, 2]
  b := [0, 3, 4, 2, 1, 0, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD389 : CertificateDedekindCriterionLists l 389 where
  n := 2
  a' := [142, 80, 54, 124, 312, 289]
  b' := [281, 1, 286, 2, 320, 352, 181]
  k := [348, 32, 88, 5, 144, 96, 1]
  f := [104, 120, 129, 14, 100, 23, 90, 1]
  g := [279, 320, 344, 35, 268, 60, 241, 1]
  h := [145, 1]
  a := [152, 154, 310, 73, 169, 136, 90]
  b := [27, 199, 263, 189, 158, 228, 299]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD7741 : CertificateDedekindCriterionLists l 7741 where
  n := 2
  a' := [6924, 7648, 3645, 2486, 2101, 489]
  b' := [997, 2551, 1322, 3606, 2511, 7116, 1036]
  k := [5916, 5633, 5184, 907, 3117, 5767, 1]
  f := [781, 1926, 3391, 3104, 2136, 459, 1808, 1]
  g := [1245, 3070, 5405, 4947, 3404, 731, 2882, 1]
  h := [4856, 1]
  a := [3818, 3068, 5498, 5622, 6014, 1434, 2986]
  b := [1006, 1104, 4963, 3668, 5847, 756, 4755]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 389, 7741]
  exp := ![1, 1, 1]
  pdgood := [5, 389, 7741]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp389.out
    exact hp7741.out
  a := [-28730299, 501851952, -202521034, -636809136, 320709068, 126536320, -66203392]
  b := [13674054, 46492399, -186093811, 39305114, 134969926, -52647644, -18920324, 8275424]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 389 T_ofList CD389
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7741 T_ofList CD7741

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

noncomputable def bOm : Basis (Fin 8) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 8 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 8
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 8 := T_degree

noncomputable def bQ : Basis (Fin 8) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 8) (Fin 8) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 8) :
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
          (∑ x : Fin 8,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 8,
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
        (List.ofFn fun i : Fin 8 =>
          (List.ofFn fun j : Fin 8 =>
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
      (voightPolynomialDiscriminantInput 8 row row_mem)
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

end VoightMaximalOrderD8R100

namespace VoightMaximalOrderD8R101

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1891678448, [-1, 4, 3, -17, 2, 17, -5, -3, 1], 1⟩
local notation "l" => [-1, 4, 3, -17, 2, 17, -5, -3, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsEight := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsEight_irreducible row row_mem
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
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![1, -4, -3, 17, -2, -17, 5, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![1, -4, -3, 17, -2, -17, 5, 3], ![3, -11, -13, 48, 11, -53, -2, 14]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![1, -4, -3, 17, -2, -17, 5, 3], ![3, -11, -13, 48, 11, -53, -2, 14], ![14, -53, -53, 225, 20, -227, 17, 40]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![1, -4, -3, 17, -2, -17, 5, 3], ![3, -11, -13, 48, 11, -53, -2, 14], ![14, -53, -53, 225, 20, -227, 17, 40], ![40, -146, -173, 627, 145, -660, -27, 137]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![1, -4, -3, 17, -2, -17, 5, 3], ![3, -11, -13, 48, 11, -53, -2, 14], ![14, -53, -53, 225, 20, -227, 17, 40], ![40, -146, -173, 627, 145, -660, -27, 137], ![137, -508, -557, 2156, 353, -2184, 25, 384]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![1, -4, -3, 17, -2, -17, 5, 3], ![3, -11, -13, 48, 11, -53, -2, 14], ![14, -53, -53, 225, 20, -227, 17, 40], ![40, -146, -173, 627, 145, -660, -27, 137], ![137, -508, -557, 2156, 353, -2184, 25, 384], ![384, -1399, -1660, 5971, 1388, -6175, -264, 1177]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![1, -4, -3, 17, -2, -17, 5, 3], ![3, -11, -13, 48, 11, -53, -2, 14], ![14, -53, -53, 225, 20, -227, 17, 40], ![40, -146, -173, 627, 145, -660, -27, 137], ![137, -508, -557, 2156, 353, -2184, 25, 384], ![384, -1399, -1660, 5971, 1388, -6175, -264, 1177], ![1177, -4324, -4930, 18349, 3617, -18621, -290, 3267]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-14, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-14, -3, -1], [-40, -14, -3, -1]], ![[], [], [], [-1], [-3, -1], [-14, -3, -1], [-40, -14, -3, -1], [-137, -40, -14, -3, -1]], ![[], [], [-1], [-3, -1], [-14, -3, -1], [-40, -14, -3, -1], [-137, -40, -14, -3, -1], [-384, -137, -40, -14, -3, -1]], ![[], [-1], [-3, -1], [-14, -3, -1], [-40, -14, -3, -1], [-137, -40, -14, -3, -1], [-384, -137, -40, -14, -3, -1], [-1177, -384, -137, -40, -14, -3, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 8 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 8) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 8) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 8) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [1, -4, -3, 17, -2, -17, 5, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [1, -4, -3, 17, -2, -17, 5, 3], [3, -11, -13, 48, 11, -53, -2, 14]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [1, -4, -3, 17, -2, -17, 5, 3], [3, -11, -13, 48, 11, -53, -2, 14], [14, -53, -53, 225, 20, -227, 17, 40]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [1, -4, -3, 17, -2, -17, 5, 3], [3, -11, -13, 48, 11, -53, -2, 14], [14, -53, -53, 225, 20, -227, 17, 40], [40, -146, -173, 627, 145, -660, -27, 137]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [1, -4, -3, 17, -2, -17, 5, 3], [3, -11, -13, 48, 11, -53, -2, 14], [14, -53, -53, 225, 20, -227, 17, 40], [40, -146, -173, 627, 145, -660, -27, 137], [137, -508, -557, 2156, 353, -2184, 25, 384]], ![[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [1, -4, -3, 17, -2, -17, 5, 3], [3, -11, -13, 48, 11, -53, -2, 14], [14, -53, -53, 225, 20, -227, 17, 40], [40, -146, -173, 627, 145, -660, -27, 137], [137, -508, -557, 2156, 353, -2184, 25, 384], [384, -1399, -1660, 5971, 1388, -6175, -264, 1177]], ![[0, 0, 0, 0, 0, 0, 0, 1], [1, -4, -3, 17, -2, -17, 5, 3], [3, -11, -13, 48, 11, -53, -2, 14], [14, -53, -53, 225, 20, -227, 17, 40], [40, -146, -173, 627, 145, -660, -27, 137], [137, -508, -557, 2156, 353, -2184, 25, 384], [384, -1399, -1660, 5971, 1388, -6175, -264, 1177], [1177, -4324, -4930, 18349, 3617, -18621, -290, 3267]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp523 : Fact (Nat.Prime 523) := fact_iff.2 (by norm_num)
instance hp20551 : Fact (Nat.Prime 20551) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1]
  b' := [0, 1, 1, 0, 1]
  k := [1, 0, 0, 1, 1]
  f := [1, -1, 0, 10, 0, -8, 3, 2]
  g := [1, 1, 1, 1, 0, 0, 1]
  h := [1, 1, 1]
  a := [1, 0, 0, 1, 0, 1]
  b := [0, 1, 1, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [0, 6, 3, 6, 2, 6]
  b' := [1, 10, 5, 0, 7, 5, 7]
  k := [8, 9, 5, 4, 6, 1, 1]
  f := [5, 1, 8, 9, 3, 2, 9, 2]
  g := [6, 1, 10, 8, 3, 4, 10, 1]
  h := [9, 1]
  a := [2, 7, 5, 0, 4, 2]
  b := [4, 6, 10, 1, 3, 7]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD523 : CertificateDedekindCriterionLists l 523 where
  n := 2
  a' := [126, 197, 294, 256, 510, 37]
  b' := [47, 464, 275, 200, 62, 3, 443]
  k := [26, 473, 293, 354, 416, 212, 1]
  f := [101, 51, 28, 123, 27, 34, 108, 1]
  g := [343, 171, 94, 417, 89, 115, 366, 1]
  h := [154, 1]
  a := [12, 273, 55, 38, 336, 189, 145]
  b := [306, 456, 244, 479, 106, 88, 378]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD20551 : CertificateDedekindCriterionLists l 20551 where
  n := 2
  a' := [15955, 7183, 12651, 16531, 16364, 12131]
  b' := [19787, 7065, 11030, 439, 14098, 1726, 18818]
  k := [1019, 19327, 14755, 18750, 11576, 8876, 1]
  f := [2171, 2699, 76, 1613, 1306, 807, 4178, 1]
  g := [7645, 9503, 266, 5680, 4598, 2841, 14712, 1]
  h := [5836, 1]
  a := [10582, 2959, 10452, 18645, 2184, 18662, 10119]
  b := [18718, 15963, 8337, 20492, 3080, 17949, 10432]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![2, 11, 523, 20551]
  exp := ![1, 1, 1, 1]
  pdgood := [2, 11, 523, 20551]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp11.out
    exact hp523.out
    exact hp20551.out
  a := [8414783690, 25444571668, -71283791272, -84411251206, 61595247968, 23151809413, -12085878792]
  b := [2162810874, -5297857084, -14053982984, 16068055309, 18550561482, -9989713108, -3460501745, 1510734849]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 523 T_ofList CD523
    exact satisfiesDedekindCriterion_of_certificate_lists T l 20551 T_ofList CD20551

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

noncomputable def bOm : Basis (Fin 8) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 8 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 8
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 8 := T_degree

noncomputable def bQ : Basis (Fin 8) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 8) (Fin 8) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 8) :
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
          (∑ x : Fin 8,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 8,
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
        (List.ofFn fun i : Fin 8 =>
          (List.ofFn fun j : Fin 8 =>
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
      (voightPolynomialDiscriminantInput 8 row row_mem)
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

end VoightMaximalOrderD8R101

namespace VoightMaximalOrderD8R106

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1933869832, [-1, 3, 5, -15, -6, 16, -1, -4, 1], 1⟩
local notation "l" => [-1, 3, 5, -15, -6, 16, -1, -4, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsEight := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsEight_irreducible row row_mem
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
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -5, 15, 6, -16, 1, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -5, 15, 6, -16, 1, 4], ![4, -11, -23, 55, 39, -58, -12, 17]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -5, 15, 6, -16, 1, 4], ![4, -11, -23, 55, 39, -58, -12, 17], ![17, -47, -96, 232, 157, -233, -41, 56]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -5, 15, 6, -16, 1, 4], ![4, -11, -23, 55, 39, -58, -12, 17], ![17, -47, -96, 232, 157, -233, -41, 56], ![56, -151, -327, 744, 568, -739, -177, 183]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -5, 15, 6, -16, 1, 4], ![4, -11, -23, 55, 39, -58, -12, 17], ![17, -47, -96, 232, 157, -233, -41, 56], ![56, -151, -327, 744, 568, -739, -177, 183], ![183, -493, -1066, 2418, 1842, -2360, -556, 555]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -5, 15, 6, -16, 1, 4], ![4, -11, -23, 55, 39, -58, -12, 17], ![17, -47, -96, 232, 157, -233, -41, 56], ![56, -151, -327, 744, 568, -739, -177, 183], ![183, -493, -1066, 2418, 1842, -2360, -556, 555], ![555, -1482, -3268, 7259, 5748, -7038, -1805, 1664]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -5, 15, 6, -16, 1, 4], ![4, -11, -23, 55, 39, -58, -12, 17], ![17, -47, -96, 232, 157, -233, -41, 56], ![56, -151, -327, 744, 568, -739, -177, 183], ![183, -493, -1066, 2418, 1842, -2360, -556, 555], ![555, -1482, -3268, 7259, 5748, -7038, -1805, 1664], ![1664, -4437, -9802, 21692, 17243, -20876, -5374, 4851]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-17, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-17, -4, -1], [-56, -17, -4, -1]], ![[], [], [], [-1], [-4, -1], [-17, -4, -1], [-56, -17, -4, -1], [-183, -56, -17, -4, -1]], ![[], [], [-1], [-4, -1], [-17, -4, -1], [-56, -17, -4, -1], [-183, -56, -17, -4, -1], [-555, -183, -56, -17, -4, -1]], ![[], [-1], [-4, -1], [-17, -4, -1], [-56, -17, -4, -1], [-183, -56, -17, -4, -1], [-555, -183, -56, -17, -4, -1], [-1664, -555, -183, -56, -17, -4, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 8 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 8) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 8) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 8) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -5, 15, 6, -16, 1, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -5, 15, 6, -16, 1, 4], [4, -11, -23, 55, 39, -58, -12, 17]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -5, 15, 6, -16, 1, 4], [4, -11, -23, 55, 39, -58, -12, 17], [17, -47, -96, 232, 157, -233, -41, 56]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -5, 15, 6, -16, 1, 4], [4, -11, -23, 55, 39, -58, -12, 17], [17, -47, -96, 232, 157, -233, -41, 56], [56, -151, -327, 744, 568, -739, -177, 183]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -5, 15, 6, -16, 1, 4], [4, -11, -23, 55, 39, -58, -12, 17], [17, -47, -96, 232, 157, -233, -41, 56], [56, -151, -327, 744, 568, -739, -177, 183], [183, -493, -1066, 2418, 1842, -2360, -556, 555]], ![[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -5, 15, 6, -16, 1, 4], [4, -11, -23, 55, 39, -58, -12, 17], [17, -47, -96, 232, 157, -233, -41, 56], [56, -151, -327, 744, 568, -739, -177, 183], [183, -493, -1066, 2418, 1842, -2360, -556, 555], [555, -1482, -3268, 7259, 5748, -7038, -1805, 1664]], ![[0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -5, 15, 6, -16, 1, 4], [4, -11, -23, 55, 39, -58, -12, 17], [17, -47, -96, 232, 157, -233, -41, 56], [56, -151, -327, 744, 568, -739, -177, 183], [183, -493, -1066, 2418, 1842, -2360, -556, 555], [555, -1482, -3268, 7259, 5748, -7038, -1805, 1664], [1664, -4437, -9802, 21692, 17243, -20876, -5374, 4851]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp241733729 : Fact (Nat.Prime 241733729) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 1, 0, 1]
  b' := [0, 1, 1, 1, 1, 1]
  k := [1, 1, 0, 0, 0, 0, 1]
  f := [1, -1, -2, 8, 3, -8, 1, 3]
  g := [1, 0, 1, 0, 0, 0, 1, 1]
  h := [1, 1]
  a := [0, 1, 1, 1]
  b := [1, 1, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD241733729 : CertificateDedekindCriterionLists l 241733729 where
  n := 2
  a' := [121453853, 129923532, 138819646, 215607060, 153860481, 130322858]
  b' := [196359692, 204822476, 40277703, 61967738, 46253549, 108764834, 188582788]
  k := [225994422, 10959860, 65239598, 100505705, 240176979, 226024941, 1]
  f := [5970649, 6162630, 4546366, 1470188, 4914077, 2941543, 7599188, 1]
  g := [183757985, 189666539, 139922965, 45247791, 151239983, 90531515, 233879333, 1]
  h := [7854392, 1]
  a := [197289619, 127868104, 163016201, 72673629, 187052868, 189466563, 14738597]
  b := [26321730, 235792433, 102193983, 22027482, 190651652, 84020337, 226995132]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![2, 241733729]
  exp := ![2, 1]
  pdgood := [2, 241733729]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp241733729.out
  a := [8328469441, 53144074933, -4432530622, -94856526206, 19565782406, 32404171596, -10379312088]
  b := [3098468119, -942004860, -18885329557, -508651888, 19397025810, -3015290098, -4699228455, 1297414011]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 241733729 T_ofList CD241733729

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

noncomputable def bOm : Basis (Fin 8) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 8 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 8
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 8 := T_degree

noncomputable def bQ : Basis (Fin 8) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 8) (Fin 8) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 8) :
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
          (∑ x : Fin 8,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 8,
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
        (List.ofFn fun i : Fin 8 =>
          (List.ofFn fun j : Fin 8 =>
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
      (voightPolynomialDiscriminantInput 8 row row_mem)
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

end VoightMaximalOrderD8R106

end TraceEuclidean
