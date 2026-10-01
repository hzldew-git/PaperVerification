import TraceEuclidean.VoightMaximalOrderCertificates.Chunk005
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

namespace VoightMaximalOrderD5R387

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨949576, [4, 18, 3, -9, -1, 1], 4⟩
local notation "l" => [4, 18, 3, -9, -1, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsFive := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsFive_irreducible row row_mem
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

def basisDenominator : ℤ := 2
def basisNumerator : Fin 5 → Fin 5 → ℤ := ![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 1, 0, 1, 0], ![0, 0, 1, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, -1, 0, 2, 0], ![0, 0, 0, 0, 1], ![-2, -14, -2, 10, 1]], ![![0, 0, 1, 0, 0], ![0, -1, 0, 2, 0], ![0, 0, -1, 0, 2], ![-2, -14, -2, 10, 1], ![-2, -14, -16, 6, 11]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1], ![-2, -14, -2, 10, 1], ![-1, -7, -8, 3, 6], ![-12, -77, -19, 44, 9]], ![![0, 0, 0, 0, 1], ![-2, -14, -2, 10, 1], ![-2, -14, -16, 6, 11], ![-12, -77, -19, 44, 9], ![-18, -119, -95, 52, 53]]]
  s := ![![[], [], [], [], []], ![[], [], [], [], [-2]], ![[], [], [], [-2], [-2, -2]], ![[], [], [-2], [-1, -1], [-12, -1, -1]], ![[], [-2], [-2, -2], [-12, -1, -1], [-18, -12, -1, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 5 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 5) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 5) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 5) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 5 → Fin 5 → List ℤ := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, -1, 0, 2, 0], [0, 0, 0, 0, 1], [-2, -14, -2, 10, 1]], ![[0, 0, 1, 0, 0], [0, -1, 0, 2, 0], [0, 0, -1, 0, 2], [-2, -14, -2, 10, 1], [-2, -14, -16, 6, 11]], ![[0, 0, 0, 1, 0], [0, 0, 0, 0, 1], [-2, -14, -2, 10, 1], [-1, -7, -8, 3, 6], [-12, -77, -19, 44, 9]], ![[0, 0, 0, 0, 1], [-2, -14, -2, 10, 1], [-2, -14, -16, 6, 11], [-12, -77, -19, 44, 9], [-18, -119, -95, 52, 53]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)
instance hp4093 : Fact (Nat.Prime 4093) := fact_iff.2 (by norm_num)

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 2
  a' := [22, 21, 5]
  b' := [25, 21, 24, 6]
  k := [13, 0, 11, 1]
  f := [7, 10, 17, 5, 1]
  g := [9, 13, 21, 5, 1]
  h := [23, 1]
  a := [14, 20, 27, 20]
  b := [15, 2, 2, 9]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD4093 : CertificateDedekindCriterionLists l 4093 where
  n := 2
  a' := [613, 266, 124]
  b' := [3994, 3645, 143, 4062]
  k := [1036, 743, 211, 1]
  f := [677, 44, 2859, 103, 1]
  g := [695, 45, 2935, 105, 1]
  h := [3987, 1]
  a := [2125, 1339, 1930, 1740]
  b := [1334, 2662, 1550, 2353]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 3
  p := ![2, 29, 4093]
  exp := ![3, 1, 1]
  pdgood := [29, 4093]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp29.out
    exact hp4093.out
  a := [-144962, 184488, 88053, -58885]
  b := [84968, 75642, -77657, -19966, 11777]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
    exact satisfiesDedekindCriterion_of_certificate_lists T l 4093 T_ofList CD4093

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 1
  n := 4
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1]], ![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1]], ![[0, 0, 0, 1, 0], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [1, 1, 0, 1, 0], [0, 1, 1, 0, 1]], ![[0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 1, 1, 0, 1], [0, 1, 1, 0, 1]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 1, 1, 0, 0]]
  b2 := ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 1], ![0, 1, 0, 0, 0], ![1, 1, 0, 1, 1]]
  v := ![![0, 1, 1, 0, 0]]
  w := ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 1], ![0, 1, 0, 0, 0], ![1, 1, 0, 1, 1]]
  wFrob := ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 1], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 1]]
  v_ind := ![2]
  w_ind := ![0, 1, 2, 3]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 1, 1], ![1, 0, 1, 1, 1], ![0, 0, 0, 1, 1], ![0, 1, 1, 0, 0], ![0, 0, 0, 0, 1]]
  a := ![![![-19]], ![![-20]], ![![-20]], ![![0]], ![![-18]]]
  c := ![![![-16, -6, -18, 13]], ![![-17, -6, -19, 14]], ![![-16, -6, -18, 13]], ![![-2, -1, -2, 2]], ![![-10, -2, -11, 8]]]
  d := ![![![0], ![-232], ![-4], ![-286]], ![![2], ![-264], ![-4], ![-320]], ![![0], ![-232], ![-4], ![-286]], ![![2], ![-34], ![2], ![-36]], ![![0], ![-194], ![-4], ![-232]]]
  e := ![![![0, 0, -1, 1], ![-138, -41, -158, 106], ![-12, -8, -13, 10], ![-199, -74, -231, 155]], ![![0, 0, -2, 1], ![-148, -38, -168, 114], ![-14, -10, -14, 12], ![-221, -80, -255, 173]], ![![-1, 0, -1, 1], ![-138, -42, -158, 106], ![-12, -8, -14, 10], ![-199, -74, -231, 154]], ![![0, 0, 0, 0], ![-22, -6, -24, 18], ![-2, -2, -2, 2], ![-34, -14, -38, 28]], ![![0, 1, -1, 0], ![-82, -8, -90, 62], ![-12, -9, -13, 10], ![-138, -42, -158, 106]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inr 0, Sum.inr 0), (Sum.inl 0, Sum.inr 1), (Sum.inr 0, Sum.inr 1)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [2]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateLists K 2 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M2
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 5) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 5 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 5
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 5 := T_degree

noncomputable def bQ : Basis (Fin 5) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 5) (Fin 5) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 5) :
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
          (∑ x : Fin 5,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 5,
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
        (List.ofFn fun i : Fin 5 =>
          (List.ofFn fun j : Fin 5 =>
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
      (voightPolynomialDiscriminantInput 5 row row_mem)
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

end VoightMaximalOrderD5R387

namespace VoightMaximalOrderD5R404

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨981488, [-4, 8, 8, -10, -1, 1], 8⟩
local notation "l" => [-4, 8, 8, -10, -1, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsFive := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsFive_irreducible row row_mem
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

def basisDenominator : ℤ := 4
def basisNumerator : Fin 5 → Fin 5 → ℤ := ![![4, 0, 0, 0, 0], ![0, 4, 0, 0, 0], ![0, 0, 4, 0, 0], ![0, 0, 2, 2, 0], ![0, 2, 2, 1, 1]]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, -1, 2, 0], ![0, -1, -1, 0, 2], ![1, -3, -5, 5, 2]], ![![0, 0, 1, 0, 0], ![0, 0, -1, 2, 0], ![0, -2, -1, -2, 4], ![2, -6, -10, 8, 4], ![2, -10, -13, 0, 14]], ![![0, 0, 0, 1, 0], ![0, -1, -1, 0, 2], ![2, -6, -10, 8, 4], ![3, -12, -17, 4, 14], ![8, -25, -40, 22, 21]], ![![0, 0, 0, 0, 1], ![1, -3, -5, 5, 2], ![2, -10, -13, 0, 14], ![8, -25, -40, 22, 21], ![12, -45, -65, 15, 51]]]
  s := ![![[], [], [], [], []], ![[], [], [], [], [-4]], ![[], [], [], [-8], [-8, -4]], ![[], [], [-8], [-12, -4], [-32, -6, -2]], ![[], [-4], [-8, -4], [-32, -6, -2], [-48, -18, -3, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 5 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 5) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 5) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 5) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 5 → Fin 5 → List ℤ := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, -1, 2, 0], [0, -1, -1, 0, 2], [1, -3, -5, 5, 2]], ![[0, 0, 1, 0, 0], [0, 0, -1, 2, 0], [0, -2, -1, -2, 4], [2, -6, -10, 8, 4], [2, -10, -13, 0, 14]], ![[0, 0, 0, 1, 0], [0, -1, -1, 0, 2], [2, -6, -10, 8, 4], [3, -12, -17, 4, 14], [8, -25, -40, 22, 21]], ![[0, 0, 0, 0, 1], [1, -3, -5, 5, 2], [2, -10, -13, 0, 14], [8, -25, -40, 22, 21], [12, -45, -65, 15, 51]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp61343 : Fact (Nat.Prime 61343) := fact_iff.2 (by norm_num)

def CD61343 : CertificateDedekindCriterionLists l 61343 where
  n := 2
  a' := [1687, 15291, 11946]
  b' := [16000, 57815, 42321, 27685]
  k := [11703, 8856, 18117, 1]
  f := [37988, 18618, 34793, 7721, 1]
  g := [44570, 21843, 40821, 9058, 1]
  h := [52284, 1]
  a := [11913, 42288, 30751, 5401]
  b := [50764, 17893, 13255, 55942]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 2
  p := ![2, 61343]
  exp := ![4, 1]
  pdgood := [61343]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp61343.out
  a := [-11576, 547684, 26711, -95145]
  b := [116898, 51622, -187629, -9148, 19029]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 61343 T_ofList CD61343

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 2
  n := 3
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 1, 1, 0, 0], [1, 1, 1, 1, 0]], ![[0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [0, 0, 1, 0, 0]], ![[0, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 1, 0, 0, 1]], ![[0, 0, 0, 0, 1], [1, 1, 1, 1, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 1], [0, 1, 1, 1, 1]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 1, 1, 0, 0], ![1, 1, 0, 1, 0]]
  b2 := ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 1], ![0, 1, 0, 0, 0]]
  v := ![![0, 1, 1, 0, 0], ![1, 1, 0, 1, 0]]
  w := ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 1], ![0, 1, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0], ![0, 1, 0, 1, 1], ![0, 0, 1, 0, 0]]
  v_ind := ![2, 3]
  w_ind := ![0, 1, 2]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0], ![1, 0, 1, 1, 1], ![0, 1, 1, 0, 0], ![1, 1, 1, 1, 0], ![0, 0, 1, 0, 0]]
  a := ![![![1, 0], ![0, 1]], ![![-30, 13], ![-73, 43]], ![![-2, 2], ![-10, 10]], ![![-12, 10], ![-28, 16]], ![![-2, 0], ![-10, 10]]]
  c := ![![![0, 0, 0], ![0, 0, 0]], ![![-4, 13, -15], ![-14, 22, -30]], ![![-1, 2, -3], ![-4, 3, -6]], ![![-4, 5, -8], ![-5, 11, -14]], ![![0, 2, -2], ![-4, 2, -5]]]
  d := ![![![0, 0], ![0, 0], ![0, 0]], ![![2, 2], ![-250, 88], ![-14, 14]], ![![2, 0], ![-36, 14], ![0, 4]], ![![2, 2], ![-118, 58], ![-2, 4]], ![![2, 0], ![-28, 4], ![-2, 4]]]
  e := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![0, 1, -3], ![-21, 91, -93], ![-6, 4, -7]], ![![0, 0, 0], ![-4, 16, -18], ![-2, 0, -2]], ![![0, 0, -1], ![-18, 40, -48], ![-2, 2, -3]], ![![0, 0, -1], ![0, 14, -12], ![-2, 0, -1]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inl 1, Sum.inr 0), (Sum.inl 1, Sum.inr 2)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [2]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateLists K 2 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M2
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 5) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 5 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 5
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 5 := T_degree

noncomputable def bQ : Basis (Fin 5) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 5) (Fin 5) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 5) :
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
          (∑ x : Fin 5,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 5,
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
        (List.ofFn fun i : Fin 5 =>
          (List.ofFn fun j : Fin 5 =>
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
      (voightPolynomialDiscriminantInput 5 row row_mem)
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

end VoightMaximalOrderD5R404

namespace VoightMaximalOrderD5R413

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨998068, [-2, 3, 10, -6, -2, 1], 2⟩
local notation "l" => [-2, 3, 10, -6, -2, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsFive := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsFive_irreducible row row_mem
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

def basisDenominator : ℤ := 2
def basisNumerator : Fin 5 → Fin 5 → ℤ := ![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 1, 1, 1, 1]]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, -1, -1, -1, 2], ![1, -3, -6, 2, 3]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, -1, -1, -1, 2], ![2, -5, -12, 4, 4], ![3, -10, -23, -2, 13]], ![![0, 0, 0, 1, 0], ![0, -1, -1, -1, 2], ![2, -5, -12, 4, 4], ![4, -14, -33, -8, 20], ![13, -34, -86, 5, 35]], ![![0, 0, 0, 0, 1], ![1, -3, -6, 2, 3], ![3, -10, -23, -2, 13], ![13, -34, -86, 5, 35], ![26, -72, -182, -8, 83]]]
  s := ![![[], [], [], [], []], ![[], [], [], [], [-2]], ![[], [], [], [-4], [-6, -2]], ![[], [], [-4], [-8, -4], [-26, -6, -2]], ![[], [-2], [-6, -2], [-26, -6, -2], [-52, -17, -4, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 5 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 5) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 5) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 5) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 5 → Fin 5 → List ℤ := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, -1, -1, -1, 2], [1, -3, -6, 2, 3]], ![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, -1, -1, -1, 2], [2, -5, -12, 4, 4], [3, -10, -23, -2, 13]], ![[0, 0, 0, 1, 0], [0, -1, -1, -1, 2], [2, -5, -12, 4, 4], [4, -14, -33, -8, 20], [13, -34, -86, 5, 35]], ![[0, 0, 0, 0, 1], [1, -3, -6, 2, 3], [3, -10, -23, -2, 13], [13, -34, -86, 5, 35], [26, -72, -182, -8, 83]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp249517 : Fact (Nat.Prime 249517) := fact_iff.2 (by norm_num)

def CD249517 : CertificateDedekindCriterionLists l 249517 where
  n := 2
  a' := [26364, 19871, 103262]
  b' := [25596, 224724, 119559, 98943]
  k := [11888, 39308, 207001, 1]
  f := [16358, 16965, 2324, 19446, 1]
  g := [192012, 199128, 27270, 228258, 1]
  h := [21257, 1]
  a := [11977, 161492, 18072, 101876]
  b := [202309, 26299, 91888, 147641]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 2
  p := ![2, 249517]
  exp := ![1, 1]
  pdgood := [249517]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp249517.out
  a := [-190324, 278586, 94645, -81050]
  b := [39462, 112968, -97424, -25413, 16210]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 249517 T_ofList CD249517

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 2
  n := 3
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 1, 1, 1, 0], [1, 1, 0, 0, 1]], ![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 1, 1, 1, 0], [0, 1, 0, 0, 0], [1, 0, 1, 0, 1]], ![[0, 0, 0, 1, 0], [0, 1, 1, 1, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 0, 1, 1]], ![[0, 0, 0, 0, 1], [1, 1, 0, 0, 1], [1, 0, 1, 0, 1], [1, 0, 0, 1, 1], [0, 0, 0, 0, 1]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 1, 1, 0, 0], ![0, 1, 0, 1, 0]]
  b2 := ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 0, 1]]
  v := ![![0, 1, 1, 0, 0], ![0, 1, 0, 1, 0]]
  w := ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 0, 1]]
  wFrob := ![![1, 0, 0, 0, 0], ![0, 1, 1, 1, 0], ![0, 0, 0, 0, 1]]
  v_ind := ![2, 3]
  w_ind := ![0, 1, 4]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 1, 0, 1, 0], ![1, 0, 1, 0, 0], ![0, 0, 1, 0, 1]]
  a := ![![![1, 0], ![0, 1]], ![![2, 1], ![0, 0]], ![![-12, 4], ![-34, -10]], ![![0, 0], ![-12, 6]], ![![-30, 0], ![-104, 12]]]
  c := ![![![0, 0, 0], ![0, 0, 0]], ![![0, -1, 0], ![0, 0, 1]], ![![1, 1, 3], ![2, 14, 12]], ![![0, 0, 1], ![1, 1, 2]], ![![2, 8, 9], ![8, 25, 21]]]
  d := ![![![0, 0], ![0, 0], ![0, 0]], ![![0, 0], ![2, 0], ![-12, 4]], ![![0, 2], ![0, -2], ![-184, 14]], ![![2, 0], ![0, 2], ![-46, -4]], ![![2, 0], ![-12, 6], ![-410, -20]]]
  e := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![1, 1, 0], ![0, 0, 0], ![1, 1, 4]], ![![0, 0, 0], ![0, 0, 2], ![14, 48, 38]], ![![1, -1, 0], ![0, 0, 0], ![3, 15, 14]], ![![0, -1, 1], ![1, 0, 3], ![29, 133, 96]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 0, Sum.inl 1), (Sum.inl 0, Sum.inr 0), (Sum.inl 1, Sum.inr 0), (Sum.inr 1, Sum.inr 0)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [2]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateLists K 2 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M2
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 5) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 5 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 5
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 5 := T_degree

noncomputable def bQ : Basis (Fin 5) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 5) (Fin 5) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 5) :
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
          (∑ x : Fin 5,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 5,
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
        (List.ofFn fun i : Fin 5 =>
          (List.ofFn fun j : Fin 5 =>
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
      (voightPolynomialDiscriminantInput 5 row row_mem)
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

end VoightMaximalOrderD5R413

namespace VoightMaximalOrderD5R418

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1006192, [2, 8, 3, -9, -1, 1], 2⟩
local notation "l" => [2, 8, 3, -9, -1, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsFive := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsFive_irreducible row row_mem
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

def basisDenominator : ℤ := 2
def basisNumerator : Fin 5 → Fin 5 → ℤ := ![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 1, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, -1, 0, 2], ![-1, -4, -2, 5, 1]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, -1, 0, 2], ![-2, -8, -4, 9, 2], ![-1, -5, -11, 3, 11]], ![![0, 0, 0, 1, 0], ![0, 0, -1, 0, 2], ![-2, -8, -4, 9, 2], ![-2, -10, -21, 6, 20], ![-11, -45, -30, 44, 17]], ![![0, 0, 0, 0, 1], ![-1, -4, -2, 5, 1], ![-1, -5, -11, 3, 11], ![-11, -45, -30, 44, 17], ![-9, -42, -67, 29, 58]]]
  s := ![![[], [], [], [], []], ![[], [], [], [], [-2]], ![[], [], [], [-4], [-2, -2]], ![[], [], [-4], [-4, -4], [-22, -2, -2]], ![[], [-2], [-2, -2], [-22, -2, -2], [-18, -12, -1, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 5 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 5) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 5) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 5) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 5 → Fin 5 → List ℤ := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, -1, 0, 2], [-1, -4, -2, 5, 1]], ![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, -1, 0, 2], [-2, -8, -4, 9, 2], [-1, -5, -11, 3, 11]], ![[0, 0, 0, 1, 0], [0, 0, -1, 0, 2], [-2, -8, -4, 9, 2], [-2, -10, -21, 6, 20], [-11, -45, -30, 44, 17]], ![[0, 0, 0, 0, 1], [-1, -4, -2, 5, 1], [-1, -5, -11, 3, 11], [-11, -45, -30, 44, 17], [-9, -42, -67, 29, 58]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp5717 : Fact (Nat.Prime 5717) := fact_iff.2 (by norm_num)

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [1, 3, 8]
  b' := [0, 6, 9, 9]
  k := [6, 7, 6, 1]
  f := [0, 1, 2, 3, 1]
  g := [1, 9, 8, 8, 1]
  h := [2, 1]
  a := [9, 5, 0, 2]
  b := [1, 4, 10, 9]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD5717 : CertificateDedekindCriterionLists l 5717 where
  n := 2
  a' := [2815, 5040, 1333]
  b' := [3807, 1349, 605, 1096]
  k := [2097, 2663, 1809, 1]
  f := [218, 3919, 489, 761, 1]
  g := [259, 4656, 580, 904, 1]
  h := [4812, 1]
  a := [1229, 3087, 2755, 2597]
  b := [2409, 4059, 2728, 3120]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 3
  p := ![2, 11, 5717]
  exp := ![2, 1, 1]
  pdgood := [11, 5717]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp11.out
    exact hp5717.out
  a := [-677090, 1011572, 257837, -210040]
  b := [200716, 273660, -349951, -59969, 42008]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5717 T_ofList CD5717

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 3
  n := 2
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [1, 0, 0, 1, 1]], ![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [1, 1, 1, 1, 1]], ![[0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [1, 1, 0, 0, 1]], ![[0, 0, 0, 0, 1], [1, 0, 0, 1, 1], [1, 1, 1, 1, 1], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 1, 1, 0, 0], ![0, 1, 0, 1, 0], ![1, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  v := ![![0, 1, 1, 0, 0], ![0, 1, 0, 1, 0], ![1, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0]]
  v_ind := ![2, 3, 4]
  w_ind := ![0, 2]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0], ![1, 1, 1, 0, 1], ![1, 1, 1, 1, 0], ![0, 1, 1, 0, 0], ![0, 0, 1, 1, 0]]
  a := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![-12, 10, 14], ![-36, 60, 22], ![-79, 37, 72]], ![![-4, 11, 6], ![-26, 17, 26], ![-42, 53, 30]], ![![0, 2, 2], ![-4, 10, 4], ![-12, 8, 12]], ![![-6, 10, 6], ![-26, 16, 24], ![-40, 48, 28]]]
  c := ![![![0, 0], ![0, 0], ![0, 0]], ![![-8, -3], ![-18, -40], ![-41, -4]], ![![-4, -7], ![-15, -4], ![-21, -32]], ![![-1, -1], ![-3, -7], ![-7, -2]], ![![-4, -6], ![-14, -4], ![-20, -29]]]
  d := ![![![0, 0, 0], ![0, 0, 0]], ![![2, 0, 2], ![-2, 12, 2]], ![![2, 2, 0], ![0, 2, 4]], ![![2, 0, 0], ![2, 2, 0]], ![![2, 2, 0], ![-2, 2, 4]]]
  e := ![![![1, 0], ![0, 1]], ![![0, 0], ![-2, -8]], ![![1, -1], ![-2, 0]], ![![0, 0], ![0, -2]], ![![0, -2], ![-2, 0]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 2, Sum.inl 0), (Sum.inl 0, Sum.inl 1), (Sum.inl 0, Sum.inr 0), (Sum.inl 2, Sum.inr 1)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [2]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateLists K 2 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M2
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 5) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 5 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 5
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 5 := T_degree

noncomputable def bQ : Basis (Fin 5) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 5) (Fin 5) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 5) :
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
          (∑ x : Fin 5,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 5,
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
        (List.ofFn fun i : Fin 5 =>
          (List.ofFn fun j : Fin 5 =>
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
      (voightPolynomialDiscriminantInput 5 row row_mem)
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

end VoightMaximalOrderD5R418

end TraceEuclidean
