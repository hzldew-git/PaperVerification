import TraceEuclidean.VoightMaximalOrderCertificates.Chunk077
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

namespace VoightMaximalOrderD6R766

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨15774208, [-1, 4, 14, -2, -8, 0, 1], 2⟩
local notation "l" => [-1, 4, 14, -2, -8, 0, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSix := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSix_irreducible row row_mem
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 2, 0], ![1, 1, 1, 1, 1, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-1, -1, -1, -1, -1, 2], ![0, -2, -7, 1, 4, 1]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-1, -1, -1, -1, -1, 2], ![1, -4, -14, 2, 8, 0], ![-4, -6, -13, -10, 1, 9]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-1, -1, -1, -1, -1, 2], ![1, -4, -14, 2, 8, 0], ![-8, -7, -12, -22, -6, 16], ![-1, -23, -70, -5, 25, 11]], ![![0, 0, 0, 0, 1, 0], ![-1, -1, -1, -1, -1, 2], ![1, -4, -14, 2, 8, 0], ![-8, -7, -12, -22, -6, 16], ![6, -34, -113, 10, 48, 4], ![-25, -48, -125, -84, 14, 61]], ![![0, 0, 0, 0, 0, 1], ![0, -2, -7, 1, 4, 1], ![-4, -6, -13, -10, 1, 9], ![-1, -23, -70, -5, 25, 11], ![-25, -48, -125, -84, 14, 61], ![-22, -120, -352, -88, 95, 86]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-2]], ![[], [], [], [], [-4], [-2, -2]], ![[], [], [], [-4], [0, -4], [-18, -2, -2]], ![[], [], [-4], [0, -4], [-32, 0, -4], [-22, -18, -2, -2]], ![[], [-2], [-2, -2], [-18, -2, -2], [-22, -18, -2, -2], [-83, -22, -11, -2, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 6 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 6) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 6) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 6) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-1, -1, -1, -1, -1, 2], [0, -2, -7, 1, 4, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-1, -1, -1, -1, -1, 2], [1, -4, -14, 2, 8, 0], [-4, -6, -13, -10, 1, 9]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-1, -1, -1, -1, -1, 2], [1, -4, -14, 2, 8, 0], [-8, -7, -12, -22, -6, 16], [-1, -23, -70, -5, 25, 11]], ![[0, 0, 0, 0, 1, 0], [-1, -1, -1, -1, -1, 2], [1, -4, -14, 2, 8, 0], [-8, -7, -12, -22, -6, 16], [6, -34, -113, 10, 48, 4], [-25, -48, -125, -84, 14, 61]], ![[0, 0, 0, 0, 0, 1], [0, -2, -7, 1, 4, 1], [-4, -6, -13, -10, 1, 9], [-1, -23, -70, -5, 25, 11], [-25, -48, -125, -84, 14, 61], [-22, -120, -352, -88, 95, 86]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp30809 : Fact (Nat.Prime 30809) := fact_iff.2 (by norm_num)

def CD30809 : CertificateDedekindCriterionLists l 30809 where
  n := 2
  a' := [18785, 16405, 26759, 21355]
  b' := [18858, 9498, 5532, 7533, 26538]
  k := [19488, 8555, 29326, 3151, 1]
  f := [5938, 8988, 8503, 4386, 7622, 1]
  g := [13229, 20023, 18942, 9770, 16980, 1]
  h := [13829, 1]
  a := [12709, 12453, 30347, 26133, 13469]
  b := [5013, 10972, 2894, 7959, 17340]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 2
  p := ![2, 30809]
  exp := ![4, 1]
  pdgood := [30809]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp30809.out
  a := [-404460, -60720, 594058, 65106, -132366]
  b := [22121, 234433, 16995, -157839, -10851, 22061]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 30809 T_ofList CD30809

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 3
  n := 3
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 1, 1, 1, 1, 0], [0, 0, 1, 1, 0, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 1, 1, 1, 1, 0], [1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 1, 1]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 1, 1, 1, 1, 0], [1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [1, 1, 0, 1, 1, 1]], ![[0, 0, 0, 0, 1, 0], [1, 1, 1, 1, 1, 0], [1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 1]], ![[0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1], [0, 0, 1, 0, 1, 1], [1, 1, 0, 1, 1, 1], [1, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![1, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0]]
  v := ![![1, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0]]
  v_ind := ![3, 4, 5]
  w_ind := ![0, 2, 4]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 1, 1, 1, 0], ![0, 1, 0, 1, 1, 1], ![0, 0, 1, 1, 1, 0], ![0, 1, 0, 0, 1, 0], ![1, 1, 0, 1, 1, 0], ![0, 0, 1, 0, 0, 1]]
  a := ![![![-19, 2, 18], ![-10, 51, 22], ![-98, 48, 84]], ![![-24, 29, 28], ![-97, 59, 86], ![-184, 146, 170]], ![![-20, 2, 18], ![-10, 50, 22], ![-98, 48, 83]], ![![-22, -4, 16], ![8, 46, 8], ![-80, 26, 62]], ![![-18, 4, 16], ![-14, 42, 24], ![-86, 50, 76]], ![![-6, 24, 14], ![-80, 26, 62], ![-108, 98, 104]]]
  c := ![![![6, -7, -22], ![4, -48, -81], ![34, -65, -153]], ![![8, -31, -62], ![34, -76, -172], ![66, -175, -376]], ![![6, -7, -22], ![4, -48, -81], ![34, -65, -153]], ![![7, -1, -14], ![-2, -41, -61], ![28, -40, -104]], ![![6, -7, -21], ![5, -42, -75], ![30, -64, -146]], ![![2, -24, -42], ![28, -40, -104], ![39, -115, -241]]]
  d := ![![![2, 2, 0], ![0, 0, 4], ![2, 16, 4]], ![![2, 2, 2], ![0, 8, 6], ![-16, 16, 22]], ![![2, 2, 0], ![0, 0, 4], ![2, 16, 4]], ![![0, 2, 0], ![-2, -2, 4], ![6, 16, 0]], ![![2, 2, 0], ![-2, 0, 4], ![4, 14, 4]], ![![0, 0, 2], ![4, 8, 2], ![-20, 4, 18]]]
  e := ![![![0, -1, 1], ![-1, 0, -3], ![-1, -13, -16]], ![![-1, 0, -1], ![-1, -7, -10], ![4, -19, -39]], ![![-1, -1, 1], ![-1, -1, -3], ![-1, -13, -17]], ![![0, 0, 0], ![0, 0, -2], ![-2, -12, -14]], ![![0, 0, 0], ![0, 0, -2], ![-2, -12, -16]], ![![0, 0, 0], ![-2, -6, -8], ![6, -8, -22]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 2, Sum.inl 2), (Sum.inl 0, Sum.inr 0), (Sum.inl 1, Sum.inr 0), (Sum.inl 2, Sum.inr 0)]
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

noncomputable def bOm : Basis (Fin 6) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 6 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 6
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 6 := T_degree

noncomputable def bQ : Basis (Fin 6) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 6) :
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
          (∑ x : Fin 6,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 6,
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
        (List.ofFn fun i : Fin 6 =>
          (List.ofFn fun j : Fin 6 =>
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
      (voightPolynomialDiscriminantInput 6 row row_mem)
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

end VoightMaximalOrderD6R766

namespace VoightMaximalOrderD6R768

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨15785984, [8, -32, 16, 16, -9, -2, 1], 8⟩
local notation "l" => [8, -32, 16, 16, -9, -2, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSix := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSix_irreducible row row_mem
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![4, 0, 0, 0, 0, 0], ![0, 4, 0, 0, 0, 0], ![0, 0, 4, 0, 0, 0], ![0, 0, 0, 4, 0, 0], ![0, 0, 2, 0, 2, 0], ![0, 0, 2, 3, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, -1, 0, 2, 0], ![0, 0, -1, -1, 0, 2], ![-2, 8, -8, -5, 6, 2]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, -1, 0, 2, 0], ![0, 0, -2, -3, 0, 4], ![-4, 16, -15, -11, 10, 4], ![-4, 14, -9, -24, 2, 16]], ![![0, 0, 0, 1, 0, 0], ![0, 0, -1, 0, 2, 0], ![0, 0, -2, -3, 0, 4], ![-8, 32, -29, -22, 18, 8], ![-8, 28, -15, -45, 2, 28], ![-32, 124, -92, -91, 48, 36]], ![![0, 0, 0, 0, 1, 0], ![0, 0, -1, -1, 0, 2], ![-4, 16, -15, -11, 10, 4], ![-8, 28, -15, -45, 2, 28], ![-30, 116, -84, -84, 44, 32], ![-38, 135, -65, -172, 18, 92]], ![![0, 0, 0, 0, 0, 1], ![-2, 8, -8, -5, 6, 2], ![-4, 14, -9, -24, 2, 16], ![-32, 124, -92, -91, 48, 36], ![-38, 135, -65, -172, 18, 92], ![-110, 418, -274, -329, 129, 136]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-4]], ![[], [], [], [], [-8], [-8, -4]], ![[], [], [], [-16], [-16, -8], [-64, -8, -4]], ![[], [], [-8], [-16, -8], [-60, -8, -4], [-76, -34, -4, -2]], ![[], [-4], [-8, -4], [-64, -8, -4], [-76, -34, -4, -2], [-220, -44, -19, -2, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 6 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 6) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 6) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 6) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, -1, 0, 2, 0], [0, 0, -1, -1, 0, 2], [-2, 8, -8, -5, 6, 2]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, -1, 0, 2, 0], [0, 0, -2, -3, 0, 4], [-4, 16, -15, -11, 10, 4], [-4, 14, -9, -24, 2, 16]], ![[0, 0, 0, 1, 0, 0], [0, 0, -1, 0, 2, 0], [0, 0, -2, -3, 0, 4], [-8, 32, -29, -22, 18, 8], [-8, 28, -15, -45, 2, 28], [-32, 124, -92, -91, 48, 36]], ![[0, 0, 0, 0, 1, 0], [0, 0, -1, -1, 0, 2], [-4, 16, -15, -11, 10, 4], [-8, 28, -15, -45, 2, 28], [-30, 116, -84, -84, 44, 32], [-38, 135, -65, -172, 18, 92]], ![[0, 0, 0, 0, 0, 1], [-2, 8, -8, -5, 6, 2], [-4, 14, -9, -24, 2, 16], [-32, 124, -92, -91, 48, 36], [-38, 135, -65, -172, 18, 92], [-110, 418, -274, -329, 129, 136]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp41 : Fact (Nat.Prime 41) := fact_iff.2 (by norm_num)
instance hp47 : Fact (Nat.Prime 47) := fact_iff.2 (by norm_num)

def CD41 : CertificateDedekindCriterionLists l 41 where
  n := 2
  a' := [31, 31, 12, 4]
  b' := [5, 20, 9, 19, 32]
  k := [40, 30, 2, 1, 1]
  f := [10, 18, 13, 10, 10, 1]
  g := [22, 36, 27, 21, 20, 1]
  h := [19, 1]
  a := [9, 4, 11, 5, 3]
  b := [9, 32, 5, 25, 38]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD47 : CertificateDedekindCriterionLists l 47 where
  n := 2
  a' := [31, 45, 19, 40]
  b' := [25, 6, 24, 24, 39]
  k := [1, 23, 6, 26, 1]
  f := [23, 7, 23, 13, 9, 1]
  g := [33, 8, 33, 18, 12, 1]
  h := [33, 1]
  a := [2, 6, 8, 24, 44]
  b := [20, 29, 16, 14, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 3
  p := ![2, 41, 47]
  exp := ![6, 1, 1]
  pdgood := [41, 47]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp41.out
    exact hp47.out
  a := [-125496, 5424, 183824, 11638, -29238]
  b := [-35228, 91624, 16566, -47317, -3564, 4873]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 41 T_ofList CD41
    exact satisfiesDedekindCriterion_of_certificate_lists T l 47 T_ofList CD47

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 4
  n := 2
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 1, 1, 0, 0], [0, 0, 0, 1, 0, 0]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0], [0, 0, 1, 0, 0, 0]], ![[0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 1, 1, 0, 0], [0, 0, 0, 1, 0, 0]], ![[0, 0, 0, 0, 1, 0], [0, 0, 1, 1, 0, 0], [0, 0, 1, 1, 0, 0], [0, 0, 1, 1, 0, 0], [0, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0]], ![[0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 1, 1, 0, 0, 0], [0, 0, 0, 1, 1, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 1, 1, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0]]
  v := ![![0, 1, 1, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0]]
  v_ind := ![2, 3, 4, 5]
  w_ind := ![0, 2]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![1, 0, 1, 1, 0, 1], ![0, 1, 1, 1, 1, 1], ![0, 1, 1, 0, 1, 0], ![0, 1, 0, 1, 0, 0], ![0, 0, 1, 1, 0, 0]]
  a := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![-20, -31, 12, 22], ![-132, -119, 74, 50], ![-95, -228, 31, 124], ![-384, -448, 187, 191]], ![![-36, -42, 22, 28], ![-148, -166, 78, 80], ![-180, -313, 74, 158], ![-457, -626, 211, 286]], ![![-16, -10, 12, 6], ![-18, -48, 4, 34], ![-100, -96, 54, 38], ![-82, -201, 26, 112]], ![![-2, -2, 2, 4], ![-30, -22, 22, 8], ![-16, -46, 2, 30], ![-100, -96, 56, 38]], ![![-4, -2, 4, 4], ![-32, -24, 20, 12], ![-30, -56, 12, 32], ![-102, -114, 52, 52]]]
  c := ![![![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![-3, 26], ![-21, 183], ![-25, 189], ![-74, 603]], ![![-5, 44], ![-25, 213], ![-40, 315], ![-94, 752]], ![![-2, 18], ![-4, 30], ![-17, 145], ![-22, 164]], ![![0, 0], ![-4, 38], ![-4, 30], ![-17, 145]], ![![0, 1], ![-4, 38], ![-6, 49], ![-18, 151]]]
  d := ![![![0, 0, 0, 0], ![0, 0, 0, 0]], ![![2, 2, 0, 2], ![-18, -8, 16, 4]], ![![2, 2, 2, 2], ![-18, -10, 16, 8]], ![![2, 0, 2, 0], ![0, 0, 0, 4]], ![![0, 2, 0, 0], ![0, 0, 4, 0]], ![![2, 2, 0, 0], ![-2, 2, 4, 0]]]
  e := ![![![1, 0], ![0, 1]], ![![1, -3], ![-2, 20]], ![![0, -2], ![-2, 18]], ![![0, 0], ![0, -2]], ![![0, 0], ![0, 0]], ![![0, -2], ![0, 0]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 2, Sum.inl 0), (Sum.inl 3, Sum.inl 0), (Sum.inl 3, Sum.inl 1), (Sum.inl 3, Sum.inr 0), (Sum.inl 0, Sum.inr 1)]
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

noncomputable def bOm : Basis (Fin 6) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 6 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 6
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 6 := T_degree

noncomputable def bQ : Basis (Fin 6) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 6) :
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
          (∑ x : Fin 6,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 6,
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
        (List.ofFn fun i : Fin 6 =>
          (List.ofFn fun j : Fin 6 =>
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
      (voightPolynomialDiscriminantInput 6 row row_mem)
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

end VoightMaximalOrderD6R768

namespace VoightMaximalOrderD6R769

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨15831693, [-19, -12, 33, 18, -9, -3, 1], 3⟩
local notation "l" => [-19, -12, 33, 18, -9, -3, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSix := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSix_irreducible row row_mem
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

def basisDenominator : ℤ := 3
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![3, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0], ![0, 0, 0, 3, 0, 0], ![0, 0, 0, 0, 3, 0], ![1, 1, 1, 1, 1, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-1, -1, -1, -1, -1, 3], ![5, 3, -12, -7, 2, 4]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-1, -1, -1, -1, -1, 3], ![16, 9, -36, -21, 6, 9], ![18, 15, -47, -42, -1, 22]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-1, -1, -1, -1, -1, 3], ![16, 9, -36, -21, 6, 9], ![39, 37, -105, -105, -9, 54], ![111, 85, -248, -200, 3, 85]], ![![0, 0, 0, 0, 1, 0], ![-1, -1, -1, -1, -1, 3], ![16, 9, -36, -21, 6, 9], ![39, 37, -105, -105, -9, 54], ![279, 210, -602, -474, 12, 189], ![422, 363, -938, -846, -33, 349]], ![![0, 0, 0, 0, 0, 1], ![5, 3, -12, -7, 2, 4], ![18, 15, -47, -42, -1, 22], ![111, 85, -248, -200, 3, 85], ![422, 363, -938, -846, -33, 349], ![778, 656, -1679, -1481, -48, 586]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-3]], ![[], [], [], [], [-9], [-12, -3]], ![[], [], [], [-9], [-27, -9], [-66, -12, -3]], ![[], [], [-9], [-27, -9], [-162, -27, -9], [-255, -66, -12, -3]], ![[], [-3], [-12, -3], [-66, -12, -3], [-255, -66, -12, -3], [-461, -112, -27, -5, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 6 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 6) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 6) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 6) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-1, -1, -1, -1, -1, 3], [5, 3, -12, -7, 2, 4]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-1, -1, -1, -1, -1, 3], [16, 9, -36, -21, 6, 9], [18, 15, -47, -42, -1, 22]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-1, -1, -1, -1, -1, 3], [16, 9, -36, -21, 6, 9], [39, 37, -105, -105, -9, 54], [111, 85, -248, -200, 3, 85]], ![[0, 0, 0, 0, 1, 0], [-1, -1, -1, -1, -1, 3], [16, 9, -36, -21, 6, 9], [39, 37, -105, -105, -9, 54], [279, 210, -602, -474, 12, 189], [422, 363, -938, -846, -33, 349]], ![[0, 0, 0, 0, 0, 1], [5, 3, -12, -7, 2, 4], [18, 15, -47, -42, -1, 22], [111, 85, -248, -200, 3, 85], [422, 363, -938, -846, -33, 349], [778, 656, -1679, -1481, -48, 586]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)
instance hp127 : Fact (Nat.Prime 127) := fact_iff.2 (by norm_num)

def CD19 : CertificateDedekindCriterionLists l 19 where
  n := 2
  a' := [9, 10, 13, 3]
  b' := [16, 6, 16, 15, 7]
  k := [0, 16, 10, 1, 1]
  f := [1, 6, 12, 7, 17, 2]
  g := [0, 6, 15, 8, 18, 1]
  h := [17, 1]
  a := [1, 2, 16, 2, 1]
  b := [5, 3, 15, 15, 17]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD127 : CertificateDedekindCriterionLists l 127 where
  n := 2
  a' := [88, 71, 76, 79]
  b' := [77, 63, 28, 120, 35]
  k := [116, 6, 81, 38, 1]
  f := [12, 41, 21, 22, 28, 1]
  g := [35, 120, 60, 64, 81, 1]
  h := [43, 1]
  a := [122, 112, 67, 8, 124]
  b := [9, 89, 29, 87, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3] where
  n := 3
  p := ![3, 19, 127]
  exp := ![3, 1, 1]
  pdgood := [19, 127]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp19.out
    exact hp127.out
  a := [38883, -258084, -28449, 143892, -34932]
  b := [-66994, 1283, 115640, -8011, -26893, 5822]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 19 T_ofList CD19
    exact satisfiesDedekindCriterion_of_certificate_lists T l 127 T_ofList CD127

noncomputable def M3 : MaximalOrderCertificateLists 3 O Om hm where
  m := 4
  n := 2
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [2, 2, 2, 2, 2, 0], [2, 0, 0, 2, 2, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [2, 2, 2, 2, 2, 0], [1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 2, 1]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [2, 2, 2, 2, 2, 0], [1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 1, 1, 1, 0, 1]], ![[0, 0, 0, 0, 1, 0], [2, 2, 2, 2, 2, 0], [1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [2, 0, 1, 0, 0, 1]], ![[0, 0, 0, 0, 0, 1], [2, 0, 0, 2, 2, 1], [0, 0, 1, 0, 2, 1], [0, 1, 1, 1, 0, 1], [2, 0, 1, 0, 0, 1], [1, 2, 1, 1, 0, 1]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![2, 0, 1, 0, 0, 0], ![0, 2, 0, 1, 0, 0], ![2, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0]]
  v := ![![2, 0, 1, 0, 0, 0], ![0, 2, 0, 1, 0, 0], ![2, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0]]
  v_ind := ![2, 3, 4, 5]
  w_ind := ![0, 3]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 2, 2, 2], ![1, 2, 0, 2, 1, 1], ![1, 1, 0, 2, 0, 1], ![2, 2, 1, 1, 0, 0], ![1, 2, 0, 1, 2, 0]]
  a := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![-168, -124, 12, 72], ![-830, -684, 8, 324], ![-3290, -2846, -56, 1188], ![-5730, -5052, -154, 2042]], ![![-84, -59, 5, 39], ![-447, -362, 14, 171], ![-1752, -1528, -38, 654], ![-3137, -2739, -70, 1115]], ![![-48, -39, -3, 30], ![-342, -255, 24, 111], ![-1149, -1053, -51, 462], ![-2187, -1886, -40, 762]], ![![3, 3, 0, 3], ![-33, -18, 9, 12], ![-141, -126, -3, 69], ![-318, -255, 6, 117]], ![![-72, -39, 15, 21], ![-246, -234, -12, 129], ![-1311, -1053, 18, 438], ![-2148, -1905, -57, 792]]]
  c := ![![![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![102, 98], ![556, 546], ![2328, 2304], ![4116, 4104]], ![![51, 48], ![295, 290], ![1235, 1235], ![2244, 2225]], ![![30, 31], ![226, 207], ![813, 848], ![1566, 1534]], ![![-2, -1], ![17, 16], ![92, 100], ![216, 206]], ![![42, 33], ![159, 183], ![915, 855], ![1528, 1543]]]
  d := ![![![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 6, 6, 6], ![-78, -48, 12, 42]], ![![0, 6, 3, 3], ![-33, -24, 9, 21]], ![![0, 6, 0, 3], ![-33, -21, 12, 12]], ![![3, 3, 0, 0], ![6, 3, 3, 0]], ![![0, 3, 6, 0], ![0, -6, -3, 18]]]
  e := ![![![1, 0], ![0, 1]], ![![-6, -4], ![38, 36]], ![![-2, -2], ![13, 19]], ![![0, -3], ![15, 18]], ![![0, 0], ![-6, 0]], ![![-3, 0], ![-6, 3]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 3, Sum.inl 0), (Sum.inl 3, Sum.inl 1), (Sum.inl 0, Sum.inr 0), (Sum.inl 3, Sum.inr 0)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [3]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateLists K 3 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M3
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [3] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 6) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 6 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 6
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 6 := T_degree

noncomputable def bQ : Basis (Fin 6) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 6) :
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
          (∑ x : Fin 6,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 6,
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
        (List.ofFn fun i : Fin 6 =>
          (List.ofFn fun j : Fin 6 =>
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
      (voightPolynomialDiscriminantInput 6 row row_mem)
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

end VoightMaximalOrderD6R769

namespace VoightMaximalOrderD6R771

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨15883625, [-44, -34, 37, 22, -10, -3, 1], 34⟩
local notation "l" => [-44, -34, 37, 22, -10, -3, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSix := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSix_irreducible row row_mem
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

def basisDenominator : ℤ := 34
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![34, 0, 0, 0, 0, 0], ![0, 34, 0, 0, 0, 0], ![0, 0, 34, 0, 0, 0], ![0, 0, 0, 34, 0, 0], ![0, 0, 0, 0, 34, 0], ![32, 31, 8, 30, 9, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-32, -31, -8, -30, -9, 34], ![-10, -9, -3, -11, -2, 12]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-32, -31, -8, -30, -9, 34], ![-52, -59, -61, -112, -17, 102], ![-56, -56, -29, -75, -17, 76]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-32, -31, -8, -30, -9, 34], ![-52, -59, -61, -112, -17, 102], ![-476, -443, -229, -673, -163, 646], ![-216, -213, -148, -355, -74, 334]], ![![0, 0, 0, 0, 1, 0], ![-32, -31, -8, -30, -9, 34], ![-52, -59, -61, -112, -17, 102], ![-476, -443, -229, -673, -163, 646], ![-1244, -1237, -1077, -2445, -498, 2210], ![-972, -928, -623, -1602, -357, 1492]], ![![0, 0, 0, 0, 0, 1], ![-10, -9, -3, -11, -2, 12], ![-56, -56, -29, -75, -17, 76], ![-216, -213, -148, -355, -74, 334], ![-972, -928, -623, -1602, -357, 1492], ![-573, -553, -380, -951, -206, 889]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-34]], ![[], [], [], [], [-1156], [-408, -34]], ![[], [], [], [-1156], [-3468, -1156], [-2584, -408, -34]], ![[], [], [-1156], [-3468, -1156], [-21964, -3468, -1156], [-11356, -2584, -408, -34]], ![[], [-34], [-408, -34], [-2584, -408, -34], [-11356, -2584, -408, -34], [-6905, -1386, -214, -21, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 6 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 6) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 6) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 6) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-32, -31, -8, -30, -9, 34], [-10, -9, -3, -11, -2, 12]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-32, -31, -8, -30, -9, 34], [-52, -59, -61, -112, -17, 102], [-56, -56, -29, -75, -17, 76]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-32, -31, -8, -30, -9, 34], [-52, -59, -61, -112, -17, 102], [-476, -443, -229, -673, -163, 646], [-216, -213, -148, -355, -74, 334]], ![[0, 0, 0, 0, 1, 0], [-32, -31, -8, -30, -9, 34], [-52, -59, -61, -112, -17, 102], [-476, -443, -229, -673, -163, 646], [-1244, -1237, -1077, -2445, -498, 2210], [-972, -928, -623, -1602, -357, 1492]], ![[0, 0, 0, 0, 0, 1], [-10, -9, -3, -11, -2, 12], [-56, -56, -29, -75, -17, 76], [-216, -213, -148, -355, -74, 334], [-972, -928, -623, -1602, -357, 1492], [-573, -553, -380, -951, -206, 889]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp17 : Fact (Nat.Prime 17) := fact_iff.2 (by norm_num)
instance hp31 : Fact (Nat.Prime 31) := fact_iff.2 (by norm_num)
instance hp4099 : Fact (Nat.Prime 4099) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1]
  b' := [1, 3]
  k := [1]
  f := [12, 10, -5, -2, 3, 1]
  g := [4, 2, 1, 1]
  h := [4, 2, 1, 1]
  a := [1, 3, 1]
  b := [1, 3, 4, 0, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD31 : CertificateDedekindCriterionLists l 31 where
  n := 2
  a' := [0, 28, 22, 26]
  b' := [23, 13, 5, 18, 1]
  k := [14, 29, 8, 10, 1]
  f := [2, 9, 2, 1, 6, 1]
  g := [2, 27, 8, 5, 19, 1]
  h := [9, 1]
  a := [17, 0, 30, 14, 4]
  b := [30, 30, 17, 7, 27]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD4099 : CertificateDedekindCriterionLists l 4099 where
  n := 2
  a' := [241, 3611, 3077, 921]
  b' := [2458, 1739, 2058, 286, 3095]
  k := [2933, 1537, 1277, 3203, 1]
  f := [2468, 1597, 2440, 1776, 975, 1]
  g := [4053, 2621, 4006, 2915, 1600, 1]
  h := [2496, 1]
  a := [1884, 2637, 2149, 4003, 329]
  b := [2972, 1793, 3194, 771, 3770]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 17] where
  n := 5
  p := ![2, 5, 17, 31, 4099]
  exp := ![1, 1, 2, 1, 1]
  pdgood := [5, 31, 4099]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp5.out
    exact hp17.out
    exact hp31.out
    exact hp4099.out
  a := [58034804, -196308646, 31877233, 60722877, -16811862]
  b := [-85904729, 9042563, 71135912, -13095027, -11521468, 2801977]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 31 T_ofList CD31
    exact satisfiesDedekindCriterion_of_certificate_lists T l 4099 T_ofList CD4099

noncomputable def M2 : MaximalOrderCertificateOfUnramifiedLists 2 O Om hm where
  n := 6
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0], [0, 1, 1, 1, 0, 0]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0], [0, 0, 1, 1, 1, 0]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0], [0, 1, 1, 1, 1, 0], [0, 1, 0, 1, 0, 0]], ![[0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0], [0, 1, 1, 1, 1, 0], [0, 1, 1, 1, 0, 0], [0, 0, 1, 0, 1, 0]], ![[0, 0, 0, 0, 0, 1], [0, 1, 1, 1, 0, 0], [0, 0, 1, 1, 1, 0], [0, 1, 0, 1, 0, 0], [0, 0, 1, 0, 1, 0], [1, 1, 0, 1, 0, 1]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 1, 1, 0, 1, 0], ![0, 1, 1, 1, 0, 0], ![1, 1, 0, 1, 0, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hindw := by decide
  hwFrobComp := by decide

noncomputable def M17 : MaximalOrderCertificateOfUnramifiedLists 17 O Om hm where
  n := 6
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [2, 3, 9, 4, 8, 0], [7, 8, 14, 6, 15, 12]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [2, 3, 9, 4, 8, 0], [16, 9, 7, 7, 0, 0], [12, 12, 5, 10, 0, 8]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [2, 3, 9, 4, 8, 0], [16, 9, 7, 7, 0, 0], [0, 16, 9, 7, 7, 0], [5, 8, 5, 2, 11, 11]], ![[0, 0, 0, 0, 1, 0], [2, 3, 9, 4, 8, 0], [16, 9, 7, 7, 0, 0], [0, 16, 9, 7, 7, 0], [14, 4, 11, 3, 12, 0], [14, 7, 6, 13, 0, 13]], ![[0, 0, 0, 0, 0, 1], [7, 8, 14, 6, 15, 12], [12, 12, 5, 10, 0, 8], [5, 8, 5, 2, 11, 11], [14, 7, 6, 13, 0, 13], [5, 8, 11, 1, 15, 5]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![13, 12, 5, 4, 2, 0], ![8, 16, 10, 0, 0, 0], ![7, 3, 11, 14, 9, 0], ![13, 1, 8, 14, 15, 0], ![8, 11, 15, 0, 0, 16]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [2, 17]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 2 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M2
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 17 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M17
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 17] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 6) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 6 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 6
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 6 := T_degree

noncomputable def bQ : Basis (Fin 6) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 6) :
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
          (∑ x : Fin 6,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 6,
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
        (List.ofFn fun i : Fin 6 =>
          (List.ofFn fun j : Fin 6 =>
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
      (voightPolynomialDiscriminantInput 6 row row_mem)
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

end VoightMaximalOrderD6R771

end TraceEuclidean
