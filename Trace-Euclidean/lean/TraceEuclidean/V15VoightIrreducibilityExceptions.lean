import TraceEuclidean.V15FiniteFieldIrreducibilityCertificate

/-! Explicit boundary of the single-prime Rabin certificate method. -/

namespace TraceEuclidean

def v15VoightRabinExceptionsFive :
    List V15VoightPolynomialRow :=
  []

def v15VoightRabinExceptionsSix :
    List V15VoightPolynomialRow :=
  [
    ⟨810448, [1, -5, 0, 9, -2, -3, 1], 1⟩,
    ⟨3356224, [-1, 0, 8, 0, -6, 0, 1], 1⟩,
    ⟨3829849, [1, -3, -5, 15, -6, -2, 1], 1⟩,
    ⟨4227136, [-1, 0, 7, 0, -6, 0, 1], 1⟩,
    ⟨7711729, [-1, 0, 10, 0, -9, 0, 1], 8⟩,
    ⟨7997584, [-2, -4, 12, 5, -7, -1, 1], 2⟩,
    ⟨8248384, [2, -6, -2, 14, -5, -3, 1], 3⟩,
    ⟨9684544, [2, -6, -2, 14, -6, -2, 1], 1⟩,
    ⟨10909809, [3, -9, 1, 13, -6, -2, 1], 1⟩,
    ⟨11587216, [-17, 18, 29, -10, -13, 0, 1], 16⟩,
    ⟨12002256, [1, -3, -6, 17, -6, -3, 1], 4⟩,
    ⟨12008989, [-1, -2, 14, 0, -14, -2, 1], 32⟩,
    ⟨12730624, [-4, 0, 13, 0, -8, 0, 1], 4⟩,
    ⟨13122000, [-20, 0, 36, 0, -12, 0, 1], 64⟩,
    ⟨15848361, [3, -10, 2, 15, -5, -3, 1], 1⟩,
    ⟨16484816, [9, -39, 26, 25, -10, -3, 1], 36⟩
  ]

def v15VoightRabinExceptionsSeven :
    List V15VoightPolynomialRow :=
  []

def v15VoightRabinExceptionsEight :
    List V15VoightPolynomialRow :=
  [
    ⟨324000000, [1, 0, -8, 0, 14, 0, -7, 0, 1], 1⟩,
    ⟨432640000, [-1, 4, 2, -18, 4, 16, -7, -2, 1], 1⟩,
    ⟨442050625, [-1, 11, -5, -36, 17, 26, -12, -2, 1], 63⟩,
    ⟨1024000000, [1, 0, -12, 0, 19, 0, -8, 0, 1], 1⟩,
    ⟨1064390625, [1, 0, -17, 0, 44, 0, -13, 0, 1], 256⟩,
    ⟨1142440000, [1, 4, -5, -15, 8, 15, -5, -3, 1], 1⟩,
    ⟨1358954496, [1, 0, -16, 0, 20, 0, -8, 0, 1], 1⟩,
    ⟨1534132224, [1, -4, -12, 8, 21, -4, -10, 0, 1], 19⟩,
    ⟨1948160000, [-1, 6, -3, -20, 8, 18, -4, -4, 1], 1⟩,
    ⟨2127515625, [1, -36, 114, -102, -1, 36, -9, -3, 1], 1⟩,
    ⟨2152960000, [16, 0, -56, 0, 52, 0, -14, 0, 1], 4096⟩,
    ⟨2393655625, [1, 1, -13, 4, 23, -4, -12, 0, 1], 17⟩
  ]

def v15VoightRabinExceptionsNine :
    List V15VoightPolynomialRow :=
  [
    ⟨17515230173, [1, -5, -2, 34, -24, -26, 29, -3, -4, 1], 1⟩
  ]

def v15VoightRabinExceptionsTen :
    List V15VoightPolynomialRow :=
  [
    ⟨1704131819776, [-1, 0, 16, 0, -44, 0, 34, 0, -10, 0, 1], 2⟩,
    ⟨2837392015936, [-1, 0, 32, 0, -64, 0, 42, 0, -11, 0, 1], 4⟩
  ]

/-- Rows not covered by one irreducible modular reduction. -/
def v15VoightRabinExceptions : ℕ → List V15VoightPolynomialRow
  | 0 => []
  | 1 => []
  | 2 => []
  | 3 => []
  | 4 => []
  | 5 => v15VoightRabinExceptionsFive
  | 6 => v15VoightRabinExceptionsSix
  | 7 => v15VoightRabinExceptionsSeven
  | 8 => v15VoightRabinExceptionsEight
  | 9 => v15VoightRabinExceptionsNine
  | 10 => v15VoightRabinExceptionsTen
  | _ => []

end TraceEuclidean
