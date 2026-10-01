import TraceEuclidean.VoightDiscriminantData

/-!
# The combined archived Voight row list

This data-only module keeps the list definition independent of any executable
certificate replay.
-/

namespace TraceEuclidean

/-- The complete list of archived defining-polynomial rows in degrees five
through ten. -/
def allVoightPolynomialRows : List VoightPolynomialRow :=
  voightPolynomialRowsFive ++
    (voightPolynomialRowsSix ++
      (voightPolynomialRowsSeven ++
        (voightPolynomialRowsEight ++
          (voightPolynomialRowsNine ++
            voightPolynomialRowsTen))))

end TraceEuclidean
