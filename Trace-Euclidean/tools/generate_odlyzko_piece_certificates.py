#!/usr/bin/env python3
"""Generate the small pure-kernel Odlyzko quadrature certificate modules."""

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1] / "lean" / "TraceEuclidean" / "OdlyzkoCertificates"

CERTIFICATES = [
    ("SinhMiddleOne", "sinhMiddleOneQuadrature", "stableSinhIntegrand", "sinhMiddleOne", 128, "1", 225221, "quadrature20Depth10"),
    ("SinhMiddleTwo", "sinhMiddleTwoQuadrature", "stableSinhIntegrand", "sinhMiddleTwo", 96, "(1 / 2)", 272119, "quadrature20Depth12"),
    ("SinhMiddleThree", "sinhMiddleThreeQuadrature", "stableSinhIntegrand", "sinhMiddleThree", 64, "(1 / 4)", 197324, "quadrature20Depth13"),
    ("SinhFarFourFive", "sinhFarFourFiveQuadrature", "farSinhIntegrand", "unitFourFive", 80, "(1 / 4)", 105268, "quadrature19Depth14"),
    ("SinhFarFiveSix", "sinhFarFiveSixQuadrature", "farSinhIntegrand", "unitFiveSix", 80, "(1 / 4)", 64662, "quadrature20Depth14"),
    ("SinhFarSixSeven", "sinhFarSixSevenQuadrature", "farSinhIntegrand", "unitSixSeven", 80, "(1 / 4)", 39249, "quadrature20Depth14"),
    ("SinhFarSevenEight", "sinhFarSevenEightQuadrature", "farSinhIntegrand", "unitSevenEight", 64, "(1 / 4)", 23797, "quadrature20Depth14"),
    ("CoshNearZeroOne", "coshNearZeroOneQuadrature", "stableCoshIntegrand", "unitZeroOne", 128, "1", 32691, "quadrature20Depth8"),
    ("CoshNearOneTwo", "coshNearOneTwoQuadrature", "stableCoshIntegrand", "unitOneTwo", 64, "(1 / 4)", 145489, "quadrature20Depth10"),
    ("CoshNearTwoThree", "coshNearTwoThreeQuadrature", "stableCoshIntegrand", "unitTwoThree", 64, "(1 / 4)", 188736, "quadrature20Depth12"),
    ("CoshNearThreeFour", "coshNearThreeFourQuadrature", "stableCoshIntegrand", "unitThreeFour", 64, "(1 / 4)", 153359, "quadrature20Depth13"),
    ("CoshFarFourFive", "coshFarFourFiveQuadrature", "farCoshIntegrand", "unitFourFive", 64, "(1 / 4)", 102769, "quadrature19Depth14"),
    ("CoshFarFiveSix", "coshFarFiveSixQuadrature", "farCoshIntegrand", "unitFiveSix", 64, "(1 / 4)", 64092, "quadrature20Depth14"),
    ("CoshFarSixSeven", "coshFarSixSevenQuadrature", "farCoshIntegrand", "unitSixSeven", 64, "(1 / 4)", 39123, "quadrature19Depth14"),
    ("CoshFarSevenEight", "coshFarSevenEightQuadrature", "farCoshIntegrand", "unitSevenEight", 64, "(1 / 4)", 23770, "quadrature19Depth14"),
]

TEMPLATE = """import TraceEuclidean.OdlyzkoNumericalPieceData

namespace TraceEuclidean.OdlyzkoNumerical.Certificate

open LeanCert.Core LeanCert.Engine
open LeanCert.Validity.TrapezoidalDyadic

elab \"kernel_rfl\" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    Lean.Meta.withTransparency .all goal.applyRfl
  Lean.Elab.Tactic.replaceMainGoal []

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The closed interval computation exceeds Lean's default elaboration budget.
theorem {theorem} : checkTrapezoidalUpperDyadicFull
    {expr} {interval} {points} {bound} ({numerator} / 1000000)
    {config} = true := by
  kernel_rfl

end TraceEuclidean.OdlyzkoNumerical.Certificate
"""


def main() -> None:
    ROOT.mkdir(parents=True, exist_ok=True)
    for module, theorem, expr, interval, points, bound, numerator, config in CERTIFICATES:
        path = ROOT / f"{module}.lean"
        content = TEMPLATE.format(
            theorem=theorem,
            expr=expr,
            interval=interval,
            points=points,
            bound=bound,
            numerator=numerator,
            config=config,
        )
        if not path.exists() or path.read_text(encoding="utf-8") != content:
            path.write_text(content, encoding="utf-8")

    aggregate = ROOT.parent / "OdlyzkoNumericalPieceCertificates.lean"
    aggregate_content = (
        "\n".join(
            f"import TraceEuclidean.OdlyzkoCertificates.{module}"
            for module, *_ in CERTIFICATES
        )
        + "\n"
    )
    if not aggregate.exists() or aggregate.read_text(encoding="utf-8") != aggregate_content:
        aggregate.write_text(aggregate_content, encoding="utf-8")


if __name__ == "__main__":
    main()
