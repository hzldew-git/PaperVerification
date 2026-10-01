# Voight totally real field tables

These are archived copies of John Voight's public tables accompanying
*Enumeration of totally real number fields of bounded root discriminant*.
The current author page links to the former table site, which now returns 404;
the files below were recovered from the Internet Archive on 2026-09-26.

| File | Original bound | Archive timestamp | SHA-256 |
| --- | ---: | ---: | --- |
| `5-17.txt` | degree 5, root discriminant at most 17 | 20230529163403 | `7c2ce57f51de3ad34bb60ade85659689fc629406315e9699a144f737d1b34192` |
| `6-16.txt` | degree 6, root discriminant at most 16 | 20230529153658 | `6e6bc75b54ad2643a42a3dfdd9497347eb89735d00c5b7367e934ad32d8ae082` |
| `7-15.5.txt` | degree 7, root discriminant at most 15.5 | 20230529161102 | `95ed179560eb866445eee3da22826cf98cc5eb0bc7f5091c27f4d332dc421a3d` |
| `8-15.txt` | degree 8, root discriminant at most 15 | 20230529153508 | `204a0ea04e2f4079f6fea20369ad8822d4d678a718272b9aaea68cf144b83294` |
| `9-14.5.txt` | degree 9, root discriminant at most 14.5 | 20230529160741 | `9c14aa90371184020bb121c36e63ceaa5bd4ada0eb55198fd94d4df67d6d3821` |
| `10.txt` | known degree 10 fields | 20230529150504 | `cceac525009d9ab6b947e17186a5e74df2643eace152955702d306af6defbe83` |

The archived URL pattern is
`https://web.archive.org/web/TIMESTAMPid_/https://math.dartmouth.edu/~jvoight/nf-tables/FILE`.
The generator validates all six hashes and, for every file, its row structure,
degree, monicity, row count, first discriminant, and sorted order. An exact
integer Bareiss determinant calculation also checks for all 2,773 rows that
the defining-polynomial discriminant is the recorded positive index squared
times the field discriminant. It checks that the first degree-ten
discriminant exceeds `14^10` before writing the complete degree 5--10 rows and
the degree 5--9 discriminant columns to Lean.

Lean separately checks both the five imported column lengths and order and
the six full-row counts, structural conditions, positive indices, column
projections, and maximum indices. These are two disclosed `native_decide`
certificates. The independent Mathematica script
`checks/voight_polynomial_integrity.wls` additionally verifies all 2,773
defining polynomials are irreducible and totally real, recomputes the
polynomial-discriminant index equation, and confirms the actual number-field
discriminant.

These finite checks do not establish enumeration completeness. That statement
is isolated separately as the source-facing Voight input.
