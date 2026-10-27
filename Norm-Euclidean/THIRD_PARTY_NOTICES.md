# Source provenance and licenses

Existing copyright and license notices in source files are retained. This
release does not assert a new blanket license over files without a license
notice; publication permission is distinct from a relicensing grant.

## Class-field arithmetic

The selected `lean/ArithmeticClassFields` sources originate from Naganori
Yamaguchi's class-field development, preserved at commit
`01b4bcb786c458c9af029860c9bbdbd67dd7c978` in
[the archived repository](https://github.com/PalomarArchive/n-yamaguchi-0729--FiniteAbelianGlobalReciprocityv2--ccc6f4bb14f4/tree/01b4bcb786c458c9af029860c9bbdbd67dd7c978/Lean4).
They are licensed under Apache 2.0; the license is retained in
`lean/ArithmeticClassFields/LICENSE` and `licenses/ClassFieldArithmetic.txt`.

The sources were adapted from the upstream toolchain to Lean 4.32.1, including
API/elaboration adjustments and proved compatibility lemmas. The release
contains only the import closure required by the selected endpoints. Original
copyright headers remain attached to the individual files.

## BONG and related reused modules

BongTheory is an external dependency at commit
`a1343b6e471cbf417cab0e09dc5876b74358260a`. Its own license and notices are
distributed by that dependency. Copied/adapted modules under
`lean/NormEuclidean/Reuse` and the Chapter X files with BONG contributor headers
retain their Apache 2.0 notices. The corresponding license text is retained
under `lean/NormEuclidean/Reuse/LICENSE` and `licenses/BongTheory.txt`.

`FrobeniusSplitting.lean` retains its Yamaguchi attribution. Other locally
written proof modules keep their existing notices; no authorship of upstream
work is reassigned by this package.

## Build dependencies

Lean and mathlib, together with their transitive dependencies, are obtained at
the pinned revisions in the lock file. Their respective upstream licenses
apply. Build caches and downloaded dependency trees are not committed here.
