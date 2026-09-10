# Reproducibility report

## Development-checkout run

| Item | Result |
|---|---|
| Host | Windows x86-64 |
| Lean | 4.32.1, commit `f054605aea4b840552cca2e725580bffd1e1b704` |
| Lake | 5.0.0 |
| mathlib | `520045ab14e26149ee970e2e617ca04b09bde5d6` |
| `lake exe cache get` | PASS |
| `lake build` | PASS, more than 8,600 jobs |
| Endpoint signature/axiom audit | PASS, 40 endpoints |
| Forbidden-construct scan | PASS, zero matches |
| Mathematica verification | PASS, 2,165 records |
| Verification-manual build | PASS |
| Manuscript-exclusion gate | PASS |

The public computational run uses frozen extracted inputs. Rebinding the source
hash to a new manuscript version is a private maintainer operation and cannot
be reproduced from the public repository alone.

## Clean-checkout boundary

A detached clean-checkout rerun is required after the current changes are
committed. The previous release passed that protocol; the current development
checkout has passed the same build commands and publication gate, but its
post-commit clean-checkout record is not yet available in this draft.

| Item | Result |
|---|---|
| Pinned dependency restoration | PASS, including mathlib revision `520045ab14e26149ee970e2e617ca04b09bde5d6` |
| `lake build` | Pending post-commit clean checkout |
| Endpoint signature/axiom audit | Pending post-commit clean checkout |
| Public Mathematica rerun | Pending post-commit clean checkout |
| Delivery integrity check | Pending post-commit clean checkout |
| Manuscript-exclusion gate | Pending post-commit clean checkout |
| Repository state after public rerun | Pending post-commit clean checkout |

The Windows clean build used `LEAN_NUM_THREADS=4` to avoid exhausting local
process resources. This limits build concurrency only; it does not change the
Lean sources, toolchain, dependencies, or kernel checks.

GitHub Actions is configured to repeat the Lean build, forbidden-construct
scan, endpoint-axiom audit, and manuscript-exclusion check from a fresh Ubuntu
checkout.

Current reproducibility status before the release commit:
`REPRODUCIBLE_DEVELOPMENT_CHECKOUT`. This file is updated to
`REPRODUCIBLE_CLEAN_CHECKOUT_VERIFIED` only after the detached checkout
passes.
