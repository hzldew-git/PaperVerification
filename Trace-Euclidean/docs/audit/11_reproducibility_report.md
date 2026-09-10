# Reproducibility report

## Development-checkout run

| Item | Result |
|---|---|
| Host | Windows x86-64 |
| Lean | 4.32.1, commit `f054605aea4b840552cca2e725580bffd1e1b704` |
| Lake | 5.0.0 |
| mathlib | `520045ab14e26149ee970e2e617ca04b09bde5d6` |
| `lake exe cache get` | PASS |
| `lake build` | PASS, 8,696 jobs |
| Endpoint signature/axiom audit | PASS, 50 endpoints |
| Forbidden-construct scan | PASS, zero matches |
| Mathematica verification | PASS, 2,165 records |
| Verification-manual build | PASS |
| Manuscript-exclusion gate | PASS |

The public computational run uses frozen extracted inputs. Rebinding the source
hash to a new manuscript version is a private maintainer operation and cannot
be reproduced from the public repository alone.

## Clean-checkout run

A detached worktree at commit
`972c30b8d977fad41f716cb4b15fced13ed44ace` was populated from the committed
repository state and rerun independently of the development checkout.

| Item | Result |
|---|---|
| Pinned dependency restoration | PASS, including mathlib revision `520045ab14e26149ee970e2e617ca04b09bde5d6` |
| `lake build` | PASS, 8,673 jobs |
| Endpoint signature/axiom audit | PASS, 40/40 standard axiom sets |
| Public Mathematica rerun | PASS, 2,165 records |
| Delivery integrity check | PASS, zero errors |
| Manuscript-exclusion gate | PASS, 86 files inspected and 9 approved verification documents |
| Repository state after public rerun | PASS, clean |

The Windows clean build used `LEAN_NUM_THREADS=4` to avoid exhausting local
process resources. This limits build concurrency only; it does not change the
Lean sources, toolchain, dependencies, or kernel checks.

GitHub Actions is configured to repeat the Lean build, forbidden-construct
scan, endpoint-axiom audit, and manuscript-exclusion check from a fresh Ubuntu
checkout.

Current reproducibility status: `REPRODUCIBLE_CLEAN_CHECKOUT_VERIFIED`.
