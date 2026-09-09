# Reproducibility report

## Development-checkout run

| Item | Result |
|---|---|
| Host | Windows x86-64 |
| Lean | 4.32.1, commit `f054605aea4b840552cca2e725580bffd1e1b704` |
| Lake | 5.0.0 |
| mathlib | `520045ab14e26149ee970e2e617ca04b09bde5d6` |
| `lake exe cache get` | PASS |
| `lake build` | PASS, 8,665 jobs |
| Endpoint signature/axiom audit | PASS, 13 endpoints |
| Forbidden-construct scan | PASS, zero matches |
| Mathematica verification | PASS, 2,165 records |
| Verification-manual build | PASS |
| Manuscript-exclusion gate | Pending final staged-tree check |

The public computational run uses frozen extracted inputs. Rebinding the source
hash to a new manuscript version is a private maintainer operation and cannot
be reproduced from the public repository alone.

## Clean-checkout boundary

GitHub Actions is configured to rebuild the Lean project from a fresh Ubuntu
checkout and rerun the forbidden-construct and endpoint-axiom audits. A local
clean-checkout receipt will be added below before deployment is declared
complete.

Current reproducibility status:
`REPRODUCIBLE_IN_DEVELOPMENT_CHECKOUT_PENDING_CLEAN_CHECKOUT_RECEIPT`.
