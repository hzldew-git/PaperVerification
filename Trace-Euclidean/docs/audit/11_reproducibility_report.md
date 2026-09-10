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

A detached worktree based on code-and-tooling commit
`ec66708818e971b349e71777327ab638b3fa4554` was populated from the committed
repository state and rerun independently of the development checkout. The
project build directory was empty before its first Lean build.

| Item | Result |
|---|---|
| Pinned dependency verification | PASS, 9/9 package revisions matched `lake-manifest.json`, including mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6` |
| `lake build` | PASS, 8,696 jobs |
| Endpoint signature/axiom audit | PASS, 50/50 standard axiom sets |
| Public Mathematica rerun | PASS, 2,165 records |
| Verification-manual rebuild | PASS, identical SHA-256 `c4aab923487ffe37c90eab5d7249eb5c7ba77400466126458219d94b4cee37b7` in both checkout paths |
| Delivery integrity check | PASS, zero errors |
| Manuscript-exclusion gate | PASS, 109 files inspected and 9 approved verification documents |
| Repository state after public rerun | PASS, clean |

The Windows clean build used `LEAN_NUM_THREADS=4` to avoid exhausting local
process resources. This limits build concurrency only; it does not change the
Lean sources, toolchain, dependencies, or kernel checks. A fresh GitHub package
fetch was attempted twice, but the connection was reset and then unavailable.
The fallback reused local package checkouts only after checking all nine Git
HEAD revisions against the committed manifest; no dependency revision was
substituted. The final evidence-only update was rerun in the same detached
worktree, including the clean-state check.

GitHub Actions is configured to repeat the Lean build, forbidden-construct
scan, endpoint-axiom audit, and manuscript-exclusion check from a fresh Ubuntu
checkout.

Current reproducibility status: `REPRODUCIBLE_CLEAN_CHECKOUT_VERIFIED`.
