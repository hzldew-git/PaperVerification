# Trust and axiom report

The Lean project has a successful complete build on Lean 4.32.1 with the pinned mathlib revision. All 105 selected v15 endpoint axiom sets contain only propext, Classical.choice, and Quot.sound. Four additional finite-array equality theorems are kernel computations with no axiom dependencies. Source scanning found no sorry, sorryAx, project axiom, native_decide, run_tac, unsafe, extern, or implemented_by in the proof source.

Odlyzko's unconditional Table 4 is an EXTERNAL_INPUT. Its row b=4 lists A=36.347 and E=10.667. The table itself states D > A^r1 B^(2r2) exp(-E); the official description confirms its unconditional status and rounding convention. For totally real fields this gives D > 36.347^d exp(-10.667). V15OdlyzkoTable4Input is an explicit theorem parameter for the coded totally real fields, and Lean proves the downstream numerical bound. This input is not proved by the Lean kernel and is not concealed as a custom axiom.

The public Python and Wolfram checks trust their kernels and the extracted v15 input file. The private source-bound checks additionally verify the manuscript hash and printed data. Neither computational PASS counts nor Lean compilation certifies paper-to-code semantic fidelity. The v9 verification manual, tests, and result summary are retained as historical artifacts.
