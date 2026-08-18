# LOG: counting perfect matchings in Lean 4 + Mathlib

Running log. Appended as things happen, because a session can be killed at
any moment and a result held only in a chat window is a result that is lost.

Pin: toolchain `leanprover/lean4:v4.33.0-rc2`, mathlib rev `51e6992e`
(from `lean/lake-manifest.json`). Compiles are run as
`cd /home/user/zeta-lab/lean && lake env lean <abs path>`.

## 2026-08-18, entry 1: the oracle, run first

`hunts/rogue_frontier/matchings/oracle.py` already existed in the tree. Run
before writing any Lean, so that the target numbers are fixed before the
formal statement is:

```
 n   brute force   recursion    (n/2-1)!!
 0            1           1            1   OK
 1            0           0            0   OK
 2            1           1            1   OK
 3            0           0            0   OK
 4            3           3            3   OK
 5            0           0            0   OK
 6           15          15           15   OK
 7            0           0            0   OK
 8          105         105          105   OK
 9            0           0            0   OK
10          945         945          945   OK

all three routes agree: True
```

So the target row is `1, 0, 1, 0, 3, 0, 15, 0, 105, 0, 945`, matching the
brief. Any Lean statement disagreeing with this table on a small case is
wrong; the oracle is not.

## 2026-08-18, entry 2: gap evidence probe written

`Probe.lean` written. It does three things rather than the one asked for,
because a `#check` that succeeds is evidence of presence and there is no
`#check` that succeeds for an absent name. So absence is probed with
`run_cmd` over `getEnv`, which asks the environment directly, and then the
whole environment is swept for any declaration mentioning `PerfectMatching`,
`Isserlis`/`Wick`, or `doubleFactorial`. That converts "I grepped and found
nothing" into "the elaborated environment contains exactly these".

Compile launched (first Mathlib import, expected slow).
