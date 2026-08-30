# Vendored: formal-conjectures (Util + ForMathlib)

`FormalConjecturesUtil.lean`, `FormalConjecturesUtil/`, `FormalConjecturesForMathlib.lean`
and `FormalConjecturesForMathlib/` are verbatim copies from

- repo: https://github.com/google-deepmind/formal-conjectures
- commit: `7e662f771cec2c6d893ee048d163c3cb3aa2a377`
- license: Apache-2.0 (Copyright The Formal Conjectures Authors); every file keeps
  its original header. The rest of this repository is MIT; these directories are not.

What is vendored and why:

- `FormalConjecturesUtil` (22 files): the `Answer`/`category`/AMS attributes and
  linters that every upstream problem file imports via `import FormalConjecturesUtil`.
- `FormalConjecturesForMathlib` (166 files): `FormalConjecturesUtil.lean` does
  `public import FormalConjecturesForMathlib`, whose root imports every module in
  the directory, so the closure of `import FormalConjecturesUtil` is the whole library.

Every copied file was checked against the git blob SHA in the upstream tree at that
commit before being written (`hashlib.sha1(b"blob %d\0" % len + bytes)`).

Upstream pins Mathlib `v4.33.1` (`0df444a`); this project pins `v4.33.0-rc2`
(`51e6992`). Any local edits needed to compile against the older Mathlib are listed
below; if the list is empty, the copies are byte-identical to upstream.

Local edits: none.

Consumers: the `Erdos` library (`Erdos.lean`, `Erdos/*.lean`) imports
`FormalConjecturesUtil` the way upstream `FormalConjectures/ErdosProblems/*.lean` do.
Build with `cd lean && lake build Erdos`.
