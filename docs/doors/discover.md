# Guide: the conjecture funnel, and its hit rate

**For you if** you want to generate leads automatically, and, more usefully,
to see what fraction of them survive.

**First command:**

```bash
.venv/bin/python scripts/13_discovery_run.py --dry-run
.venv/bin/python scripts/13_discovery_run.py --report
```

## The premise

Most numerical "discoveries" are already known or trivial, **and a system that
does not measure its own hit rate is measuring its operator's enthusiasm.**

So the funnel is built to make the unflattering outcomes cheap to record and
impossible to skip:

- `already-known` is a first-class terminal state with its own detector, run
  *before* any screen, because "this is in the literature" is the most likely
  true answer and the cheapest to obtain;
- `survives` cannot be claimed without naming the three checks that ran;
- a refutation is not accepted unless it survived a precision increase.

## The seam, and why it is strict

`ontology/schema.py`, `funnel.py`, `metrics.py` and `registry.py` contain **no
subject-matter knowledge whatsoever**. They would work unchanged for a
chemistry lab or a compiler-optimisation search. Everything that knows the
subject lives in `ontology/domains/`.

Four tests enforce it: an AST import scan, a clean-interpreter `sys.modules`
check, a lexical scan for subject vocabulary, and a subprocess that runs the
whole pipeline with the laboratory made *unimportable* and still requires it to
generate, screen and report.

If the seam leaks the design is worthless, a bookkeeping layer entangled with
its subject cannot be trusted to report a number its operator does not want.

Read `ontology/README.md` before touching any of it.

## The ledger is private, on purpose

The funnel writes to `conjectures/`, which is **gitignored**. It is a notebook
of unreviewed leads, and by the package's own premise most of them are known,
trivial or wrong. A list nobody has checked, published in a repository that is
otherwise checked, would be read as a set of claims.

Publish `ontology.metrics.render_text`. Never the log. An empty
`conjectures/` in a fresh clone is the rule working, not a bug.

Related: [refute.md](refute.md), the funnel generates leads, the battery refutes
them.
