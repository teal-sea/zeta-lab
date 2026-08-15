# MISSION

Test AGY conversation context and handback 8.

```huntspec
question: Does the AGY context test framework correctly process a basic script and JSON handback?
frontier: process validation phase 8
dead_routes:
  - process iterations lacking proper HANDBACK validation
required_oracles:
  - framework script reading HANDBACK.json for structural correctness
kill_conditions:
  - missing or malformed HANDBACK.json
  - the package will not import after a genuine install attempt
  - budget exceeded
agents_may:
  - run scripts
  - write to internal hunt directory
agents_may_not:
  - assert theorem status
  - promote their own claim
```
