# Bounded run record

Before launch: complete odd fundamental discriminants to 20,000, brute-force
forms with a<=sqrt(|D|/3); roughly 4,000 small inputs, hard 20-second CPU cap.
No heavy enumeration, external service, network or numerical-library threads.

Completed first probe in 1.20 seconds; added the pinned PR279 reference counter
as an orthogonal loop-boundary check, then reproduced in about 2 seconds.
One final repeat records UTC start, wall time, output hashes in manifest.json.
All finite assertions passed. Repetitions were justified by added checking
and provenance recording, not increased search scope. No jobs remain live.

Outputs: probe.json, manifest.json, RESULTS.md. Script probe.py; unmodified
upstream comparison implementation reference_pinned.py. No full class-number
dataset was available or regenerated. No master records were changed.
