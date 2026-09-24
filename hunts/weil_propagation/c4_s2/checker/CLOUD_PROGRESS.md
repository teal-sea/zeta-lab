started 2026-09-24T13:25:33Z
2026-09-24T13:29:21Z venv ready; rigor.BACKEND = python-flint, available ['mpmath.iv', 'python-flint']
2026-09-24T13:30:48Z units 0-6 already built by session_018f8 at key 323b8a07 (merged). Launching unit 7 (240, 2400, 32, Kmax 14), the RESULTS s7.6 door. Estimate: cloud (200,2400,32) took 427 s; x(240/200)^2 x2 for Kmax 13->14 gives ~20 min, rough (laptop scaling model failed here).
2026-09-24T13:32:04Z prolate sweep config 0 (40,800,N8) done in 17 s; ta_ts_prolate.json updated (write outside checker/ authorized by operator)
2026-09-24T13:32:22Z analyse(): adds door_N32_200_vs_240 (200 vs 240 modes at N = 32, counts at the s7.3 band and at the real-refinement band); s7.3 keys unchanged
2026-09-24T13:32:52Z prolate sweep config 1 (80,1200,N8+16) done in 37 s; ta_ts_prolate.json updated (write outside checker/ authorized by operator)
2026-09-24T13:35:32Z prolate sweep config 2 (120,1600,N16) done in 147 s; ta_ts_prolate.json updated (write outside checker/ authorized by operator)
2026-09-24T13:38:52Z prolate sweep config 3 (130,1800,N32) done in 177 s; ta_ts_prolate.json updated (write outside checker/ authorized by operator)
2026-09-24T13:46:08Z heartbeat: unit 7 (240, 2400, 32) still running, 15 min in; load 5.41 4.83 2.98
2026-09-24T13:46:39Z prolate sweep config 4 (200,2400,N32) done in 463 s; ta_ts_prolate.json updated (write outside checker/ authorized by operator)
2026-09-24T13:46:46Z prolate tate_check (old, new) = 8.753880183100264e-14 8.76303084312083e-14 in 2 s
2026-09-24T13:47:14Z prolate sweep vs prior committed ta_ts_prolate.json: 18 rows, max change 1.4e-7 (T_S low3), gram_sensitivity 7.4e-8, no count moved; rows now carry Kmax. Unit 7 still running.
2026-09-24T13:53:37Z unit 7 (240, 2400, 32, Kmax 14) done in 1339.2 s (22.3 min, against the ~20 min estimate); snapshot committed. Running --analyse 015895f.
2026-09-24T13:54:48Z analyse done (42 s). Door: ||T_S(240)-T_S(200)||_2 at N=32 = 3.9e-2 / 2.4e-2 / 3.2e-2 (c = 2.2/2.5/2.9), 2.5-8.5x the N=16 proxy; central |n|<=16 block moves 1.8e-2/2.3e-2/2.7e-2. n_- at s7.3 band: 3->9, 20->19, 20->23; at the real band: 0->0, 2->5, 2->4. Confound: 200 used Kmax 13, 240 Kmax 14.
2026-09-24T13:55:12Z launching run_checker_kmax.py: (200, 2400, 32) at Kmax 14 to split the 200->240 step into Kmax and mode responses. Estimate 15-20 min.
