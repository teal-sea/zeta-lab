"""Where the 17th digit went: abs() evaluated at the ambient precision.

``epstein_completed`` returns an ``mpc`` carrying ``dps`` digits, but ``abs``
of it is evaluated at whatever ``mp.dps`` happens to be.  Outside a
``workdps`` block that is mpmath's default 15, so the magnitude is rounded to
~16 digits and every digit printed after that is the binary tail rather than
the number.  This is ordinary mpmath semantics, not a defect in
``zeta/epstein.py`` — it is recorded because it is the same shape as the cap
under measurement, precision discarded silently at an interface, and because
it is what made two earlier control runs disagree at digit 17.
"""

from mpmath import mp, mpc

from zeta.epstein import epstein_completed

with mp.workdps(90):
    s = mpc("0.8", "85.7")
value = epstein_completed(s, (2, 1, 3), dps=80)

outside = abs(value)                      # evaluated at mp.dps = 15
with mp.workdps(90):
    inside = abs(value)                   # evaluated at 90 digits
    print("abs() at ambient dps=15 :", mp.nstr(outside, 25))
    print("abs() at dps=90         :", mp.nstr(inside, 25))
    agree = 0
    a, b = mp.nstr(outside, 25), mp.nstr(inside, 25)
    for x, y in zip(a, b):
        if x != y:
            break
        agree += x.isdigit()
    print("leading digits in common:", agree)
