#!/usr/bin/env python3
"""Require exactly the advertised axiom reports of hunt #137's package, standard axioms only.

The fail-closed log audit of hunts #132 and #133 (`hunts/hardy_*/lean/check_axioms.py`), with
this package's names. Run it on the log of `build.sh` after the build succeeds; it does not
itself run a proof kernel. Usage:

    bash hunts/rh_height_lean/lean/build.sh OUT 2>&1 | tee build.log
    .venv/bin/python hunts/rh_height_lean/lean/check_axioms.py build.log
    bash hunts/rh_height_lean/lean/build.sh --assembly OUT 2>&1 | tee build.log
    .venv/bin/python hunts/rh_height_lean/lean/check_axioms.py build.log --assembly
    bash hunts/rh_height_lean/lean/build.sh --full OUT 2>&1 | tee build.log
    .venv/bin/python hunts/rh_height_lean/lean/check_axioms.py build.log --full

The skeleton and assembly theorems are conditional on the four pieces of
`RHHeight/Skeleton.lean`. Under `--full` the log also carries the four pieces' reports and
those of `RHHeight/Main.lean`, whose `RHHeight.rh_height_fifty` is the target `RHHeight50`
itself. The audit checks only that every advertised report is present exactly once and is
`propext`, `Classical.choice` and `Quot.sound`, that the build reached its last line, and that
Lean reported no error and no `sorry`.
"""
import re
import sys
from pathlib import Path

expected = {
    "RHHeight.toNat_analyticOrderAt_eq_one_iff",
    "RHHeight.mem_stripZerosUpTo",
    "RHHeight.rhUpToHeight_iff",
    "RHHeight.RHUpToHeight.mono",
    "RHHeight.RHHeight100.toRHHeight50",
    "RHHeight.count_eq_ten_of",
    "RHHeight.mem_and_simple_of_Ncount_le",
    "RHHeight.on_line_and_simple_of_count",
    "RHHeight.rhUpToHeight52_of_pieces",
    "RHHeight.rhHeight50_of_pieces",
    "RHHeight.zeroCount50_of_pieces",
}
assembly = {
    "RHHeight.tenZerosOnLine",
    "RHHeight.rhHeight50_of_four",
    "RHHeight.zeroCount50_of_four",
}
# RHHeight/CheckGammaIncrement.lean
gamma_increment = {
    "RHHeight.GammaSide.abs_mu_sub_muMain_le",
    "RHHeight.GammaSide.hasDerivAt_muPrim",
    "RHHeight.GammaSide.continuous_muMain",
    "RHHeight.GammaSide.hasDerivAt_six_div",
    "RHHeight.GammaSide.abs_integral_mu_sub_le",
    "RHHeight.GammaSide.log_one_sub_bounds",
    "RHHeight.GammaSide.log_10817_div_16_mem",
    "RHHeight.GammaSide.log_37_div_16_mem",
    "RHHeight.GammaSide.pi_gt_6283_div_2000",
    "RHHeight.GammaSide.pi_lt_3927_div_1250",
    "RHHeight.GammaSide.log_pi_mem",
    "RHHeight.GammaSide.two_pi_mul_muPrim_sub",
    "RHHeight.gamma_increment",
    "RHHeight.gamma_increment_holds",
}
# RHHeight/CheckHorizontalLegs.lean
horizontal_legs = {
    "RHHeight.horizontal_legs",
    "RHHeight.horizontalLegs",
    "RHHeight.re_zeta_pos_bottom",
    "RHHeight.re_zeta_pos_top",
    "RHHeight.arg_zeta_bottom",
    "RHHeight.arg_zeta_top",
    "RHHeight.Legs.cBoxG_contains",
    "RHHeight.Legs.mainBoxG_contains",
    "RHHeight.Legs.norm_le_normUp",
    "RHHeight.Legs.log_le_logTab",
    "RHHeight.Legs.norm_cpow_sub_le",
    "RHHeight.Legs.norm_cN_le",
    "RHHeight.Legs.norm_cN_sub_le",
    "RHHeight.Legs.norm_mainTerm_sub_le",
    "RHHeight.Legs.norm_zeta_sub_mainTerm_le",
    "RHHeight.Legs.re_pos_of_segment",
    "RHHeight.Legs.zeta_mem_pointBox",
    "RHHeight.Legs.arg_mem_of_box",
    "RHHeight.Legs.H3S1.seg",
    "RHHeight.Legs.H3S2.seg",
    "RHHeight.Legs.H3S3.seg",
    "RHHeight.Legs.H52S1.seg",
    "RHHeight.Legs.H52S2.seg",
    "RHHeight.Legs.H52S3.seg",
    "RHHeight.Legs.H52S4.seg",
    "RHHeight.Legs.H52S5.seg",
    "RHHeight.Legs.H52S6.seg",
    "RHHeight.Legs.Arg3.arg_bounds",
    "RHHeight.Legs.Arg52.arg_bounds",
}
# RHHeight/CheckExactArgument.lean
exact_argument = {
    "RHHeight.goodHeight_of_re_pos",
    "RHHeight.integral_logDeriv_horizontal",
    "RHHeight.integral_logDeriv_vertical",
    "RHHeight.halfContour_logDeriv_riemannZeta",
    "RHHeight.im_halfContour_logDeriv_riemannZeta",
    "RHHeight.exact_argument",
    "RHHeight.exact_argument_holds",
}
# RHHeight/CheckLowHeight.lean
low_height = {
    "RHHeight.norm_tail_one_le",
    "RHHeight.norm_zeta_sub_main_one_le",
    "RHHeight.riemannZeta_ne_zero_of_im_le_three",
    "RHHeight.low_height",
}
# CheckMain.lean: the theorem
main = {
    "RHHeight.ncount_three_fiftytwo",
    "RHHeight.rh_up_to_height_fiftytwo",
    "RHHeight.rh_height_fifty",
    "RHHeight.zero_count_fifty",
}
flags = sys.argv[2:]
if "--assembly" in flags or "--full" in flags:
    expected |= assembly
if "--full" in flags:
    expected |= gamma_increment | horizontal_legs | exact_argument | low_height | main
allowed = {"propext", "Classical.choice", "Quot.sound"}
text = Path(sys.argv[1]).read_text()
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
names = [name for name, _ in reports]
if set(names) != expected or len(names) != len(expected):
    raise SystemExit(f"Expected exactly {sorted(expected)}, received {names}")
for name, axioms in reports:
    actual = [a.strip() for a in axioms.split(",")]
    if set(actual) != allowed or len(actual) != len(allowed):
        raise SystemExit(f"{name}: expected the three standard axioms, received {actual}")
# Lean v4.35 writes "declaration uses `sorry`"; older releases used straight quotes.
if re.search(r"\bsorryAx\b|\berror:|declaration uses [`']sorry[`']", text):
    raise SystemExit("Lean reported a placeholder or an error")
if not re.search(r"^== done ", text, re.MULTILINE):
    raise SystemExit("the build log does not reach build.sh's last line")
print(f"Accepted all {len(expected)} reports: propext, Classical.choice, Quot.sound only.")
