import re

with open('scripts/pub1_certify_display.py', 'r') as f:
    content = f.read()

# Replace _f definition
old_f_def = """def _f(x: Fraction, p: int = 18) -> str:
    with localcontext() as ctx:
        ctx.prec = _PREC
        return f"{Decimal(x.numerator) / Decimal(x.denominator):.{p}f}"
"""

new_f_def = """def _f(x: Fraction, p: int = 18, direction: int = 0) -> str:
    from decimal import ROUND_CEILING, ROUND_FLOOR
    with localcontext() as ctx:
        ctx.prec = _PREC
        if direction > 0:
            ctx.rounding = ROUND_CEILING
        elif direction < 0:
            ctx.rounding = ROUND_FLOOR
        return f"{Decimal(x.numerator) / Decimal(x.denominator):.{p}f}"
"""

content = content.replace(old_f_def, new_f_def)

# Replace usage of _f where it's a bound
content = content.replace("_f(z['bound'], p)", "_f(z['bound'], p, 1)")
content = content.replace("_f(z['uSecondDerivBound'], 18)", "_f(z['uSecondDerivBound'], 18, 1)")
content = content.replace("_f(z['concavity_lhs'], 18)", "_f(z['concavity_lhs'], 18, 1)")
content = content.replace("_f(z['concavity_bound'], 18)", "_f(z['concavity_bound'], 18, 1)")

content = content.replace("_f(e['c_lower'], 20)", "_f(e['c_lower'], 20, -1)")
content = content.replace("_f(e['c_upper'], 20)", "_f(e['c_upper'], 20, 1)")
content = content.replace("_f(e['H_lower'], 20)", "_f(e['H_lower'], 20, -1)")
content = content.replace("_f(e['H_upper'], 20)", "_f(e['H_upper'], 20, 1)")
content = content.replace("_f(e['D_lower'], 20)", "_f(e['D_lower'], 20, -1)")
content = content.replace("_f(e['D_upper'], 20)", "_f(e['D_upper'], 20, 1)")

with open('scripts/pub1_certify_display.py', 'w') as f:
    f.write(content)

print("Patched display script.")
