import sympy as sp
sigma, c, b, c0 = sp.symbols('sigma c b c0', positive=True)
terms = {
 'e^{-2c0 sqrt l}': 2*c0,
 'R^-1': sigma,
 'R^2 e^{-(2c/sigma) sqrt l}': 2*c/sigma - 2*sigma,
 'R e^{-(c/(2sigma)) sqrt l}': c/(2*sigma) - sigma,
 'R e^{-(b/(2sigma)) sqrt l}': b/(2*sigma) - sigma,
 'R^-3': 3*sigma,
 'R^3 e^{-2 sqrt l /3}': sp.Rational(2,3) - 3*sigma,
 'R^4 e^{-(2/3+2c0) sqrt l}': 4*sigma - (sp.Rational(2,3)+2*c0),
}
for name, expr in terms.items():
    val = expr.subs(sigma, 2*c0)
    print(name, '->', sp.simplify(val))

print()
print("Corrected (if R^2 term were actually R^1, i.e. R e^{-(2c/sigma) sqrt l}):")
corrected = sigma_expr = (2*c/sigma - sigma).subs(sigma, 2*c0)
print('R e^{-(2c/sigma) sqrt l} ->', sp.simplify(corrected))
print("condition for >= 2c0:", sp.solve(sp.Eq(corrected, 2*c0), c0))
print("condition for old (R^2) term >= 2c0:", sp.solve(sp.Eq((2*c/sigma-2*sigma).subs(sigma,2*c0), 2*c0), c0))
