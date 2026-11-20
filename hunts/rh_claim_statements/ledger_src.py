"""Curated half of the claim ledger: where each statement is, how it is read,
how it is tested and which mutants the test must reject. Pure data.

`build_ledger.py` joins this with the read-only archive (verbatim statement,
hash, namespace context) and with the Mathlib checkout (definition sites) and
writes `claims.json`. Nothing here is copied from the archive except the short
local definitions quoted with path:line under `local_definitions`.
"""

ARCHIVE = dict(
    author="Levent Alpoge",
    posted="2026-11-20",
    tarball_sha256="9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc",
    files=175187,
    root="x/lean/src",
    toolchain="leanprover/lean4:v4.33.1",
    mathlib_rev="0df444a360eaa60ab8c11dca51a86af692955474",
    status="no kernel has checked the archive; every entry below is 'the archive states'",
)

# ---------------------------------------------------------------------------
# conventions a tester must reproduce
# ---------------------------------------------------------------------------

CONV = {
    "natsub": "subtraction on the naturals truncates at 0",
    "natdiv": "division on the naturals is floor division, and n / 0 = 0",
    "rdiv0": "division by 0 in a field is 0",
    "log": "Real.log x = log|x| for x != 0 and Real.log 0 = 0 (Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:44)",
    "sqrt": "Real.sqrt x = 0 for x < 0 (Mathlib/Analysis/Real/Sqrt.lean:112)",
    "rpow": "x ^ (y : R) is Real.rpow: exp(y log x) for x > 0, and 0 ^ y = 0 for y != 0",
    "cpow": "(n : C) ^ s is Complex.cpow: exp(s log n) for n != 0",
    "npow": "x ^ (n : N) is the monoid power, with x ^ 0 = 1 (so 0 ^ 0 = 1)",
    "app": "function application binds tighter than ^ and than /: Real.log x ^ 2 is (log x)^2",
    "zeta1": "riemannZeta 1 is a junk value; the hypotheses keep s away from 1",
    "deriv": "deriv is the complex derivative (0 where the function is not differentiable)",
    "norm": "the double bars are the complex modulus (the real absolute value on R)",
    "abs": "the single bars are the absolute value of a real number",
    "icc": "Finset.Icc 1 M = {1, ..., M}, empty for M = 0; Finset.Ioc 0 N = {1, ..., N}; Finset.range n = {0, ..., n - 1}",
    "vM": "vonMangoldt n = log p if n = p^k with k >= 1 and 0 otherwise, so it is 0 at n = 0 and n = 1",
    "pi": "Nat.primeCounting n and Nat.count Nat.Prime (n + 1) both count the primes <= n",
    "padic": "padicValNat p 0 = 0 and padicValNat 1 n = 0",
    "natlog": "Nat.log b n = floor(log_b n) for b >= 2 and n >= 1, and 0 otherwise",
    "totient0": "Nat.totient 0 = 0 and Nat.divisors 0 is empty",
    "floor": "the floor and ceiling with a plus subscript are Nat.floor and Nat.ceil (0 for negative arguments)",
    "L": "DirichletCharacter.LFunction chi s continues sum chi(n) n^-s for chi as a character mod N, not for its "
         "primitive inducing character; it is entire for chi != 1, and (1 : DirichletCharacter C N) is the "
         "principal character mod N",
    "card": "Nat.card of a finite type is its number of elements (0 for an infinite type); Fintype.card likewise",
    "cast": "numerals and casts are exact: 1.26 is 126/100, and 3 / 5 in R is the rational 3/5",
    "gamma": "Complex.Gamma has junk value 0 at its poles, which the stated domain does not reach",
}

# ---------------------------------------------------------------------------
# identifier resolution: token as written -> (qualified name, origin, file, regex for the defining line)
# origin 'core' means Lean core or Batteries: outside the Mathlib checkout, and not defined in the archive
# ---------------------------------------------------------------------------

M = "Mathlib"
RESOLVE = {
    "riemannZeta": ("riemannZeta", M, "Mathlib/NumberTheory/LSeries/RiemannZeta.lean", r"^def riemannZeta\b"),
    "riemannZeta₁": ("riemannZeta₁", M, "Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean", r"def riemannZeta₁ "),
    "DirichletCharacter": ("DirichletCharacter", M, "Mathlib/NumberTheory/DirichletCharacter/Basic.lean", r"^abbrev DirichletCharacter\b"),
    "DirichletCharacter.LFunction": ("DirichletCharacter.LFunction", M, "Mathlib/NumberTheory/LSeries/DirichletContinuation.lean", r"def LFunction \(χ : DirichletCharacter"),
    "LFunction": ("DirichletCharacter.LFunction (through `open DirichletCharacter`)", M, "Mathlib/NumberTheory/LSeries/DirichletContinuation.lean", r"def LFunction \(χ : DirichletCharacter"),
    ".IsPrimitive": ("DirichletCharacter.IsPrimitive", M, "Mathlib/NumberTheory/DirichletCharacter/Basic.lean", r"^def IsPrimitive : Prop"),
    ".Even": ("DirichletCharacter.Even", M, "Mathlib/NumberTheory/DirichletCharacter/Basic.lean", r"^def Even : Prop"),
    "ZMod": ("ZMod", M, "Mathlib/Data/ZMod/Defs.lean", r"^def ZMod : ℕ → Type"),
    "ZMod.χ₈": ("ZMod.χ₈", M, "Mathlib/NumberTheory/LegendreSymbol/ZModChar.lean", r"^def χ₈ : MulChar \(ZMod 8\) ℤ"),
    "quadraticChar": ("quadraticChar", M, "Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean", r"^def quadraticChar : MulChar F ℤ"),
    "deriv": ("deriv", M, "Mathlib/Analysis/Calculus/Deriv/Basic.lean", r"^def deriv \("),
    "Complex.Gamma": ("Complex.Gamma", M, "Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean", r"def Gamma \(s : ℂ\) : ℂ"),
    "I": ("Complex.I (through `open Complex`)", M, "Mathlib/Data/Complex/Basic.lean", r"^def I : ℂ"),
    ".re": ("Complex.re", M, "Mathlib/Data/Complex/Basic.lean", r"^structure Complex : Type"),
    ".im": ("Complex.im", M, "Mathlib/Data/Complex/Basic.lean", r"^structure Complex : Type"),
    "Real.log": ("Real.log", M, "Mathlib/Analysis/SpecialFunctions/Log/Basic.lean", r"^noncomputable def log \(x : ℝ\) : ℝ"),
    "log": ("Real.log (through `open Real`)", M, "Mathlib/Analysis/SpecialFunctions/Log/Basic.lean", r"^noncomputable def log \(x : ℝ\) : ℝ"),
    "Real.exp": ("Real.exp", M, "Mathlib/Analysis/Complex/Exponential.lean", r"^nonrec def exp \(x : ℝ\) : ℝ"),
    "Real.sqrt": ("Real.sqrt", M, "Mathlib/Analysis/Real/Sqrt.lean", r"noncomputable def sqrt \(x : ℝ\) : ℝ"),
    "Real.pi": ("Real.pi", M, "Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean", r"^protected noncomputable def pi : ℝ"),
    "π": ("Real.pi (notation, through `open scoped Real`)", M, "Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean", r"^protected noncomputable def pi : ℝ"),
    "Real.cosh": ("Real.cosh", M, "Mathlib/Analysis/Complex/Trigonometric.lean", r"^nonrec def cosh \(x : ℝ\) : ℝ"),
    "Real.eulerMascheroniConstant": ("Real.eulerMascheroniConstant", M, "Mathlib/NumberTheory/Harmonic/EulerMascheroni.lean", r"^noncomputable def eulerMascheroniConstant : ℝ"),
    "Nat.Prime": ("Nat.Prime", M, "Mathlib/Data/Nat/Prime/Defs.lean", r"^def Prime \(p : ℕ\)"),
    ".Prime": ("Nat.Prime", M, "Mathlib/Data/Nat/Prime/Defs.lean", r"^def Prime \(p : ℕ\)"),
    "Nat.primeCounting": ("Nat.primeCounting", M, "Mathlib/NumberTheory/PrimeCounting.lean", r"^def primeCounting \(n : ℕ\) : ℕ"),
    "primeCounting": ("Nat.primeCounting (through `open Nat`)", M, "Mathlib/NumberTheory/PrimeCounting.lean", r"^def primeCounting \(n : ℕ\) : ℕ"),
    "Nat.primesLE": ("Nat.primesLE", M, "Mathlib/NumberTheory/PrimeCounting.lean", r"^def primesLE \(n : ℕ\) : Finset ℕ"),
    "Nat.count": ("Nat.count", M, "Mathlib/Data/Nat/Count.lean", r"^def count \(n : ℕ\) : ℕ"),
    "Nat.sqrt": ("Nat.sqrt", "core", None, None),
    "Nat.log": ("Nat.log", M, "Mathlib/Data/Nat/Log.lean", r"^def log \(b n : ℕ\) : ℕ"),
    "Nat.card": ("Nat.card", M, "Mathlib/SetTheory/Cardinal/Finite.lean", r"^protected def card \(α : Type\*\) : ℕ :="),
    "Nat.Coprime": ("Nat.Coprime", "core", None, None),
    ".factorial": ("Nat.factorial", M, "Mathlib/Data/Nat/Factorial/Basic.lean", r"^def factorial : ℕ → ℕ"),
    ".choose": ("Nat.choose", M, "Mathlib/Data/Nat/Choose/Basic.lean", r"^def choose : ℕ → ℕ → ℕ"),
    ".centralBinom": ("Nat.centralBinom", M, "Mathlib/Data/Nat/Choose/Central.lean", r"^def centralBinom \(n : ℕ\)"),
    ".descFactorial": ("Nat.descFactorial", M, "Mathlib/Data/Nat/Factorial/Basic.lean", r"^def descFactorial \(n : ℕ\) : ℕ → ℕ"),
    ".totient": ("Nat.totient", M, "Mathlib/Data/Nat/Totient.lean", r"^def totient \(n : ℕ\) : ℕ"),
    ".primeFactors": ("Nat.primeFactors", M, "Mathlib/Data/Nat/PrimeFin.lean", r"^def primeFactors \(n : ℕ\) : Finset ℕ"),
    ".divisors": ("Nat.divisors", M, "Mathlib/NumberTheory/Divisors.lean", r"^def divisors : Finset ℕ"),
    "padicValNat": ("padicValNat", M, "Mathlib/Data/Nat/MaxPowDiv.lean", r"def _root_\.padicValNat \(p n : ℕ\) : ℕ"),
    "ArithmeticFunction.vonMangoldt": ("ArithmeticFunction.vonMangoldt", M, "Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean", r"^noncomputable def vonMangoldt : ArithmeticFunction ℝ"),
    "vonMangoldt": ("ArithmeticFunction.vonMangoldt (through `open ArithmeticFunction`)", M, "Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean", r"^noncomputable def vonMangoldt : ArithmeticFunction ℝ"),
    "ArithmeticFunction.sigma": ("ArithmeticFunction.sigma", M, "Mathlib/NumberTheory/ArithmeticFunction/Misc.lean", r"^def sigma \(k : ℕ\) : ArithmeticFunction ℕ"),
    "Squarefree": ("Squarefree", M, "Mathlib/Algebra/Squarefree/Basic.lean", r"^def Squarefree \["),
    "Odd": ("Odd", M, "Mathlib/Algebra/Ring/Parity.lean", r"^def Odd \(a : α\) : Prop"),
    "Finset": ("Finset", M, "Mathlib/Data/Finset/Defs.lean", r"^structure Finset \("),
    "Finset.range": ("Finset.range", M, "Mathlib/Data/Finset/Range.lean", r"^def range \(n : ℕ\) : Finset ℕ"),
    "range": ("Finset.range (through `open Finset`)", M, "Mathlib/Data/Finset/Range.lean", r"^def range \(n : ℕ\) : Finset ℕ"),
    "Finset.Icc": ("Finset.Icc", M, "Mathlib/Order/Interval/Finset/Defs.lean", r"^def Icc \(a b : α\) : Finset α"),
    "Icc": ("Finset.Icc (through `open Finset`)", M, "Mathlib/Order/Interval/Finset/Defs.lean", r"^def Icc \(a b : α\) : Finset α"),
    "Finset.Ioc": ("Finset.Ioc", M, "Mathlib/Order/Interval/Finset/Defs.lean", r"^def Ioc \(a b : α\) : Finset α"),
    "Finset.Iic": ("Finset.Iic (generated from Finset.Ici by the to_dual attribute)", M, "Mathlib/Order/Interval/Finset/Defs.lean", r"def Ici \(a : α\) : Finset α"),
    "Finset.univ": ("Finset.univ", M, "Mathlib/Data/Fintype/Defs.lean", r"^def univ : Finset α"),
    "univ": ("Finset.univ (through `open Finset`)", M, "Mathlib/Data/Fintype/Defs.lean", r"^def univ : Finset α"),
    ".filter": ("Finset.filter", M, "Mathlib/Data/Finset/Filter.lean", r"^def filter \(s : Finset α\) : Finset α"),
    ".card": ("Finset.card", M, "Mathlib/Data/Finset/Card.lean", r"^def card \(s : Finset α\) : ℕ"),
    "Fintype": ("Fintype", M, "Mathlib/Data/Fintype/Defs.lean", r"^class Fintype \("),
    "Fintype.card": ("Fintype.card", M, "Mathlib/Data/Fintype/Card.lean", r"^def card \(α\) \[Fintype α\] : ℕ"),
    "Fintype.piFinset": ("Fintype.piFinset", M, "Mathlib/Data/Fintype/Pi.lean", r"^def piFinset \("),
    "Matrix": ("Matrix", M, "Mathlib/LinearAlgebra/Matrix/Defs.lean", r"^def Matrix \("),
    ".IsSymm": ("Matrix.IsSymm", M, "Mathlib/LinearAlgebra/Matrix/Symmetric.lean", r"^def IsSymm \(A : Matrix n n α\) : Prop"),
    ".det": ("Matrix.det", M, "Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean", r"^def det \(M : Matrix n n R\) : R"),
    ".mulVec": ("Matrix.mulVec", M, "Mathlib/Data/Matrix/Mul.lean", r"^def mulVec \["),
    ".map": ("Matrix.map", M, "Mathlib/LinearAlgebra/Matrix/Defs.lean", r"^def map \(M : Matrix m n α\)"),
    ".transpose": ("Matrix.transpose", M, "Mathlib/LinearAlgebra/Matrix/Defs.lean", r"^def transpose \(M : Matrix m n α\)"),
    "GL": ("Matrix.GeneralLinearGroup (notation GL)", M, "Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean", r'notation "GL" => GeneralLinearGroup'),
    "ringChar": ("ringChar", M, "Mathlib/Algebra/CharP/Defs.lean", r"^noncomputable def ringChar \["),
    "Field": ("Field", M, "Mathlib/Algebra/Field/Defs.lean", r"^class Field \("),
    "IsCyclic": ("IsCyclic", M, "Mathlib/Algebra/Group/Defs.lean", r"^class IsCyclic \("),
    "minpoly": ("minpoly", M, "Mathlib/FieldTheory/Minpoly/Basic.lean", r"^noncomputable def minpoly \("),
    ".natDegree": ("Polynomial.natDegree", M, "Mathlib/Algebra/Polynomial/Degree/Defs.lean", r"^def natDegree \(p : R\[X\]\) : ℕ"),
    "eval": ("Polynomial.eval (through `open Polynomial`)", M, "Mathlib/Algebra/Polynomial/Eval/Defs.lean", r"^def eval \(x : R\) \(p : R\[X\]\) : R"),
    "cyclotomic": ("Polynomial.cyclotomic (through `open Polynomial`)", M, "Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.lean", r"^def cyclotomic \(n : ℕ\)"),
    "HasSum": ("HasSum (generated from HasProd by to_additive)", M, "Mathlib/Topology/Algebra/InfiniteSum/Defs.lean", r"^def HasProd \("),
    "Tendsto": ("Filter.Tendsto (through `open Filter`)", M, "Mathlib/Order/Filter/Defs.lean", r"^def Tendsto \("),
    "analyticOrderNatAt": ("analyticOrderNatAt", M, "Mathlib/Analysis/Analytic/Order.lean", r"^noncomputable def analyticOrderNatAt"),
    "Fact": ("Fact", M, "Mathlib/Logic/Basic.lean", r"^class Fact \("),
    "NeZero": ("NeZero", "core", None, None),
    "DecidableEq": ("DecidableEq", "core", None, None),
    "Nonempty": ("Nonempty", "core", None, None),
    "Fin": ("Fin", "core", None, None),
    "Type": ("Type", "core", None, None),
    "max": ("Max.max", "core", None, None),
    "min": ("Min.min", "core", None, None),
    # archive-local definitions: quoted and unfolded in the claim that uses them
    "legendreCharacter": ("GroundTheory.Heights₂.Theta.legendreCharacter", "archive", None, None),
    "Formalism.CyclotomicNorms.Fbar": ("Formalism.CyclotomicNorms.Fbar", "archive", None, None),
    "sigNOK": ("Formalism.NOK.sigNOK", "archive", None, None),
    "sigE": ("Formalism.TruncatedSeriesCounting.WachCoordinates.sigE", "archive", None, None),
}

# notation: symbol -> meaning (all Mathlib or core notation; the archive declares no global notation)
SYMBOLS = {
    "‖": "norm (Norm.norm): complex modulus, real absolute value",
    "|": "abs (Mathlib/Algebra/Order/Group/Unbundled/Abs.lean:45 macro)",
    "∑": "Finset.sum (Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean)",
    "∏": "Finset.prod",
    "⌊": "Nat.floor (Mathlib/Algebra/Order/Floor/Defs.lean:135)",
    "#": "Finset.card (Mathlib/Data/Finset/Card.lean:50, scoped in Finset)",
    "⬝ᵥ": "dotProduct (Mathlib/Data/Matrix/Mul.lean:72)",
    "*ᵥ": "Matrix.mulVec",
    "⁻¹": "inverse; 0⁻¹ = 0 in a field",
    "∣": "divisibility",
    "ˣ": "the group of units",
    "≃+*": "RingEquiv",
    "𝓝": "nhds; the bracketed form is nhdsWithin on the complement of the point",
    "ℝ": "Real", "ℂ": "Complex", "ℕ": "Nat", "ℤ": "Int", "ℚ": "Rat",
    "//": "subtype",
}


def T(fn, params, fast="same", route=""):
    return dict(fn=fn, params=params, fast=params if fast == "same" else fast, route=route)


def Mu(tag, replace, params, why, fast=None, kind="constant"):
    return dict(tag=tag, replace=None if replace is None else list(replace), params=params, fast=fast, why_false=why, kind=kind)


CLAIMS = []


def claim(**kw):
    CLAIMS.append(kw)


_Z = "Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/"
_GI = "Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/"
_EF = "Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/"
_JC = "Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/"

# ===========================================================================
# zeta
# ===========================================================================

claim(id="C01", name="zeta_norm_le_on_circle", path=_Z + "BqGrowth.lean", line=29, topic="zeta",
      math="For every complex s with |s - 2| = 3/2: |zeta(s)| <= 14.",
      conv=["norm", "zeta1", "cast"],
      quant="all s on the circle of centre 2 and radius 3/2 (compact; it passes through 1/2 and 7/2 and does not meet s = 1)",
      domain="compact", grade="complete_cover",
      test=T("analytic.zeta_circle", dict(center="2", radius="3/2", K="14"),
             route="Taylor models of zeta on 64 arcs refined by branch and bound; Arb, 64 bits"),
      mutants=[Mu("K", ("≤ 14", "≤ 73 / 50"), dict(K="73/50"), "|zeta(1/2)| = 1.4603545 > 1.46")],
      sharpness="loose: sup |zeta| on the circle is 1.46035 (at s = 1/2), the constant is 9.6 times larger")

claim(id="C02", name="re_ge_and_norm_zeta_le_of_near_eleven_tenths", path=_Z + "ZetaLogDerivLandauBound.lean", line=22, topic="zeta",
      math="For real t with |t| > 2 and complex z with |z - (11/10 + it)| <= 3/5: Re z >= 1/2, z != 1, and |zeta(z)| <= 6(|t| + 2).",
      conv=["norm", "abs", "cast", "zeta1"],
      quant="all real t with |t| > 2 and all z in the closed disc of radius 3/5 about 11/10 + it (unbounded in t)",
      domain="unbounded", grade="measured_range",
      test=T("analytic.zeta_near_abscissa", dict(a="11/10", r="3/5", K="6", half="1/2", t0="2", T=200),
             fast=dict(a="11/10", r="3/5", K="6", half="1/2", t0="2", T=24),
             route="first two conjuncts exact; third by a complete Taylor-model cover of the union of discs for 2 < |t| <= T"),
      mutants=[Mu("radius", ("≤ 3 / 5", "≤ 61 / 100"), dict(r="61/100"), "z = 49/100 + it lies in the disc and has Re z < 1/2", kind="hypothesis"),
               Mu("K", ("≤ 6 * (|t| + 2)", "≤ 23 / 100 * (|t| + 2)"), dict(K="23/100"), "the ratio |zeta z|/(|t|+2) reaches 0.2367 near z = 1.39 + 1.48i")],
      sharpness="first conjunct sharp (Re z = 1/2 is attained); the zeta bound is loose by a factor 25 on the tested range")

claim(id="C03", name="zeta_log_deriv_landau_bound", path=_Z + "ZetaLogDerivLandauBound.lean", line=57, topic="zeta",
      math="For real t, sigma with |t| > 2 and 1 < sigma <= 6/5: Re(-zeta'/zeta(sigma + it)) <= 840 log(|t| + 2).",
      conv=["deriv", "log", "abs", "zeta1", "cast"],
      quant="all real t with |t| > 2, all sigma in (1, 6/5] (unbounded in t)",
      domain="unbounded", grade="measured_range",
      test=T("analytic.zeta_logderiv", dict(sigma_lo="1", sigma_hi="6/5", K="840", t0="2", T=200),
             fast=dict(sigma_lo="1", sigma_hi="6/5", K="840", t0="2", T=32),
             route="complete Taylor-model cover of the closed rectangle [1, 6/5] x [2, T]"),
      mutants=[Mu("sigma", ("(hσ : 1 < σ)", "(hσ : 49 / 100 < σ)"), dict(sigma_lo="49/100"),
                  "left of a zero 1/2 + i gamma the quantity is about (1/2 - sigma)/|s - rho|^2, unbounded", kind="hypothesis"),
               Mu("K", ("840 * Real.log", "3 / 20 * Real.log"), dict(K="3/20"), "the ratio to log(|t|+2) reaches 0.16 on the tested range")],
      sharpness="very loose: on the tested range the constant could be about 0.17 in place of 840")

claim(id="C04", name="zeta_one_sub_le", path=_EF + "LGrowthZeta.lean", line=12, topic="zeta",
      math="For complex w with 1/2 <= Re w <= 5 and w != 1: |zeta(1 - w)| <= 6 |w + 1|^5 |zeta(w)|.",
      conv=["norm", "npow", "zeta1", "cast"],
      quant="all w in the closed strip 1/2 <= Re w <= 5 except w = 1 (unbounded in Im w); 1 - w = 1 would need w = 0, outside the strip",
      domain="unbounded", grade="measured_range",
      test=T("analytic.zeta_one_sub", dict(sigma_lo="1/2", sigma_hi="5", K="6", E=5, T=100),
             fast=dict(sigma_lo="1/2", sigma_hi="5", K="6", E=5, T=64),
             route="cover of |2 (2 pi)^-w cos(pi w/2) Gamma(w)| / (6|w+1|^5) on the rectangle (functional equation), plus the literal inequality at 20 points"),
      mutants=[Mu("strip", ("(h2 : w.re ≤ 5)", "(h2 : w.re ≤ 12)"), dict(sigma_hi="12"),
                  "on Re w = 12 the quotient grows like (|Im w|/2 pi)^11.5, faster than |w+1|^5", kind="hypothesis"),
               Mu("K", ("≤ 6 * ‖w + 1‖ ^ 5", "≤ 13 / 100 * ‖w + 1‖ ^ 5"), dict(K="13/100"), "at w = 1/2 the quotient is 1 and 6 (3/2)^5 times the ratio is 0.1317")],
      sharpness="loose: the largest ratio is 1/(6 (3/2)^5) = 0.02195 at w = 1/2")

claim(id="C05", name="norm_zeta_sub_le", path=_GI + "DifferentiableAtFractInt.lean", line=121, topic="zeta",
      math="For complex s with Re s > 0 and s != 1: |zeta(s) - s/(s - 1)| <= |s| / Re s.",
      conv=["norm", "zeta1", "rdiv0"],
      quant="all s in the open right half-plane except s = 1 (unbounded)",
      domain="unbounded", grade="measured_range",
      test=T("analytic.zeta_partial_sum", dict(M=1, c="1", sigma_hi="16", T=100),
             fast=dict(M=1, c="1", sigma_hi="8", T=16),
             route="complete Taylor-model cover of 0 <= Re s <= 16, |Im s| <= T for the entire function zeta(s) - 1 - 1/(s-1), deflated at s = 1"),
      mutants=[Mu("c", ("≤ ‖s‖ / s.re", "≤ 49 / 100 * (‖s‖ / s.re)"), dict(c="49/100"), "as s -> 0+ the left side tends to 1/2 and the right side to 49/100")],
      sharpness="factor 2: the ratio of the two sides has supremum 1/2, approached as s -> 0+")

claim(id="C06", name="norm_zeta_sub_sum_le", path=_GI + "NormRiemannZetaSubPartialSumLe.lean", line=103, topic="zeta",
      math="For Re s > 0, s != 1 and every integer M >= 1: |zeta(s) - sum_{n=1}^{M} n^-s - M^(1-s)/(s-1)| <= (|s|/Re s) M^(-Re s).",
      conv=["norm", "cpow", "rpow", "icc", "zeta1"],
      quant="all s in the open right half-plane except 1, all natural M >= 1 (unbounded in s and M)",
      domain="unbounded", grade="measured_range",
      test=T("analytic.zeta_partial_sums", dict(Ms=[2, 3, 10, 100], c="1", sigma_hi="6", T=40),
             fast=dict(Ms=[2, 10], c="1", sigma_hi="4", T=8),
             route="as C05, for M in {2, 3, 10, 100}, through the entire function M^s f_M(s)"),
      mutants=[Mu("c", ("≤ ‖s‖ / s.re * (M : ℝ) ^ (-s.re)", "≤ 49 / 100 * (‖s‖ / s.re * (M : ℝ) ^ (-s.re))"), dict(c="49/100"),
                  "for every M the ratio tends to 1/2 as s -> 0+")],
      sharpness="factor 2 for every M tested: supremum 1/2, approached as s -> 0+")

claim(id="C07", name="le_norm_zeta₁", path=_GI + "LogDerivRiemannZetaLocalZeroSum.lean", line=74, topic="zeta",
      math="For every real t: 1/6 <= |zeta_1(3/2 + it)|, where zeta_1(s) = (s - 1) zeta(s) (and zeta_1(1) = 1).",
      conv=["norm", "cast"],
      extra_conv=["riemannZeta₁ is Mathlib's entire function 1 + (s-1) riemannZeta₀ s, with riemannZeta s = (s-1)⁻¹ riemannZeta₁ s for s != 1 (ZetaAsymp.lean:536, :548)"],
      quant="all real t (unbounded)", domain="unbounded", grade="complete_cover",
      test=T("analytic.zeta1_lower", dict(c="1/6", a="3/2", T=200), fast=dict(c="1/6", a="3/2", T=30),
             route="Arb cover of |t| <= T; every t by |zeta(3/2+it)| >= zeta(3)/zeta(3/2) (Euler product) and |s - 1| >= 1/2"),
      mutants=[Mu("c", ("1 / 6 ≤", "131 / 100 ≤"), dict(c="131/100"), "|zeta_1(3/2)| = zeta(3/2)/2 = 1.3062")],
      sharpness="loose: the infimum is 1.3062 at t = 0, 7.8 times the stated 1/6")

claim(id="C08", name="riemannZeta_ne_zero_of_mem_Ioo", path="Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean", line=150, topic="zeta",
      math="For real sigma with 0 < sigma < 1: zeta(sigma) != 0.",
      conv=["zeta1"], quant="all real sigma in the open interval (0, 1)", domain="compact", grade="complete_cover",
      test=T("analytic.real_nonvanishing", dict(a="0", b="1"),
             route="sign enclosure (Taylor models) on (0, 3/4]; maximum principle for (s-1)zeta(s) on |s-1| <= 5/16"),
      mutants=[Mu("interval", ("(h0 : 0 < σ)", "(h0 : -3 < σ)"), dict(a="-3"), "zeta(-2) = 0", kind="hypothesis")],
      sharpness="a nonvanishing statement: inf |zeta| on the interval is 1/2 (at 0+); the left end can go to -2 exclusive and no further")

claim(id="C09", name="no_real_zero", path="Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean", line=256, topic="L",
      math="zeta(sigma) != 0 for 0 < sigma < 1; and for the Dirichlet character chi mod 8 with chi(1) = chi(7) = 1, chi(3) = chi(5) = -1 (0 on even residues): L(sigma, chi) != 0 for every real sigma > 0.",
      conv=["L", "zeta1"],
      extra_conv=["ZMod.χ₈ is the even primitive quadratic character mod 8 (values 0,1,0,-1,0,-1,0,1 on 0..7); the hypothesis pins chi to it pointwise"],
      quant="first conjunct: sigma in (0, 1); second: the one character, all real sigma > 0 (unbounded)",
      domain="unbounded", grade="complete_cover",
      test=T("analytic.no_real_zero", dict(zeta_a="0", chi8_a="0"),
             route="as C08; for chi_8: L(0) = 0 exactly and L' > 0 on [0, 1/8] (Taylor model at 0), sign enclosure on [1/8, 2], |L - 1| <= zeta(2) - 1 beyond"),
      mutants=[Mu("closed", ("∀ σ : ℝ, 0 < σ → DirichletCharacter.LFunction χ σ ≠ 0", "∀ σ : ℝ, 0 ≤ σ → DirichletCharacter.LFunction χ σ ≠ 0"),
                  dict(chi8_closed=True), "L(0, chi_8) = -B_{1,chi} = 0 for an even character", kind="inequality")],
      sharpness="sharp in the hypothesis: L(sigma, chi_8) -> 0 as sigma -> 0+")

claim(id="C10", name="zeta_neg_odd_ne_zero", path="Formalism/ZetaNonvanishing/RHofHalfPlane.lean", line=9, topic="zeta",
      math="For every natural m: zeta(-(2m + 1)) != 0.",
      conv=["cast"], quant="all natural m (unbounded)", domain="unbounded", grade="measured_range",
      test=T("analytic.zeta_neg_integers", dict(off=1, M=3000), fast=dict(off=1, M=200),
             route="zeta(-n) = (-1)^n B_{n+1}/(n+1) with exact Bernoulli numbers (FLINT; own recurrence to index 60; Arb's zeta to m = 60)"),
      mutants=[Mu("parity", ("(2 * m + 1 : ℕ)", "(2 * m + 2 : ℕ)"), dict(off=2), "zeta(-2) = 0 (B_3 = 0)")],
      sharpness="a nonvanishing statement: the smallest |zeta(-(2m+1))| is 1/252 at m = 2")

claim(id="C11", name="riemannZeta_six", path="GroundTheory/GlobalFields/ComplexMultiplication/JInvariant.lean", line=45, topic="zeta",
      math="zeta(6) = pi^6 / 945.", conv=["npow", "cast"], quant="none (one identity)", domain="finite", grade="exact_finite",
      test=T("analytic.zeta_even_value", dict(k=3, D="945", N=2000),
             route="exact: (-1)^(k+1) B_2k 2^(2k-1)/(2k)! = 1/945 (Euler); independent bracket S_N + 1/(5(N+1)^5) < zeta(6) < S_N + 1/(5N^5) of width 1.6e-20"),
      mutants=[Mu("D", ("/ 945", "/ 946"), dict(D="946"), "pi^6/946 lies outside the partial-sum bracket")],
      sharpness="identity")

claim(id="C12", name="zeta_logderiv_limit", path="Formalism/GL3MeanSquares/HookFormulaTorsion/PsiZeroIntegral.lean", line=216, topic="zeta",
      math="zeta'(s)/zeta(s) + 1/(s - 1) tends to Euler's constant as s -> 1, s != 1.",
      conv=["deriv", "zeta1"], quant="a limit along the punctured neighbourhood filter of 1", domain="limit", grade="measured_range",
      test=T("analytic.zeta_logderiv_limit", dict(sign=1),
             route="Arb at radii 1e-2 .. 1e-16 in four directions, 256 bits: the distance to the limit shrinks linearly"),
      mutants=[Mu("sign", ("(𝓝 (Real.eulerMascheroniConstant : ℂ))", "(𝓝 (-Real.eulerMascheroniConstant : ℂ))"), dict(sign=-1),
                  "the values stay at distance 1.154 from -gamma")],
      sharpness="a limit; the test pins the sign and the constant, it does not enclose a limit")

claim(id="C13", name="norm_sq_Gamma_half", path=_EF + "LGrowthGamma.lean", line=28, topic="zeta",
      math="For every real t: |Gamma(1/2 + it)|^2 = pi / cosh(pi t).",
      conv=["norm", "npow", "gamma"], quant="all real t (unbounded)", domain="unbounded", grade="measured_range",
      test=T("analytic.gamma_half_identity", dict(), route="Arb at nine t in [0, 60], 256 bits: the two enclosures overlap, relative width below 1e-60"),
      mutants=[Mu("argument", ("Real.cosh (Real.pi * t)", "Real.cosh t"), dict(cosh_scale="1"), "at t = 1/7 the two sides are 2.850 and 3.110")],
      sharpness="identity (the reflection formula at s = 1/2 + it)")

claim(id="C14", name="half_line", path=_EF + "LGrowthGamma.lean", line=45, topic="zeta",
      math="For every real t: |Gamma(1/2 + it)| exp(pi |t| / 2) <= 3.",
      conv=["norm", "abs", "gamma"], quant="all real t (unbounded)", domain="unbounded", grade="complete_cover",
      test=T("analytic.gamma_half_line", dict(K="3", T=200), fast=dict(K="3", T=30),
             route="closed form 2 pi/(1 + e^(-2 pi |t|)) < 2 pi < 9 for every t (reflection formula, C13); direct Gamma cover on |t| <= T in mean value form"),
      mutants=[Mu("K", ("≤ 3", "≤ 5 / 2"), dict(K="5/2"), "the left side tends to sqrt(2 pi) = 2.5066")],
      sharpness="slack 1.197: the supremum sqrt(2 pi) is approached as |t| grows")

claim(id="C15", name="Gamma_decay", path=_EF + "LGrowthGamma.lean", line=222, topic="zeta",
      math="For complex w with 1/2 <= Re w <= 11/2: |Gamma(w)| exp(pi |Im w| / 2) <= 3 |w + 1|^5.",
      conv=["norm", "abs", "npow", "gamma"], quant="all w in the closed strip (unbounded in Im w)", domain="unbounded", grade="measured_range",
      test=T("analytic.gamma_decay", dict(K="3", sigma_lo="1/2", sigma_hi="11/2", E=5, T=200),
             fast=dict(K="3", sigma_lo="1/2", sigma_hi="11/2", E=5, T=64),
             route="complete cover of the rectangle in mean value form (digamma), Arb 64 bits"),
      mutants=[Mu("K", ("≤ 3 * ‖w + 1‖ ^ 5", "≤ 12 / 5 * ‖w + 1‖ ^ 5"), dict(K="12/5"), "on Re w = 11/2 the ratio tends to sqrt(2 pi)/3 = 0.8355 > 0.8"),
               Mu("strip", ("(h2 : w.re ≤ 11 / 2)", "(h2 : w.re ≤ 6)"), dict(sigma_hi="6"), "on Re w = 6 the left side grows like |Im w|^5.5", kind="hypothesis")],
      sharpness="sharp in the strip edge (11/2 - 1/2 equals the exponent 5) and within 1.2 in the constant")

# ===========================================================================
# L-functions
# ===========================================================================

claim(id="C16", name="lfunction_one_lower_bound", path=_JC + "ExceptionalCharacterBounds/LfunctionOneLowerBound.lean", line=34, topic="L",
      math="For every q >= 1 and every Dirichlet character chi mod q with chi^2 = 1 and chi != 1: 1/(20 (q + 1)) <= Re L(1, chi).",
      conv=["L", "cast", "rdiv0"],
      extra_conv=["chi ^ 2 = 1 and chi != 1 compare with the principal character mod q, so chi is any real non-principal character mod q, primitive or not"],
      quant="all moduli q and all real non-principal characters mod q (unbounded in q)", domain="unbounded", grade="measured_range",
      test=T("analytic.l_one_lower", dict(K="20", Q=2000), fast=dict(K="20", Q=150),
             route="L(1, chi_d) by the digamma formula in Arb for every fundamental d, exact Euler factors for every multiple q <= Q; enumeration and values cross-checked against Arb's characters for q <= 48"),
      mutants=[Mu("K", ("1 / (20 * ((q : ℝ) + 1))", "1 / (2 / 5 * ((q : ℝ) + 1))"), dict(K="2/5"), "at q = 3: 1/(0.4 * 4) = 0.625 > L(1, chi_-3) = 0.6046")],
      sharpness="loose: the binding case is q = 3 and the constant 20 could be 0.4135")

claim(id="C17", name="dhl_inv", path=_JC + "PNTDHLocalB.lean", line=66, topic="L",
      math="For every M >= 1, every Dirichlet character psi mod M and every real t: 1 <= 26 |L(26/25 + it, psi)|.",
      conv=["L", "norm", "cast"], quant="all moduli, all characters (principal included), all real t (unbounded)", domain="unbounded", grade="measured_range",
      test=T("analytic.l_inverse_line", dict(K="26", sigma="26/25", M_max=16, T=40), fast=dict(K="26", sigma="26/25", M_max=5, T=16),
             route="for every character mod M <= 16: branch and bound on t in [0, T] with Taylor models of L"),
      mutants=[Mu("K", ("1 ≤ 26 *", "1 ≤ 5 / 2 *"), dict(K="5/2"), "|zeta(26/25 + 14.1i)| = 0.336 < 0.4"),
               Mu("abscissa", ("(26 / 25 : ℂ)", "(1 / 2 : ℂ)"), dict(sigma="1/2"), "zeta vanishes on the line 1/2")],
      sharpness="theoretical slack 1.60 (the infimum over all characters and t is zeta(52/25)/zeta(26/25) = 0.0616); "
                "no finite search of this size comes near it, so no mutant near 26 can be rejected numerically")

claim(id="C18", name="norm_L_one_sub_le", path=_EF + "LGrowthFE.lean", line=49, topic="L",
      math="For N >= 1, chi a primitive Dirichlet character mod N, and w with 1/2 <= Re w <= 5 (and w != 1 when N = 1): |L(1 - w, chi)| <= 6 N^5 |w + 1|^5 |L(w, chi^-1)|.",
      conv=["L", "norm", "npow"],
      extra_conv=["the hypothesis `χ 0 = 0 ∨ w ≠ 1`: chi(0) = 0 exactly when N != 1, so w = 1 is excluded only for N = 1 (zeta)",
                  "χ⁻¹ is the inverse character, which is the complex conjugate"],
      quant="all N, all primitive characters, all w in the strip (unbounded)", domain="unbounded", grade="measured_range",
      test=T("analytic.l_one_sub", dict(K="6", expN=5, E=5, N_max=30), fast=dict(K="6", expN=5, E=5, N_max=17),
             route="both sides evaluated directly in Arb at nine points for every primitive character of conductor <= 30; samples, not a cover"),
      mutants=[Mu("N-power", ("(N : ℝ) ^ 5", "(N : ℝ) ^ 0"), dict(expN=0), "the functional equation carries a factor N^(Re w - 1/2), up to N^4.5")],
      sharpness="loose: largest ratio 0.02195 (N = 1, w = 1/2)")

claim(id="C19", name="LFunction_legendreCharacter_seven_one_ne_zero", path="GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmStatements.lean", line=128, topic="L",
      math="L(1, chi) != 0 for chi the Legendre symbol mod 7.", conv=["L"],
      local_definitions=[dict(name="legendreCharacter", where="GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmStatements.lean:44",
                              text="def legendreCharacter (d : ℕ) [Fact d.Prime] : DirichletCharacter ℂ d :=\n  (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)",
                              unfolded="the quadratic character of ZMod d (Mathlib's quadraticChar, values 0, 1, -1) cast to C: for d = 7 the Legendre symbol (a/7), an odd character")],
      quant="none (one value)", domain="finite", grade="exact_finite",
      test=T("analytic.l_point_nonzero", dict(q=7, d=-7, s=1),
             route="three routes agree in Arb at 128 bits: Arb's Dirichlet L, the digamma formula, pi/sqrt(7) (class number 1); the enclosure excludes 0"),
      mutants=[Mu("point", ("(legendreCharacter 7) 1 ≠ 0", "(legendreCharacter 7) (-1) ≠ 0"), dict(s=-1), "L(-1, chi) = -B_{2,chi}/2 = 0 for an odd character")],
      sharpness="a nonvanishing statement: the value is pi/sqrt(7) = 1.1874")

claim(id="C20", name="mult_zero_of_even", path=_EF + "LStructB.lean", line=150, topic="L",
      math="For N >= 1 and chi a primitive, even, non-principal Dirichlet character mod N: L(0, chi) = 0 and the zero has order exactly 1.",
      conv=["L"], extra_conv=["analyticOrderNatAt f z = 1 means f(z) = 0 and f'(z) != 0 for an analytic f that is not locally zero",
                              "χ.Even means chi(-1) = 1"],
      quant="all N and all such characters (unbounded)", domain="unbounded", grade="measured_range",
      test=T("analytic.l_zero_at_origin", dict(parity="even", N_max=80), fast=dict(parity="even", N_max=20),
             route="L(0, chi) = -(1/N) sum chi(b) b reduced exactly modulo the cyclotomic polynomial; L'(0, chi) enclosed away from 0 in Arb"),
      mutants=[Mu("parity", ("(he : χ.Even)", "(he : χ.Odd)"), dict(parity="odd"), "L(0, chi_-3) = 1/3", kind="hypothesis")],
      sharpness="identity plus a nonvanishing: the smallest |L'(0, chi)| found is 0.4812 (N = 5)")

# ===========================================================================
# primes
# ===========================================================================

claim(id="C21", name="small_nat", path="Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/CountSuccLe.lean", line=93, topic="primes",
      math="For every integer m with 1 <= m < 131072: pi(m) log m < 1.26 m.",
      conv=["pi", "log", "cast"], extra_conv=["`log` is Real.log through `open Real` (the file does not open Nat)"],
      quant="the 131071 integers 1 <= m < 2^17", domain="finite", grade="exact_finite",
      test=T("exact.prime_count_log", dict(K="126/100", N=131072),
             route="own sieve; each strict inequality decided by an Arb enclosure of log m, 64 bits"),
      mutants=[Mu("K", ("< 1.26 * m", "< 1.255 * m"), dict(K="1255/1000"), "pi(113) log 113 / 113 = 1.25506")],
      sharpness="sharp to 0.4 percent: the maximum of pi(m) log m / m is 1.2550587 at m = 113")

claim(id="C22", name="three_mul_primeCounting_le", path="Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean", line=121, topic="primes",
      math="For every integer s >= 6: 3 pi(s) <= s + 9.", conv=["pi"], quant="all natural s >= 6 (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.prime_count_linear", dict(c=9, s0=6, S=10000000), fast=dict(c=9, s0=6, S=200000), route="own sieve, exact integers"),
      mutants=[Mu("c", ("≤ s + 9", "≤ s + 4"), dict(c=4), "3 pi(7) = 12 > 11")],
      sharpness="additive slack 4: 3 pi(s) <= s + 5 holds on the range, with equality at s = 7, 13, 19")

claim(id="C23", name="primeCounting_le", path="Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeRecipSum.lean", line=186, topic="primes",
      math="For every integer s >= 6: pi(s) <= s/3 + 3 (real division).", conv=["pi", "cast"], quant="all natural s >= 6 (unbounded)",
      domain="unbounded", grade="measured_range",
      test=T("exact.prime_count_linear", dict(c=9, s0=6, S=10000000), fast=None, route="equivalent to 3 pi(s) <= s + 9 over the integers; own sieve"),
      mutants=[Mu("c", ("≤ s / 3 + 3", "≤ s / 3 + 4 / 3"), dict(c=4, S=200000), "pi(7) = 4 > 11/3")],
      sharpness="as C22")

claim(id="C24", name="centralBinom_le_pow_primeCounting", path="Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean", line=129, topic="primes",
      math="For n >= 3: C(2n, n) <= (2n)^pi(floor(sqrt(2n))) * 4^floor(2n/3) * (2n)^#{primes p : n < p <= 2n}.",
      conv=["pi", "natdiv", "npow"], extra_conv=["Nat.sqrt is the integer square root; `2 * n / 3` is floor(2n/3)"],
      quant="all natural n >= 3 (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.central_binom", dict(div=3, n0=3, N=4000), fast=dict(div=3, n0=3, N=300), route="exact big integers"),
      mutants=[Mu("exponent", ("4 ^ (2 * n / 3)", "4 ^ (2 * n / 30)"), dict(div=30), "fails first at n = 48")],
      sharpness="loose (Erdos's inequality with room): the two sides differ by at least 5 bits")

claim(id="C25", name="inv_five_log_le_sum_inv_primes", path="Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean", line=303, topic="primes",
      math="For every integer N >= 100: 1/(5 log N) <= sum of 1/p over primes p with N/2 < p <= N - 3.",
      conv=["log", "rdiv0", "icc"], extra_conv=["the filter is p prime, N < 2p and p + 3 <= N, inside {0, ..., N}"],
      quant="all natural N >= 100 (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.inv_log_prime_sum", dict(K="5", N0=100, N1=10000000), fast=dict(K="5", N0=100, N1=100000),
             route="own sieve; the 64 tightest N by exact rational sums against Arb, the rest by float64 prefix sums with margin far above their rounding error"),
      mutants=[Mu("threshold", ("100 ≤ N", "7 ≤ N"), dict(N0=7, N1=100000), "for N = 7 the sum is empty", kind="hypothesis"),
               Mu("K", ("1 / (5 * Real.log N)", "1 / (8 / 5 * Real.log N)"), dict(K="8/5", N1=100000), "at N = 226 the sum times 1.6 log N is 0.9407")],
      sharpness="slack 2.94 in the constant (binding at N = 226); the threshold 100 could be 8")

claim(id="C26", name="mertens_upper_psi_bound", path="Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/mertensUpper.lean", line=31, topic="primes",
      math="For every integer N >= 1: psi(N) + 1 + log N <= 3N, with psi(N) = sum_{n <= N} Lambda(n).",
      conv=["vM", "log", "icc"], quant="all natural N >= 1 (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.chebyshev", dict(kind="psi_plus", K="3", N1=2000000), fast=dict(kind="psi_plus", K="3", N1=50000),
             route="own sieve; Arb for N <= 3000, float64 beyond where the margin exceeds N"),
      mutants=[Mu("K", ("≤ 3 * N", "≤ 13 / 10 * N"), dict(K="13/10", N1=50000), "at N = 5 the left side is 6.704 > 6.5")],
      sharpness="loose: (psi(N) + 1 + log N)/N peaks at 1.3408 (N = 5)")

claim(id="C27", name="mertens_upper_nat", path="Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/mertensUpper.lean", line=72, topic="primes",
      math="For every integer N >= 1: sum_{n <= N} Lambda(n)/n <= log N + 2.",
      conv=["vM", "log", "icc"], quant="all natural N >= 1 (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.chebyshev", dict(kind="lambda_over_n", c="2", N1=2000000), fast=None, route="as C26"),
      mutants=[Mu("c", ("≤ Real.log N + 2", "≤ Real.log N - 1 / 10"), dict(c="-1/10", N1=50000), "at N = 1 both sums are 0")],
      sharpness="loose: sum - log N is at most 0 (N = 1) and tends to -0.577; the constant 2 could be 0")

claim(id="C28", name="prime_sum_le", path="Formalism/QuotientMetricDivisors/HermitianTwistDivisors/PlaceSumSquares.lean", line=261, topic="primes",
      math="For every finite set s of primes: sum_{p in s} log p / p^2 <= 4995/10000.",
      conv=["log", "npow", "cast"], quant="all finite sets of primes; equivalently the full series over primes", domain="compact", grade="complete_cover",
      test=T("exact.prime_sum_log_p2", dict(K="4995/10000", P=10000000), fast=dict(K="4995/10000", P=200000),
             route="Arb partial sum over primes <= P (128 bits) plus the tail bound (log P + 1)/P"),
      mutants=[Mu("K", ("≤ 4995 / 10000", "≤ 493 / 1000"), dict(K="493/1000"), "the primes up to 10^5 already sum to more than 0.493")],
      sharpness="sharp to 1.3 percent: the series is 0.493091")

claim(id="C29", name="primeLogSum_small", path="ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/PrimeLogSum.lean", line=229, topic="primes",
      math="sum over primes p <= 30 of log p/(p(p-1)) <= log 2 * (1/2 + 2/6 + 3/20 + 3/42 + 4/110 + 4/156 + 5/272 + 5/342 + 5/506 + 5/812).",
      conv=["log", "cast"], extra_conv=["Finset.Iic 30 on the naturals is {0, ..., 30}"], quant="none (one inequality)", domain="finite", grade="exact_finite",
      test=T("exact.prime_log_sum_small", dict(B=30, terms=[[1, 2], [2, 6], [3, 20], [3, 42], [4, 110], [4, 156], [5, 272], [5, 342], [5, 506], [5, 812]]),
             route="Arb at 128 bits; the two sides differ by 0.084"),
      mutants=[Mu("numerator", ("2 / 6", "1 / 6"), dict(terms=[[1, 2], [1, 6], [3, 20], [3, 42], [4, 110], [4, 156], [5, 272], [5, 342], [5, 506], [5, 812]]),
                  "the right side drops by log 2/6 = 0.1155, more than the margin 0.0840")],
      sharpness="margin 0.084 on 0.724 (each log p replaced by ceil(log2 p) log 2)")

claim(id="C30", name="sum_log_primes_le_mul_log_four", path="Development/AutomorphicArithmetic/MeanSquareBounds/SPsqLe.lean", line=10, topic="primes",
      math="For every natural Y: theta(Y) = sum_{p <= Y} log p <= Y log 4.", conv=["log", "icc"], quant="all natural Y (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.chebyshev", dict(kind="theta", base="4", N1=2000000), fast=None, route="as C26"),
      mutants=[Mu("base", ("Y * Real.log 4", "Y * Real.log 2"), dict(base="2", N1=50000), "theta(7) = log 210 = 5.347 > 7 log 2")],
      sharpness="slack 1.387: theta(Y)/Y stays below 1 on the range")

claim(id="C31", name="sum_div_mul_log_le_log_factorial", path="Formalism/LogFactorialBounds/LogFactorialProofs/PrimeSum.lean", line=22, topic="primes",
      math="For every natural n: sum over primes p <= n of floor(n/p) log p <= log(n!).",
      conv=["natdiv", "log"], extra_conv=["Nat.primesLE n is the set of primes <= n (Mathlib/NumberTheory/PrimeCounting.lean:132)"],
      quant="all natural n (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.log_factorial_prime_sum", dict(N=5000), fast=dict(N=600), route="integer coefficients of log p on both sides (log n! = sum v_p(n!) log p)"),
      mutants=[Mu("strict", ("≤ Real.log (n.factorial : ℕ)", "< Real.log (n.factorial : ℕ)"), dict(strict=True), "equality at n = 0, 1, 2, 3", kind="inequality"),
               Mu("shift", ("((n / p : ℕ) : ℝ)", "(((n + 1) / p : ℕ) : ℝ)"), dict(shift=1), "at n = 3 the left side is log 12 > log 6")],
      sharpness="equality exactly for n <= 3")

_PF = "Development/AbelianVarietyTheory/Definitions/Foundations/FoundationsPrimeFact.lean"
_PR = "Formalism/LocalRingCardinality/SpanPowerMembership/Primes.lean"
_n94 = 1 + 599 * (123 * (16 * 571 * 599 * (10944929 * 128860109809) ** 2)) ** 2
_n116 = 65794571027774832745588537266486439382601586586498771901135640963549130131839564588689999034983373394040350895271937
for _i, (_name, _path, _line, _n, _nm1) in enumerate([
        ("foundations_prime_fact_ter", _PF, 43, 10944929, None),
        ("prime_128860109809", _PF, 47, 128860109809, None),
        ("foundations_prime_fact", _PF, 51, 328347841, None),
        ("foundations_prime_fact_bis", _PF, 55, 1395478321, None),
        ("siteGood_prime_torsion", _PF, 59, _n94, [2, 3, 41, 571, 599, 10944929, 128860109809]),
        ("siteGood_prime_torsion", "Formalism/LocalToGlobal/Columns/BaseInst.lean", 329, 571253801, None),
        ("prime_fourteen_billion_example", "Formalism/LocalToGlobal/Columns/ColFormsInst.lean", 26, 14145788201, None),
        ("prime_seven_hundred_trillion_example", "Formalism/LocalToGlobal/Columns/NonDeg.lean", 600, 763521676554817, None),
        ("gA_prime", _PR, 86, 413718278401, None),
        ("gB_prime", _PR, 155, 603339156001, None),
        ("prime_large", _PR, 518, _n116, [2, 3, 571, 599, 413718278401, 603339156001])]):
    _d = len(str(_n))
    _k = next(k for k in range(2, 200, 2) if any((_n + k) % q == 0 for q in (3, 5, 7, 11, 13, 17, 19, 23)))
    claim(id="C%02d" % (32 + _i), name=_name, path=_path, line=_line, topic="primes",
          math=f"The {_d}-digit number {_n if _d <= 20 else str(_n)[:12] + '...' + str(_n)[-12:]} is prime."
               + (" It is 1 + 599 X^2 with X = 123 * 16 * 571 * 599 * (10944929 * 128860109809)^2." if _d == 94 else ""),
          conv=["cast"], quant="none (one number)", domain="finite", grade="exact_finite",
          literal=str(_n),
          test=T("exact.literal_prime", dict(n=str(_n), **({"nm1_primes": _nm1} if _nm1 else {})),
                 route=("PARI isprime (a proof: BPSW is exhaustively verified below 2^64); own trial division by every prime up to the square root; own Miller-Rabin, 12 bases"
                        if _d <= 15 else
                        "PARI isprime (APRCL or the n-1 test, a proof); own Pocklington-Lucas proof from the complete factorisation of n - 1, "
                        "whose prime factors are each proved by own trial division; own Miller-Rabin")),
          mutants=[Mu("offset", None, dict(n=str(_n + _k), offset=_k), f"n + {_k} has a prime factor below 25")],
          sharpness="a primality statement")

claim(id="C43", name="log_abs_eval_one_cyclotomic_eq_vonMangoldt", path="Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdDiff.lean", line=9, topic="primes",
      math="For every integer m > 1: log |Phi_m(1)| = Lambda(m), Phi_m the m-th cyclotomic polynomial.",
      conv=["log", "vM"], extra_conv=["at m = 1 (excluded) the statement would still hold as Lean reads it: Phi_1(1) = 0 and Real.log 0 = 0 = Lambda(1)"],
      quant="all natural m > 1 (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.cyclotomic_value", dict(x=1, m0=2, M_poly=400, M_rec=6000), fast=dict(x=1, m0=2, M_poly=150, M_rec=600),
             route="exact integers by two routes: the polynomial by division (m <= 400) and prod_{d | m, d > 1} Phi_d(1) = m (m <= 6000)"),
      mutants=[Mu("point", ("(eval 1 (cyclotomic m ℚ) : ℚ)", "(eval (-1) (cyclotomic m ℚ) : ℚ)"), dict(x=-1, M_rec=0), "Phi_2(-1) = 0, so the left side is 0 and Lambda(2) = log 2")],
      sharpness="identity")

claim(id="C44", name="weight_sum", path="Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RdArith.lean", line=45, topic="primes",
      math="For N >= 1 and m | N with m != 1: sum over m' | N with m | m' of Lambda(m') phi(N/m') = phi(N) Lambda(m)/phi(m).",
      conv=["vM", "natdiv", "totient0", "rdiv0"], quant="all natural N != 0 and all divisors m != 1 (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.vonmangoldt_weight_sum", dict(N_max=4000), fast=dict(N_max=300), route="exact rational coefficients of log p on both sides"),
      mutants=[Mu("m=1", ("(hm1 : m ≠ 1)", "(hm1 : m ≠ 0)"), dict(allow_m_eq_1=True), "for N = 2, m = 1 the left side is log 2 and the right side is 0", kind="hypothesis")],
      sharpness="identity; the hypothesis m != 1 is needed")

# ===========================================================================
# totients
# ===========================================================================

_DZ = "Development/DiscreteGroups/GlobalIrreducibility/DzDigTot.lean"
claim(id="C45", name="sq_le_totient", path=_DZ, line=90, topic="arithmetic",
      math="For N >= 2: N^2 <= 4 (2 omega(N) - 1) phi(N)^2, omega the number of distinct prime factors.",
      conv=["natsub", "npow"], extra_conv=["# is Finset.card through `open Finset`; 2 * #N.primeFactors - 1 is truncated subtraction, harmless for N >= 2"],
      quant="all natural N >= 2 (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.totient_sq", dict(c=4, N0=2, N1=10000000), fast=dict(c=4, N0=2, N1=200000), route="own int64 sieves of phi and omega"),
      mutants=[Mu("c", ("≤ 4 * (2 *", "≤ 3 * (2 *"), dict(c=3, N1=200000), "at N = 2: 4 > 3"),
               Mu("threshold", ("(hN : 2 ≤ N)", "(hN : 1 ≤ N)"), dict(N0=1, N1=200000), "at N = 1 the truncated 2*0 - 1 is 0, so the right side is 0 < 1", kind="hypothesis")],
      sharpness="sharp: equality at N = 2")

claim(id="C46", name="two_n_N_lt", path=_DZ, line=121, topic="arithmetic",
      math="For p prime and n >= 2 with 16 n^2 < p: 2n (p^n - 1) < (p - 1) phi(p^n - 1).",
      conv=["natsub", "npow"], quant="all primes p and natural n >= 2 with p > 16 n^2 (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.totient_prime_power_minus_one", dict(c="16", P2=2000000, Pn=5000, n_max=7), fast=dict(c="16", P2=3000, Pn=400, n_max=6),
             route="phi(p^n - 1) from PARI eulerphi, cross-checked by own factorisation below 1e9; exact integers"),
      mutants=[Mu("c", ("16 * n ^ 2 < p", "3 * n ^ 2 < p"), dict(c="3", P2=3000, Pn=400, n_max=6), "(p, n) = (13, 2): 672 > 576")],
      sharpness="slack 4.9 in the hypothesis: with the hypothesis dropped the conclusion fails only for p <= 3.25 n^2 on the range")

claim(id="C47", name="le_totient_sq", path="Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsIntegralOfMulMem.lean", line=14, topic="arithmetic",
      math="For every natural n: n <= 2 phi(n)^2, and if n is odd then n <= phi(n)^2.",
      conv=["totient0", "npow"], quant="all natural n, 0 included (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.totient_le_sq", dict(c1=2, c2=1, N1=10000000), fast=dict(c1=2, c2=1, N1=200000), route="own int64 sieve"),
      mutants=[Mu("c", ("n ≤ 2 * n.totient ^ 2", "n ≤ 1 * n.totient ^ 2"), dict(c1=1, N1=200000), "n = 2: phi = 1")],
      sharpness="sharp: equality at n = 0, 1, 2")

claim(id="C48", name="dvd_twelve_of_totient_le_two", path="Development/AutomorphicArithmetic/AutomorphicVarieties/WeakShimuraTheory/FrobeniusDensity/QuadFacts.lean", line=158, topic="arithmetic",
      math="For k >= 1 with phi(k) <= 2: k divides 12.", conv=["totient0"], quant="all natural k > 0 (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.totient_small_divides", dict(b=2, D=12, N1=10000000), fast=dict(b=2, D=12, N1=200000), route="own int64 sieve: the k with phi(k) <= 2 are 1, 2, 3, 4, 6"),
      mutants=[Mu("D", ("k ∣ 12", "k ∣ 6"), dict(D=6, N1=200000), "k = 4"),
               Mu("b", ("k.totient ≤ 2", "k.totient ≤ 4"), dict(b=4, N1=200000), "k = 5", kind="hypothesis")],
      sharpness="exact (12 is the least common multiple of 1, 2, 3, 4, 6)")

_LS = _GI + "ArithmeticLargeSieveOneResidueClassPerPrime.lean"
claim(id="C49", name="totient_mul_sigma_pow_le_pow_succ", path=_LS, line=49, topic="arithmetic",
      math="For K >= 0 and n >= 1: phi(n) sigma(n^K) <= n^(K+1), sigma the sum of divisors.",
      conv=["npow"], quant="all natural K and n > 0 (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.totient_sigma", dict(j=1, N=5000, K_max=6), fast=dict(j=1, N=300, K_max=4), route="exact integers from own factorisation"),
      mutants=[Mu("strict", ("≤ n ^ (K + 1)", "< n ^ (K + 1)"), dict(strict=True), "equality at n = 1", kind="inequality"),
               Mu("sigma", ("ArithmeticFunction.sigma 1", "ArithmeticFunction.sigma 2"), dict(j=2), "n = 2, K = 1: 5 > 4")],
      sharpness="equality at n = 1 only")

claim(id="C50", name="sum_inv_le_mul_sum_squarefree_inv_totient", path=_LS, line=78, topic="arithmetic",
      math="For q >= 1 and Q >= 0: sum_{n=1}^{Q} 1/n <= (q/phi(q)) sum over squarefree f <= Q coprime to q of 1/phi(f).",
      conv=["icc", "rdiv0"], quant="all natural Q and q >= 1 (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.harmonic_squarefree", dict(Q_max=400, q_max=210), fast=dict(Q_max=60, q_max=30), route="exact rationals"),
      mutants=[Mu("strict", ("(1:ℝ) / n ≤ ((q:ℝ)", "(1:ℝ) / n < ((q:ℝ)"), dict(strict=True), "equality at Q = 0, and at Q = q = 1", kind="inequality")],
      sharpness="equality at Q = 0 and at (Q, q) = (1, 1)")

# ===========================================================================
# finite fields
# ===========================================================================

_QC = [[3, 1, 400], [5, 1, 400], [7, 1, 400], [11, 1, 2000], [13, 1, 3000], [3, 2, 600], [5, 2, 120], [7, 2, 30], [3, 3, 60]]
_QCf = [[3, 1, 400], [5, 1, 400], [7, 1, 400], [3, 2, 40]]
claim(id="C51", name="card_quadric_even", path="CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FiniteFieldQuadraticFormPointCount.lean", line=108, topic="finite_field",
      math="k a finite field of odd characteristic with q elements, B a symmetric 2M x 2M matrix over k with det B != 0, M >= 1, s in k: "
           "|#{x in k^(2M) : (1/2) x^T B x = s} - q^(2M-1)| <= q^M.",
      conv=["card", "natsub", "npow", "abs"], quant="all finite fields of characteristic != 2, all M >= 1, all nondegenerate symmetric B, all s (unbounded)",
      domain="unbounded", grade="measured_range",
      test=T("ff.quadric_even", dict(bound="M", s_nonzero=False, cases=_QC), fast=dict(bound="M", s_nonzero=False, cases=_QCf),
             route="exact enumeration of k^(2M) over prime fields; every symmetric nondegenerate B for 2 x 2, seeded samples for 4 x 4 and 6 x 6"),
      mutants=[Mu("bound", ("≤ (Fintype.card k : ℝ) ^ M", "≤ (Fintype.card k : ℝ) ^ M / 2"), dict(bound="M/2"), "q = 3, M = 1, s = 0, hyperbolic plane: deviation 2 > 3/2")],
      sharpness="slack q/(q-1): at s = 0 the deviation is q^M - q^(M-1)")

claim(id="C52", name="card_quadric_sub_sq_le", path="Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CardQuadricSubSqLe.lean", line=66, topic="finite_field",
      math="k a finite field with 2 != 0, S a symmetric n x n matrix with det S != 0, n >= 1, beta in k: (#{x in k^n : x^T S x = beta} - q^(n-1))^2 <= q^n.",
      conv=["card", "natsub", "npow"], extra_conv=["this form has no factor 1/2, unlike C51 and C53"],
      quant="all finite fields of characteristic != 2, all n >= 1, all nondegenerate symmetric S, all beta (unbounded)", domain="unbounded", grade="measured_range",
      test=T("ff.quadric_sq", dict(divisor="1", cases=[[3, 1, 100], [3, 2, 100], [3, 3, 800], [5, 1, 10], [5, 2, 200], [5, 3, 600], [7, 1, 10], [7, 2, 400], [7, 3, 200],
                                                        [11, 2, 2000], [13, 2, 3000], [17, 2, 5000], [3, 4, 400], [3, 5, 60], [5, 4, 40]]),
             fast=dict(divisor="1", cases=[[3, 1, 100], [3, 2, 100], [3, 3, 200], [5, 2, 200], [7, 2, 400]]), route="exact enumeration, as C51"),
      mutants=[Mu("bound", ("≤ (Fintype.card k : ℝ) ^ Fintype.card ι", "≤ (Fintype.card k : ℝ) ^ Fintype.card ι / 2"), dict(divisor="2"), "q = 5, n = 2, beta = 0: 16 > 25/2")],
      sharpness="asymptotically sharp: the ratio (1 - 1/q)^2 at beta = 0 on a hyperbolic plane tends to 1")

claim(id="C53", name="sharp", path="Development/WeilBound/CoreStatements/AutomorphicKernels/UnitarySchrodingerModel/UnitarySchrodingerLemmas/LowRankSiegelDensities/SharpCount.lean", line=134, topic="finite_field",
      math="As C51 with s != 0: |#{x : (1/2) x^T B x = s} - q^(2M-1)| <= q^(M-1).",
      conv=["card", "natsub", "npow", "abs"], extra_conv=["k and the index type come from `variable` lines: k a finite field with decidable equality, the index type finite"],
      quant="as C51, s != 0 (unbounded)", domain="unbounded", grade="measured_range",
      test=T("ff.quadric_even", dict(bound="M-1", s_nonzero=True, cases=_QC), fast=dict(bound="M-1", s_nonzero=True, cases=_QCf), route="as C51"),
      mutants=[Mu("strict", ("≤ (Fintype.card k : ℝ) ^ (M - 1)", "< (Fintype.card k : ℝ) ^ (M - 1)"), dict(strict=True), "the deviation equals q^(M-1) in every case", kind="inequality"),
               Mu("s=0", ("(hs : s ≠ 0)", "(hs : s = s)"), dict(s_nonzero=False), "at s = 0 the deviation is q^M - q^(M-1)", kind="hypothesis")],
      sharpness="sharp: equality in every case tested")

_CS = "Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/"
claim(id="C54", name="card_herm_norm_eq", path=_CS + "CardSumNormFibres.lean", line=243, topic="finite_field",
      math="k a finite field with q^2 elements, sigma its involution x -> x^q, M >= 1, c != 0 fixed by sigma: #{x in k^M : sum sigma(x_i) x_i = c} = q^(M-1) (q^M - (-1)^M).",
      conv=["card", "natsub", "npow"], extra_conv=["sigma is any ring automorphism with sigma^2 = id and sigma != id; on a finite field there is exactly one"],
      quant="all such fields, all M >= 1, all admissible c (unbounded)", domain="unbounded", grade="measured_range",
      test=T("ff.herm_norm", dict(sign=-1, fields=[[2, 1, 6], [3, 1, 5], [5, 1, 4], [7, 1, 3], [11, 1, 2]]), fast=dict(sign=-1, fields=[[2, 1, 4], [3, 1, 3], [5, 1, 2]]),
             route="the norm x * x^q tabulated on explicit fields of 4, 9, 25, 49, 121 elements, convolved M times; exact"),
      mutants=[Mu("sign", ("- (-1) ^ M)", "- 1 ^ M)"), dict(sign=1), "M = 1: there are q + 1 elements of norm c, not q - 1")],
      sharpness="identity")

claim(id="C55", name="card_dot_eq", path=_CS + "CardSumNormFibres.lean", line=269, topic="finite_field",
      math="k a finite field with q elements, M >= 1, c != 0: #{(x, y) in k^M x k^M : x . y = c} = q^(2M-1) - q^(M-1).",
      conv=["card", "natsub", "npow"], quant="all finite fields (characteristic 2 included), all M >= 1, all c != 0 (unbounded)", domain="unbounded", grade="measured_range",
      test=T("ff.dot_count", dict(sign=-1, fields=[[2, 1, 6], [3, 1, 5], [2, 2, 4], [5, 1, 4], [7, 1, 4], [2, 3, 3], [3, 2, 3], [11, 1, 3], [13, 1, 3], [5, 2, 2], [3, 3, 2]]),
             fast=dict(sign=-1, fields=[[2, 1, 4], [3, 1, 3], [2, 2, 3], [5, 1, 2], [2, 3, 2], [3, 2, 2]]),
             route="the product table of explicit fields with 2, 3, 4, 5, 7, 8, 9, 11, 13, 25, 27 elements, convolved M times; exact"),
      mutants=[Mu("sign", ("- (q : ℤ) ^ (M - 1)", "+ (q : ℤ) ^ (M - 1)"), dict(sign=1), "q = 2, M = 1: one solution, not three")],
      sharpness="identity")

claim(id="C56", name="card_unitary_fin", path=_CS + "CardUnitaryFin.lean", line=235, topic="finite_field",
      math="k a finite field with q^2 elements, sigma its involution, m >= 0: #{X in M_m(k) : sigma(X)^T X = 1} = q^(m^2) prod_{j=1}^{m} (1 - (-1/q)^j).",
      conv=["card", "npow", "icc"], extra_conv=["`(-(q : ℝ))⁻¹ ^ j` parses as ((-q)⁻¹)^j: the postfix inverse binds tighter than ^"],
      quant="all such fields and all natural m (unbounded)", domain="unbounded", grade="measured_range",
      test=T("ff.unitary_count", dict(sign=-1, fields=[[2, 1, 3], [3, 1, 2], [5, 1, 2], [7, 1, 2]]), fast=dict(sign=-1, fields=[[2, 1, 3], [3, 1, 2]]),
             route="exact enumeration of all m x m matrices over fields of 4, 9, 25, 49 elements (m <= 3, 2, 2, 2)"),
      mutants=[Mu("sign", ("(1 - (-(q : ℝ))⁻¹ ^ j)", "(1 - ((q : ℝ))⁻¹ ^ j)"), dict(sign=1), "m = 1: q + 1 elements of norm 1, not q - 1")],
      sharpness="identity")

claim(id="C57", name="card_proper_subfield_elements_lt", path="Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardProperSubfieldElementsLt.lean", line=67, topic="finite_field",
      math="For a prime g >= 5 and d >= 1: 2d * #{z in the field of g^d elements : z != 0, degree of z over F_g is not d} < g^d - 1.",
      conv=["card", "natsub", "npow"],
      local_definitions=[dict(name="Formalism.CyclotomicNorms.Fbar", where="Formalism/CyclotomicNorms/StatementT.lean:14",
                              text="abbrev Fbar (g : ℕ) [Fact g.Prime] : Type := AlgebraicClosure (ZMod g)",
                              unfolded="an algebraic closure of F_g; z ^ (g ^ d) = z cuts out the subfield with g^d elements, and natDegree (minpoly (ZMod g) z) is the degree of z")],
      quant="all primes g >= 5 and all d > 0 (unbounded)", domain="unbounded", grade="measured_range",
      test=T("ff.subfield_elements", dict(g_min=5, g_max=200, d_max=60), fast=dict(g_min=5, g_max=30, d_max=20),
             route="the count is (g^d - 1) - sum_{e | d} mu(d/e) g^e, validated by Frobenius-orbit enumeration on ten explicit fields; then exact integers"),
      mutants=[Mu("g", ("5 ≤ g", "3 ≤ g"), dict(g_min=3), "g = 3, d = 2: 8 < 8 is false", kind="hypothesis")],
      sharpness="slack 1.5 at g = 5, d = 2; the hypothesis 5 <= g is sharp (g = 3 gives equality)")

claim(id="C58", name="hda_card_qc", path="Formalism/DirichletDensity/DirichletDensityProofs/HostDensityArith.lean", line=21, topic="finite_field",
      math="For an odd prime p and e = 1 or e = -1: 2 * #{y in ZMod p : quadratic character of y is e} = p - 1.",
      conv=["natsub", "card"], quant="all odd primes p (unbounded)", domain="unbounded", grade="measured_range",
      test=T("ff.quad_char_count", dict(P=20000, p_min=3, e_values=[1, -1]), fast=dict(P=1000, p_min=3, e_values=[1, -1]), route="exact enumeration of squares"),
      mutants=[Mu("p=2", ("(hp : p ≠ 2)", "(hp : p ≠ 1)"), dict(p_min=2), "p = 2, e = 1: one element, and 2 != 1", kind="hypothesis")],
      sharpness="identity; the hypothesis p != 2 is needed")

_CP = "Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardPowEqOneLeOfIsCyclicUnits.lean"
claim(id="C59", name="card_pow_eq_one_le_of_isCyclic_units", path=_CP, line=48, topic="finite_field",
      math="For n >= 1 with (Z/n)^x cyclic and d >= 1: #{x in Z/n : x^d = 1} <= d.", conv=["card", "npow"],
      quant="all n != 0 with cyclic unit group and all d > 0 (unbounded)", domain="unbounded", grade="measured_range",
      test=T("ff.roots_of_unity_count", dict(family="cyclic", factor=1, n_max=600, d_max=60), fast=dict(family="cyclic", factor=1, n_max=150, d_max=24),
             route="exact enumeration; cyclicity decided by exhibiting a generator"),
      mutants=[Mu("cyclic", ("[IsCyclic (ZMod n)ˣ]", "[Nonempty (ZMod n)ˣ]"), dict(family="all"), "n = 8, d = 2: four square roots of 1", kind="hypothesis")],
      sharpness="sharp: equality whenever d divides phi(n)")

claim(id="C60", name="card_pow_eq_one_two_pow_le", path=_CP, line=52, topic="finite_field",
      math="For w >= 1 and d >= 1: #{x in Z/2^w : x^d = 1} <= 2d.", conv=["card", "npow"], quant="all w >= 1 and d > 0 (unbounded)", domain="unbounded", grade="measured_range",
      test=T("ff.roots_of_unity_count", dict(family="two_power", factor=2, w_max=14, n_max=0, d_max=64), fast=dict(family="two_power", factor=2, w_max=9, n_max=0, d_max=16),
             route="exact enumeration"),
      mutants=[Mu("factor", ("≤ 2 * d", "≤ d"), dict(factor=1), "w = 3, d = 2: four solutions")],
      sharpness="sharp: equality at w = 3, d = 2")

claim(id="C61", name="card_GL_le", path="Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FieldDatumSizeLogDiscriminant.lean", line=169, topic="finite_field",
      math="#GL_2(Z/12) <= 20736.", conv=["card"], quant="none (one number)", domain="finite", grade="exact_finite",
      test=T("ff.gl2_card", dict(n=12, bound=20736), route="exact enumeration of the 12^4 matrices: 4608 have unit determinant"),
      mutants=[Mu("bound", ("≤ 20736", "≤ 4607"), dict(bound=4607), "the group has 4608 elements")],
      sharpness="loose: 20736 = 12^4 counts all matrices; the group has 4608 elements")

# ===========================================================================
# elementary inequalities and identities
# ===========================================================================

claim(id="C62", name="exp_ge_quad", path="Formalism/LogSumExpBounds/CharacterSumPhase/LogSumExpBoundHolds.lean", line=7, topic="elementary",
      math="For real z with |z| <= 1: 1 + z + z^2/3 <= exp z.", conv=["abs", "npow", "cast"], quant="all real z in [-1, 1] (compact)", domain="compact", grade="complete_cover",
      test=T("analytic.exp_ge_quad", dict(c="1/3", R="1"),
             route="g = exp z - 1 - z - z^2/3 has g(0) = g'(0) = 0 and g'' > 0 on [-1/4, 1/4] (Arb), so g >= 0 there; sign enclosure by bisection elsewhere"),
      mutants=[Mu("coefficient", ("z ^ 2 / 3", "z ^ 2 * (3 / 8)"), dict(c="3/8"), "at z = -1: 3/8 > 1/e = 0.3679"),
               Mu("range", ("|z| ≤ 1", "|z| ≤ 3 / 2"), dict(R="3/2"), "at z = -3/2: 1/4 > e^(-3/2) = 0.2231", kind="hypothesis")],
      sharpness="equality at z = 0 (double zero); the coefficient 1/3 could be 1/e = 0.3679 and no more")

_ID = "Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/IdealCounting/"
claim(id="C63", name="classC_const", path=_ID + "ClassC.lean", line=32, topic="elementary",
      math="For natural n >= 1 and r with 2r <= n: (4/pi)^r n!/n^n <= 1.", conv=["npow", "rdiv0"], quant="all natural n > 0 and r <= n/2 (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.minkowski_const", dict(r_rule="2r<=n", N=5000), fast=dict(r_rule="2r<=n", N=300), route="r = 0 exact rationals; r >= 1 by Arb on the logarithm (lgamma), 128 bits"),
      mutants=[Mu("strict", ("^ n) ≤ 1", "^ n) < 1"), dict(strict=True), "equality at n = 1, r = 0", kind="inequality"),
               Mu("r", ("(hr : 2 * r ≤ n)", "(hr : r ≤ n)"), dict(r_rule="r<=n"), "n = r = 1: 4/pi > 1", kind="hypothesis")],
      sharpness="sharp: equality at (n, r) = (1, 0); next largest value 2/pi at (2, 1)")

claim(id="C64", name="classC_fact", path=_ID + "ClassC.lean", line=8, topic="elementary",
      math="For every natural n: 2^n (n+1)! <= (n+1)^(n+1).", conv=["npow"], quant="all natural n (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.fact_pow", dict(N=3000), fast=dict(N=300), route="exact integers"),
      mutants=[Mu("strict", ("≤ ((n + 1 : ℕ) : ℝ) ^ (n + 1)", "< ((n + 1 : ℕ) : ℝ) ^ (n + 1)"), dict(strict=True), "equality at n = 0 and n = 1", kind="inequality")],
      sharpness="sharp: equality at n = 0, 1")

claim(id="C65", name="thin_ptw", path="Development/AutomorphicArithmetic/MeanSquareBounds/IntThin.lean", line=16, topic="elementary",
      math="For real c > 0, v >= 1, 0 < lam <= v^0.61: (v + lam)^2 exp(-c v/(lam + sqrt v)) <= 4 v^2 exp(-(c/2) v^0.39).",
      conv=["rpow", "sqrt", "cast"], extra_conv=["`-c * v / (lam + Real.sqrt v)` is (-(c v))/(lam + sqrt v); `v ^ (2 : ℝ)` is rpow, equal to v^2 for v > 0"],
      quant="all real c > 0, v >= 1, lam in (0, v^0.61] (unbounded)", domain="unbounded", grade="complete_cover",
      test=T("analytic.thin_ptw", dict(K="4", e_lam="61/100", e_rhs="39/100"),
             route="exact reduction: the statement for every c > 0 is equivalent to (v + lam)^2 <= 4 v^2 and lam + sqrt v <= 2 v^0.61, which hold iff 4 >= 4 and "
                   "61/100 <= 1 - 39/100 (rationals); the literal inequality is evaluated in Arb on a 63-point grid up to v = e^400"),
      mutants=[Mu("K", ("4 * (v ^ (2 : ℝ)", "399 / 100 * (v ^ (2 : ℝ)"), dict(K="399/100"), "at v = lam = 1 both sides are a multiple of exp(-c/2), and 4 > 3.99"),
               Mu("exponent", ("v ^ (39 / 100 : ℝ)", "v ^ (40 / 100 : ℝ)"), dict(e_rhs="40/100"), "0.61 + 0.40 > 1: fails for large v")],
      sharpness="sharp in both constants: equality at v = lam = 1 for every c, and 0.61 + 0.39 = 1 exactly")

_MG = "Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean"
claim(id="C66", name="legendre'", path=_MG, line=208, topic="arithmetic",
      math="For a prime p and natural n: n/(p-1) - v_p(n!) <= floor(log_p n) + 1.", conv=["padic", "natlog", "rdiv0"], quant="all primes p and natural n (unbounded)",
      domain="unbounded", grade="measured_range",
      test=T("exact.legendre_digits", dict(add="1", primes=[2, 3, 5, 7, 11, 13, 47, 101], N=200000), fast=dict(add="1", primes=[2, 3, 5, 7, 47], N=5000), route="exact rationals"),
      mutants=[Mu("strict", ("≤ (Nat.log p n : ℝ) + 1", "< (Nat.log p n : ℝ) + 1"), dict(strict=True), "equality at n = p^k - 1", kind="inequality"),
               Mu("add", ("(Nat.log p n : ℝ) + 1", "(Nat.log p n : ℝ) + 9 / 10"), dict(add="9/10"), "p = 2, n = 1")],
      sharpness="sharp: equality at n = p^k - 1 (the left side is the digit sum over p - 1)")

claim(id="C67", name="vchoose_le", path=_MG, line=237, topic="arithmetic",
      math="For a prime p and natural n, k: v_p(C(n, k)) <= floor(log_p n).", conv=["padic", "natlog"],
      extra_conv=["for k > n the binomial is 0 and padicValNat p 0 = 0"], quant="all primes p, all natural n and k (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.padic_choose", dict(primes=[2, 3, 5, 7, 11, 13], N=600), fast=dict(primes=[2, 3, 5], N=120), route="exact integers"),
      mutants=[Mu("strict", ("≤ (Nat.log p n : ℝ)", "< (Nat.log p n : ℝ)"), dict(strict=True), "equality already at n = 0, and at C(2, 1)", kind="inequality")],
      sharpness="sharp: equality for example at C(p^j, 1)")

claim(id="C68", name="padicValNat_factorial_le_sub_one_div", path="Formalism/GaussJetBounds/GaussJetProofs/LogStep.lean", line=14, topic="arithmetic",
      math="For a prime l and natural k != 0: v_l(k!) <= (k - 1)/(l - 1).", conv=["padic", "rdiv0"], quant="all primes l and natural k >= 1 (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.padic_factorial", dict(k0=1, primes=[2, 3, 5, 7, 11, 13, 47, 101], N=200000), fast=dict(k0=1, primes=[2, 3, 5, 7, 47], N=5000), route="exact rationals"),
      mutants=[Mu("k=0", ("(hk : k ≠ 0)", "(hk : k ≠ 1)"), dict(k0=0), "k = 0: 0 <= -1/(l-1) is false", kind="hypothesis"),
               Mu("strict", ("≤ ((k : ℝ) - 1) *", "< ((k : ℝ) - 1) *"), dict(strict=True), "equality at k = l^j", kind="inequality")],
      sharpness="sharp: equality at k = l^j; the hypothesis k != 0 is needed")

claim(id="C69", name="card_tuples_le", path=_ID + "ClassA.lean", line=27, topic="arithmetic",
      math="For natural n and M >= 1: #{(a_0, ..., a_n) in {1..M}^(n+1) : a_0 ... a_n <= M} <= M (1 + log M)^n.",
      conv=["icc", "log", "npow"], quant="all natural n and M >= 1 (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.tuples_count", dict(add="1", M_max=3000, n_max=5), fast=dict(add="1", M_max=200, n_max=3), route="exact counts by recursion on floor(M/a); Arb for the right side"),
      mutants=[Mu("add", ("(1 + Real.log M)", "(9 / 10 + Real.log M)"), dict(add="9/10"), "n = 1, M = 1: one tuple, bound 9/10"),
               Mu("strict", ("≤ M * (1 +", "< M * (1 +"), dict(strict=True), "equality for n = 0", kind="inequality")],
      sharpness="sharp: equality for n = 0 and for M = 1")

claim(id="C70", name="sum_min_le_div", path="Development/AutomorphicArithmetic/MeanSquareBounds/SumMinLeDiv.lean", line=44, topic="arithmetic",
      math="For real x >= 0, natural N and a prime p: sum_{i=1}^{N} min(1, x/p^i) <= 2x/p.", conv=["icc", "npow", "rdiv0"], quant="all real x >= 0, natural N, primes p (unbounded)",
      domain="unbounded", grade="measured_range",
      test=T("exact.sum_min", dict(K="2"), route="exact rationals on a grid of x, p in {2, 3, 5, 7, 11}, N <= 40"),
      mutants=[Mu("K", ("≤ 2 * (x / p)", "≤ 199 / 100 * (x / p)"), dict(K="199/100"), "p = 2, x = 1/8, N = 8: 255/2048 > 199/1600"),
               Mu("x<0", ("(hx0 : 0 ≤ x)", "(hx0 : -1 ≤ x)"), dict(allow_negative=True), "for x < 0 and N = 0 the left side is 0 > 2x/p", kind="hypothesis")],
      sharpness="sharp in the limit: the ratio is 1 - 2^-N for p = 2 and small x")

claim(id="C71", name="harm_le", path="Formalism/LogVandermondeBounds/LogVandermondeProofs/LogVandermondeVariationUnbounded.lean", line=95, topic="elementary",
      math="For every natural N: sum_{i=0}^{N-1} 1/(i+1) <= 1 + log N.", conv=["icc", "log"], extra_conv=["at N = 0 the statement reads 0 <= 1 + Real.log 0 = 1"],
      quant="all natural N (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.harmonic_log", dict(add="1", N1=1000000), fast=dict(add="1", N1=20000), route="N = 0, 1 exact; N >= 2 by Arb cumulative sums, 128 bits"),
      mutants=[Mu("strict", ("≤ 1 + Real.log N", "< 1 + Real.log N"), dict(strict=True), "equality at N = 1", kind="inequality")],
      sharpness="sharp: equality at N = 1")

claim(id="C72", name="exp_sqrt_le", path="Development/AutomorphicArithmetic/MeanSquareBounds/GIntegral.lean", line=44, topic="elementary",
      math="For real c > 0 and x > 1: exp(-c sqrt(log x)) <= 24/(c^4 (log x)^2).", conv=["sqrt", "log", "app", "npow"],
      extra_conv=["`24 / c ^ 4 / Real.log x ^ 2` is (24/c^4)/(log x)^2"], quant="all real c > 0 and x > 1; with t = c sqrt(log x) this is every t > 0", domain="unbounded", grade="complete_cover",
      test=T("analytic.exp_power", dict(K="24", E=4, literal="sqrt_log"),
             route="t = c sqrt(log x) ranges over (0, oo) and the statement is t^4 e^-t <= 24: Arb cover of [0, 16], decreasing beyond t = 4; literal form at 20 points"),
      mutants=[Mu("K", ("≤ 24 / c ^ 4", "≤ 23 / 5 / c ^ 4"), dict(K="23/5"), "at t = 4: 256 e^-4 = 4.689 > 4.6")],
      sharpness="slack 5.12: the smallest admissible constant is 256/e^4 = 4.6888")

claim(id="C73", name="exp_neg_le_div_pow_four", path="Formalism/GL3MeanSquares/HookFormulaTorsion/ExpNegLeDivPowFour.lean", line=290, topic="elementary",
      math="For real y > 0: exp(-y) <= 24/y^4.", conv=["npow"], quant="all real y > 0 (unbounded)", domain="unbounded", grade="complete_cover",
      test=T("analytic.exp_power", dict(K="24", E=4), route="Arb cover of [0, 16]; y^4 e^-y is decreasing beyond y = 4"),
      mutants=[Mu("K", ("≤ 24 / y ^ 4", "≤ 23 / 5 / y ^ 4"), dict(K="23/5"), "at y = 4: 256 e^-4 = 4.689 > 4.6")],
      sharpness="slack 5.12, as C72")

claim(id="C74", name="nok_exponent", path="Formalism/GaussValuationBounds/NokLemmaCVal.lean", line=40, topic="arithmetic",
      math="For natural l >= 3, g, h, ell, j >= 1 and real r, kappa, R, K with 0 <= r <= R, kappa <= K, with sigma = floor((3g + M/l^(j-1)) l/(l-1)^2) + 1 and M = floor((h+2g)/(l-1)) + 1: "
           "2r + 4 sigma + max(r, 2(2 sigma + r + 2 g ell)) + 2 kappa <= 4R + 8((3/2)(h+2g)/(l-1)^(j+1) + (9/4) g + 7/4) + 4 g ell + 2K. "
           "With r = R and kappa = K this is sigma <= (3/2)(h+2g)/(l-1)^(j+1) + (9/4) g + 7/4.",
      conv=["natsub", "natdiv", "floor", "npow"],
      extra_conv=["the third argument of sigNOK, `(h + 2 * g) / (ℓ - 1) + 1`, is natural-number arithmetic (floor division); the bound on the right is real arithmetic", "l need not be prime"],
      local_definitions=[dict(name="sigNOK", where="Formalism/GaussValuationBounds/Statement.lean:11",
                              text="def sigNOK (ℓ E M j : ℕ) : ℕ :=\n  ⌊((E : ℝ) + (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) * (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2⌋₊ + 1",
                              unfolded="sigNOK l E M j = floor((E + M/l^(j-1)) l/(l-1)^2) + 1, called with E = 3g and M = floor((h+2g)/(l-1)) + 1")],
      quant="all natural l >= 3, g, h, ell, j >= 1 and all real r, kappa, R, K with the three order hypotheses (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.nok_exponent", dict(const="7/4", l_min=3), route="exact rationals on 3 <= l <= 13, g <= 13, h <= 49, j <= 4, three ell, four (r, kappa, R, K)"),
      mutants=[Mu("const", ("9 / 4 * g + 7 / 4)", "9 / 4 * g + 5 / 3)"), dict(const="5/3"), "(l, g, h, j) = (3, 0, 6, 1): sigma = 4 = 9/4 + 7/4"),
               Mu("l", ("(hℓ : 3 ≤ ℓ)", "(hℓ : 2 ≤ ℓ)"), dict(l_min=2), "l = 2, g = h = 0, j = 1: sigma = 3 > 7/4", kind="hypothesis")],
      sharpness="sharp: equality at (l, g, h, j) = (3, 0, 6, 1) with r = R, kappa = K; the hypothesis 3 <= l is needed")

claim(id="C75", name="sigma_exponent_le_real", path="Formalism/TruncatedSeriesCounting/TruncatedSeriesProofs/ThmEExp.lean", line=7, topic="arithmetic",
      math="For natural l >= 3, g, h, j >= 1: sigE(l, g, h, j) <= (3/2)(h+2g)/(l-1)^(j+1) + (9/4) g + 11/4, with sigE = ceil((3g + M/l^(j-1)) l/(l-1)^2 + 1), M = floor((h+2g)/(l-1)) + 1.",
      conv=["natsub", "natdiv", "floor", "npow"],
      local_definitions=[dict(name="Mpar, sigE", where="Formalism/TruncatedSeriesCounting/AprimeArith.lean:8, :10",
                              text="def Mpar (ℓ g h : ℕ) : ℕ := (h + 2 * g) / (ℓ - 1) + 1\ndef sigE (ℓ g h j : ℕ) : ℕ :=\n  ⌈((3 * g : ℝ) + (Mpar ℓ g h : ℝ) / (ℓ : ℝ) ^ (j - 1)) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + 1⌉₊",
                              unfolded="Mpar is natural-number arithmetic; sigE is the Nat.ceil of the same quantity as in C74 plus 1")],
      quant="all natural l >= 3, g, h, j >= 1 (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.sigma_exponent", dict(const="11/4", l_min=3), route="exact rationals on 3 <= l <= 13, g <= 13, h <= 49, j <= 4"),
      mutants=[Mu("const", ("9 / 4 * g + 11 / 4", "9 / 4 * g + 12 / 5"), dict(const="12/5"), "(l, g, h, j) = (3, 0, 4, 1): sigE = 4 > 3/2 + 12/5")],
      sharpness="additive slack 1/4: the constant 11/4 could be 5/2 (equality at (3, 0, 4, 1)) and no less")

claim(id="C76", name="four_padicValNat_le", path="Formalism/GrowthSums/FactorialBaseGrowth/LogCoef.lean", line=19, topic="arithmetic",
      math="For a prime p >= 5 and natural s >= 1: 4 v_p(s) + 2 <= 3s.", conv=["padic"], quant="all primes p >= 5 and natural s >= 1 (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.four_padic", dict(add=2, p_min=5, N=200000), fast=dict(add=2, p_min=5, N=3000), route="exact integers, primes below 60"),
      mutants=[Mu("add", ("+ 2 ≤ 3 * s", "+ 4 ≤ 3 * s"), dict(add=4), "s = 1: 4 > 3")],
      sharpness="additive slack 1 (at s = 1); the hypothesis 5 <= p is not needed for truth")

claim(id="C77", name="coef_nat", path="Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean", line=778, topic="arithmetic",
      math="For natural A, o, s, j with s + j <= o: C(A, o) o! = C(A-s-j, o-s-j) (o-s-j)! (C(A-s, j) j!) (A)_s, every subtraction truncated and (A)_s the falling factorial.",
      conv=["natsub"], extra_conv=["when o > A both sides are 0; when s > A the falling factorial is 0"], quant="all natural A, o, s, j with s + j <= o (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.coef_nat", dict(N=14), fast=dict(N=8), route="exact integers with truncated subtraction"),
      mutants=[Mu("hyp", ("(hsj : s + j ≤ o)", "(hsj : s ≤ o)"), dict(require=False), "A = o = s = 0, j = 1: 1 != 0", kind="hypothesis")],
      sharpness="identity; the hypothesis s + j <= o is needed")

claim(id="C78", name="altVand", path="Formalism/MahlerMeasure/MahlerMeasureProofs/LevelSum.lean", line=7, topic="arithmetic",
      math="For natural B, z, l: sum_{j=0}^{l} (-1)^j C(B, j) C(z + B + l - j, l - j) = C(z + l, l), over Q.", conv=["natsub", "icc"],
      quant="all natural B, z, l (unbounded)", domain="unbounded", grade="measured_range",
      test=T("exact.alt_vandermonde", dict(sign=-1, N=24), fast=dict(sign=-1, N=10), route="exact integers"),
      mutants=[Mu("sign", ("(-1 : ℚ) ^ j", "(1 : ℚ) ^ j"), dict(sign=1), "B = 1, z = 0, l = 1: 3 != 1")],
      sharpness="identity")

claim(id="C79", name="hasSum_inv_succ_sq", path="Formalism/LogVandermondeBounds/LogVandermondeProofs/LogRatioLowerBoundOfLogVandermondeGap.lean", line=7, topic="zeta",
      math="sum_{n=0}^{oo} 1/(n+1)^2 = pi^2/6 (the series converges to that value).", conv=["npow"], quant="none (one identity)", domain="finite", grade="exact_finite",
      test=T("analytic.zeta_even_value", dict(k=1, D="6", N=1000000), fast=dict(k=1, D="6", N=50000),
             route="exact: B_2 = 1/6 gives the coefficient 1/6 (Euler); independent bracket S_N + 1/(N+1) < sum < S_N + 1/N of width 1e-12"),
      mutants=[Mu("D", ("(Real.pi ^ 2 / 6)", "(Real.pi ^ 2 / 7)"), dict(D="7"), "pi^2/7 lies outside the partial-sum bracket")],
      sharpness="identity")
