# Closure of the explicit-formula source leaf

**Verdict: externally proved in the exact required form.** Montgomery and Vaughan, Theorem 12.5, matches the inherited input (I4). Its hypotheses justify the dominated-convergence step in PR276 Lemma 3.1. This addendum closes the exact-source caveat in AUDIT.md; it does not authenticate or prove QRH(7/8).

## Authentication and exact locator

Hugh L. Montgomery and Robert C. Vaughan, *Multiplicative Number Theory I: Classical Theory*, Cambridge Studies in Advanced Mathematics 97, Cambridge University Press, first published 2006. Hardback ISBN 978-0-521-84903-6; eBook ISBN 978-0-511-25746-9. The inherited citation's 2007 year should be replaced by 2006 for this checked edition.

Primary text examined: chapter 12, section 12.1, printed pages 397 and 400-401. Theorem 12.5 is on printed page 400 (physical PDF page 419); its proof continues on printed page 401. The PDF's title and copyright pages identify the authors, publisher, year and ISBN. The source is the book itself, hosted by an institutional digital library, not a quotation in another paper.

- [Institutional full-text locator](https://ndl.ethernet.edu.et/bitstreams/dc06c9b5-e590-41c8-9f19-43a3e78c375f/download)
- [Montgomery's own book page](https://public.websites.umich.edu/~hlm/mnt1.html), reached through his publications list, independently matches title, authors, publisher and year.
- [Author-hosted errata](https://public.websites.umich.edu/~hlm/mnt1err.pdf), dated 28 January 2016, inspected: no entry changes printed pages 400-401 or this theorem.

Checked 2026-10-08. Local PDF SHA256:
`0b1129e66cba7c349eab6c1900c6e80408c02b9145f3167ef88a67564c62f191`.

Local inspection copy: source-cache/mv.pdf. Text extracted with `pdftotext -layout` to source-cache/mv.txt. A render of physical page 419 was visually inspected against the extraction. The local source cache is excluded from Git and must not be redistributed as part of research publication. Retention is the explicitly authorized local source-check copy.

## Source contract

The source defines psi0 on printed page 397 as the average of the right and left limits of psi. For any fixed c>1, its theorem applies to all real y>=c and all T>=2, with no upper restriction on T relative to y. Equations (12.3)-(12.4) say

    psi0(y) = y - sum_{rho: |Im rho|<=T} y^rho/rho
              - log(2*pi) - (1/2)*log(1-y^(-2)) + R(y,T),
    R(y,T) <<_c log(y)*min(1, y/(T*d(y)))
              + (y/T)*log(y*T)^2.

Here d(y) is the distance to the nearest prime power other than y itself, hence is positive even when y is a prime power. Zeros are counted with multiplicity. The theorem itself uses the inclusive ordinate truncation. Although its proof chooses an auxiliary height, the stated result holds for every T>=2.

## Independent application check

Fix the interval [x,x+h], with x>=2 and finite h>0, and set M=x+h. Choose c=2 once. The entire integration interval lies in the theorem's domain. Dependence of the unspecified implied constant on c is harmless; c is fixed independently of y and T.

For each fixed y in this interval, d(y)>0. The first error term tends to zero as T tends to infinity, including when y is a prime power. The second tends to zero because log(T)^2/T tends to zero. Thus R(y,T) tends to zero pointwise on the whole interval.

A dominating function independent of y and T is available without uniform convergence near prime powers. The first summand is at most log M. For T>=2,

    (y/T)*log(y*T)^2
    <= M * (2*log(M)^2/T + 2*log(T)^2/T)
    <= M * (log(M)^2 + 8/e^2).

The last inequality follows by maximizing log(T)^2/T at T=e^2. Consequently |R(y,T)| is bounded by a fixed finite constant on [x,M] for all T>=2. Multiplication by |w'(y)| gives an integrable dominating function, since the spline weight is C^1 with bounded derivative and compact support. Dominated convergence therefore gives integral R(y,T)w'(y)dy -> 0. No assumption of uniform convergence at prime powers was used.

The finite discontinuities of psi on this fixed compact interval have measure zero, so psi and psi0 have identical integrals against w'. The half-weight convention causes no residual endpoint term: w(x)=w(M)=0. Riemann-Stieltjes integration by parts yields sum Lambda(n)w(n)=-integral psi0(y)w'(y)dy.

For each finite truncated zero sum, integration by parts is legitimate term by term. The main term yields integral w=h; the constant contributes zero; each zero term yields -W(rho). Differentiating log(1-y^-2) gives 2/[y(y^2-1)], so the trivial-zero contribution is

    -tau, where tau = integral w(y)/[y(y^2-1)] dy.

The inherited three integrations by parts give W(rho)=O_{x,h}(|Im rho|^-3). With the independently authenticated zero-count estimate N(T)=O(T log T), a dyadic summation proves absolute convergence: the contribution from ordinates in [2^j,2^(j+1)] is O(j*2^(-2j)). Thus the limit of inclusive truncated smoothed zero sums equals the absolutely convergent zero sum, independently of ordering and of T coinciding with an ordinate.

It follows that, exactly as required,

    sum Lambda(n)w(n) = h - sum_rho W(rho) - tau,
    0 <= tau <= h/[x(x^2-1)].

Every source-to-application obligation is now checked: fixed lower domain, unbounded T, half-weights, inclusive truncation, pointwise remainder limit, an integrable dominating function, zero-sum absolute convergence, and sign of the trivial-zero term.

## Search and reproducibility boundary

Searched existing repository references/external directories first; no local copy was found. Inspected both authors' public publication pages and Montgomery's errata. General web search returned irrelevant results, so those results supplied no mathematical evidence. The parent then located the institutional copy. Web-reader retrieval failed, but the ordinary authorized network download succeeded. No account, credential, paid source, or external communication was used. A broad filesystem filename search was aborted after irrelevant/protected-directory results; it supplied no source evidence.

Reproduce extraction and page rendering locally:

```
shasum -a 256 audits/prime-gap/source-cache/mv.pdf
pdftotext -layout audits/prime-gap/source-cache/mv.pdf audits/prime-gap/source-cache/mv.txt
pdftoppm -f 419 -singlefile -scale-to 1800 -png audits/prime-gap/source-cache/mv.pdf audits/prime-gap/source-cache/theorem12-5
```

No replacement contour argument is needed. This authenticates the exact original dependency and leaves the conditional eighth-power conclusion with its original QRH assumption, standard published mathematical inputs, written proof and enclosure arithmetic. It remains non-kernel-checked.
