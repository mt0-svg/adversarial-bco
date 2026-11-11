<h1 align="center">Adversarial bandit convex optimisation: regret d<sup>3/2</sup>&radic;n with polynomial-time steps on a real RAM, and a matching lower bound</h1>

<p align="center">
  <a href="https://github.com/mt0-svg/adversarial-bco/releases/latest/download/adversarial-bco.pdf"><img alt="Paper" src="https://img.shields.io/badge/Paper-PDF-b31b1b"></a>
  <a href="https://doi.org/10.5281/zenodo.24115413"><img alt="DOI" src="https://zenodo.org/badge/DOI/10.5281/zenodo.24115413.svg"></a>
  <a href="https://mt0-svg.github.io/adversarial-bco/run.html"><img alt="Lean Proved" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Fadversarial-bco%2Fbadges%2Flean.json"></a>
  <a href="https://mt0-svg.github.io/adversarial-bco/run.html"><img alt="Lean Comparator" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Fadversarial-bco%2Fbadges%2Fcomparator.json"></a>
  <a href="LICENSE"><img alt="License" src="https://img.shields.io/badge/License-Apache%202.0-blue"></a>
</p>

<p align="center"><i>This is AI-generated research: the results, proofs and code were found and written by AI.<br>Credit goes to all the humans whose work it builds on.</i></p>

## The result

In adversarial bandit convex optimisation a learner plays $`n`$ rounds in a convex body of $`\mathbb R^d`$ against convex losses in $`[0,1]`$, seeing only its loss. Bubeck, Eldan and Lee conjectured that some learner whose rounds take time polynomial in $`d`$ and $`\ln n`$ on polytopes with polynomially many rational constraints has regret $`d^{3/2}\sqrt n`$ up to logarithms, and that none does better. In their game, against an adaptive adversary, we prove the first on their polytopes, timed on a real RAM with square root, exponential, logarithm, Gaussian draws and spectral functions: a learner has upper expected regret at most a constant times $`d^{3/2}\sqrt n\,\ln^5(2dn)`$. We prove the second on the unit ball: for $`d\ge4\cdot10^6`$, $`n\ge d^{10}`$ every learner has expected regret at least $`7\cdot10^{-9}d^{3/2}\sqrt n/\ln d`$ against some adversary. For fixed losses on bodies of diameter $`D`$ containing a unit ball, an explicit learner has expected regret $`O(d^{3/2}\sqrt n\,\ln^{3/2}(nD))`$.

The conjecture is Conjecture 1 of Bubeck, Eldan and Lee, [Kernel-based methods for bandit convex optimization](https://doi.org/10.1145/3453721), J. ACM 68 (2021) ([arXiv:1607.03084](https://arxiv.org/abs/1607.03084)).

```lean
theorem AdversarialBco.theoremConj1UpperExp : TheoremConj1UpperExp
theorem AdversarialBco.theoremConj1Upper : TheoremConj1Upper
theorem AdversarialBco.theoremConj1UpperPolyExp : TheoremConj1UpperPolyExp
theorem AdversarialBco.theoremConj1UpperPoly : TheoremConj1UpperPoly
theorem AdversarialBco.theoremConj1Lower : TheoremConj1Lower
theorem AdversarialBco.theoremPoly32O_holds : TheoremPoly32O
theorem AdversarialBco.Explicit.corollaryExplicit : CorollaryExplicit
```

`TheoremConj1UpperExp` (`AdversarialBco/StatementConj1Exp.lean`) is Theorem 1.1 of the paper: one program of the machine of `AdversarialBco/StatementPoly.lean`, which on every compact convex body between two balls, against every strategy that chooses each loss from the earlier plays and observations, plays in the body, makes its first play within a number of steps polynomial in $`d`$, $`\ln n`$ and $`\ln(R_0/r_0)`$ and every later play within a number polynomial in $`d`$ and $`\ln n`$; some measurable function above its regret on every run has expectation at most $`C d^{3/2}\sqrt n\,\ln^5(2dn(n+1))+1`$, a bound on the upper expectation of the positive part of the regret, since the statement does not assert that the regret is measurable. `TheoremConj1Upper` (`AdversarialBco/StatementConj1.lean`) is Remark 1.2, the bound in probability for a program that reads a confidence $`\delta`$: its regret exceeds $`C d^{3/2}\sqrt n\,\ln^5(2dn/\delta)`$ with probability at most $`\delta`$. `TheoremConj1UpperPoly` (`AdversarialBco/StatementConj1Poly.lean`) is Theorem 1.3 (a), the same bound on the polytopes of Bubeck, Eldan and Lee, given by their rational inequalities: a program with no membership question, run on the coefficients, makes each play within a number of steps polynomial in $`d`$, the number of inequalities and $`\ln(n/\delta)`$, the first play also in the logarithm of the height of the coefficients. `TheoremConj1UpperPolyExp` (`AdversarialBco/StatementConj1PolyExp.lean`) is Theorem 1.3 (b), the headline: on those polytopes, a program with no membership question, run with $`\delta=1/(n+1)`$, has the expected form of Theorem 1.1, with the bound $`C d^{3/2}\sqrt n\,\ln^5(2dn(n+1))+1`$ and every play within a number of steps polynomial in $`d`$, the number of inequalities and $`\ln n`$, the first also in the logarithm of the height of the coefficients. `TheoremConj1Lower` (`AdversarialBco/StatementConj1Lower.lean`) is Theorem 1.4: on the unit ball, for $`d\ge4\cdot10^6`$ and $`n\ge d^{10}`$, against every learner given by jointly measurable maps of a seed and its history, some strategy whose loss of round $`t`$ reads only the earlier plays and is $`\frac14`$-Lipschitz makes the expected regret at least $`7\cdot10^{-9}d^{3/2}\sqrt n/\ln d`$. `TheoremPoly32O` is the bound in probability for losses fixed in advance, with $`n`$ in the cost (Corollary 8.6, the (POLY) theorem). `CorollaryExplicit` is Corollary 1.6, the bound on the minimax regret for losses fixed in advance.

## What is checked

- **Lean 4.** The results are proved in Lean 4 with Mathlib, with no `sorry` and no axiom beyond `propext`, `Classical.choice` and `Quot.sound`:
  - Theorem 1.1: `AdversarialBco.theoremConj1UpperExp`, and from Remark 1.2, `AdversarialBco.theoremConj1UpperExp_of_conj1`;
  - Remark 1.2: `AdversarialBco.theoremConj1Upper`;
  - Theorem 1.3 (a): `AdversarialBco.theoremConj1UpperPoly`, and from Remark 1.2, `AdversarialBco.theoremConj1UpperPoly_of_conj1`;
  - Theorem 1.3 (b): `AdversarialBco.theoremConj1UpperPolyExp`, and from Theorem 1.3 (a), `AdversarialBco.theoremConj1UpperPolyExp_of_poly`;
  - Theorem 1.4: `AdversarialBco.theoremConj1Lower`;
  - Corollary 8.6, the (POLY) theorem: `AdversarialBco.theoremPoly32O_holds`, and from Remark 1.2, `AdversarialBco.theoremPoly32O_of_conj1`;
  - Theorem 1.5, with its constants and its bound against an adaptive adversary: `AdversarialBco.Explicit.theoremExplicit`;
  - Corollary 1.6: `AdversarialBco.Explicit.corollaryExplicit`, through Lemma 7.13: `AdversarialBco.Explicit.lemmaMarg`;
  - Proposition 2.2 with $`C_0=1.2\cdot10^9`$: `AdversarialBco.BodySpec.bodyExplicit`, and the form that Theorem 1.5 uses: `AdversarialBco.BodySpec.bodyHExplicit`;
  - Theorem 3.1 for every family: `AdversarialBco.BodySpec.dilTheorem`;
  - Corollary 1.6 for learners that are measurable maps of a seed and the observations, with a constant it does not give and $`n\ge2`$: `AdversarialBco.corollaryADV`.

  The statements are written out from the definitions of the paper in `AdversarialBco/StatementConj1Exp.lean`, `AdversarialBco/StatementConj1PolyExp.lean` over `AdversarialBco/StatementConj1Poly.lean`, `AdversarialBco/StatementConj1Poly.lean` and `AdversarialBco/StatementConj1Lower.lean` over `AdversarialBco/StatementConj1.lean` and `AdversarialBco/StatementPoly.lean`, `AdversarialBco/StatementExplicit.lean`, `AdversarialBco/StatementBody.lean` and `AdversarialBco/Statement.lean`; Section 11.1 of the paper explains them. Comparator checks each theorem against a copy of its statement file that imports only Mathlib (`config-conj1-exp.json`, `config-conj1.json`, `config-conj1-poly.json`, `config-conj1-poly-exp.json`, `config-conj1-lower.json`, `config-poly.json`, `config-explicit.json`, `config-body.json` and `config.json`), and nanoda, a second implementation of the Lean kernel, checks the proofs again. Every numerical constant of the paper is proved in Lean, and so is every other numbered statement; [`STATEMENTS.md`](STATEMENTS.md) gives the Lean declarations of each numbered statement.

The CI builds the package, reusing an earlier build from its cache or from the latest release. It fails on any other axiom, scans the sources for `sorry`, `admit` and `native_decide`, and runs Comparator with nanoda on each configuration, after building the package one module at a time in Comparator's sandbox. `release.yml` releases a tagged commit whose CI run, started by hand, is green; it attaches the PDF, the logs of that run and the Lake build that Comparator checked. A run started by hand on `main` writes the two badges.

## Layout

| Path | Content |
| --- | --- |
| `AdversarialBco/` | the Lean proof (Lean and Mathlib `v4.34.1`): `Conj1Exp/Main.lean`, `Conj1/Main.lean`, `Conj1Poly/Main.lean`, `Conj1PolyExp/Main.lean` and `Conj1Lower/Main.lean` prove Theorem 1.1, Remark 1.2, Theorem 1.3 (a) and (b) and Theorem 1.4, from `Conj1/` and `Conj1Exp/` (Section 8), `Conj1Poly/` and `Conj1PolyExp/` (Section 8.6) and `Conj1Lower/` (Section 9); `Poly/Poly32OFinal.lean` proves Corollary 8.6, from `Poly/` (Section 8 and Appendices D to F); `Explicit.lean` proves Theorem 1.5, Lemma 7.13 and Corollary 1.6, from `Explicit/` (Section 7, Lemma 7.13 and Appendix C); `Body2/Main.lean` proves Theorem 3.1 and Proposition 2.2, from `Body2/` (Sections 3 and 4); `Main.lean` proves Corollary 1.6 for measurable learners; `Lemmas.lean` is Lemma 2.1, Section 5, Section 7 and the reduction of that form to Proposition 2.2, `Body/` Section 3 and Proposition 2.2 with a constant not computed, `Gauss/` the Gaussian concentration of Appendix A |
| `AdversarialBco/Statement*.lean` | the definitions of the statements |
| `AdversarialBco/Challenge*.lean`, `config*.json` | the statements with `sorry` and the Comparator configurations |
| `paper/` | the TeX source |
| `code/formal-proof/` | the scripts of the CI (build, sequential build in the sandbox, axioms, badges) and the recorded outputs of Comparator |

## Check and reuse

Fast check, with the build of the release:

```sh
lake exe cache get          # Mathlib, from its cache
lake build :release         # this package, from the release archive
lake build --no-build       # nothing left to build
rm -f .lake/build/lib/lean/AdversarialBco/Challenge*.* .lake/build/ir/AdversarialBco/Challenge*.*
# then Comparator with each config*.json, as .github/workflows/ci.yml runs it
```

On the release tree each Comparator run, with nanoda on four cores, took between 69 and 178 seconds and at most 5210 MiB of memory; the outputs are in `code/formal-proof/comparator*.out`.

Full check, from source:

```sh
lake exe cache get && code/formal-proof/clean_build.sh
```

With Mathlib from its cache, `lake build` of the whole package from an empty build directory took 25 minutes on three cores of an AMD Ryzen 9 5900X, its largest process using 4.6 GiB.

As a dependency (Lean and Mathlib `v4.34.1`):

```toml
[[require]]
name = "adversarial-bco"
git = "https://github.com/mt0-svg/adversarial-bco"
rev = "v2.0.0"
```

then `lake update adversarial-bco`, `lake exe cache get` and `lake build`, which downloads the build archive of the release.

## Built on

- [Lean 4](https://github.com/leanprover/lean4) and [Mathlib](https://github.com/leanprover-community/mathlib4) (Apache 2.0): the formalization.
- [Comparator](https://github.com/leanprover/comparator), [lean4export](https://github.com/leanprover/lean4export) and [landrun](https://github.com/zouuup/landrun): the check of the statements in CI.
- [nanoda](https://github.com/ammkrn/nanoda_lib) of Chris Bailey (Apache 2.0): the second implementation of the Lean kernel, built by the CI, which Comparator runs to check again every declaration the theorems depend on.
- [Maiti2026Power](https://github.com/RemyDegenne/Maiti2026Power) of Rémy Degenne (Apache 2.0), commit `b9431dd9b3811779479d1ea108e51268eb7b24ce`: the argument of Maurey and Pisier for Gaussian concentration of continuously differentiable functions, in `AdversarialBco/Gauss/MaureyPisier.lean`, ported from `Maiti2026Power/ForLMLExplore/Probability/MaureyPisier.lean`, `.../Probability/GaussianMGF.lean`, `.../Analysis/Calculus/QuarterCircle.lean` and `.../Analysis/Calculus/Gradient.lean` (names moved into `AdversarialBco.Gauss`, `ContDiff.continuous_gradient` renamed `continuous_gradient_of_contDiff`, the `IsGaussian.` prefixes of the exponential moment lemmas dropped; no proof changed).
- [Tau Ceti](https://github.com/TauCetiProject/TauCeti) (Apache 2.0), commit `e0610cce4004d628cbd9d2aafdbbb5459fe72938`: `ContDiff.gradient_right` (`TauCeti/Analysis/Calculus/Gradient.lean`) and `IsGaussian.mgf_dual` (`TauCeti/Probability/Distributions/Gaussian/Transforms.lean`), in `AdversarialBco/Gauss/MaureyPisier.lean` as `contDiff_gradient_right` and `mgf_dual` (no proof changed).

## Citation

```bibtex
@misc{adversarial-bco,
  title     = {Adversarial bandit convex optimisation: regret $d^{3/2}\sqrt{n}$ with polynomial-time steps on a real {RAM}, and a matching lower bound},
  author    = {{mt0-svg}},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.24115413},
  url       = {https://doi.org/10.5281/zenodo.24115413}
}
```

## Contact

Questions and corrections: [open an issue](https://github.com/mt0-svg/adversarial-bco/issues/new/choose).

## License

Apache 2.0 (`LICENSE`, `NOTICE`).
