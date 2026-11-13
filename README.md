<h1 align="center">Optimal regret for adversarial bandit convex optimisation in polynomial time</h1>

<p align="center">
  <a href="https://github.com/mt0-svg/adversarial-bco/releases/latest/download/adversarial-bco.pdf"><img alt="Paper" src="https://img.shields.io/badge/Paper-PDF-b31b1b"></a>
  <a href="https://doi.org/10.5281/zenodo.24115413"><img alt="DOI" src="https://zenodo.org/badge/DOI/10.5281/zenodo.24115413.svg"></a>
  <a href="https://mt0-svg.github.io/adversarial-bco/run.html"><img alt="Lean Proved" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Fadversarial-bco%2Fbadges%2Flean.json"></a>
  <a href="https://mt0-svg.github.io/adversarial-bco/run.html"><img alt="Lean Comparator" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Fadversarial-bco%2Fbadges%2Fcomparator.json"></a>
  <a href="LICENSE"><img alt="License" src="https://img.shields.io/badge/License-Apache%202.0-blue"></a>
</p>

<p align="center"><i>This is AI-generated research: the results, proofs and code were found and written by AI.<br>Credit goes to all the humans whose work it builds on.</i></p>

## The result

In adversarial bandit convex optimisation a learner plays $`n`$ rounds in a convex body of $`\mathbb R^d`$ against convex losses in $`[0,1]`$, seeing only its loss. Bubeck, Eldan and Lee conjectured that on rational polytopes some learner whose rounds take time polynomial in $`d`$ and $`\ln n`$ has expected regret $`\tilde O(d^{3/2}\sqrt n)`$, and that none does better. We prove both in their game, against an adversary that sees the earlier plays. On each such polytope, given by $`m`$ rational constraints with numerators and denominators at most $`M`$ in absolute value, a program on a random access machine with logarithmic cost plays each round in a number of bit operations polynomial in $`d`$, $`m`$, $`\ln n`$ and $`\ln M`$, with expected regret at most a constant times $`d^{3/2}\sqrt n\,\ln^5(2dn)`$. On the cube, for $`d\ge4\cdot10^6`$ and $`n\ge d^{10}`$, every learner has expected regret at least $`7\cdot10^{-9}d^{3/2}\sqrt n/\ln d`$ against some adversary.

The conjecture is Conjecture 1 of Bubeck, Eldan and Lee, [Kernel-based methods for bandit convex optimization](https://doi.org/10.1145/3453721), J. ACM 68 (2021) ([arXiv:1607.03084](https://arxiv.org/abs/1607.03084)).

```lean
theorem AdversarialBco.theoremConj1UpperBit : TheoremConj1UpperBit
theorem AdversarialBco.theoremConj1UpperBitExp : TheoremConj1UpperBitExp
theorem AdversarialBco.theoremConj1LowerPoly_holds : TheoremConj1LowerPoly
```

`TheoremConj1UpperBit` (`AdversarialBco/StatementConj1Bit.lean`) is Theorem 1.1 of the paper: one program of the random access machine with logarithmic cost of `AdversarialBco/StatementBitRAM.lean`, which reads $`d`$, $`n`$, $`m`$ and the rational constraints of a polytope that contains a ball of radius $`1`$ and has diameter at most $`n`$, and nothing else. Against every randomised adversary that chooses each loss from the earlier plays, it plays every round at a rational point of the polytope within cost $`C'(dm\ln(2dn)\ln(2M))^k`$, where $`M`$ bounds the numerators and denominators of the constraints, with memory under the same bound; some measurable function above its regret on every run has expectation at most $`C d^{3/2}\sqrt n\,\ln^5(2dn)`$, a bound on the upper expectation of the positive part of the regret. `TheoremConj1UpperBitExp` (`AdversarialBco/StatementConj1BitExp.lean`) is Corollary 1.2: a program with the same cost, space and play clauses whose regret is integrable, with expectation at most $`C d^{3/2}\sqrt n\,\ln^5(2dn)`$. `TheoremConj1LowerPoly` (`AdversarialBco/StatementConj1LowerPoly.lean`) is Theorem 1.3: for $`d\ge4\cdot10^6`$ some polytope with $`2d`$ constraints of height $`1`$ that contains a ball of radius $`1`$ (the cube $`[-1,1]^d`$) has, for every $`n\ge d^{10}`$ and every learner given by jointly measurable maps of a seed and its history, a strategy whose loss of round $`t`$ reads only the earlier plays and is $`\frac14`$-Lipschitz, against which the expected regret is at least $`7\cdot10^{-9}d^{3/2}\sqrt n/\ln d`$.

## What is checked

- **Lean 4.** The results are proved in Lean 4 with Mathlib, with no `sorry` and no axiom beyond `propext`, `Classical.choice` and `Quot.sound`:
  - Theorem 1.1: `AdversarialBco.theoremConj1UpperBit`;
  - Corollary 1.2: `AdversarialBco.theoremConj1UpperBitExp`, from Theorem 1.1 by `AdversarialBco.theoremConj1UpperBit_exp`;
  - Theorem 1.3: `AdversarialBco.theoremConj1LowerPoly_holds`.

  The statements are written out from the definitions of the paper in `AdversarialBco/StatementConj1Bit.lean` over `AdversarialBco/StatementBitRAM.lean`, `AdversarialBco/StatementConj1BitExp.lean` and `AdversarialBco/StatementConj1LowerPoly.lean`; Section 5.1 of the paper explains them. Comparator checks each theorem against a copy of its statement file that imports only Mathlib (`config-conj1-bit.json`, `config-conj1-bit-exp.json` and `config-conj1-lower-poly.json`), and nanoda, a second implementation of the Lean kernel, checks the proofs again. Next to each theorem, Comparator checks a witness that the hypotheses of the theorem can be met, so that none of the three holds vacuously. Every numerical constant of the paper is proved in Lean, and so is every other numbered statement; [`STATEMENTS.md`](STATEMENTS.md) gives the Lean declarations of each numbered statement.

The CI builds the package, reusing an earlier build from its cache or from the latest release. It fails on any other axiom, scans the sources for `sorry`, `admit` and `native_decide`, and runs Comparator with nanoda on each configuration, after building the package one module at a time in Comparator's sandbox.

## Layout

| Path | Content |
| --- | --- |
| `AdversarialBco/` | the Lean proof (Lean and Mathlib `v4.34.1`), the import closure of the three theorems: `Conj1Bit/Main.lean`, `Conj1BitExp/Main.lean` and `Conj1LowerPoly/Main.lean` prove Theorem 1.1, Corollary 1.2 and Theorem 1.3; `Bit/` the program BL, its machine and its analysis (Section 2 and Appendices A and E to H); `Poly/` and `Conj1/` the reference learner and its regret (Sections 2.2 to 2.4 and Appendices C and D); `Conj1Poly/` the geometry of a rational polytope (Lemma 2.9); `Conj1Exp/` and `Conj1PolyExp/` the bound on the regret and its measurable majorant (Section 2.12); `Conj1Lower/` and `Conj1LowerPoly/` the lower bound (Section 3 and Appendix B); `Gauss/` Gaussian concentration (Appendix C), with the lemmas of Maiti2026Power listed under Built on; `Body/`, `Body2/` and `Lemmas.lean` Gaussian identities, convexity lemmas and definitions that these modules import |
| `AdversarialBco/Statement*.lean` | the definitions of the statements |
| `AdversarialBco/Challenge*.lean`, `AdversarialBco/ChallengeBase/`, `config-conj1-bit.json`, `config-conj1-bit-exp.json`, `config-conj1-lower-poly.json` | the Comparator challenges (the statement files copied by `code/formal-proof/challenges.sh`, the theorems with `sorry`) and the three Comparator configurations |
| `paper/` | the TeX source |
| `code/formal-proof/` | the scripts of the CI (build, sequential build in the sandbox, challenges, axioms, badges); `code/README.md` describes them |

## Check and reuse

Fast check, with the build of the release:

```sh
lake exe cache get          # Mathlib, from its cache
lake build :release         # this package, from the release archive
lake build --no-build       # nothing left to build
rm -f .lake/build/lib/lean/AdversarialBco/Challenge*.* .lake/build/ir/AdversarialBco/Challenge*.*
# then Comparator with each config*.json, as .github/workflows/ci.yml runs it
```

On the release tree, Comparator with nanoda ran in 226 s of wall time for `config-conj1-bit.json`, 294 s for `config-conj1-bit-exp.json` and 75 s for `config-conj1-lower-poly.json`.
The outputs of Comparator, with those of every other check of the CI run, are in `verification-v2.1.0.tar.gz`, an asset of the release.

Full check, from source:

```sh
lake exe cache get && code/formal-proof/clean_build.sh
rm -f .lake/build/lib/lean/AdversarialBco/Challenge*.* .lake/build/ir/AdversarialBco/Challenge*.*
# then Comparator with each config*.json, as for the fast check
```

From an empty build directory, with Mathlib from its cache, `lake build` ran in 39 min 44.68 s of wall time.

As a dependency (Lean and Mathlib `v4.34.1`):

```toml
[[require]]
name = "adversarial-bco"
git = "https://github.com/mt0-svg/adversarial-bco"
rev = "v2.1.0"
```

then `lake update adversarial-bco`, `lake exe cache get` and `lake build`, which downloads the build archive of the release.

## Built on

- [Lean 4](https://github.com/leanprover/lean4) and [Mathlib](https://github.com/leanprover-community/mathlib4) (Apache 2.0): the formalization.
- [Comparator](https://github.com/leanprover/comparator), [lean4export](https://github.com/leanprover/lean4export) and [landrun](https://github.com/zouuup/landrun): the check of the statements in CI.
- [nanoda](https://github.com/ammkrn/nanoda_lib) of Chris Bailey (Apache 2.0): the second implementation of the Lean kernel, built by the CI, which Comparator runs to check again every declaration the theorems depend on.
- [Maiti2026Power](https://github.com/RemyDegenne/Maiti2026Power) of Rémy Degenne (Apache 2.0), commit `b9431dd9b3811779479d1ea108e51268eb7b24ce`: gradient bounds and integrability under Gaussian laws, in `AdversarialBco/Gauss/Integrability.lean`, ported from `Maiti2026Power/ForLMLExplore/Probability/GaussianMGF.lean` and `.../Analysis/Calculus/Gradient.lean` (names moved into `AdversarialBco.Gauss`, the `IsGaussian.` prefixes of the exponential moment lemmas dropped; no proof changed).

## Citation

```bibtex
@misc{adversarial-bco,
  title     = {Optimal regret for adversarial bandit convex optimisation in polynomial time},
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
