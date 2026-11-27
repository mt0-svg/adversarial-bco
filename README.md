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

In adversarial bandit convex optimisation a learner plays $`n`$ rounds in a convex body of $`\mathbb R^d`$ against convex losses with values in $`[0,1]`$, and observes only its loss, possibly with a noise. We give one program of a random access machine with logarithmic cost and a weak membership oracle which, on every convex body $`\mathcal K`$ given by such an oracle and by two rational balls $`B(a,r_0)\subset\mathcal K\subset B(a,R_0)`$, and for every rational confidence $`\delta`$ that it reads, plays each round in a number of bit operations polynomial in $`d`$, $`\ln n`$ and the bit length of $`\delta`$, $`a`$, $`r_0`$ and $`R_0`$. With probability at least $`1-\delta`$ its regret is at most a constant times $`d^{3/2}\sqrt n\,\ln^5(2dn/\delta)`$, and the mean of its positive part is at most that bound plus $`n\delta`$. The adversary chooses each loss from the whole past, the earlier random bits of the learner included, and the noise of a round has mean $`0`$ and $`\mathbb E\,e^{\varepsilon^2}\le2`$ given the past and the draw of the learner in that round. On every such body, for $`d\ge4\cdot10^6`$ and $`n\ge d^{10}`$, every learner has regret at least $`7\cdot10^{-9}d^{3/2}\sqrt n/\ln d`$ in mean, and at least $`2.8\cdot10^{-9}d^{3/2}\sqrt n/\ln d`$ with probability at least $`\frac12`$, against some adversary of the same kind without noise. On the rational polytopes of Bubeck, Eldan and Lee a program of the same machine without an oracle has expected regret at most a constant times $`d^{3/2}\sqrt n\,\ln^5(2dn)`$, which with the lower bound on the cube proves their Conjecture 1 in their game, against an adversary that chooses each loss from the earlier plays, with time counted in bit operations.

The conjecture is Conjecture 1 of Bubeck, Eldan and Lee, [Kernel-based methods for bandit convex optimization](https://doi.org/10.1145/3453721), J. ACM 68 (2021) ([arXiv:1607.03084](https://arxiv.org/abs/1607.03084)). The regret $`d^{3/2}\sqrt n`$ up to logarithms against an adaptive adversary was obtained first by Bakhtiari, Jamieson, Lattimore and Ratliff, [arXiv:2611.33531](https://arxiv.org/abs/2611.33531).

```lean
theorem AdversarialBco.theoremUnified : TheoremUnified
theorem AdversarialBco.theoremLowerU : TheoremLowerU
theorem AdversarialBco.theoremLowerUProg : TheoremLowerUProg
theorem AdversarialBco.corollaryMatch : CorollaryMatch
theorem AdversarialBco.theoremConj1UpperBitHP : TheoremConj1UpperBitHP
theorem AdversarialBco.theoremConj1LowerPoly_holds : TheoremConj1LowerPoly
theorem AdversarialBco.theoremConj1Upper : TheoremConj1Upper
```

`TheoremUnified` (`AdversarialBco/StatementUnified.lean`, over the machine of `AdversarialBco/StatementBitRAMO.lean`) is Theorem 1.2 of the paper: one program of the random access machine with logarithmic cost and a weak membership oracle, with its cost, space, play and coin clauses against every sequence of losses, noises and coins, and its regret bound in probability and in mean for every environment with its windows (Definition 1.1). `TheoremLowerU` and `TheoremLowerUProg` (`AdversarialBco/StatementUnifiedLower.lean`) are Theorem 1.3, for every learner and for every program of the same machine; `CorollaryMatch` (same file) is Corollary 1.4, the two bounds for one program. `TheoremConj1UpperBitHP` (`AdversarialBco/StatementConj1BitHP.lean`) and `TheoremConj1LowerPoly` (`AdversarialBco/StatementConj1LowerPoly.lean`) are the two halves of Corollary 1.5 on the polytopes of Bubeck, Eldan and Lee. `TheoremConj1Upper` (`AdversarialBco/StatementConj1.lean`) is Theorem 3.2, the learner on a machine with exact real arithmetic.

## What is checked

- **Lean 4.** The results are proved in Lean 4 with Mathlib, with no `sorry` and no axiom beyond `propext`, `Classical.choice` and `Quot.sound`: Theorem 1.2 (`AdversarialBco.theoremUnified`), Theorem 1.3 (`AdversarialBco.theoremLowerU` and `AdversarialBco.theoremLowerUProg`), Corollary 1.4 (`AdversarialBco.corollaryMatch`), Corollary 1.5 (`AdversarialBco.theoremConj1UpperBitHP` and `AdversarialBco.theoremConj1LowerPoly_holds`) and Theorem 3.2 (`AdversarialBco.theoremConj1Upper`).

  The statements are written out from the definitions of the paper in the `AdversarialBco/Statement*.lean` files; Section 7.1 of the paper explains them. Comparator checks each theorem against a copy of its statement files that imports only Mathlib (the `config-*.json` files), and nanoda, a second implementation of the Lean kernel, checks the proofs again. Next to each theorem, Comparator checks witnesses that its hypotheses can be met, so that none holds vacuously. Every other numbered statement of the paper is a step of these proofs; [`STATEMENTS.md`](STATEMENTS.md) gives the Lean declarations of each one.

The CI builds the package, reusing an earlier build from its cache or from the latest release. It fails on any other axiom, scans the sources for `sorry`, `admit` and `native_decide`, and runs Comparator with nanoda on each configuration, after building the package one module at a time in Comparator's sandbox.

## Layout

| Path | Content |
| --- | --- |
| `AdversarialBco/` | the Lean proof (Lean and Mathlib `v4.34.1`): `Unified/` the program BL-O, its machine with the oracle and its analysis (Section 4 and Appendix E), and in `Unified/Poly*.lean` the compiler of Corollary 1.5 from the program of Theorem 1.2 to the machine without an oracle on polytopes; `UnifiedLower/` the lower bound on every body and for every program (Section 5 and Appendix G); `Poly/` and `Conj1/` the reference learner and its regret (Section 2 and Appendices A to C); `Bit/` the parts of the program on the bit RAM that BL-O shares with the program on polytopes; `Conj1BitHP/` and `Conj1LowerPoly/` Corollary 1.5; `Gauss/` Gaussian concentration, with the lemmas of Maiti2026Power listed under Built on |
| `AdversarialBco/Statement*.lean` | the definitions of the statements |
| `AdversarialBco/Challenge*.lean`, `AdversarialBco/ChallengeBase/`, `config-*.json` | the Comparator challenges (the statement files copied by `code/formal-proof/challenges.sh`, the theorems with `sorry`) and the Comparator configurations |
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

On one machine, Comparator with nanoda at 4 threads takes between 101 s and 336 s per configuration (unified 336 s, unified-lower 151 s, match 331 s, conj1-bit-hp 329 s, conj1 222 s, conj1-lower-poly 101 s), with a memory peak of 11 GiB: a Comparator job needs a runner with at least 12 GiB of memory, 16 GiB to be safe. The full build from an empty build directory takes 66 min at 3 threads, with a peak of 8.3 GiB.
The outputs of Comparator, with those of every other check of the CI run, are in `verification-v2.3.0.tar.gz`, an asset of the release.

Full check, from source:

```sh
lake exe cache get && code/formal-proof/clean_build.sh
rm -f .lake/build/lib/lean/AdversarialBco/Challenge*.* .lake/build/ir/AdversarialBco/Challenge*.*
# then Comparator with each config*.json, as for the fast check
```

As a dependency (Lean and Mathlib `v4.34.1`):

```toml
[[require]]
name = "adversarial-bco"
git = "https://github.com/mt0-svg/adversarial-bco"
rev = "v2.3.0"
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
