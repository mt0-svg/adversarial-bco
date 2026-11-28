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

In adversarial bandit convex optimisation a learner plays $`n`$ rounds in a convex body of $`\mathbb R^d`$ against convex losses with values in $`[0,1]`$, chosen by an adversary that sees the whole past, and observes only its loss, possibly with a subgaussian noise. We give a program of a random access machine with a weak membership oracle which, on every convex body given by such an oracle and two rational balls and for every rational $`\delta\in(0,1)`$ that it reads, plays each round in time polynomial in $`d`$, $`\ln n`$ and the bit lengths of $`\delta`$ and of the balls. With probability at least $`1-\delta`$ its regret is at most a constant times $`d^{3/2}\sqrt n\ln^5(2dn)+d\sqrt{n\ln(2/\delta)}\ln^{9/2}(2dn)`$, and the mean of its positive part is at most that bound plus $`n\delta`$. For $`d\ge4\cdot10^6`$, $`n\ge d^{10}`$, $`\delta<\frac12`$ and $`\ln(1/\delta)\le n/d^6`$, the minimax $`(1-\delta)`$-quantile of the regret on every such body is at least a constant times $`d^{3/2}\sqrt n/\ln d+d\sqrt{n\ln(1/\delta)}/(\ln d\sqrt{\ln n})`$, which the program attains up to a factor polylogarithmic in $`d`$ and $`n`$, and the minimax mean of the positive part of the regret at least a constant times $`d^{3/2}\sqrt n/\ln d`$, which the program attains up to such a factor at $`\delta=1/n`$. On the rational polytopes of Bubeck, Eldan and Lee a program of the same machine without an oracle has expected regret at most a constant times $`d^{3/2}\sqrt n\ln^5(2dn)`$, which with the lower bound on the cube proves their Conjecture 1 in their game, against an adversary that chooses each loss from the earlier plays, with time counted in bit operations. All proofs are formalized in Lean 4.

The question is Conjecture 1 of Bubeck, Eldan and Lee, [Kernel-based methods for bandit convex optimization](https://doi.org/10.1145/3453721), J. ACM 68 (2021) ([arXiv:1607.03084](https://arxiv.org/abs/1607.03084)). The upper bound holds on every convex body given by a weak membership oracle and two rational balls, and on the polytopes of their conjecture given by their constraints, with no oracle; the lower bound in mean holds on the cube, one of these polytopes. The regret $`d^{3/2}\sqrt n`$ up to logarithms against an adaptive adversary was obtained first by Bakhtiari, Jamieson, Lattimore and Ratliff, [arXiv:2611.33531](https://arxiv.org/abs/2611.33531).

```lean
theorem AdversarialBco.theoremUnified : TheoremUnified
theorem AdversarialBco.LowerDeltaQ.theoremLowerUDQ : TheoremLowerUDQ
theorem AdversarialBco.LowerDeltaQ.theoremLowerUDProgQ : TheoremLowerUDProgQ
theorem AdversarialBco.LowerDeltaQ.theoremMinimaxQ : TheoremMinimaxQ
theorem AdversarialBco.UW.theoremUW : TheoremUW
theorem AdversarialBco.Grow.theoremGrowG : TheoremGrowG
theorem AdversarialBco.Grow.theoremGrowGProg : TheoremGrowGProg
theorem AdversarialBco.Matched.theoremMinimaxMatched : TheoremMinimaxMatched
theorem AdversarialBco.theoremConj1UpperBitHP : TheoremConj1UpperBitHP
theorem AdversarialBco.theoremConj1LowerPolyDQ_holds : TheoremConj1LowerPolyDQ
theorem AdversarialBco.theoremConj1Upper : TheoremConj1Upper
```

`TheoremUnified` (`AdversarialBco/StatementUnified.lean`, over the machine of `AdversarialBco/StatementBitRAMO.lean`) is Theorem 1.2 of the paper: one program of the random access machine with logarithmic cost and a weak membership oracle, with its cost, space, play and coin clauses against every sequence of losses, noises and coins, and its regret bound with probability $`1-\delta`$ and in mean for every environment with its windows (Definition 1.1). `TheoremUW` (`AdversarialBco/StatementUW.lean`) is Theorem 1.5, the bound matched in $`\delta`$, of which Theorem 1.2 is a corollary. `TheoremLowerUDQ` and `TheoremLowerUDProgQ` are Theorem 1.3, the lower bound with probability $`1-\delta`$ and in mean, for every learner and for every program of the same machine; `TheoremMinimaxQ` is Theorem 1.4, the minimax values; `TheoremConj1LowerPolyDQ` is the lower half of Corollary 1.8, on the cube; all four in `AdversarialBco/StatementMinimaxQ.lean`. `TheoremConj1UpperBitHP` (`AdversarialBco/StatementConj1BitHP.lean`, over the machine without an oracle of `AdversarialBco/StatementBitRAM.lean`) is the upper half of Corollary 1.8: one program that reads the constraints of a rational polytope of the conjecture, with its cost and space per round, and its regret in mean and with probability $`1-1/n`$ against every randomised adversary without noise. `TheoremGrowG` and `TheoremGrowGProg` are Theorem 1.6, the lower bound that grows with $`\ln(1/\delta)`$, and `TheoremMinimaxMatched` is Theorem 1.7, the minimax values matched in $`\delta`$, in `AdversarialBco/StatementMatched.lean`. `TheoremConj1Upper` (`AdversarialBco/StatementConj1.lean`) is Theorem 3.2, the learner on a machine with exact real arithmetic.

## What is checked

- **Lean 4.** The results are proved in Lean 4 with Mathlib, with no `sorry` and no axiom beyond `propext`, `Classical.choice` and `Quot.sound`: Theorem 1.2 (`AdversarialBco.theoremUnified`), Theorem 1.3 (`AdversarialBco.LowerDeltaQ.theoremLowerUDQ` and `theoremLowerUDProgQ`), Theorem 1.4 (`AdversarialBco.LowerDeltaQ.theoremMinimaxQ`), Theorem 1.5 (`AdversarialBco.UW.theoremUW`), Theorem 1.6 (`AdversarialBco.Grow.theoremGrowG` and `theoremGrowGProg`), Theorem 1.7 (`AdversarialBco.Matched.theoremMinimaxMatched`), Corollary 1.8 (`AdversarialBco.theoremConj1UpperBitHP` and `AdversarialBco.theoremConj1LowerPolyDQ_holds`) and Theorem 3.2 (`AdversarialBco.theoremConj1Upper`).

  The statements are written out from the definitions of the paper in the `AdversarialBco/Statement*.lean` files; Section 8.1 of the paper explains them. Comparator checks each theorem against a copy of its statement files that imports only Mathlib (the six `config-*.json` files), and nanoda, a second implementation of the Lean kernel, checks the proofs again. The CI builds nanoda at its pinned commit with a one-line patch, `.github/nanoda-stack.patch`, which raises the stack of its worker threads from 16 MiB to 256 MiB, as a declaration of the proof of Theorem 1.5 needs, and changes no check. Next to each theorem, Comparator checks witnesses that its hypotheses can be met, so that none holds vacuously. Every other numbered statement of the paper is a step of these proofs; [`STATEMENTS.md`](STATEMENTS.md) gives the Lean declarations of each one.

The CI builds the package, reusing an earlier build from its cache or from the latest release. It fails on any other axiom, scans the sources for `sorry`, `admit` and `native_decide`, and runs Comparator with nanoda on each configuration.

## Layout


| Path | Content |
| --- | --- |
| `AdversarialBco/` | the Lean proof (Lean and Mathlib `v4.34.1`): `UW/` the weighted learner, the program BL-OW and the proof of Theorem 1.5, with Theorem 1.2 as its corollary (Section 5 and Appendix G); `Unified/` and `Bit/` the program BL-O and the machine with the oracle on which BL-OW is built (Section 4 and Appendix E); `Poly/` the reference learner and its regret (Section 2 and Appendices A to D); `Conj1/` Theorem 3.2 (Section 3 and Appendix F), and `Conj1Arith/`, `Conj1Exp/` and `Conj1Poly/` the parts its proof shares with the others; `Conj1BitHP/`, `Conj1Bit/` and the `Poly*` files of `Unified/` the program on a polytope and the upper half of Corollary 1.8 (Section 4.12 and Appendix E); `LowerDelta/`, `LowerDeltaQ/`, `Lower/`, `UnifiedLower/`, `Conj1Lower/`, `Conj1LowerPolyD/` and `Grow/` the lower bounds and Corollary 1.8 (Section 6 and Appendix H); `Minimax/` and `Matched/` the minimax values of Theorems 1.4 and 1.7; `Body/`, `Body2/`, `Gauss/` and `Lemmas.lean` tools on Gaussian laws and convex sets, with Gaussian concentration and the lemmas of Maiti2026Power listed under Built on |
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
# then Comparator with each config-*.json, as .github/workflows/ci.yml runs it
```

On one machine, Comparator with nanoda at 4 threads takes between 213 s and 373 s per configuration (unified 319 s, uw 328 s, minimax-q 348 s, matched 373 s, conj1-bit-hp 317 s, conj1 213 s), with a memory peak of 11 GiB: a Comparator job needs a runner with at least 12 GiB of memory, 16 GiB to be safe. The full build from an empty build directory takes 73 min at 3 threads, with a peak of 8.3 GiB. The outputs of Comparator, with those of every other check of the CI run, are in `verification-v2.4.0.tar.gz`, an asset of the release.

Full check, from source:

```sh
lake exe cache get && code/formal-proof/clean_build.sh
rm -f .lake/build/lib/lean/AdversarialBco/Challenge*.* .lake/build/ir/AdversarialBco/Challenge*.*
# then Comparator with each config-*.json, as for the fast check
```

As a dependency (Lean and Mathlib `v4.34.1`):

```toml
[[require]]
name = "adversarial-bco"
git = "https://github.com/mt0-svg/adversarial-bco"
rev = "v2.4.0"
```

then `lake update adversarial-bco`, `lake exe cache get` and `lake build`, which downloads the build archive of the release.

## Versions

Version 2.4 implies the theorems of the earlier versions, with no hypothesis the earlier ones did not carry, except in four places:

- the bound in mean of the lower bound has the constant $`3.71\cdot10^{-9}`$, read from the bound with probability at $`\delta=\frac12`$, where versions 2.0 to 2.3 state $`7\cdot10^{-9}`$;
- the upper bounds carry $`\ln^5`$ where version 1.0 has $`\ln^{3/2}`$, and the minimax corollaries of version 1.0, over its own classes of learners, are not restated;
- the upper bound of version 2.0 on the polytopes of Bubeck, Eldan and Lee (its Theorem 1.3), on the real RAM with a noise and every confidence $`\delta`$, is not carried; Corollary 1.8 states the upper bound on these polytopes on the random access machine without an oracle and without noise, as versions 2.1 to 2.3 do;
- the one-round inequality of version 1.0 (its Proposition 2.2, Theorem 3.1 and Lemma 7.13) has no counterpart.

## Built on

- [Lean 4](https://github.com/leanprover/lean4) and [Mathlib](https://github.com/leanprover-community/mathlib4) (Apache 2.0): the formalization.
- [Comparator](https://github.com/leanprover/comparator), [lean4export](https://github.com/leanprover/lean4export) and [landrun](https://github.com/zouuup/landrun): the check of the statements in CI.
- [nanoda](https://github.com/ammkrn/nanoda_lib) of Chris Bailey (Apache 2.0): the second implementation of the Lean kernel, built by the CI with the stack patch above, which Comparator runs to check again every declaration the theorems depend on.
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
