<h1 align="center">Adversarial bandit convex optimisation with regret d<sup>3/2</sup>&radic;n up to logarithms</h1>

<p align="center">
  <a href="https://github.com/mt0-svg/adversarial-bco/releases/latest/download/adversarial-bco.pdf"><img alt="Paper" src="https://img.shields.io/badge/Paper-PDF-b31b1b"></a>
  <a href="https://doi.org/10.5281/zenodo.24115413"><img alt="DOI" src="https://zenodo.org/badge/DOI/10.5281/zenodo.24115413.svg"></a>
  <a href="https://mt0-svg.github.io/adversarial-bco/run.html"><img alt="Lean Proved" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Fadversarial-bco%2Fbadges%2Flean.json"></a>
  <a href="https://mt0-svg.github.io/adversarial-bco/run.html"><img alt="Lean Comparator" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Fmt0-svg%2Fadversarial-bco%2Fbadges%2Fcomparator.json"></a>
  <a href="LICENSE"><img alt="License" src="https://img.shields.io/badge/License-Apache%202.0-blue"></a>
</p>

<p align="center"><i>This is AI-generated research: the results, proofs and code were found and written by AI.<br>Credit goes to all the humans whose work it builds on.</i></p>

## The result

In adversarial bandit convex optimisation a learner plays points of a convex body in $`d`$ dimensions for $`n`$ rounds against convex losses with values in $`[0,1]`$ chosen in advance, observing only the loss at the point played. When the body contains a unit ball and has diameter $`D`$, we give a learner whose expected regret, like the minimax regret, is at most a constant times $`d^{3/2}\sqrt n\,\ln^{3/2}(nD)`$; the best bound known had $`d^{5/2}`$. The new step is a one-round inequality: for every finitely supported law on convex $`n`$-Lipschitz losses, some law on the body has regret at most $`1/n`$ plus the square root of $`d^2`$ times the variance of the losses under it, up to logarithms, where $`d^4`$ was known. The learner, exploration by optimisation with the observation replaced by a coin, is explicit.

The best bound known was Theorem 1 of Lattimore, [Improved regret for zeroth-order adversarial bandit convex optimisation](https://doi.org/10.4171/MSL/17), Math. Stat. Learn. 2 (2020) ([arXiv:2006.00475](https://arxiv.org/abs/2006.00475)).

```lean
def AdversarialBco.Explicit.CorollaryExplicit : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ K : Set (E d), IsCompact K → Convex ℝ K → (∃ c : E d, Metric.closedBall c 1 ⊆ K) →
    ∀ n : ℕ, 1 ≤ n →
      minimaxRegretC K n ≤
        190000 * (d : ℝ) ^ (3 / 2 : ℝ) * √(n : ℝ) * Real.log (n * Metric.diam K) ^ (3 / 2 : ℝ)

theorem AdversarialBco.Explicit.corollaryExplicit : CorollaryExplicit
```

Here `E d` is $`\mathbb{R}^d`$ and `minimaxRegretC K n` is the infimum, over the finite sets `C ⊆ K` and the `C`-policies (maps from the histories of actions and observations to probability vectors on `C`, with no measurability asked), of the supremum over the sequences of convex losses `K → [0, 1]` fixed in advance of the regret under the law of play (`AdversarialBco/StatementExplicit.lean`, Sections 1 and 9.1 of the paper). This is Corollary 1.2 of the paper.

## What is checked

- **Lean 4.** The main results are proved in Lean 4 with Mathlib, with no `sorry` and no axiom beyond `propext`, `Classical.choice` and `Quot.sound`:
  - Theorem 1.1, with its constants and its bound against an adaptive adversary: `AdversarialBco.Explicit.theoremExplicit`;
  - Corollary 1.2: `AdversarialBco.Explicit.corollaryExplicit`, through Lemma 7.13: `AdversarialBco.Explicit.lemmaMarg`;
  - Proposition 2.2 with $`C_0=1.2\cdot10^9`$: `AdversarialBco.BodySpec.bodyExplicit`, and the form that Theorem 1.1 uses: `AdversarialBco.BodySpec.bodyHExplicit`;
  - Theorem 3.1 for every family: `AdversarialBco.BodySpec.dilTheorem`;
  - Corollary 1.2 for learners that are measurable maps of a seed and the observations, with a constant it does not give and $`n\ge2`$: `AdversarialBco.corollaryADV`.

  The statements are written out from the definitions of the paper in `AdversarialBco/StatementExplicit.lean`, `AdversarialBco/StatementBody.lean` and `AdversarialBco/Statement.lean`; Section 9.1 of the paper explains them. Comparator checks each theorem against a copy of its statement file that imports only Mathlib (`config-explicit.json`, `config-body.json` and `config.json`), and nanoda, a second implementation of the Lean kernel, checks the proofs again. Every numerical constant of the paper is proved in Lean, and so is every other numbered statement except four remarks; [`STATEMENTS.md`](STATEMENTS.md) gives the Lean declarations of each.

The CI builds the package, reusing an earlier build from its cache or from the latest release. It fails on any other axiom, scans the sources for `sorry`, `admit` and `native_decide`, and runs Comparator with nanoda on the three configurations. `release.yml` releases a tagged commit whose CI run, started by hand, is green; it attaches the PDF, the logs of that run and the Lake build that Comparator checked. A run started by hand on `main` writes the two badges.

## Layout

| Path | Content |
| --- | --- |
| `AdversarialBco/` | the Lean proof (Lean and Mathlib `v4.34.1`): `Explicit.lean` proves Theorem 1.1, Lemma 7.13 and Corollary 1.2, from `Explicit/` (Section 7, Lemma 7.13 and Appendix D); `Body2/Main.lean` proves Theorem 3.1 and Proposition 2.2, from `Body2/` (Sections 3 and 4); `Main.lean` proves Corollary 1.2 for measurable learners; `Lemmas.lean` is Lemma 2.1, Section 5, Section 7 and the reduction of that form to Proposition 2.2, `Body/` Section 3 and Proposition 2.2 with a constant not computed, `Gauss/` the Gaussian concentration of Appendix A |
| `AdversarialBco/StatementExplicit.lean`, `AdversarialBco/StatementBody.lean`, `AdversarialBco/Statement.lean` | the definitions of the statements |
| `AdversarialBco/ChallengeExplicit.lean`, `config-explicit.json`; `AdversarialBco/ChallengeBody.lean`, `config-body.json`; `AdversarialBco/Challenge.lean`, `AdversarialBco/Solution.lean`, `config.json` | the statements with `sorry` and the Comparator configurations, whose solution modules are `AdversarialBco.Explicit`, `AdversarialBco.Body2.Main` and `AdversarialBco.Solution` |
| `paper/` | the TeX source |
| `code/formal-proof/` | the scripts of the CI (build, axioms, badges) and the recorded outputs of Comparator on the three configurations |

## Check and reuse

Fast check, with the build of the release:

```sh
lake exe cache get          # Mathlib, from its cache
lake build :release         # this package, from the release archive
lake build --no-build       # nothing left to build
rm -f .lake/build/lib/lean/AdversarialBco/Challenge*.* .lake/build/ir/AdversarialBco/Challenge*.*
# then Comparator with config.json, config-explicit.json and config-body.json, as .github/workflows/ci.yml runs it
# (with nanoda on four cores after the build above: 112, 108 and 113 seconds for config.json, config-explicit.json and
# config-body.json, recorded in code/formal-proof/comparator.out, comparator-explicit.out and comparator-body.out)
```

Full check, from source (less than seven minutes on four cores, Mathlib aside):

```sh
lake exe cache get && lake build
```

As a dependency (Lean and Mathlib `v4.34.1`):

```toml
[[require]]
name = "adversarial-bco"
git = "https://github.com/mt0-svg/adversarial-bco"
rev = "v1.0.0"
```

then `lake update adversarial-bco`, `lake exe cache get` and `lake build`, which downloads the build archive of the release.

## Built on

- [Lean 4](https://github.com/leanprover/lean4) and [Mathlib](https://github.com/leanprover-community/mathlib4) (Apache 2.0): the formalization.
- [Comparator](https://github.com/leanprover/comparator), [lean4export](https://github.com/leanprover/lean4export) and [landrun](https://github.com/zouuup/landrun): the check of the statement in CI.
- [nanoda](https://github.com/ammkrn/nanoda_lib) of Chris Bailey (Apache 2.0): the second implementation of the Lean kernel, built by the CI, which Comparator runs to check again every declaration the theorem depends on.
- [Maiti2026Power](https://github.com/RemyDegenne/Maiti2026Power) of Rémy Degenne (Apache 2.0), commit `b9431dd9b3811779479d1ea108e51268eb7b24ce`: the argument of Maurey and Pisier for Gaussian concentration of continuously differentiable functions, in `AdversarialBco/Gauss/MaureyPisier.lean`, ported from `Maiti2026Power/ForLMLExplore/Probability/MaureyPisier.lean`, `.../Probability/GaussianMGF.lean`, `.../Analysis/Calculus/QuarterCircle.lean` and `.../Analysis/Calculus/Gradient.lean` (names moved into `AdversarialBco.Gauss`, `ContDiff.continuous_gradient` renamed `continuous_gradient_of_contDiff`, the `IsGaussian.` prefixes of the exponential moment lemmas dropped; no proof changed).
- [Tau Ceti](https://github.com/TauCetiProject/TauCeti) (Apache 2.0), commit `e0610cce4004d628cbd9d2aafdbbb5459fe72938`: `ContDiff.gradient_right` (`TauCeti/Analysis/Calculus/Gradient.lean`) and `IsGaussian.mgf_dual` (`TauCeti/Probability/Distributions/Gaussian/Transforms.lean`), in `AdversarialBco/Gauss/MaureyPisier.lean` as `contDiff_gradient_right` and `mgf_dual` (no proof changed).

## Citation

```bibtex
@misc{adversarial-bco,
  title     = {Adversarial bandit convex optimisation with regret $d^{3/2}\sqrt{n}$ up to logarithms},
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
