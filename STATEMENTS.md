# From the paper to the proof

The table below gives, for each numbered statement of the paper, the Lean declarations that prove it.

Seven theorems carry the results of the paper. Their statements are written out from the paper's definitions in three statement files, and Comparator checks each theorem against a copy of its file:

- `AdversarialBco.Explicit.theoremExplicit`, `lemmaMarg` and `corollaryExplicit`: Theorem 1.1, Lemma 7.13 and Corollary 1.2, stated in `AdversarialBco/StatementExplicit.lean` and checked with `config-explicit.json`;
- `AdversarialBco.BodySpec.dilTheorem`, `bodyExplicit` and `bodyHExplicit`: Theorem 3.1 and Proposition 2.2, stated in `AdversarialBco/StatementBody.lean` and checked with `config-body.json`;
- `AdversarialBco.corollaryADV`: Corollary 1.2 for measurable learners, stated in `AdversarialBco/Statement.lean` and checked with `config.json`.

The constants of the main results are written into these statements. Every other declaration below is a step of their proofs, including the inequalities between explicit numbers that the proofs use, which the rows of Theorem 1.1, Proposition 2.2, Theorem 3.1, Proposition 3.5 and Lemma 4.1 name. Everything rests on the axioms `propext`, `Classical.choice` and `Quot.sound` alone, and `code/formal-proof/main_axioms.lean` prints the axioms of the main theorems. Four remarks lie outside the formal proof, and Section 9.2 of the paper lists the places where the formal proof departs from the text.

<!-- statement-map: generated from paper/main.tex, do not edit -->

| Paper | Lean |
| --- | --- |
| Theorem 1.1 | `AdversarialBco.Explicit.theoremExplicit` (`AdversarialBco/Explicit.lean`), the statement `TheoremExplicit` of `AdversarialBco/StatementExplicit.lean`, Algorithm 7.1 written out (Section 9.1); from `AdversarialBco.Explicit.theoremExplicit_of_bodyH` (`AdversarialBco/Explicit/Main.lean`) and `AdversarialBco.BodySpec.bodyHExplicit`; the numerical inequalities of the proof: `AdversarialBco.Explicit.ex_params`, `ex_const`, `ex_CX_beta`, `ex_CX_log`, `ex_CX_final` and `ex_CX`, and `AdversarialBco.thmC_c_large` |
| Corollary 1.2 | `AdversarialBco.Explicit.corollaryExplicit` (`AdversarialBco/Explicit.lean`), the statement `CorollaryExplicit` of `AdversarialBco/StatementExplicit.lean`, from `AdversarialBco.Explicit.corollaryExplicit_of_bodyH` and `AdversarialBco.Explicit.lemmaMarg`; for measurable learners, with a constant that is not computed and n >= 2: `AdversarialBco.corollaryADV` (`AdversarialBco/Main.lean`, Section 9.1) |
| Lemma 2.1 | (a) `AdversarialBco.convex_inner`, `isCompact_inner`, `closedBall_subset_inner`, `AdversarialBco.Body2.inner_ball`, `AdversarialBco.Body2.one_le_diam`, `AdversarialBco.Body.tr_inner`; (b) `abs_sub_le_inner`, `sub_le_of_convex_bdd`; (c) `sInf_inner_le`, `convex_comb_le`, `closedBall_shrink_subset` |
| Proposition 2.2 | `AdversarialBco.BodySpec.bodyExplicit` (`AdversarialBco/Body2/Main.lean`), the statement `BodyExplicit` of `AdversarialBco/StatementBody.lean`; from `AdversarialBco.Body2.bodyExplicit_of_dil` (`AdversarialBco/Body2/PropBody.lean`), with (4.1) from `AdversarialBco.Body2.proj_var`, `lipExt_ge` and `proj_nonexp`, and the steps `mass_arith`, `sh_arith`, `outside_arith` and `final_arith`; on the inner body of Lemma 2.1, for every D >= diam K: `AdversarialBco.BodySpec.bodyHExplicit`; the numerical inequalities of the proof: `AdversarialBco.Body2.KS_bounds` and `C0_bound` |
| Theorem 3.1 | `AdversarialBco.BodySpec.dilTheorem` (`AdversarialBco/Body2/Main.lean`), the statement `DilTheorem` of `AdversarialBco/StatementBody.lean`: an entropic Gaussian at the temperature exists, and every one has the conclusions; from the regular case `AdversarialBco.Body2.dilRegExplicit` (`AdversarialBco/Body2/Dil2.lean`) by `AdversarialBco.DilAll.dilTheorem_of_reg` (`AdversarialBco/Explicit/DilAll.lean`); the numerical inequalities of the proof: `AdversarialBco.Body2.KS_bounds`, `phi_T_le` and `scale_arith2` |
| Lemma 3.2 | existence of a minimiser over the invertible S: `AdversarialBco.Body.ec_min_exists`; one with S positive definite: `AdversarialBco.DilAll.isMinInv_spd`, which minimises over the positive definite S: `AdversarialBco.DilAll.isEntropicGaussian_of_isMinInv`; uniqueness: `AdversarialBco.DilAll.entropic_unique`; (S4): `AdversarialBco.Body.ec_S4`; (S1) and (S2): `AdversarialBco.Body.ec_first_order` and `AdversarialBco.Body2.minInv_stationary`; (S3): `AdversarialBco.Body.ec_S3` |
| Lemma 3.3 | `AdversarialBco.Body2.inf_std` (`AdversarialBco/Body2/Half.lean`); E k = kappa: `AdversarialBco.Body2.integral_kfun_inner`; E m = 1/(2R): `AdversarialBco.Body2.integral_ind_inner`; the bound on E(l - m)^2: `AdversarialBco.Body2.score_sq_std`; kappa_2 as an integral: `AdversarialBco.Body2.integral_score_sq_phi` |
| Lemma 3.4 | `AdversarialBco.Body2.half_std` (`AdversarialBco/Body2/Half.lean`); the kernel bound: `AdversarialBco.Body2.Kker_ge` |
| Proposition 3.5 | `AdversarialBco.Body2.core_one` (`AdversarialBco/Body2/Half.lean`); the bounds on kappa: `AdversarialBco.Body2.kappa_bounds`, used in `AdversarialBco.Body2.core_bracket` |
| Lemma 3.6 | `AdversarialBco.Body2.mills_lower`, `mills_antitone` and `mills_zero` (`AdversarialBco/Body2/Gauss1.lean`) |
| Lemma 3.7 | (a) `AdversarialBco.Body2.ibp_a` and (b) `AdversarialBco.Body2.ibp_b` (`AdversarialBco/Body2/Ibp.lean`) |
| Lemma 4.1 | `AdversarialBco.Body2.penalty_need` (`AdversarialBco/Body2/Penalty.lean`); T(2) >= 7, Theta(2) >= 20 and need(2) <= 2^10 C': `AdversarialBco.Body2.penalty_numeric` |
| Lemma 5.1 | (a) `AdversarialBco.card_le_of_separated`; (b) `AdversarialBco.exists_maximal_separated` |
| Lemma 5.2 | (a), together with Lemma 2.1 (c): `AdversarialBco.Explicit.ex_comparator`; (b): `AdversarialBco.integral_comp_le_add`, `sqrt_V_le_bdd`, `sqrt_integral_sq_add_le`, `sqrt_wsum_sq_add_le`, `var_le_sq_mean`, with a measurable nearest point in place of the one of least index (`exists_measurable_nearest`); (5.1) in the proof of `AdversarialBco.conv_coin` |
| Algorithm 7.1 | `AdversarialBco.Explicit.net`, `IsStep1`, `IsSolver`, weights, `exoKernel` and `coinLaw` (`AdversarialBco/StatementExplicit.lean`): rounds from 0, the scan order and the procedure of step 1 given as arguments (Section 9.1) |
| Theorem 7.2 | `AdversarialBco.Explicit.ex_pseudo_main` (the adaptive form) and `AdversarialBco.Explicit.ex_coinReg_of_pseudo` (sequences fixed in advance) (`AdversarialBco/Explicit/Main.lean`), for every finite C in J of covering radius below eps in place of the net; the size of the net: `AdversarialBco.Explicit.ex_net_card` and `ex_net_two` |
| Lemma 7.3 | `AdversarialBco.ew_recursive`, rounds indexed from 0, and its form along a path, `ew_path` |
| Lemma 7.4 | `AdversarialBco.br_round` (the expectation written as a finite sum) and `br_step` |
| Lemma 7.5 | `AdversarialBco.mm1` |
| Lemma 7.6 | `AdversarialBco.convex_advSet`, `isCompact_advSet`, `convex_Fq` and `convex_Eq`; (7.4): `AdversarialBco.round_exists`, with `omega_mix` |
| Lemma 7.7 | `AdversarialBco.gibbs_lower` (the inequality >=) and `gibbs_upper` (the infimum approached within every delta > 0) |
| Lemma 7.8 | `AdversarialBco.primal_vertex`, with `AdversarialBco.compensation` in its proof |
| Lemma 7.9 | `AdversarialBco.conv_coin`, with `pinsker_var`, `pinsker_bern` and `clamp_extension_PL`, for C of covering radius at most eps through a measurable projection |
| Proposition 7.10 | `AdversarialBco.Explicit.ex_Rbar_lower`; the bound: `AdversarialBco.value_dual` and `round_exists`, with `vertex_value_le`, `value_arith` and `min_le_avg`, and at the net `AdversarialBco.Explicit.ex_step1_exists` and `ex_round_value` |
| Lemma 7.11 | (i) `AdversarialBco.sg_exists`; (ii) `convex_PL`, `isCompact_PL`, `PL_of_convex` and `PL_of_adm`; (iii) `extension_PL` and `clamp_extension_PL` |
| Lemma 7.12 | `AdversarialBco.Explicit.ex_net_facts`, `ex_net_card` and `ex_net_two` |
| Lemma 7.13 | `AdversarialBco.Explicit.lemmaMarg` (`AdversarialBco/Explicit/Marg.lean`), the statement `LemmaMarg` of `AdversarialBco/StatementExplicit.lean`, for every learner with coins whose laws are probability vectors on C |
| Remark 7.14 | not formalized: the cost of a round only; not in the formal proof |
| Theorem A.1 | `AdversarialBco.Gauss.gaussConcAt` (`AdversarialBco/Gauss/Concentration.lean`), for F(b + S Z) with F Lipschitz on R^d and S linear from R^k to R^d (b = 0, S = Id is the statement here), through `AdversarialBco.Gauss.hasSubgaussianMGF_sub_integral_of_lipschitz` |
| Lemma A.2 | `AdversarialBco.Gauss.hasSubgaussianMGF_sub_integral_stdGaussian` (`AdversarialBco/Gauss/MaureyPisier.lean`) |
| Lemma A.3 | `AdversarialBco.Body.stein_coord`, on the standard Gaussian of R^d for Phi with a derivative of at most exponential growth, with `AdversarialBco.gaussian_ibp_1d`, `gaussian_ibp_pi` and `hasDerivAt_gaussianPDFReal_0_1` |
| Remark B.1 | not formalized: the formal proof of Lemma 7.5 (`AdversarialBco.mm1`) rests on the minimax theorem of Sion in Mathlib |
| Remark C.1 | not formalized: the formal proof uses the case of two Bernoulli laws, `AdversarialBco.pinsker_bern`, the only case Lemma 7.9 uses |
| Lemma D.1 | `AdversarialBco.Body.smooth_convex` (`AdversarialBco/Body/Smooth.lean`) |
| Lemma D.2 | `AdversarialBco.DilAll.entropic_unique` (`AdversarialBco/Explicit/DilAll.lean`) |
| Lemma D.3 | `AdversarialBco.DilAll.limit_isMinInv`, `uniform_bounds` and `tendsto_integral_cloud` (`AdversarialBco/Explicit/DilAll.lean`), for minimisers over the invertible S |
| Remark D.4 | not formalized: the formal proof passes (S3) to the limit only in the proof of Lemma D.5 (`AdversarialBco.DilAll.dilTheorem_of_reg`) |
| Lemma D.5 | `AdversarialBco.DilAll.dilTheorem_of_reg` (`AdversarialBco/Explicit/DilAll.lean`), from the regular case `AdversarialBco.Body2.dilRegExplicit` (minimisers over the invertible S), the regular families from `AdversarialBco.DilAll.approx_family` |
