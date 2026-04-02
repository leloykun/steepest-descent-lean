# Steepest Descent Scaling Laws

This folder contains the large-horizon scaling-law layer built on top of the
project's proxy bounds.

`Commons.lean` is the shared algebra layer. It contains family-agnostic
asymptotic lemmas and `rpow`/`sqrt` identities reused across the scaling-law
files.

Exact optimizer-identification formulas keep the relevant project constants
explicit. Public asymptotic bounds absorb fixed constants such as `\lambda` and
`\mu_{\mathrm{FW}}` into the comparison constants.

## Star-Convex Expected Suboptimality

- `StarConvexScalingLawsTheorem1.lean` is the fixed-momentum large-horizon
  proxy layer.
- `StarConvexScalingLawsTheorem2.lean` is the fixed-batch large-horizon proxy
  layer.

The public laws are:

- with fixed momentum `\beta`, `\eta \asymp \log T / T`;
- under a token budget `N`, `batchSize \asymp (N / \log N)^{2/3}`;
- under that token-budget tuning, `\eta \asymp (\log N)^{1/3} / N^{1/3}`;
- with fixed batch size, `1 - \beta \asymp batchSize * ((\log N) / N)^{2/3}`;
- under that fixed-batch tuning, `\eta \asymp batchSize * \log N / N`.

## FW Expected Gap

- `FWExpectedGapSLTheorem1.lean` is the fixed-momentum large-horizon
  Frank-Wolfe expected-gap scaling-law layer.
- `FWExpectedGapSLTheorem2.lean` is the fixed-batch large-horizon
  Frank-Wolfe expected-gap scaling-law layer.

The public laws are:

- with fixed momentum `\beta`, `\eta \asymp T^{-1/2}`;
- under a token budget `N`, `batchSize \asymp N^{1/2}`;
- under that token-budget tuning, `\eta \asymp N^{-1/4}`;
- with fixed batch size, `1 - \beta \asymp \sqrt{batchSize / N}`;
- under that fixed-batch tuning, `\eta \asymp batchSize^{3/4} N^{-3/4}`.

## FW Expected Suboptimality

- `FWExpectedSuboptimalitySLTheorem1.lean` is the fixed-momentum large-horizon
  Frank-Wolfe expected-suboptimality scaling-law layer.
- `FWExpectedSuboptimalitySLTheorem2.lean` is the fixed-batch large-horizon
  Frank-Wolfe expected-suboptimality scaling-law layer.

The public laws are:

- with fixed momentum `\beta`, `\eta \asymp \log T / T`;
- under a token budget `N`, `batchSize \asymp (N / \log N)^{2/3}`;
- under that token-budget tuning,
  `\eta \asymp (\log N)^{1/3} / N^{1/3}`;
- with fixed batch size,
  `1 - \beta \asymp batchSize * ((\log N) / N)^{2/3}`;
- under that fixed-batch tuning, `\eta \asymp batchSize * \log N / N`.

These exponents match the star-convex expected-suboptimality family, but they
are derived from the Frank-Wolfe KL expected-suboptimality proxy instead of the
star-convex proxy.

## File Layout

Each theorem file follows the same structure:

1. public definitions
2. private definitions
3. private lemmas and proof machinery
4. public theorems at the bottom
