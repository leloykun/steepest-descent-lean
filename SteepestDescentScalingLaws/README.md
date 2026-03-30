# Steepest Descent Scaling Laws

This folder contains the large-horizon scaling-law layer derived from Theorem 14.

## Overview

- `TheoremSL1.lean` covers the fixed-momentum regime: hold `β` fixed, optimize the learning rate, and then study how the token-budget optimizer scales with `batchSize` and `N`.
- `TheoremSL2.lean` covers the fixed-batch regime: hold `batchSize` fixed, tune momentum through `1 - β`, and derive the corresponding learning-rate scaling law.
- `Commons.lean` contains the shared asymptotic algebra used by both files.

## Theorem SL1 in paper-style language

The public SL1 theorems say that when momentum is fixed (`β` fixed with `0 ≤ β < 1`):

- In the fixed-step view, the optimal learning rate decays like `log T / (λ T)`.
- In the token-budget view, an interior small-branch optimal batch-size schedule grows like `(N / log N)^(2/3)`.
- The associated optimal learning-rate schedule scales like `(log N)^(1/3) / (λ N^(1/3))`.

In other words, fixed momentum does not change the basic cube-root token-budget law: the optimizer trades off exponential bias decay against the minibatch noise floor, and this balance produces the familiar `(N / log N)^(2/3)` batch-growth law.

## Theorem SL2 in paper-style language

The public SL2 theorems say that when batch size is fixed:

- The quantity `1 - β` should shrink with the horizon, rather than stay constant.
- The asymptotically relevant tuning law is
  `1 - β ≍ batchSize * ((log N) / N)^(2/3)`.
- Under that tuning, the optimal learning rate scales like
  `batchSize * log N / (λ N)`.

Equivalently, if `N = batchSize * T`, the step-based form is the same statement rewritten in terms of total steps `T`: the momentum gap `1 - β` closes as the horizon grows, and the learning rate decays at the corresponding logarithmic-over-linear scale.

## Reading guide

Each theorem file is organized as:

1. public-facing definitions
2. private definitions
3. private lemmas and proof machinery
4. public-facing theorems at the bottom

So the mathematically meaningful API is always concentrated near the top and bottom of each file.
