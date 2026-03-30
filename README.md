# steepest-descent-lean

Deriving steepest descent convergence bounds and hyperparameter scaling laws from first principles, formalized in Lean.

![](./experiments/outputs/figure1_sl1_fixed_momentum.png)

> Note: This is more of an art project than something production-grade, at least not yet. The main goal is to demonstrate that frontier machine learning optimizations research can now not only be formalized in a proof assistant, but also that a single researcher can do it in mere hours or days, rather than weeks or months for entire research teams.
>
> And while I'm trained in mathematics, I'm not a Lean expert, and this is actually the first time I've formalized any 'real' mathematics with it. I mainly used Codex, under heavy supervision by me, to 'translate' my blog posts [Ponder: Critical Batch Size for Steepest Descent Under Arbitrary Norms](https://leloykun.github.io/ponder/steepest-descent-crit-bz/) and [Ponder: Convergence Bounds for Steepest Descent Under Arbitrary Norms](https://leloykun.github.io/ponder/steepest-descent-convergence/) into Lean which you can find in [SteepestDescentOptimizationBounds/](./SteepestDescentOptimizationBounds/). I then asked it to derive hyperparameter scaling laws from those bounds, which you can find in [SteepestDescentScalingLaws/](./SteepestDescentScalingLaws/), and the results matched my (yet unpublished) scaling-law derivations by hand, which was a nice sanity check.
>
> So yah, while I'm confident the mathematics is correct, the Lean code may have hidden 'bugs' (e.g. hidden assumptions, strengthenings, weakenings of statements, etc.) that I haven't noticed. Hence why I'm open-sourcing this: if you're a Lean expert, please help me!

> NOTE: In my blog post, Assumption 4 states the (local) smoothness of the map $X^\dagger \mapsto \frac{1}{2}\| X^\dagger \|^{\dagger 2}$, but in [Assumptions.lean](./SteepestDescentOptimizationBounds/Assumptions.lean) we use a proxy potential map and its corresponding (smooth) mirror map instead. This is intentional. The latter is more mathematically sound and also more general, perfect for the Lean code. The former, while less rigorous, produces a more digestible proof of Lemma 5 fitting the tone of the blog post. In practice, $D \approx 1$ either way.

## Expected Suboptimality Bounds

Let $\eta > 0$ be the learning rate, weight decay parameter $\lambda > 0$ (such that $\lambda\eta \leq 1$), Nesterov momentum parameter $\beta \in [0, 1)$, and initial momentum $M_0 = 0$. Then, under Assumptions 1 to 4 and Assumption 12 in [Ponder: Critical Batch Size for Steepest Descent Under Arbitrary Norms](https://leloykun.github.io/ponder/steepest-descent-crit-bz/), the bounded-weight conditions $\| W_0 \| \leq \frac{1}{\lambda}$ and $\| W_* \| \leq \frac{1}{\lambda}$, and arbitrary norm pair $(\| \cdot \|, \| \cdot \|^{\dagger})$, we have,

$$\begin{align}
    \mathbb{E}\left[ f(W_T) - f(W_*) \right]
        &\leq (1 - \lambda\eta)^T \Delta_0 \nonumber \\
        &\quad+ \frac{2}{\lambda} \left(\sqrt{\frac{1 - \beta}{1 + \beta}} \beta + (1 - \beta)\right) \frac{\sqrt{D} \sigma}{\sqrt{b}} \nonumber \\
        &\quad+ \left[
            \frac{4 L}{\lambda} \left(1 + \frac{\beta^2}{1 - \beta} \right)
            + \frac{2 \beta}{1 - \beta} G_0
        \right] \eta
\end{align}$$
where $\Delta_0 = f(W_0) - f(W_*)$ and $G_0 = \| \nabla f(W_0) \|^{\dagger}$.

## Hyperparameter Scaling Laws

**Theorem 1 (Fixed momentum, large horizon proxy)** Fix $\beta \in [0, 1)$ and consider the Expected Suboptimality in [Theorem 14 of Ponder: Critical Batch Size for Steepest Descent Under Arbitrary Norms](https://leloykun.github.io/ponder/steepest-descent-crit-bz/).

1. (Iteration scaling.) For fixed large number of training steps $T$ and fixed batch size $b$, the Expected Suboptimality proxy is minimized by,
$$\begin{equation}
    \eta_T^{*}(b) \propto \frac{\log T}{T},
\end{equation}$$
Thus at fixed $T$ (ignoring token costs), the optimal learning rate is batch-independent.

1. (Token-budget scaling.) For fixed token budget $N$, the minimizer of the Expected Suboptimality proxy $(\eta_T^{*}, b_T^{*})$ satisfies,
$$\begin{align}
    b_T^{*} &\propto \left( \frac{N}{\log N} \right)^{2/3} \\
    \eta_T^{*} &\propto \left( \frac{\log N}{N} \right)^{1/3}
\end{align}$$

**Theorem 2 (Fixed batch size, large horizon proxy)** At fixed batch size $b$, the minimizer of the Expected Suboptimality proxy $(\eta_T^{*}, \beta_T^{*})$ satisfies,
$$\begin{align}
    1 - \beta_T^{*} &\propto b \left( \frac{\log N}{N} \right)^{2/3} \\
    \eta_T^{*} &\propto b \frac{\log N}{N}
\end{align}$$

## Discussion

1. When do the results here hold?

The two most important things to consider are (1) the norm to do steepest descent with, and (2) the metric to track.

Regarding the norm, what this means in practice is that we have to choose optimizers, layers, and parameterizations on our model such that, when composed with the loss function, we get an $L$-Lipschitz objective function $f = \ell \circ \operatorname{model}$. For a single-layer linear model, we can already construct well-known optimizers such as SignSGD (AdamW w/o accumulation) and Muon (Shampoo w/o accumulation) from the dualizer of the chosen norm (elementwise max norm and spectral norm for the two examples, respectively) ([Bernstein and Newhouse, 2024](https://arxiv.org/abs/2409.20325)). Multilayer models require more careful design on how to compose the layers and the layerwise norms, but the core idea is the same: we can derive the appropriate optimizer and parameterization from the chosen norm ([Large et al., 2024](https://arxiv.org/abs/2405.14813)).

Regarding the metric, we currently use Expected Suboptimality bounds to derive our convergence bounds and scaling laws. We could instead use the Expected Gradient Stationarity as in [Kovalev, 2025](https://arxiv.org/abs/2503.12645), [Shulgin et al., 2026](https://arxiv.org/abs/2603.15958), and [Islamov et al., 2026](https://arxiv.org/abs/2603.21191). But these are *expected* bounds at time $T$. Last-iterate bounds may be more relevant in practice, but they are more difficult to derive, and may not be amenable for purely analytical scaling law derivations. So for now, we stick to Expected Suboptimality bounds.

## References

1. Franz Cesista and Kaiyue Wen (2025). Critical Batch Size for Steepest Descent Under Arbitrary Norms. URL https://leloykun.github.io/ponder/steepest-descent-crit-bz/
2. Franz Cesista (2025). Convergence Bounds for Steepest Descent Under Arbitrary Norms. URL https://leloykun.github.io/ponder/steepest-descent-convergence/
3. Jeremy Bernstein and Laker Newhouse (2024). Old Optimizer, New Norm: An Anthology. URL https://arxiv.org/abs/2409.20325
4. Tim Large, Yang Liu, Minyoung Huh, Hyojin Bahng, Phillip Isola, Jeremy Bernstein (2024). Scalable Optimization in the Modular Norm. URL https://arxiv.org/abs/2405.14813
5. Dmitry Kovalev (2025). Understanding Gradient Orthogonalization for Deep Learning via Non-Euclidean Trust-Region Optimization. URL https://arxiv.org/abs/2503.12645
6. Egor Shulgin, Dimitri von Rütte, Tianyue H. Zhang, Niccolò Ajroldi, Bernhard Schölkopf, Antonio Orvieto (2026). Deriving Hyperparameter Scaling Laws via Modern Optimization Theory. URL https://arxiv.org/abs/2603.15958
7. Rustem Islamov, Roman Machacek, Aurelien Lucchi, Antonio Silveti-Falls, Eduard Gorbunov, Volkan Cevher (2026). On the Role of Batch Size in Stochastic Conditional Gradient Methods. URL https://arxiv.org/abs/2603.21191
