# Bastien–Khormali Conjecture

The Bastien and Khormali (2025) assert that nontrivial link-irregular tournaments with `n` vertices exist if and only if `n ≥ 6`. They themselves established the conjecture true up to `n = 100`. Their preprint is as follows: [https://arxiv.org/abs/2512.20494](https://arxiv.org/abs/2512.20494).

This program serves as Lean 4 formalization for proving the existence of a link-irregular tournament with `n` vertices when `n ≥ 9`, and that a uniformly random tournament is asymptotically almost surely link-irregular. The former existence statement resolves the Bastien–Khormali Conjecture in the affirmative.

# Instructions

Install Lean 4.27.0, and from your directory run in powershell:

```powershell
lake build
```

The build completed successfully under Lean 4.27.0 in our session. There are no `sorry`, `admit`, nor `native_decide`.

However, the formalization uses two stated external results as Lean 4 axioms: the values from OEIS A000088 and Corollary 2 of Buhrman–Li–Tromp–Vitányi. They can be found in `Proof/External/`.

# Remark

I completed the initial formalization on August 22, 2026, but delayed writing it up for arXiv while occupied with classwork and research. Apparently, I found out a claimed proof was announced afterwards in [this Reddit post](https://www.reddit.com/r/mathematics/comments/1w0ti58/i_think_ive_proved_a_minor_conjecture_on_graph). Personally biased, though; I prefer the probabilistic method.
