# Bastien–Khormali Conjecture

The Bastien-Khormali (2025) assert that nontrivial link-irregular tournaments with `n` vertices exist if and only if `n ≥ 6`. Bastien and Khormali themselves established the conjecture true up to `n = 100`. Their preprint is as follows: [https://arxiv.org/abs/2512.20494](https://arxiv.org/abs/2512.20494).

This program serves as Lean 4 formalization for proving the existence of a link-irregular tournament with `n` vertices when `n ≥ 9`, and that a uniformly random tournament is asymptotically almost surely link-irregular. The former existence statement resolves the Bastien-Khormali Conjecture in the affirmative.

Build with

```sh
lake build
```

The formalization uses two stated external results as Lean 4 axioms: the values from OEIS A000088 and Corollary 2 of Buhrman–Li–Tromp–Vitányi.
