# Bastien–Khormali Conjecture

Lean 4 formalization proving the existence of a link-irregular tournament on `n`
vertices when `n ≥ 9`, and that a uniformly random tournament is
asymptotically almost surely link-irregular.

Build with

```sh
lake build
```

The formalization uses two stated external results as Lean 4 axioms: the values from OEIS A000088 and Corollary 2 of Buhrman–Li–Tromp–Vitányi.
