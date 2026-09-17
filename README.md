# JSP-001007 Lean formalization candidate

This project targets **JSP-001007** / Ben Green's Problem 44.

## Result

It gives an explicit negative certificate for the exact universal statement used by
Google DeepMind's Formal Conjectures formalization of Green Problem 44.

- `N = 5,000,000`.
- `p : Fin 1000 -> Nat` is the explicit increasing list of 1000 primes from
  `1,000,003` through `1,013,501`.
- For each `p`, remove the upper half of the standard residue representatives:
  `[(p+1)/2, p)`.
- Every integer `1 <= x <= 500,001` survives every sieve.
- Therefore at least `500,001 > N/10` integers remain.

Top-level theorem:

```lean
Jsp001007.green44_negative : ¬ Jsp001007.Green44Claim
```

## Reproduce

Pinned toolchain:

- Lean `v4.33.1`
- Mathlib `v4.33.1`

Commands:

```bash
lake update
lake exe cache get
lake build
```

Then inspect the build output from:

```lean
#print axioms Jsp001007.green44_negative
```

The submission should not be filed as kernel-verified until `lake build` succeeds
on a clean machine/CI runner and the axiom output has been recorded.

## Attribution

The project does **not** claim original mathematical discovery of JSP-001007.
The Justin Sun Prize catalog currently credits the negative mathematical answer
to Liam Price and GPT-5.4 Pro. This repository is intended as an independent
Lean formalization/certificate contribution.

AI assistance used in developing the formalization should be disclosed in the
public submission. Repository ownership alone does not establish authorship.
