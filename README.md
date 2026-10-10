# jsp-000301-lean

Lean 4 formalization of the **JSP-000301** counterexample
([Erdős problem #365](https://www.erdosproblems.com/latex/365); Golomb 1970).

![Lean CI](https://github.com/fuliufu/jsp-000301-lean/actions/workflows/lean.yml/badge.svg)

## Problem

> If two consecutive positive integers are powerful, must at least one be a
> perfect square?

**No.** The consecutive pair `(12167, 12168)` is a counterexample:

| n | prime factorization | powerful? | square? |
|---|---|---|---|
| 12167 | 23³ | ✓ (exponent 3 ≥ 2) | ✗ (110² = 12100 < 12167 < 12321 = 111²) |
| 12168 | 2³ · 3² · 13² | ✓ (all exponents ≥ 2) | ✗ (110² = 12100 < 12168 < 12321 = 111²) |

This is the counterexample recorded by Solomon W. Golomb (1970) for
Erdős problem #365, filed as JSP-000301 in The Justin Sun Prize problem bank.

## Formalization

- `IsPowerful n` — `n` is powerful: every prime factor occurs with exponent
  at least 2 (`∀ p, p.Prime → p ∣ n → 2 ≤ n.factorization p`).
  - `JSP_000301_Conjecture` — the yes/no question, stated as a proposition.
  - `jsp_000301_disproved : ¬ JSP_000301_Conjecture` — **the main theorem**:
    instantiating the conjecture at `n = 12167` with the two powerfulness
      witnesses and the two non-squareness proofs yields a contradiction.

      ## Build & verify

      Pinned toolchain: Lean `v4.34.1`, mathlib `v4.34.1`
      (see `lean-toolchain` and `lake-manifest.json`).

      ```sh
      lake build                      # 0 warnings, 0 errors
      lake env lean Axioms.lean       # axiom audit for the main theorem
      ```

      Axiom audit output:

      ```
      #print axioms jsp_000301_disproved
      -- 'jsp_000301_disproved' depends on axioms: [propext, Classical.choice, Quot.sound]
      ```

      Only the standard Lean axioms are used; the proof contains no `sorry`, `admit`
      or `native_decide` steps.

      ## Repository layout

      - `MyJspSolution.lean` — definitions and the full proof
      - `Axioms.lean` — axiom audit entry point
      - `.github/workflows/lean.yml` — CI: `lake build` + axiom audit on every push/PR

      ## Submission metadata

      - Problem: JSP-000301 (problems/catalog-0301-0400.md)
      - Mathematical solution: Solomon W. Golomb, "Powerful numbers",
        Amer. Math. Monthly 77(8) (1970), 848–852
          ([doi:10.2307/2317020](https://doi.org/10.2307/2317020))
          - Lean formalization: [fuliufu](https://github.com/fuliufu)
          - 
