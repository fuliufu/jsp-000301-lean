import Mathlib

/-!
# JSP-000301: formalization of Golomb's counterexample (Lean 4)

**Problem.** If two consecutive positive integers are powerful, must at least
one be a perfect square?

**Answer.** No. The consecutive pair `(12167, 12168)` is a counterexample:

* `12167 = 23^3` is powerful (prime exponent 3 ≥ 2) and not a square;
* `12168 = 2^3 * 3^2 * 13^2` is powerful (all exponents ≥ 2) and not a square;
* `110^2 = 12100 < 12167 < 12168 < 12321 = 111^2`, so neither is a square.

This is Golomb's 1970 counterexample (Erdős problem #365; JSP-000301).
-/

/-- A **powerful number**: every prime factor occurs with exponent at least 2. -/
def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → 2 ≤ n.factorization p

/-- The conjecture as stated in JSP-000301. -/
def JSP_000301_Conjecture : Prop :=
  ∀ n : ℕ, n > 0 → IsPowerful n → IsPowerful (n + 1) → IsSquare n ∨ IsSquare (n + 1)

/-- `12167 = 23^3` is powerful: its only prime divisor `23` has exponent 3. -/
lemma isPowerful_12167 : IsPowerful 12167 := by
  intro p hp hdiv
  have hpne : p ≠ 1 := by
    have h2 : 2 ≤ p := hp.two_le
    omega
  have hp23 : p = 23 := by
    have hpow : p ∣ 23 ^ 3 := by
      norm_num at hdiv ⊢
      exact hdiv
    have hpd : p ∣ 23 := hp.dvd_of_dvd_pow hpow
    have h23p : 23 = p := (Nat.Prime.dvd_iff_eq (by norm_num : (23 : ℕ).Prime) hpne).mp hpd
    exact h23p.symm
  rw [hp23]
  norm_num [Nat.factorization]

/-- `12168 = 2^3 * 3^2 * 13^2` is powerful: every prime divisor has exponent ≥ 2. -/
lemma isPowerful_12168 : IsPowerful 12168 := by
  intro p hp hdiv
  have hpne : p ≠ 1 := by
    have h2 : 2 ≤ p := hp.two_le
    omega
  have hcases : p = 2 ∨ p = 3 ∨ p = 13 := by
    have hpow : p ∣ 2 ^ 3 * 3 ^ 2 * 13 ^ 2 := by
      norm_num at hdiv ⊢
      exact hdiv
    rw [Nat.Prime.dvd_mul hp] at hpow
    rcases hpow with hrest2 | h13
    · rw [Nat.Prime.dvd_mul hp] at hrest2
      rcases hrest2 with h2 | h3
      · left
        have h2d : p ∣ 2 := hp.dvd_of_dvd_pow h2
        have h2p : 2 = p := (Nat.Prime.dvd_iff_eq (by norm_num : (2 : ℕ).Prime) hpne).mp h2d
        exact h2p.symm
      · right; left
        have h3d : p ∣ 3 := hp.dvd_of_dvd_pow h3
        have h3p : 3 = p := (Nat.Prime.dvd_iff_eq (by norm_num : (3 : ℕ).Prime) hpne).mp h3d
        exact h3p.symm
    · right; right
      have h13d : p ∣ 13 := hp.dvd_of_dvd_pow h13
      have h13p : 13 = p := (Nat.Prime.dvd_iff_eq (by norm_num : (13 : ℕ).Prime) hpne).mp h13d
      exact h13p.symm
  rcases hcases with h2 | h3 | h13
  · rw [h2]
    norm_num [Nat.factorization]
  · rw [h3]
    norm_num [Nat.factorization]
  · rw [h13]
    norm_num [Nat.factorization]

/-- `12167` is not a perfect square: it lies strictly between `110^2` and `111^2`. -/
lemma not_isSquare_12167 : ¬ IsSquare 12167 := by
  rintro ⟨m, hm⟩
  rcases le_or_gt m 110 with h | h
  · nlinarith
  · have : 111 ≤ m := h
    nlinarith

/-- `12168` is not a perfect square: it lies strictly between `110^2` and `111^2`. -/
lemma not_isSquare_12168 : ¬ IsSquare 12168 := by
  rintro ⟨m, hm⟩
  rcases le_or_gt m 110 with h | h
  · nlinarith
  · have : 111 ≤ m := h
    nlinarith

/-- **Main theorem.** The JSP-000301 conjecture is false: the consecutive
powerful pair `(12167, 12168)` disproves it. -/
theorem jsp_000301_disproved : ¬ JSP_000301_Conjecture := by
  intro h
  have h1 : IsPowerful 12167 := isPowerful_12167
  have h2 : IsPowerful (12167 + 1) := by
    simpa using isPowerful_12168
  have h_counter := h 12167 (by norm_num) h1 h2
  cases h_counter with
  | inl h_sq => exact not_isSquare_12167 h_sq
  | inr h_sq => exact not_isSquare_12168 h_sq
