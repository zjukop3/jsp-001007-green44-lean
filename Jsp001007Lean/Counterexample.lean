import Jsp001007Lean.Sieve

/-!
# JSP-001007 / Green Problem 44: explicit negative certificate

This proves a direct counterexample to the fixed 1000-prime Green Problem 44
statement used by Formal Conjectures.

Witness: `N = 100,000`; 1000 increasing prime moduli from `20,011` to
`30,161`; modulo each prime `p`, remove the upper half of the standard
representatives, namely `[(p+1)/2, p)`. Every integer `1 ≤ x ≤ 10,001`
survives, so strictly more than `N/10` integers remain.
-/

namespace Jsp001007

open Function
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def Green44Claim : Prop :=
  ∀ (N : ℕ) (p : Fin 1000 → ℕ)
      (A : (i : Fin 1000) → Finset (ZMod (p i))),
    let remaining :=
      (Finset.Icc 1 N).filter (fun x => ∀ i, (x : ZMod (p i)) ∉ A i)
    (∀ i, (p i).Prime) →
    StrictMono p →
    (p 999) ^ 10 < N ^ 9 →
    (∀ i, (A i).card = (p i) / 2) →
    10 * remaining.card ≤ N

def witnessRemaining : Finset ℕ :=
  (Finset.Icc 1 N0).filter
    (fun x => ∀ i, (x : ZMod (primes i)) ∉ removedClasses i)

theorem initialSegment_subset_remaining :
    Finset.Icc 1 T0 ⊆ witnessRemaining := by
  intro x hx
  have hxIcc := Finset.mem_Icc.mp hx
  rw [witnessRemaining, Finset.mem_filter]
  constructor
  · apply Finset.mem_Icc.mpr
    constructor
    · exact hxIcc.1
    · dsimp [N0, T0] at *
      omega
  · intro i
    exact small_not_removed i hxIcc.2

theorem witnessRemaining_large :
    N0 < 10 * witnessRemaining.card := by
  have hcard := Finset.card_le_card initialSegment_subset_remaining
  have hT : T0 ≤ witnessRemaining.card := by
    simpa [T0] using hcard
  dsimp [N0, T0] at *
  omega

theorem green44_negative : ¬ Green44Claim := by
  intro h
  have hbound : 10 * witnessRemaining.card ≤ N0 := by
    simpa [Green44Claim, witnessRemaining] using
      h N0 primes removedClasses
        primes_prime
        primes_strictMono
        primes_power_bound
        removedClasses_card
  exact (Nat.not_lt_of_ge hbound) witnessRemaining_large

#print axioms green44_negative

end Jsp001007
