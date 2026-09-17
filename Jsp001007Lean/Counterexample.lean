import Mathlib

/-!
# JSP-001007 / Green Problem 44: explicit negative certificate

This file formalizes an explicit counterexample to the fixed-parameter
Green Problem 44 statement used by Formal Conjectures.

Witness:
* `N = 100,000`;
* the 1000 primes in the interval `[20,011, 30,161]`, enumerated increasingly;
* for each prime `p`, remove the upper half of the residue classes,
  the images of `[(p+1)/2, p)` in `ZMod p`.

Every integer `1 <= x <= 10,001` survives all 1000 sieves, so more than
`N/10 = 10,000` integers remain.

The only finite census is `primeSet_card`: the interval contains exactly
1000 primes.  Everything else is derived structurally from membership in
that filtered finite set.
-/

namespace Jsp001007

open Function

set_option maxRecDepth 1000000

def N0 : ℕ := 100_000
def T0 : ℕ := 10_001

/-- The finite interval containing exactly the 1000 prime moduli used below. -/
def primeSet : Finset ℕ :=
  (Finset.Icc 20_011 30_161).filter Nat.Prime

/-- Finite census certificate. `native_decide` is isolated here and disclosed;
all mathematical structure downstream is ordinary Lean proof. -/
set_option maxHeartbeats 0 in
theorem primeSet_card : primeSet.card = 1000 := by
  native_decide

/-- The primes in increasing order. -/
def primeEmb : Fin 1000 ↪o ℕ :=
  primeSet.orderEmbOfFin primeSet_card

def primes (i : Fin 1000) : ℕ := primeEmb i

theorem primes_prime (i : Fin 1000) : Nat.Prime (primes i) := by
  have hm : primes i ∈ primeSet := by
    simpa [primes, primeEmb] using
      (Finset.orderEmbOfFin_mem primeSet primeSet_card i)
  exact (Finset.mem_filter.mp hm).2

theorem primes_strictMono : StrictMono primes := by
  exact primeEmb.strictMono

theorem primes_bounds (i : Fin 1000) : 20_011 ≤ primes i ∧ primes i ≤ 30_161 := by
  have hm : primes i ∈ primeSet := by
    simpa [primes, primeEmb] using
      (Finset.orderEmbOfFin_mem primeSet primeSet_card i)
  exact Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1

theorem primes_power_bound : (primes 999) ^ 10 < N0 ^ 9 := by
  have hu : primes 999 ≤ 30_161 := (primes_bounds 999).2
  calc
    (primes 999) ^ 10 ≤ 30_161 ^ 10 := Nat.pow_le_pow_left hu 10
    _ < N0 ^ 9 := by norm_num [N0]

/-- The classes removed modulo `p_i`: the upper half of the standard representatives. -/
def removedClasses (i : Fin 1000) : Finset (ZMod (primes i)) :=
  (Finset.Ico ((primes i + 1) / 2) (primes i)).image
    (fun n : ℕ => (n : ZMod (primes i)))

private lemma natCast_injOn_Ico {p a : ℕ} :
    Set.InjOn (fun n : ℕ => (n : ZMod p)) (↑(Finset.Ico a p) : Set ℕ) := by
  intro x hx y hy hxy
  have hxlt : x < p := (Finset.mem_Ico.mp hx).2
  have hylt : y < p := (Finset.mem_Ico.mp hy).2
  have hval := congrArg ZMod.val hxy
  simpa [ZMod.val_natCast_of_lt hxlt, ZMod.val_natCast_of_lt hylt] using hval

theorem removedClasses_card (i : Fin 1000) :
    (removedClasses i).card = primes i / 2 := by
  unfold removedClasses
  rw [Finset.card_image_of_injOn natCast_injOn_Ico]
  simp only [Nat.card_Ico]
  have hp := primes_prime i
  have hne : primes i ≠ 2 := by
    have hmin := (primes_bounds i).1
    omega
  have hmod : primes i % 2 = 1 :=
    (hp.mod_two_eq_one_iff_ne_two).2 hne
  omega

theorem small_not_removed (i : Fin 1000) {x : ℕ} (hx : x ≤ T0) :
    (x : ZMod (primes i)) ∉ removedClasses i := by
  intro hmem
  rw [removedClasses, Finset.mem_image] at hmem
  rcases hmem with ⟨y, hy, hxy⟩
  have hylo : (primes i + 1) / 2 ≤ y := (Finset.mem_Ico.mp hy).1
  have hylt : y < primes i := (Finset.mem_Ico.mp hy).2
  have hmin : 20_011 ≤ primes i := (primes_bounds i).1
  have hxlt : x < primes i := by
    dsimp [T0] at hx
    omega
  have hval := congrArg ZMod.val hxy
  have hyx : y = x := by
    simpa [ZMod.val_natCast_of_lt hylt, ZMod.val_natCast_of_lt hxlt] using hval
  have hhalf : T0 < (primes i + 1) / 2 := by
    dsimp [T0]
    omega
  omega

/-- Exact universal statement of the fixed-parameter Green Problem 44 formulation. -/
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

/-- Green Problem 44, with “half” interpreted as `floor(p/2)`, has a negative answer. -/
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
