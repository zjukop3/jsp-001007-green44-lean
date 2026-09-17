import Jsp001007Lean.PrimeData
import Jsp001007Lean.PrimeShard0
import Jsp001007Lean.PrimeShard1
import Jsp001007Lean.PrimeShard2
import Jsp001007Lean.PrimeShard3
import Jsp001007Lean.PrimeShard4
import Jsp001007Lean.PrimeShard5
import Jsp001007Lean.PrimeShard6
import Jsp001007Lean.PrimeShard7
import Jsp001007Lean.PrimeShard8
import Jsp001007Lean.PrimeShard9
import Jsp001007Lean.PrimeShard10
import Jsp001007Lean.PrimeShard11
import Jsp001007Lean.PrimeShard12
import Jsp001007Lean.PrimeShard13
import Jsp001007Lean.PrimeShard14
import Jsp001007Lean.PrimeShard15
import Jsp001007Lean.PrimeShard16
import Jsp001007Lean.PrimeShard17
import Jsp001007Lean.PrimeShard18
import Jsp001007Lean.PrimeShard19

/-!
# JSP-001007 / Green Problem 44: explicit negative certificate

This file proves a direct counterexample to the fixed 1000-prime Green Problem 44
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

def N0 : ℕ := 100_000
def T0 : ℕ := 10_001

def primeBlock (i : Fin 1000) : Fin 20 :=
  ⟨i.1 / 50, by
    have hi := i.isLt
    omega⟩

def primeOffset (i : Fin 1000) : Fin 50 :=
  ⟨i.1 % 50, by
    exact Nat.mod_lt _ (by norm_num)⟩

lemma prime_index_decomp (i : Fin 1000) :
    50 * (primeBlock i).1 + (primeOffset i).1 = i.1 := by
  dsimp [primeBlock, primeOffset]
  omega

theorem primes_prime (i : Fin 1000) : Nat.Prime (primes i) := by
  let b := primeBlock i
  let j := primeOffset i
  have hidx : (⟨50 * b.1 + j.1, by
      have hb := b.isLt
      have hj := j.isLt
      omega⟩ : Fin 1000) = i := by
    apply Fin.ext
    simpa [b, j] using prime_index_decomp i
  rw [← hidx]
  fin_cases b
  · simpa using primes_prime_block0 j
  · simpa using primes_prime_block1 j
  · simpa using primes_prime_block2 j
  · simpa using primes_prime_block3 j
  · simpa using primes_prime_block4 j
  · simpa using primes_prime_block5 j
  · simpa using primes_prime_block6 j
  · simpa using primes_prime_block7 j
  · simpa using primes_prime_block8 j
  · simpa using primes_prime_block9 j
  · simpa using primes_prime_block10 j
  · simpa using primes_prime_block11 j
  · simpa using primes_prime_block12 j
  · simpa using primes_prime_block13 j
  · simpa using primes_prime_block14 j
  · simpa using primes_prime_block15 j
  · simpa using primes_prime_block16 j
  · simpa using primes_prime_block17 j
  · simpa using primes_prime_block18 j
  · simpa using primes_prime_block19 j

private lemma transportPrimeLt {a b c d : Fin 1000}
    (h : primes a < primes b) (hac : a = c) (hbd : b = d) :
    primes c < primes d := by
  simpa [hac, hbd] using h

theorem primes_strictMono : StrictMono primes := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  change primes ⟨i.1, by omega⟩ < primes ⟨i.1 + 1, by omega⟩
  by_cases h0 : i.1 < 50
  · simpa using primes_lt_block0 ⟨i.1, h0⟩
  by_cases h1 : i.1 < 100
  · let j : Fin 50 := ⟨i.1 - 50, by omega⟩
    apply transportPrimeLt (primes_lt_block1 j)
    · apply Fin.ext; dsimp [j]; omega
    · apply Fin.ext; dsimp [j]; omega
  by_cases h2 : i.1 < 150
  · let j : Fin 50 := ⟨i.1 - 100, by omega⟩
    apply transportPrimeLt (primes_lt_block2 j)
    · apply Fin.ext; dsimp [j]; omega
    · apply Fin.ext; dsimp [j]; omega
  by_cases h3 : i.1 < 200
  · let j : Fin 50 := ⟨i.1 - 150, by omega⟩
    apply transportPrimeLt (primes_lt_block3 j)
    · apply Fin.ext; dsimp [j]; omega
    · apply Fin.ext; dsimp [j]; omega
  by_cases h4 : i.1 < 250
  · let j : Fin 50 := ⟨i.1 - 200, by omega⟩
    apply transportPrimeLt (primes_lt_block4 j)
    · apply Fin.ext; dsimp [j]; omega
    · apply Fin.ext; dsimp [j]; omega
  by_cases h5 : i.1 < 300
  · let j : Fin 50 := ⟨i.1 - 250, by omega⟩
    apply transportPrimeLt (primes_lt_block5 j)
    · apply Fin.ext; dsimp [j]; omega
    · apply Fin.ext; dsimp [j]; omega
  by_cases h6 : i.1 < 350
  · let j : Fin 50 := ⟨i.1 - 300, by omega⟩
    apply transportPrimeLt (primes_lt_block6 j)
    · apply Fin.ext; dsimp [j]; omega
    · apply Fin.ext; dsimp [j]; omega
  by_cases h7 : i.1 < 400
  · let j : Fin 50 := ⟨i.1 - 350, by omega⟩
    apply transportPrimeLt (primes_lt_block7 j)
    · apply Fin.ext; dsimp [j]; omega
    · apply Fin.ext; dsimp [j]; omega
  by_cases h8 : i.1 < 450
  · let j : Fin 50 := ⟨i.1 - 400, by omega⟩
    apply transportPrimeLt (primes_lt_block8 j)
    · apply Fin.ext; dsimp [j]; omega
    · apply Fin.ext; dsimp [j]; omega
  by_cases h9 : i.1 < 500
  · let j : Fin 50 := ⟨i.1 - 450, by omega⟩
    apply transportPrimeLt (primes_lt_block9 j)
    · apply Fin.ext; dsimp [j]; omega
    · apply Fin.ext; dsimp [j]; omega
  by_cases h10 : i.1 < 550
  · let j : Fin 50 := ⟨i.1 - 500, by omega⟩
    apply transportPrimeLt (primes_lt_block10 j)
    · apply Fin.ext; dsimp [j]; omega
    · apply Fin.ext; dsimp [j]; omega
  by_cases h11 : i.1 < 600
  · let j : Fin 50 := ⟨i.1 - 550, by omega⟩
    apply transportPrimeLt (primes_lt_block11 j)
    · apply Fin.ext; dsimp [j]; omega
    · apply Fin.ext; dsimp [j]; omega
  by_cases h12 : i.1 < 650
  · let j : Fin 50 := ⟨i.1 - 600, by omega⟩
    apply transportPrimeLt (primes_lt_block12 j)
    · apply Fin.ext; dsimp [j]; omega
    · apply Fin.ext; dsimp [j]; omega
  by_cases h13 : i.1 < 700
  · let j : Fin 50 := ⟨i.1 - 650, by omega⟩
    apply transportPrimeLt (primes_lt_block13 j)
    · apply Fin.ext; dsimp [j]; omega
    · apply Fin.ext; dsimp [j]; omega
  by_cases h14 : i.1 < 750
  · let j : Fin 50 := ⟨i.1 - 700, by omega⟩
    apply transportPrimeLt (primes_lt_block14 j)
    · apply Fin.ext; dsimp [j]; omega
    · apply Fin.ext; dsimp [j]; omega
  by_cases h15 : i.1 < 800
  · let j : Fin 50 := ⟨i.1 - 750, by omega⟩
    apply transportPrimeLt (primes_lt_block15 j)
    · apply Fin.ext; dsimp [j]; omega
    · apply Fin.ext; dsimp [j]; omega
  by_cases h16 : i.1 < 850
  · let j : Fin 50 := ⟨i.1 - 800, by omega⟩
    apply transportPrimeLt (primes_lt_block16 j)
    · apply Fin.ext; dsimp [j]; omega
    · apply Fin.ext; dsimp [j]; omega
  by_cases h17 : i.1 < 900
  · let j : Fin 50 := ⟨i.1 - 850, by omega⟩
    apply transportPrimeLt (primes_lt_block17 j)
    · apply Fin.ext; dsimp [j]; omega
    · apply Fin.ext; dsimp [j]; omega
  by_cases h18 : i.1 < 950
  · let j : Fin 50 := ⟨i.1 - 900, by omega⟩
    apply transportPrimeLt (primes_lt_block18 j)
    · apply Fin.ext; dsimp [j]; omega
    · apply Fin.ext; dsimp [j]; omega
  · let j : Fin 49 := ⟨i.1 - 950, by omega⟩
    apply transportPrimeLt (primes_lt_block19 j)
    · apply Fin.ext; dsimp [j]; omega
    · apply Fin.ext; dsimp [j]; omega

theorem primes_bounds (i : Fin 1000) : 20_011 ≤ primes i ∧ primes i ≤ 30_161 := by
  constructor
  · have h := primes_strictMono.monotone (Fin.zero_le i)
    simpa [primes, primeBlocks] using h
  · have h := primes_strictMono.monotone (Fin.le_last i)
    simpa [primes, primeBlocks] using h

theorem primes_power_bound : (primes 999) ^ 10 < N0 ^ 9 := by
  norm_num [primes, primeBlocks, N0]

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
