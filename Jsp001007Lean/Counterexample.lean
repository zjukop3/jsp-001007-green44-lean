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

This file proves a direct counterexample to the exact right-hand side of
`FormalConjectures/GreensOpenProblems/44.lean`.

Witness: `N = 100,000`; 1000 increasing prime moduli from `20,011` to
`30,161`; modulo each prime `p`, remove the upper half of the standard
representatives, namely `[(p+1)/2, p)`. Every integer `1 ≤ x ≤ 10,001`
survives, so strictly more than `N/10` integers remain.
-/

namespace Jsp001007

open Function
set_option maxRecDepth 1000000

def N0 : ℕ := 100_000
def T0 : ℕ := 10_001

theorem primeSet_all_prime (p : ↥primeSet) : Nat.Prime p.1 := by
  rcases primeSet_chunk_cover p with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19
  · exact primeChunk0_all_prime ⟨p.1, h0⟩
  · exact primeChunk1_all_prime ⟨p.1, h1⟩
  · exact primeChunk2_all_prime ⟨p.1, h2⟩
  · exact primeChunk3_all_prime ⟨p.1, h3⟩
  · exact primeChunk4_all_prime ⟨p.1, h4⟩
  · exact primeChunk5_all_prime ⟨p.1, h5⟩
  · exact primeChunk6_all_prime ⟨p.1, h6⟩
  · exact primeChunk7_all_prime ⟨p.1, h7⟩
  · exact primeChunk8_all_prime ⟨p.1, h8⟩
  · exact primeChunk9_all_prime ⟨p.1, h9⟩
  · exact primeChunk10_all_prime ⟨p.1, h10⟩
  · exact primeChunk11_all_prime ⟨p.1, h11⟩
  · exact primeChunk12_all_prime ⟨p.1, h12⟩
  · exact primeChunk13_all_prime ⟨p.1, h13⟩
  · exact primeChunk14_all_prime ⟨p.1, h14⟩
  · exact primeChunk15_all_prime ⟨p.1, h15⟩
  · exact primeChunk16_all_prime ⟨p.1, h16⟩
  · exact primeChunk17_all_prime ⟨p.1, h17⟩
  · exact primeChunk18_all_prime ⟨p.1, h18⟩
  · exact primeChunk19_all_prime ⟨p.1, h19⟩

def primeEmb : Fin 1000 ↪o ℕ :=
  primeSet.orderEmbOfFin primeSet_card

def primes (i : Fin 1000) : ℕ := primeEmb i

theorem primes_mem (i : Fin 1000) : primes i ∈ primeSet := by
  simpa [primes, primeEmb] using
    (Finset.orderEmbOfFin_mem primeSet primeSet_card i)

theorem primes_prime (i : Fin 1000) : Nat.Prime (primes i) :=
  primeSet_all_prime ⟨primes i, primes_mem i⟩

theorem primes_strictMono : StrictMono primes :=
  primeEmb.strictMono

theorem primes_bounds (i : Fin 1000) : 20_011 ≤ primes i ∧ primes i ≤ 30_161 :=
  primeSet_bounds_cert ⟨primes i, primes_mem i⟩

theorem primes_power_bound : (primes 999) ^ 10 < N0 ^ 9 := by
  have hu : primes 999 ≤ 30_161 := (primes_bounds 999).2
  calc
    (primes 999) ^ 10 ≤ 30_161 ^ 10 := Nat.pow_le_pow_left hu 10
    _ < N0 ^ 9 := by norm_num [N0]

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
