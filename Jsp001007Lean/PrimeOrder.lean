import Jsp001007Lean.PrimeFacts

namespace Jsp001007

open Function
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

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

end Jsp001007
