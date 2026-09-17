import Jsp001007Lean.PrimeData

namespace Jsp001007

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

axiom block0 (j : Fin 50) : primes ⟨0 + j.1, by omega⟩ < primes ⟨0 + j.1 + 1, by omega⟩
axiom block1 (j : Fin 50) : primes ⟨50 + j.1, by omega⟩ < primes ⟨50 + j.1 + 1, by omega⟩
axiom block2 (j : Fin 50) : primes ⟨100 + j.1, by omega⟩ < primes ⟨100 + j.1 + 1, by omega⟩
axiom block3 (j : Fin 50) : primes ⟨150 + j.1, by omega⟩ < primes ⟨150 + j.1 + 1, by omega⟩
axiom block4 (j : Fin 50) : primes ⟨200 + j.1, by omega⟩ < primes ⟨200 + j.1 + 1, by omega⟩
axiom block5 (j : Fin 50) : primes ⟨250 + j.1, by omega⟩ < primes ⟨250 + j.1 + 1, by omega⟩
axiom block6 (j : Fin 50) : primes ⟨300 + j.1, by omega⟩ < primes ⟨300 + j.1 + 1, by omega⟩
axiom block7 (j : Fin 50) : primes ⟨350 + j.1, by omega⟩ < primes ⟨350 + j.1 + 1, by omega⟩
axiom block8 (j : Fin 50) : primes ⟨400 + j.1, by omega⟩ < primes ⟨400 + j.1 + 1, by omega⟩
axiom block9 (j : Fin 50) : primes ⟨450 + j.1, by omega⟩ < primes ⟨450 + j.1 + 1, by omega⟩
axiom block10 (j : Fin 50) : primes ⟨500 + j.1, by omega⟩ < primes ⟨500 + j.1 + 1, by omega⟩
axiom block11 (j : Fin 50) : primes ⟨550 + j.1, by omega⟩ < primes ⟨550 + j.1 + 1, by omega⟩
axiom block12 (j : Fin 50) : primes ⟨600 + j.1, by omega⟩ < primes ⟨600 + j.1 + 1, by omega⟩
axiom block13 (j : Fin 50) : primes ⟨650 + j.1, by omega⟩ < primes ⟨650 + j.1 + 1, by omega⟩
axiom block14 (j : Fin 50) : primes ⟨700 + j.1, by omega⟩ < primes ⟨700 + j.1 + 1, by omega⟩
axiom block15 (j : Fin 50) : primes ⟨750 + j.1, by omega⟩ < primes ⟨750 + j.1 + 1, by omega⟩
axiom block16 (j : Fin 50) : primes ⟨800 + j.1, by omega⟩ < primes ⟨800 + j.1 + 1, by omega⟩
axiom block17 (j : Fin 50) : primes ⟨850 + j.1, by omega⟩ < primes ⟨850 + j.1 + 1, by omega⟩
axiom block18 (j : Fin 50) : primes ⟨900 + j.1, by omega⟩ < primes ⟨900 + j.1 + 1, by omega⟩
axiom block19 (j : Fin 49) : primes ⟨950 + j.1, by omega⟩ < primes ⟨950 + j.1 + 1, by omega⟩

example : StrictMono primes := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  change primes ⟨i.1, by omega⟩ < primes ⟨i.1 + 1, by omega⟩
  by_cases h0 : i.1 < 50
  · simpa using block0 ⟨i.1, h0⟩
  by_cases h1 : i.1 < 100
  · let j : Fin 50 := ⟨i.1 - 50, by omega⟩
    have h := block1 j
    have heq : 50 + j.1 = i.1 := by dsimp [j]; omega
    rw [heq] at h
    exact h
  by_cases h2 : i.1 < 150
  · let j : Fin 50 := ⟨i.1 - 100, by omega⟩
    have h := block2 j
    have heq : 100 + j.1 = i.1 := by dsimp [j]; omega
    rw [heq] at h
    exact h
  by_cases h3 : i.1 < 200
  · let j : Fin 50 := ⟨i.1 - 150, by omega⟩
    have h := block3 j
    have heq : 150 + j.1 = i.1 := by dsimp [j]; omega
    rw [heq] at h
    exact h
  by_cases h4 : i.1 < 250
  · let j : Fin 50 := ⟨i.1 - 200, by omega⟩
    have h := block4 j
    have heq : 200 + j.1 = i.1 := by dsimp [j]; omega
    rw [heq] at h
    exact h
  by_cases h5 : i.1 < 300
  · let j : Fin 50 := ⟨i.1 - 250, by omega⟩
    have h := block5 j
    have heq : 250 + j.1 = i.1 := by dsimp [j]; omega
    rw [heq] at h
    exact h
  by_cases h6 : i.1 < 350
  · let j : Fin 50 := ⟨i.1 - 300, by omega⟩
    have h := block6 j
    have heq : 300 + j.1 = i.1 := by dsimp [j]; omega
    rw [heq] at h
    exact h
  by_cases h7 : i.1 < 400
  · let j : Fin 50 := ⟨i.1 - 350, by omega⟩
    have h := block7 j
    have heq : 350 + j.1 = i.1 := by dsimp [j]; omega
    rw [heq] at h
    exact h
  by_cases h8 : i.1 < 450
  · let j : Fin 50 := ⟨i.1 - 400, by omega⟩
    have h := block8 j
    have heq : 400 + j.1 = i.1 := by dsimp [j]; omega
    rw [heq] at h
    exact h
  by_cases h9 : i.1 < 500
  · let j : Fin 50 := ⟨i.1 - 450, by omega⟩
    have h := block9 j
    have heq : 450 + j.1 = i.1 := by dsimp [j]; omega
    rw [heq] at h
    exact h
  by_cases h10 : i.1 < 550
  · let j : Fin 50 := ⟨i.1 - 500, by omega⟩
    have h := block10 j
    have heq : 500 + j.1 = i.1 := by dsimp [j]; omega
    rw [heq] at h
    exact h
  by_cases h11 : i.1 < 600
  · let j : Fin 50 := ⟨i.1 - 550, by omega⟩
    have h := block11 j
    have heq : 550 + j.1 = i.1 := by dsimp [j]; omega
    rw [heq] at h
    exact h
  by_cases h12 : i.1 < 650
  · let j : Fin 50 := ⟨i.1 - 600, by omega⟩
    have h := block12 j
    have heq : 600 + j.1 = i.1 := by dsimp [j]; omega
    rw [heq] at h
    exact h
  by_cases h13 : i.1 < 700
  · let j : Fin 50 := ⟨i.1 - 650, by omega⟩
    have h := block13 j
    have heq : 650 + j.1 = i.1 := by dsimp [j]; omega
    rw [heq] at h
    exact h
  by_cases h14 : i.1 < 750
  · let j : Fin 50 := ⟨i.1 - 700, by omega⟩
    have h := block14 j
    have heq : 700 + j.1 = i.1 := by dsimp [j]; omega
    rw [heq] at h
    exact h
  by_cases h15 : i.1 < 800
  · let j : Fin 50 := ⟨i.1 - 750, by omega⟩
    have h := block15 j
    have heq : 750 + j.1 = i.1 := by dsimp [j]; omega
    rw [heq] at h
    exact h
  by_cases h16 : i.1 < 850
  · let j : Fin 50 := ⟨i.1 - 800, by omega⟩
    have h := block16 j
    have heq : 800 + j.1 = i.1 := by dsimp [j]; omega
    rw [heq] at h
    exact h
  by_cases h17 : i.1 < 900
  · let j : Fin 50 := ⟨i.1 - 850, by omega⟩
    have h := block17 j
    have heq : 850 + j.1 = i.1 := by dsimp [j]; omega
    rw [heq] at h
    exact h
  by_cases h18 : i.1 < 950
  · let j : Fin 50 := ⟨i.1 - 900, by omega⟩
    have h := block18 j
    have heq : 900 + j.1 = i.1 := by dsimp [j]; omega
    rw [heq] at h
    exact h
  · let j : Fin 49 := ⟨i.1 - 950, by omega⟩
    have h := block19 j
    have heq : 950 + j.1 = i.1 := by dsimp [j]; omega
    rw [heq] at h
    exact h

end Jsp001007
