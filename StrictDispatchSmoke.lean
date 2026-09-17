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
axiom block19 (j : Fin 50) (hj : j.1 < 49) : primes ⟨950 + j.1, by omega⟩ < primes ⟨950 + j.1 + 1, by omega⟩

example : StrictMono primes := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  let b : Fin 20 := ⟨i.1 / 50, by
    have hi := i.isLt
    omega⟩
  let j : Fin 50 := ⟨i.1 % 50, Nat.mod_lt _ (by norm_num)⟩
  have hval : 50 * b.1 + j.1 = i.1 := by
    dsimp [b, j]
    omega
  have hleft : (⟨50 * b.1 + j.1, by
      have hb := b.isLt
      have hj := j.isLt
      omega⟩ : Fin 1000) = i.castSucc := by
    apply Fin.ext
    exact hval
  have hright : (⟨50 * b.1 + j.1 + 1, by
      have hb := b.isLt
      have hj := j.isLt
      omega⟩ : Fin 1000) = i.succ := by
    apply Fin.ext
    simpa [hval]
  rw [← hleft, ← hright]
  fin_cases b
  · simpa using block0 j
  · simpa using block1 j
  · simpa using block2 j
  · simpa using block3 j
  · simpa using block4 j
  · simpa using block5 j
  · simpa using block6 j
  · simpa using block7 j
  · simpa using block8 j
  · simpa using block9 j
  · simpa using block10 j
  · simpa using block11 j
  · simpa using block12 j
  · simpa using block13 j
  · simpa using block14 j
  · simpa using block15 j
  · simpa using block16 j
  · simpa using block17 j
  · simpa using block18 j
  · have hj19 : j.1 < 49 := by
      have hi := i.isLt
      omega
    simpa using block19 j hj19

end Jsp001007
