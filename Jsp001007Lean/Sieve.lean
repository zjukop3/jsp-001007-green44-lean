import Jsp001007Lean.PrimeOrder

namespace Jsp001007

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

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

end Jsp001007
