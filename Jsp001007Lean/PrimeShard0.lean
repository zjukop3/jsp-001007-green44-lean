import Jsp001007Lean.PrimeData

namespace Jsp001007

set_option maxRecDepth 1000000
set_option maxHeartbeats 0 in
theorem primeChunk0_all_prime : ∀ p : ↥primeChunk0, Nat.Prime p.1 := by
  rintro ⟨p, hp⟩
  simp [primeChunk0, primeList] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

end Jsp001007
