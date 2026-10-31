/-! Core-Lean-only (no Mathlib) formalization of the algebraic core of the
pigeon-major result:  L f = f * Fub (f-1).  See README.md for scope. -/

namespace Pig

/-- Binomial coefficient via Pascal's rule. -/
def C : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _+1 => 0
  | n+1, k+1 => C n k + C n (k+1)

/-- Sum of `f j h` over `j < n` (the proof `h : j < n` lets recursive calls be justified). -/
def sumLt : (n : Nat) → ((j : Nat) → j < n → Nat) → Nat
  | 0, _ => 0
  | n+1, f => sumLt n (fun j h => f j (Nat.lt_succ_of_lt h)) + f n (Nat.lt_succ_self n)

/-- Plain sum of `g j` over `j < n`. -/
def sumR (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => sumR g n + g n

theorem sumLt_eq (g : Nat → Nat) :
    ∀ (n : Nat) (f : (j : Nat) → j < n → Nat), (∀ j h, f j h = g j) → sumLt n f = sumR g n
  | 0, _, _ => rfl
  | n+1, f, hf => by
    simp only [sumLt, sumR]
    rw [sumLt_eq g n _ (fun j h => hf j _), hf n _]

theorem sumR_congr (f g : Nat → Nat) :
    ∀ n, (∀ j, j < n → f j = g j) → sumR f n = sumR g n
  | 0, _ => rfl
  | n+1, h => by
    simp only [sumR]
    rw [sumR_congr f g n (fun j hj => h j (Nat.lt_succ_of_lt hj)), h n (Nat.lt_succ_self n)]

theorem sumR_mul (c : Nat) (f : Nat → Nat) : ∀ n, sumR (fun j => c * f j) n = c * sumR f n
  | 0 => by simp [sumR]
  | n+1 => by simp only [sumR]; rw [sumR_mul c f n, Nat.mul_add]

/-- Fubini (ordered Bell) numbers: Fub 0 = 1, Fub m = ∑_{j=1}^{m} C(m,j) Fub(m-j)
(index shifted: j ↦ j+1, j < m). -/
def Fub : Nat → Nat
  | 0 => 1
  | m+1 => sumLt (m+1) (fun j _ => C (m+1) (j+1) * Fub (m-j))
decreasing_by omega

/-- L 1 = 1, L f = f + ∑_{j=1}^{f-2} C(f,j) L(f-j) for f ≥ 2 (sum stops at f-2).
With f = g+2 and shifted index: ∑_{j<g} C(g+2,j+1) L(g+1-j). `L 0` is junk (0). -/
def L : Nat → Nat
  | 0 => 0
  | 1 => 1
  | g+2 => (g+2) + sumLt g (fun j _ => C (g+2) (j+1) * L (g+1-j))
decreasing_by omega

theorem Fub_zero : Fub 0 = 1 := by rw [Fub]

theorem Fub_succ (m : Nat) : Fub (m+1) = sumR (fun j => C (m+1) (j+1) * Fub (m-j)) (m+1) := by
  rw [Fub]; exact sumLt_eq _ _ _ (fun _ _ => rfl)

theorem L_one : L 1 = 1 := by rw [L]

theorem L_succ2 (g : Nat) : L (g+2) = (g+2) + sumR (fun j => C (g+2) (j+1) * L (g+1-j)) g := by
  rw [L]; rw [sumLt_eq (fun j => C (g+2) (j+1) * L (g+1-j)) g _ (fun _ _ => rfl)]

/-! Binomial helpers -/

theorem C_lt : ∀ n k, n < k → C n k = 0
  | 0, 0, h => by omega
  | 0, k+1, _ => rfl
  | n+1, 0, h => by omega
  | n+1, k+1, h => by
    simp only [C]
    rw [C_lt n k (by omega), C_lt n (k+1) (by omega)]

theorem C_self : ∀ n, C n n = 1
  | 0 => rfl
  | n+1 => by simp only [C]; rw [C_self n, C_lt n (n+1) (by omega)]

theorem C_pascal (n k : Nat) : C (n+1) (k+1) = C n k + C n (k+1) := rfl

/-- Arithmetic core of the Pascal step. -/
theorem arith (a b p q n d : Nat) (h1 : a * (d+1) = (n+1) * p) (h2 : b * d = (n+1) * q)
    (hb : b = p + q) : (a + b) * (d+1) = (n+2) * b := by
  subst hb
  have e1 : (a + (p+q)) * (d+1) = a * (d+1) + (p+q) * d + (p+q) := by
    rw [Nat.add_mul, Nat.mul_add (p+q) d 1, Nat.mul_one]; omega
  have e2 : (n+2) * (p+q) = (n+1) * (p+q) + (p+q) := by
    rw [show n+2 = (n+1)+1 from rfl, Nat.add_mul, Nat.one_mul]
  rw [e1, e2, h1, h2, Nat.mul_add]

/-- C(n+1,k) * (n+1-k) = (n+1) * C(n,k)  (all k; truncated subtraction). -/
theorem C_mul_sub : ∀ n k, C (n+1) k * (n+1-k) = (n+1) * C n k
  | 0, 0 => rfl
  | 0, 1 => rfl
  | 0, k+2 => by rw [C_lt 1 (k+2) (by omega), C_lt 0 (k+2) (by omega)]; simp
  | n+1, 0 => by simp [C]
  | n+1, j+1 => by
    by_cases hj : j ≤ n
    · have h1 := C_mul_sub n j
      have h2 := C_mul_sub n (j+1)
      obtain ⟨d, rfl⟩ : ∃ d, n = j + d := ⟨n - j, by omega⟩
      have e1 : j + d + 1 - j = d + 1 := by omega
      have e2 : j + d + 1 - (j+1) = d := by omega
      have e3 : j + d + 1 + 1 - (j+1) = d + 1 := by omega
      rw [e1] at h1
      rw [e2] at h2
      rw [e3, C_pascal (j+d+1) j]
      exact arith _ _ _ _ _ _ h1 h2 (C_pascal (j+d) j)
    · have : C (n+1+1) (j+1) = C (n+1) j + C (n+1) (j+1) := rfl
      rw [this, C_lt (n+1) (j+1) (by omega)]
      have : n + 1 + 1 - (j+1) = 0 := by omega
      rw [this]; simp

/-- Main theorem (shifted form): L (g+1) = (g+1) * Fub g. -/
theorem L_eq_aux : ∀ g, L (g+1) = (g+1) * Fub g
  | 0 => by rw [L_one, Fub_zero]
  | h+1 => by
    have ih : ∀ m, m < h+1 → L (m+1) = (m+1) * Fub m := fun m _ => L_eq_aux m
    rw [show h+1+1 = h+2 from rfl, L_succ2]
    have key : sumR (fun j => C (h+2) (j+1) * L (h+1-j)) h
        = sumR (fun j => (h+2) * (C (h+1) (j+1) * Fub (h-j))) h := by
      apply sumR_congr
      intro j hj
      have e : h + 1 - j = (h - j) + 1 := by omega
      rw [e, ih (h-j) (by omega)]
      have hm := C_mul_sub (h+1) (j+1)
      have e2 : h + 1 + 1 - (j+1) = h - j + 1 := by omega
      rw [e2] at hm
      calc C (h+2) (j+1) * ((h-j+1) * Fub (h-j))
          = (C (h+2) (j+1) * (h-j+1)) * Fub (h-j) := by rw [Nat.mul_assoc]
        _ = ((h+1+1) * C (h+1) (j+1)) * Fub (h-j) := by rw [show h+2 = h+1+1 from rfl, hm]
        _ = (h+2) * (C (h+1) (j+1) * Fub (h-j)) := by rw [Nat.mul_assoc]
    rw [key, sumR_mul]
    have hf : Fub (h+1) = sumR (fun j => C (h+1) (j+1) * Fub (h-j)) h + 1 := by
      rw [Fub_succ]
      simp only [sumR]
      rw [C_self, Nat.sub_self, Fub_zero]
    rw [hf, Nat.mul_add, Nat.mul_one]
    omega

/-- Main theorem: for all f ≥ 1, L f = f * Fub (f-1). -/
theorem L_eq (f : Nat) (hf : 1 ≤ f) : L f = f * Fub (f-1) := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rw [L_eq_aux g]; rfl

/-! Sanity checks (values from the paper: 1, 2, 9, 52, 375, 3246). -/
#eval (List.range 8).map fun i => L (i+1)
#eval (List.range 8).map fun i => (i+1) * Fub i
#eval (List.range 8).map Fub
#eval (List.range 6).map fun i => (List.range (i+1)).map (C i)

theorem L_vals : [L 1, L 2, L 3, L 4, L 5, L 6] = [1, 2, 9, 52, 375, 3246] := by
  rw [L_eq 1 (by omega), L_eq 2 (by omega), L_eq 3 (by omega), L_eq 4 (by omega),
      L_eq 5 (by omega), L_eq 6 (by omega)]
  simp [Fub, sumLt, C]

end Pig

#print axioms Pig.L_eq
#print axioms Pig.L_vals
