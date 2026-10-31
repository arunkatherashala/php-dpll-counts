/-! Core-Lean-only (no Mathlib): the algebraic identity behind the hole-major result
(proofhole_proof.md, Section 4, Steps 2-3):

   sum_{k=1}^{m} (nabla^k g)(q) = g(q+1) - g(q)   for g(x) = x^m   (any integer q),

where nabla g (x) = g x - g (x-1).  Here `nI k g` is nabla^k g.  The proof follows the
paper: telescoping identity  sum_{k=1}^m nabla^k g = (E-1) g - E nabla^{m+1} g, plus
nabla^{m+1} (x^m) = 0 (degree argument, formalized with a `D d g` = "degree <= d" predicate).
NOT formalized: the combinatorial identification of N(k) (words containing letters 0..k-1)
with nabla^k g (q), the DPLL-to-word-count reduction (Cor. 3, Lemma 4). -/

namespace Hole

def nabla (g : Int → Int) : Int → Int := fun x => g x - g (x - 1)

/-- nabla^k g (inner-first iteration). -/
def nI : Nat → (Int → Int) → (Int → Int)
  | 0, g => g
  | k+1, g => nI k (nabla g)

/-- "g has degree <= d" in the finite-difference sense. -/
def D : Nat → (Int → Int) → Prop
  | 0, g => ∀ x, g x = g 0
  | d+1, g => D d (nabla g)

/-- sum_{k<n} f k over Int. -/
def sumI (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n+1 => sumI f n + f n

theorem nI_succ_outer : ∀ k g, nI (k+1) g = nabla (nI k g)
  | 0, g => rfl
  | k+1, g => by
    show nI (k+1) (nabla g) = nabla (nI (k+1) g)
    rw [nI_succ_outer k (nabla g)]; rfl

theorem tele : ∀ (m : Nat) (g : Int → Int) (x : Int),
    sumI (fun k => nI (k+1) g x) m = g (x+1) - g x - nI (m+1) g (x+1)
  | 0, g, x => by
    show 0 = g (x+1) - g x - nabla g (x+1)
    simp only [nabla, Int.add_sub_cancel]; omega
  | m+1, g, x => by
    show sumI (fun k => nI (k+1) g x) m + nI (m+1) g x = _
    rw [tele m g x, nI_succ_outer (m+1) g]
    simp only [nabla, Int.add_sub_cancel]; omega

theorem D_add : ∀ d g h, D d g → D d h → D d (fun x => g x + h x)
  | 0, g, h, hg, hh => fun x => by
    show g x + h x = g 0 + h 0
    have := hg x; have := hh x; omega
  | d+1, g, h, hg, hh => by
    have e : nabla (fun x => g x + h x) = fun x => nabla g x + nabla h x := by
      funext x; simp only [nabla]; omega
    show D d (nabla (fun x => g x + h x))
    rw [e]; exact D_add d _ _ hg hh

theorem D_shift : ∀ d g, D d g → D d (fun x => g (x - 1))
  | 0, g, hg => fun x => by
    show g (x-1) = g (0-1)
    have := hg (x-1); have := hg (0-1); omega
  | d+1, g, hg => by
    have e : nabla (fun x => g (x - 1)) = fun x => nabla g (x - 1) := by
      funext x; simp only [nabla]
    show D d (nabla (fun x => g (x - 1)))
    rw [e]; exact D_shift d _ hg

/-- multiplying by x raises the degree bound by one -/
theorem D_mulx : ∀ d g, D d g → D (d+1) (fun x => x * g x)
  | 0, g, hg => by
    show D 0 (nabla (fun x => x * g x))
    intro x
    simp only [nabla]
    rw [hg x, hg (x-1), hg 0, hg (0 - 1)]
    rw [Int.sub_mul]; omega
  | d+1, g, hg => by
    show D (d+1) (nabla (fun x => x * g x))
    have e : nabla (fun x => x * g x)
        = fun x => x * nabla g x + g (x - 1) := by
      funext x; simp only [nabla]
      rw [Int.mul_sub, Int.sub_mul]; omega
    rw [e]
    exact D_add (d+1) _ _ (D_mulx d _ hg) (D_shift (d+1) g (by
      show D d (nabla g)
      exact hg))

theorem D_pow : ∀ m : Nat, D m (fun x => x ^ m)
  | 0 => fun x => by simp
  | m+1 => by
    have := D_mulx m _ (D_pow m)
    have e : (fun x : Int => x ^ (m+1)) = fun x => x * x ^ m := by
      funext x; rw [Int.pow_succ, Int.mul_comm]
    rw [e]; exact this

theorem D_kill : ∀ d g, D d g → nI (d+1) g = fun _ => 0
  | 0, g, hg => by
    funext x
    show nabla g x = 0
    simp only [nabla]; rw [hg x, hg (x-1)]; omega
  | d+1, g, hg => D_kill d (nabla g) hg

/-- The hole-major algebraic identity: sum_{k=1}^m nabla^k (x^m) (q) = (q+1)^m - q^m. -/
theorem abel_core (m : Nat) (q : Int) :
    sumI (fun k => nI (k+1) (fun x => x ^ m) q) m = (q+1) ^ m - q ^ m := by
  rw [tele m, D_kill m _ (D_pow m)]
  dsimp only
  omega

end Hole

#print axioms Hole.abel_core

#eval (Hole.sumI (fun k => Hole.nI (k+1) (fun x => x ^ 3) 5) 3, (6:Int)^3 - 5^3)
