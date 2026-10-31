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

/-! ===================================================================
Hole2 part (new): word-count / mex-sum / inclusion-exclusion / closed form.
Steps formalized (proofhole_proof.md Sections 3, 4 Steps 1, 2, 4):
  holeSum n := sum over all words w of length n-2 over the alphabet {0..n+1}
               (letters 0..n = rows, n+1 = "none") of (2 + mex w),
  mex w = min {i in 0..n : i not in w}   (= n+1 if none; cannot happen for short words).
NOT formalized: DPLL+UP semantics (Cor. 3, Lemma 4), i.e. why L(n) = holeSum n.
=================================================================== -/
namespace HoleW
open Hole

/-- sum_{a in L} h a -/
def sL : List Nat → (Nat → Nat) → Nat
  | [], _ => 0
  | a :: L, h => h a + sL L h

/-- sum of f over all words of length m with letters from the list L. -/
def cnt (L : List Nat) : Nat → (List Nat → Nat) → Nat
  | 0, f => f []
  | m+1, f => sL L (fun a => cnt L m (fun w => f (a :: w)))

/-- explicit enumeration of all words (for sanity checks) -/
def allWords (L : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | m+1 => L.flatMap (fun a => (allWords L m).map (a :: ·))

/-- sum_{k<K} f k in Nat -/
def sumN (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | K+1 => sumN f K + f K

/-- mex search: first i, i+1, ... (at most f steps) not occurring in w -/
def mexFrom (w : List Nat) : Nat → Nat → Nat
  | 0, i => i
  | f+1, i => if i ∈ w then mexFrom w f (i+1) else i

/-- mex of w over the row range 0..n (n+1 if all of 0..n occur) -/
def mex (n : Nat) (w : List Nat) : Nat := mexFrom w (n+1) 0

/-- the explicit sum of Section 3, as a Nat function of n -/
def holeSum (n : Nat) : Nat :=
  cnt (List.range (n+2)) (n-2) (fun w => 2 + mex n w)

/-- the target closed form -/
def holeClosed (n : Nat) : Nat := (n+2)^(n-2) + (n+3)^(n-2)

/-! ### basic sum lemmas -/

theorem sL_add (L : List Nat) (h h' : Nat → Nat) :
    sL L (fun a => h a + h' a) = sL L h + sL L h' := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [sL, ih]; omega

theorem sL_congr (L : List Nat) (h h' : Nat → Nat) (H : ∀ a ∈ L, h a = h' a) :
    sL L h = sL L h' := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [sL]
    rw [H a (List.mem_cons_self), ih (fun b hb => H b (List.mem_cons_of_mem _ hb))]

theorem sL_const (L : List Nat) (c : Nat) : sL L (fun _ => c) = L.length * c := by
  induction L with
  | nil => simp [sL]
  | cons a L ih => simp only [sL, ih, List.length_cons]; rw [Nat.succ_mul]; omega

theorem sL_erase (L : List Nat) (x : Nat) (h : Nat → Nat) (hx : h x = 0) :
    sL (L.erase x) h = sL L h := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.erase_cons]
    by_cases hax : a = x
    · subst hax; simp [sL, hx]
    · have : (a == x) = false := by simp [hax]
      simp [this, sL, ih]

theorem cnt_add (L : List Nat) (m : Nat) :
    ∀ f g : List Nat → Nat, cnt L m (fun w => f w + g w) = cnt L m f + cnt L m g := by
  induction m with
  | zero => intro f g; rfl
  | succ m ih =>
    intro f g
    show sL L _ = sL L _ + sL L _
    rw [← sL_add]
    congr 1; funext a; exact ih _ _

theorem cnt_const (L : List Nat) (m c : Nat) :
    cnt L m (fun _ => c) = c * L.length ^ m := by
  induction m with
  | zero => simp [cnt]
  | succ m ih =>
    show sL L (fun a => cnt L m (fun _ => c)) = _
    simp only [ih, sL_const, Nat.pow_succ]
    rw [Nat.mul_comm L.length, Nat.mul_assoc]

theorem cnt_sumN (L : List Nat) (m : Nat) (F : Nat → List Nat → Nat) (K : Nat) :
    cnt L m (fun w => sumN (fun k => F k w) K) = sumN (fun k => cnt L m (F k)) K := by
  induction K with
  | zero => simp only [sumN]; rw [cnt_const]; simp
  | succ K ih =>
    simp only [sumN]
    rw [cnt_add, ih]

/-! ### words lacking a letter -/

theorem cnt_lack (L : List Nat) (x : Nat) (hx : x ∉ L.erase x) (m : Nat) :
    ∀ f : List Nat → Nat,
      cnt L m (fun w => if x ∈ w then 0 else f w) = cnt (L.erase x) m f := by
  induction m with
  | zero => intro f; simp [cnt]
  | succ m ih =>
    intro f
    show sL L _ = sL (L.erase x) _
    have h0 : (fun a => cnt L m (fun w => if x ∈ a :: w then 0 else f (a :: w))) x = 0 := by
      show cnt L m _ = 0
      have : (fun w : List Nat => if x ∈ x :: w then 0 else f (x :: w)) = fun _ => 0 := by
        funext w; simp
      rw [this, cnt_const]; simp
    rw [← sL_erase L x _ h0]
    apply sL_congr
    intro a ha
    have hne : a ≠ x := fun h => hx (h ▸ ha)
    show cnt L m (fun w => if x ∈ a :: w then 0 else f (a :: w)) = _
    have : (fun w : List Nat => if x ∈ a :: w then 0 else f (a :: w))
         = fun w => if x ∈ w then 0 else f (a :: w) := by
      funext w
      have : x ∈ a :: w ↔ x ∈ w := by
        simp only [List.mem_cons]; constructor
        · rintro (h | h)
          · exact absurd h.symm hne
          · exact h
        · intro h; exact Or.inr h
      simp only [this]
    rw [this, ih]

/-! ### inclusion-exclusion: N(k) = nabla^k g (q) -/

/-- indicator that every letter of R occurs in w -/
def ind (R : List Nat) (w : List Nat) : Nat := if (∀ y ∈ R, y ∈ w) then 1 else 0

/-- N(L,m,R): number of words of length m over L containing every letter of R -/
def N (L : List Nat) (m : Nat) (R : List Nat) : Nat := cnt L m (ind R)

theorem N_step (L : List Nat) (x : Nat) (R : List Nat) (hx : x ∉ L.erase x) (m : Nat) :
    N L m (x :: R) + N (L.erase x) m R = N L m R := by
  unfold N
  rw [← cnt_lack L x hx m (ind R), ← cnt_add]
  congr 1; funext w
  unfold ind
  by_cases h1 : x ∈ w <;> by_cases h2 : (∀ y ∈ R, y ∈ w) <;> simp [h1, h2]

theorem N_eq (m : Nat) : ∀ (R L : List Nat), L.Nodup → R.Nodup → (∀ y ∈ R, y ∈ L) →
    (N L m R : Int) = nI R.length (fun x => x ^ m) (L.length : Int) := by
  intro R
  induction R with
  | nil =>
    intro L _ _ _
    have : N L m [] = L.length ^ m := by
      unfold N
      have : ind [] = fun _ => 1 := by funext w; simp [ind]
      rw [this, cnt_const]; simp
    rw [this]; simp [nI]
  | cons x R ih =>
    intro L hL hR hsub
    have hxL : x ∈ L := hsub x List.mem_cons_self
    have hxR : x ∉ R := (List.nodup_cons.mp hR).1
    have hR' : R.Nodup := (List.nodup_cons.mp hR).2
    have hx : x ∉ L.erase x := by
      intro h; exact ((List.Nodup.mem_erase_iff hL).mp h).1 rfl
    have hlen : (L.erase x).length = L.length - 1 := List.length_erase_of_mem hxL
    have hpos : 0 < L.length := List.length_pos_of_mem hxL
    have h1 := ih L hL hR' (fun y hy => hsub y (List.mem_cons_of_mem _ hy))
    have h2 := ih (L.erase x) (List.Nodup.erase x hL) hR' (by
      intro y hy
      rw [List.Nodup.mem_erase_iff hL]
      refine ⟨?_, hsub y (List.mem_cons_of_mem _ hy)⟩
      intro e; subst e; exact hxR hy)
    have hs := N_step L x R hx m
    have hs' : (N L m (x :: R) : Int) + (N (L.erase x) m R : Int) = (N L m R : Int) := by
      exact_mod_cast hs
    rw [List.length_cons, nI_succ_outer]
    simp only [nabla]
    rw [h2, hlen] at hs'
    have : ((L.length - 1 : Nat) : Int) = (L.length : Int) - 1 := by omega
    rw [this] at hs'
    omega

/-! ### mex = sum of indicators -/

/-- [letters i, i+1, ..., i+k-1 all occur in w] -/
def pre (w : List Nat) (i k : Nat) : Nat := if (∀ j, j < k → i + j ∈ w) then 1 else 0

theorem pre_succ (w : List Nat) (i k : Nat) :
    pre w i (k+1) = if i ∈ w then pre w (i+1) k else 0 := by
  unfold pre
  by_cases hi : i ∈ w
  · by_cases hk : (∀ j, j < k → i + 1 + j ∈ w)
    · have : ∀ j, j < k+1 → i + j ∈ w := by
        intro j hj
        cases j with
        | zero => simpa using hi
        | succ j => have := hk j (by omega); rwa [show i + (j+1) = i + 1 + j by omega]
      simp only [eq_true this, eq_true hk, hi, ↓reduceIte]
    · have : ¬ (∀ j, j < k+1 → i + j ∈ w) := by
        intro H; apply hk; intro j hj
        have := H (j+1) (by omega); rwa [show i + (j+1) = i + 1 + j by omega] at this
      simp [hi, hk, this]
  · have : ¬ (∀ j, j < k+1 → i + j ∈ w) := by
      intro H; apply hi; simpa using H 0 (by omega)
    simp [hi, this]

theorem mexFrom_succ (w : List Nat) : ∀ f i, mexFrom w (f+1) i = mexFrom w f i + pre w i (f+1) := by
  intro f
  induction f with
  | zero =>
    intro i
    rw [pre_succ]
    by_cases h : i ∈ w <;> simp [mexFrom, h, pre]
  | succ f ih =>
    intro i
    rw [pre_succ w i (f+1)]
    by_cases h : i ∈ w
    · show (if i ∈ w then mexFrom w (f+1) (i+1) else i)
          = (if i ∈ w then mexFrom w f (i+1) else i) + (if i ∈ w then pre w (i+1) (f+1) else 0)
      simp only [h, ↓reduceIte]; rw [ih]
    · simp [mexFrom, h]

theorem mexFrom_sum (w : List Nat) : ∀ f, mexFrom w f 0 = sumN (fun k => pre w 0 (k+1)) f := by
  intro f
  induction f with
  | zero => rfl
  | succ f ih =>
    rw [mexFrom_succ, ih]; rfl

theorem pre_eq_ind (w : List Nat) (k : Nat) : pre w 0 k = ind (List.range k) w := by
  unfold pre ind
  have : (∀ j, j < k → 0 + j ∈ w) ↔ (∀ y ∈ List.range k, y ∈ w) := by
    simp only [List.mem_range, Nat.zero_add]
  simp only [this]

/-! ### Nat/Int sums, vanishing of high differences -/

theorem sumN_cast (f : Nat → Nat) (K : Nat) : (sumN f K : Int) = sumI (fun k => (f k : Int)) K := by
  induction K with
  | zero => rfl
  | succ K ih => simp only [sumN, sumI]; rw [← ih]; omega

theorem nI_add : ∀ (a b : Nat) (g : Int → Int), nI (a + b) g = nI b (nI a g)
  | 0, b, g => by simp [nI]
  | a+1, b, g => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    show nI (a+b) (nabla g) = _
    rw [nI_add a b (nabla g)]; rfl

theorem nI_zero : ∀ (b : Nat), nI b (fun _ => 0) = fun _ => 0
  | 0 => rfl
  | b+1 => by
    show nI b (nabla (fun _ => 0)) = _
    have : nabla (fun _ : Int => (0:Int)) = fun _ => 0 := by funext x; simp [nabla]
    rw [this]; exact nI_zero b

theorem nI_high (m j : Nat) (hj : m + 1 ≤ j) (x : Int) : nI j (fun x => x ^ m) x = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, j = (m+1) + t := ⟨j - (m+1), by omega⟩
  rw [nI_add, D_kill m _ (D_pow m), nI_zero]

theorem sumI_tail (f : Nat → Int) (m : Nat) (hf : ∀ k, m ≤ k → f k = 0) :
    ∀ t, sumI f (m + t) = sumI f m
  | 0 => rfl
  | t+1 => by
    show sumI f (m + t) + f (m + t) = _
    rw [sumI_tail f m hf t, hf (m+t) (by omega)]; omega

/-! ### the final evaluation -/

theorem mex_sum_eq (m : Nat) :
    ((cnt (List.range (m+4)) m (fun w => mex (m+2) w) : Nat) : Int)
      = ((m+4 : Int) + 1) ^ m - (m+4 : Int) ^ m := by
  have h1 : cnt (List.range (m+4)) m (fun w => mex (m+2) w)
      = sumN (fun k => N (List.range (m+4)) m (List.range (k+1))) (m+3) := by
    unfold mex
    have : (fun w => mexFrom w (m+2+1) 0)
         = fun w => sumN (fun k => ind (List.range (k+1)) w) (m+3) := by
      funext w; rw [mexFrom_sum]; congr 1; funext k; exact pre_eq_ind w (k+1)
    rw [this, cnt_sumN]; rfl
  rw [h1, sumN_cast]
  have h2 : ∀ k, k < m + 3 →
      ((N (List.range (m+4)) m (List.range (k+1)) : Nat) : Int)
        = nI (k+1) (fun x => x ^ m) ((m + 4 : Int)) := by
    intro k hk
    have := N_eq m (List.range (k+1)) (List.range (m+4)) List.nodup_range List.nodup_range
      (by intro y hy; simp only [List.mem_range] at *; omega)
    rw [this]; simp
  have key : ∀ K, K ≤ m + 3 →
      sumI (fun k => ((N (List.range (m+4)) m (List.range (k+1)) : Nat) : Int)) K
        = sumI (fun k => nI (k+1) (fun x => x ^ m) ((m + 4 : Int))) K := by
    intro K
    induction K with
    | zero => intro _; rfl
    | succ K ih =>
      intro hK
      simp only [sumI]
      rw [ih (by omega), h2 K (by omega)]
  rw [key _ (Nat.le_refl _)]
  rw [show m + 3 = m + 3 from rfl]
  rw [sumI_tail (fun k => nI (k+1) (fun x => x ^ m) ((m + 4 : Int))) m
        (by intro k hk; exact nI_high m (k+1) (by omega) _) 3]
  exact abel_core m _

/-- Final instantiation: for all n >= 2, the explicit word sum equals (n+2)^(n-2)+(n+3)^(n-2). -/
theorem holeSum_eq (n : Nat) (hn : 2 ≤ n) : holeSum n = holeClosed n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold holeSum holeClosed
  have e : m + 2 - 2 = m := by omega
  have e2 : m + 2 + 2 = m + 4 := by omega
  have e3 : m + 2 + 3 = m + 5 := by omega
  rw [e, e2, e3]
  have hsplit : cnt (List.range (m+4)) m (fun w => 2 + mex (m+2) w)
      = 2 * (m+4)^m + cnt (List.range (m+4)) m (fun w => mex (m+2) w) := by
    rw [cnt_add, cnt_const]; simp
  rw [hsplit]
  have hm := mex_sum_eq m
  have hm' : ((cnt (List.range (m+4)) m (fun w => mex (m+2) w) : Nat) : Int)
      = ((m+5)^m : Nat) - ((m+4)^m : Nat) := by
    have a : ((m:Int) + 4 + 1) = ((m+5 : Nat) : Int) := by omega
    have b : ((m:Int) + 4) = ((m+4 : Nat) : Int) := by omega
    rw [hm, a, b, Int.natCast_pow, Int.natCast_pow]
  have hle : ((m+4)^m : Nat) ≤ (m+5)^m := Nat.pow_le_pow_left (by omega) m
  omega

end HoleW

#print axioms Hole.abel_core
#print axioms HoleW.N_eq
#print axioms HoleW.mex_sum_eq
#print axioms HoleW.holeSum_eq

/-! sanity: explicit sums, n = 2..7, versus the paper's hole(n) = 1, 2, 11, 85, 855, 10657, 159049 (n=1..). -/
#eval (List.range 6).map (fun i => HoleW.holeSum (i+2))
#eval (List.range 6).map (fun i => HoleW.holeClosed (i+2))
#eval (List.range 6).map (fun i => (i+2, HoleW.holeSum (i+2) == [2,11,85,855,10657,159049][i]!))
-- enumeration-based cross-check of cnt against explicit word lists
#eval ((HoleW.allWords (List.range 5) 1).map (fun w => 2 + HoleW.mex 3 w)).foldl (· + ·) 0 == HoleW.holeSum 3
#eval ((HoleW.allWords (List.range 6) 2).map (fun w => 2 + HoleW.mex 4 w)).foldl (· + ·) 0 == HoleW.holeSum 4
#eval ((HoleW.allWords (List.range 8) 4).map (fun w => 2 + HoleW.mex 6 w)).foldl (· + ·) 0 == HoleW.holeSum 6
