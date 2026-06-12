import Init

/-!
# Exponential partial sums over scaled integers

`S_N(p/q) = Σ_{j ≤ N} (p/q)^j / j!` is represented exactly by the integer
`expNum N p q = Σ_{j ≤ N} (N!/j!) p^j q^(N-j)`, so that
`S_N(p/q) = expNum N p q / (N! q^N)`. Arguments are nonnegative rationals
given as `Nat` pairs. For `t ≥ 0` the partial sums increase to `e^t`, which
is how the floor specification of `lnWad` is arithmetized: an upper bound
on `e^t` is `∀ N` a bound on `S_N`, a lower bound is witnessed by a single
`S_N`.

Everything here is `Nat` arithmetic: monotonicity in `N` and in the
argument, a geometric tail bound (turning one evaluated partial sum into a
bound for all `N`), and the binomial subset-product inequalities standing
in for `e^(a+b) = e^a * e^b`.
-/

set_option linter.unusedSimpArgs false

namespace LnExp

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero => decide
  | succ k ih => simp only [fact]; exact Nat.mul_pos (Nat.succ_pos k) ih

/-- `expNum N p q = Σ_{j ≤ N} (N!/j!) p^j q^(N-j)`, by the recursion
`E_{N+1} = (N+1) q E_N + p^(N+1)`. -/
def expNum : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | n + 1, p, q => (n + 1) * q * expNum n p q + p ^ (n + 1)

theorem expNum_pos {p q : Nat} (hq : 0 < q) : ∀ n, 0 < expNum n p q := by
  intro n
  induction n with
  | zero => simp only [expNum]; omega
  | succ k ih =>
    simp only [expNum]
    have h1 : 0 < (k + 1) * q * expNum k p q :=
      Nat.mul_pos (Nat.mul_pos (Nat.succ_pos k) hq) ih
    omega

/-- Comparison helpers: `S_N(p/q) ≤ y/w` and `S_N(p/q) ≥ y/w` as integer
inequalities (`q, w` positive at use sites). -/
def sumLE (n p q y w : Nat) : Prop := expNum n p q * w ≤ y * (fact n * q ^ n)
def sumGE (n p q y w : Nat) : Prop := y * (fact n * q ^ n) ≤ expNum n p q * w

instance (n p q y w : Nat) : Decidable (sumLE n p q y w) := by
  unfold sumLE; infer_instance
instance (n p q y w : Nat) : Decidable (sumGE n p q y w) := by
  unfold sumGE; infer_instance

/-! ## Finite sums -/

/-- `tsum n f = f 0 + f 1 + ... + f n`. -/
def tsum : Nat → (Nat → Nat) → Nat
  | 0, f => f 0
  | n + 1, f => tsum n f + f (n + 1)

theorem tsum_le_tsum {f g : Nat → Nat} {n : Nat} (h : ∀ i, i ≤ n → f i ≤ g i) :
    tsum n f ≤ tsum n g := by
  induction n with
  | zero => exact h 0 (Nat.le_refl 0)
  | succ k ih =>
    simp only [tsum]
    have h1 := ih (fun i hi => h i (Nat.le_succ_of_le hi))
    have h2 := h (k + 1) (Nat.le_refl _)
    omega

theorem tsum_congr {f g : Nat → Nat} {n : Nat} (h : ∀ i, i ≤ n → f i = g i) :
    tsum n f = tsum n g := by
  induction n with
  | zero => exact h 0 (Nat.le_refl 0)
  | succ k ih =>
    simp only [tsum]
    rw [ih (fun i hi => h i (Nat.le_succ_of_le hi)), h (k + 1) (Nat.le_refl _)]

theorem tsum_mul_const {f : Nat → Nat} {n c : Nat} :
    tsum n f * c = tsum n (fun i => f i * c) := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [tsum, Nat.add_mul, ih]

theorem const_mul_tsum {f : Nat → Nat} {n c : Nat} :
    c * tsum n f = tsum n (fun i => c * f i) := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [tsum, Nat.mul_add, ih]

theorem tsum_add {f g : Nat → Nat} {n : Nat} :
    tsum n (fun i => f i + g i) = tsum n f + tsum n g := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [tsum, ih]; omega

theorem first_le_tsum (f : Nat → Nat) (n : Nat) : f 0 ≤ tsum n f := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ k ih => simp only [tsum]; omega

theorem tsum_prefix_le {f : Nat → Nat} {n m : Nat} (h : n ≤ m) :
    tsum n f ≤ tsum m f := by
  induction m with
  | zero => cases Nat.le_zero.mp h; exact Nat.le_refl _
  | succ k ih =>
    rcases Nat.lt_or_ge n (k + 1) with hlt | hge
    · have := ih (by omega)
      simp only [tsum]
      omega
    · have he : n = k + 1 := by omega
      rw [he]
      exact Nat.le_refl _

/-- Sum transpose: diagonal-major to column-major over the triangle
`{(i, j) : i + j ≤ c}`. -/
theorem tri_transpose (T : Nat → Nat → Nat) (c : Nat) :
    tsum c (fun n => tsum n (fun i => T i (n - i))) =
      tsum c (fun i => tsum (c - i) (fun j => T i j)) := by
  induction c with
  | zero => rfl
  | succ k ih =>
    -- peel the diagonal n = k+1 on the left, the last entries on the right
    have hr : tsum (k + 1) (fun i => tsum (k + 1 - i) (fun j => T i j)) =
        tsum k (fun i => tsum (k - i) (fun j => T i j)) +
          tsum (k + 1) (fun i => T i (k + 1 - i)) := by
      have hsplit : ∀ i, i ≤ k →
          tsum (k + 1 - i) (fun j => T i j) =
            tsum (k - i) (fun j => T i j) + T i (k + 1 - i) := by
        intro i hi
        have he : k + 1 - i = (k - i) + 1 := by omega
        rw [he]
        rfl
      calc tsum (k + 1) (fun i => tsum (k + 1 - i) (fun j => T i j))
          = tsum k (fun i => tsum (k + 1 - i) (fun j => T i j)) +
              tsum 0 (fun j => T (k + 1) j) := by
            show tsum k _ + tsum (k + 1 - (k + 1)) _ = _
            rw [Nat.sub_self]
        _ = tsum k (fun i => tsum (k - i) (fun j => T i j) + T i (k + 1 - i)) +
              T (k + 1) 0 := by
            rw [tsum_congr (fun i hi => hsplit i hi)]
            rfl
        _ = tsum k (fun i => tsum (k - i) (fun j => T i j)) +
              tsum k (fun i => T i (k + 1 - i)) + T (k + 1) 0 := by
            rw [tsum_add]
        _ = tsum k (fun i => tsum (k - i) (fun j => T i j)) +
              tsum (k + 1) (fun i => T i (k + 1 - i)) := by
            have : tsum (k + 1) (fun i => T i (k + 1 - i)) =
                tsum k (fun i => T i (k + 1 - i)) + T (k + 1) 0 := by
              have he : k + 1 - (k + 1) = 0 := by omega
              simp only [tsum, he]
            omega
    simp only [tsum] at *
    omega

/-- Box-into-triangle: summing a nonnegative term over `[0,N] × [0,M]` is at
most the sum over the triangle `{i + j ≤ N + M}`. -/
theorem box_le_tri (T : Nat → Nat → Nat) (N M : Nat) :
    tsum N (fun i => tsum M (fun j => T i j)) ≤
      tsum (N + M) (fun n => tsum n (fun i => T i (n - i))) := by
  rw [tri_transpose]
  calc tsum N (fun i => tsum M (fun j => T i j))
      ≤ tsum N (fun i => tsum (N + M - i) (fun j => T i j)) :=
        tsum_le_tsum (fun i hi => tsum_prefix_le (by omega))
    _ ≤ tsum (N + M) (fun i => tsum (N + M - i) (fun j => T i j)) :=
        tsum_prefix_le (by omega)

/-- Triangle-into-box: the triangle `{i + j ≤ K}` sits inside `[0,K] × [0,K]`. -/
theorem tri_le_box (T : Nat → Nat → Nat) (K : Nat) :
    tsum K (fun n => tsum n (fun i => T i (n - i))) ≤
      tsum K (fun i => tsum K (fun j => T i j)) := by
  rw [tri_transpose]
  exact tsum_le_tsum (fun i hi => tsum_prefix_le (by omega))

/-! ## Coefficients -/

/-- Rising product: `ffacAux j d = (j+1)(j+2)...(j+d) = (j+d)!/j!`. -/
def ffacAux (j : Nat) : Nat → Nat
  | 0 => 1
  | d + 1 => (j + d + 1) * ffacAux j d

theorem ffacAux_mul_fact (j : Nat) : ∀ d, ffacAux j d * fact j = fact (j + d) := by
  intro d
  induction d with
  | zero => simp only [ffacAux, Nat.one_mul, Nat.add_zero]
  | succ k ih =>
    simp only [ffacAux]
    calc (j + k + 1) * ffacAux j k * fact j
        = (j + k + 1) * (ffacAux j k * fact j) := by rw [Nat.mul_assoc]
      _ = (j + k + 1) * fact (j + k) := by rw [ih]
      _ = fact (j + k + 1) := rfl

/-- Front peel: `tsum (n+1) f = f 0 + Σ_{i ≤ n} f (i+1)`. -/
theorem tsum_shift (f : Nat → Nat) (n : Nat) :
    tsum (n + 1) f = f 0 + tsum n (fun i => f (i + 1)) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    have h1 : tsum (m + 2) f = tsum (m + 1) f + f (m + 2) := rfl
    have h2 : tsum (m + 1) (fun i => f (i + 1)) =
        tsum m (fun i => f (i + 1)) + f (m + 2) := rfl
    rw [h1, ih, h2]
    omega

/-- Pascal-recursive binomial coefficient. -/
def cho : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, i + 1 => cho n i + cho n (i + 1)

theorem cho_eq_zero_of_lt : ∀ {n i : Nat}, n < i → cho n i = 0 := by
  intro n
  induction n with
  | zero => intro i h; match i, h with | i + 1, _ => rfl
  | succ k ih =>
    intro i h
    match i, h with
    | i + 1, h =>
      show cho k i + cho k (i + 1) = 0
      rw [ih (by omega), ih (by omega)]

theorem cho_self : ∀ n, cho n n = 1 := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    show cho k k + cho k (k + 1) = 1
    rw [ih, cho_eq_zero_of_lt (Nat.lt_succ_self k)]

theorem cho_fact : ∀ n i, i ≤ n → cho n i * (fact i * fact (n - i)) = fact n := by
  intro n
  induction n with
  | zero => intro i h; cases Nat.le_zero.mp h; rfl
  | succ k ih =>
    intro i h
    match i with
    | 0 =>
      show 1 * (1 * fact (k + 1)) = fact (k + 1)
      omega
    | i + 1 =>
      show (cho k i + cho k (i + 1)) * (fact (i + 1) * fact (k + 1 - (i + 1))) =
        fact (k + 1)
      have hf1 : fact (i + 1) = (i + 1) * fact i := rfl
      rcases Nat.lt_or_ge k (i + 1) with hlt | hge
      · -- top of the column: i = k, the second binomial vanishes
        have he : i = k := by omega
        rw [he, cho_self, show cho k (k + 1) = 0 from cho_eq_zero_of_lt (Nat.lt_succ_self k),
          Nat.sub_self]
        show (1 + 0) * (fact (k + 1) * 1) = fact (k + 1)
        omega
      · have h1 := ih i (by omega)
        have h2 := ih (i + 1) hge
        have hs1 : k + 1 - (i + 1) = k - i := by omega
        have hs2 : k - i = (k - (i + 1)) + 1 := by omega
        -- cho k i * ((i+1)! * (k-i)!) = (i+1) * k!
        have e1 : cho k i * (fact (i + 1) * fact (k - i)) = (i + 1) * fact k := by
          rw [hf1, ← h1]
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        -- cho k (i+1) * ((i+1)! * (k-i)!) = (k-i) * k!
        have e2 : cho k (i + 1) * (fact (i + 1) * fact (k - i)) = (k - i) * fact k := by
          rw [hs2, show fact ((k - (i + 1)) + 1) = ((k - (i + 1)) + 1) * fact (k - (i + 1))
            from rfl, ← h2]
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        rw [hs1, Nat.add_mul, e1, e2, ← Nat.add_mul]
        have hc : i + 1 + (k - i) = k + 1 := by omega
        rw [hc]
        rfl

/-- Binomial theorem. -/
theorem add_pow (a b n : Nat) :
    (a + b) ^ n = tsum n (fun i => cho n i * a ^ i * b ^ (n - i)) := by
  induction n with
  | zero =>
    show 1 = cho 0 0 * a ^ 0 * b ^ 0
    rfl
  | succ k ih =>
    have step : (a + b) ^ (k + 1) =
        tsum k (fun i => cho k i * a ^ (i + 1) * b ^ (k - i)) +
          tsum k (fun i => cho k i * a ^ i * b ^ (k + 1 - i)) := by
      have hx : (a + b) ^ (k + 1) = (a + b) ^ k * a + (a + b) ^ k * b := by
        rw [Nat.pow_succ, Nat.mul_add]
      rw [hx, ih, tsum_mul_const, tsum_mul_const]
      congr 1
      · refine tsum_congr (fun i hi => ?_)
        rw [Nat.pow_succ]
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      · refine tsum_congr (fun i hi => ?_)
        rw [show k + 1 - i = (k - i) + 1 by omega, Nat.pow_succ]
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [step]
    have peel : tsum (k + 1) (fun i => cho (k + 1) i * a ^ i * b ^ (k + 1 - i)) =
        b ^ (k + 1) +
          tsum k (fun i => cho (k + 1) (i + 1) * a ^ (i + 1) * b ^ (k - i)) := by
      rw [tsum_shift]
      congr 1
      · show cho (k + 1) 0 * a ^ 0 * b ^ (k + 1) = b ^ (k + 1)
        show 1 * 1 * b ^ (k + 1) = b ^ (k + 1)
        omega
      · exact tsum_congr (fun i hi => by rw [show k + 1 - (i + 1) = k - i by omega])
    rw [peel]
    have pascal : tsum k (fun i => cho (k + 1) (i + 1) * a ^ (i + 1) * b ^ (k - i)) =
        tsum k (fun i => cho k i * a ^ (i + 1) * b ^ (k - i)) +
          tsum k (fun i => cho k (i + 1) * a ^ (i + 1) * b ^ (k - i)) := by
      rw [← tsum_add]
      refine tsum_congr (fun i hi => ?_)
      show (cho k i + cho k (i + 1)) * _ * _ = _
      rw [Nat.add_mul, Nat.add_mul]
    rw [pascal]
    -- the b-branch of `step` equals b^(k+1) plus the shifted Pascal remainder
    have hb : tsum k (fun i => cho k i * a ^ i * b ^ (k + 1 - i)) =
        b ^ (k + 1) + tsum k (fun i => cho k (i + 1) * a ^ (i + 1) * b ^ (k - i)) := by
      cases k with
      | zero =>
        show cho 0 0 * a ^ 0 * b ^ 1 = b ^ 1 + cho 0 1 * a ^ 1 * b ^ 0
        show 1 * 1 * b ^ 1 = b ^ 1 + 0 * a ^ 1 * b ^ 0
        omega
      | succ m =>
        rw [tsum_shift]
        have hcong : tsum m
            (fun i => cho (m + 1) (i + 1) * a ^ (i + 1) * b ^ (m + 1 + 1 - (i + 1))) =
            tsum m (fun i => cho (m + 1) (i + 1) * a ^ (i + 1) * b ^ (m + 1 - i)) :=
          tsum_congr (fun i hi => by
            rw [show m + 1 + 1 - (i + 1) = m + 1 - i by omega])
        have hext : tsum (m + 1)
            (fun i => cho (m + 1) (i + 1) * a ^ (i + 1) * b ^ (m + 1 - i)) =
            tsum m (fun i => cho (m + 1) (i + 1) * a ^ (i + 1) * b ^ (m + 1 - i)) +
              cho (m + 1) (m + 2) * a ^ (m + 2) * b ^ (m + 1 - (m + 1)) := rfl
        have hz : cho (m + 1) (m + 2) = 0 := cho_eq_zero_of_lt (by omega)
        rw [hz, Nat.zero_mul, Nat.zero_mul, Nat.add_zero] at hext
        show 1 * 1 * b ^ (m + 2) +
            tsum m (fun i => cho (m + 1) (i + 1) * a ^ (i + 1) *
              b ^ (m + 1 + 1 - (i + 1))) =
          b ^ (m + 2) +
            tsum (m + 1) (fun i => cho (m + 1) (i + 1) * a ^ (i + 1) * b ^ (m + 1 - i))
        rw [hcong, hext]
        omega
    rw [hb]
    omega

/-! ## `expNum` as a sum, and the product inequalities -/

theorem expNum_eq_tsum (n p q : Nat) :
    expNum n p q = tsum n (fun j => ffacAux j (n - j) * p ^ j * q ^ (n - j)) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show (k + 1) * q * expNum k p q + p ^ (k + 1) = _
    rw [ih, const_mul_tsum]
    have hsum : tsum k (fun j => (k + 1) * q *
        (ffacAux j (k - j) * p ^ j * q ^ (k - j))) =
        tsum k (fun j => ffacAux j (k + 1 - j) * p ^ j * q ^ (k + 1 - j)) := by
      refine tsum_congr (fun j hj => ?_)
      have h1 : k + 1 - j = (k - j) + 1 := by omega
      rw [h1]
      have h2 : ffacAux j (k - j + 1) = (j + (k - j) + 1) * ffacAux j (k - j) := rfl
      rw [h2, show j + (k - j) + 1 = k + 1 by omega, Nat.pow_succ]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [hsum]
    have hlast : tsum (k + 1) (fun j => ffacAux j (k + 1 - j) * p ^ j * q ^ (k + 1 - j)) =
        tsum k (fun j => ffacAux j (k + 1 - j) * p ^ j * q ^ (k + 1 - j)) +
          ffacAux (k + 1) (k + 1 - (k + 1)) * p ^ (k + 1) * q ^ (k + 1 - (k + 1)) := rfl
    rw [hlast, Nat.sub_self]
    show _ = _ + 1 * p ^ (k + 1) * 1
    omega

theorem mul_pos' {a b : Nat} (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
  Nat.mul_pos ha hb

/-- The convolution coefficient identity behind both product inequalities. -/
theorem coef_eq {N M i j : Nat} (hi : i ≤ N) (hj : j ≤ M) :
    ffacAux i (N - i) * ffacAux j (M - j) * fact (N + M) =
      fact N * fact M * (ffacAux (i + j) (N + M - (i + j)) * cho (i + j) i) := by
  refine Nat.eq_of_mul_eq_mul_right (mul_pos' (fact_pos i) (fact_pos j)) ?_
  have hL : ffacAux i (N - i) * ffacAux j (M - j) * fact (N + M) * (fact i * fact j) =
      (ffacAux i (N - i) * fact i) * ((ffacAux j (M - j) * fact j) * fact (N + M)) := by
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hL, ffacAux_mul_fact, ffacAux_mul_fact,
    show i + (N - i) = N by omega, show j + (M - j) = M by omega]
  have hR : fact N * fact M * (ffacAux (i + j) (N + M - (i + j)) * cho (i + j) i) *
      (fact i * fact j) =
      fact N * (fact M * (ffacAux (i + j) (N + M - (i + j)) *
        (cho (i + j) i * (fact i * fact j)))) := by
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hR, show fact j = fact (i + j - i) by rw [show i + j - i = j by omega],
    cho_fact (i + j) i (by omega), ffacAux_mul_fact,
    show i + j + (N + M - (i + j)) = N + M by omega]

theorem tsum_mul_tsum (f g : Nat → Nat) (N M c : Nat) :
    tsum N f * tsum M g * c =
      tsum N (fun i => tsum M (fun j => f i * (g j * c))) := by
  calc tsum N f * tsum M g * c
      = tsum N (fun i => f i * (tsum M g * c)) := by
        rw [Nat.mul_assoc, tsum_mul_const]
    _ = tsum N (fun i => tsum M (fun j => f i * (g j * c))) := by
        refine tsum_congr (fun i hi => ?_)
        rw [tsum_mul_const, const_mul_tsum]

/-- Box form of a product of two partial sums (times a constant). -/
theorem expNum_mul_box (N M p1 p2 q c : Nat) :
    expNum N p1 q * expNum M p2 q * c =
      tsum N (fun i => tsum M (fun j =>
        ffacAux i (N - i) * ffacAux j (M - j) * c *
          (p1 ^ i * (p2 ^ j * (q ^ (N - i) * q ^ (M - j)))))) := by
  rw [expNum_eq_tsum, expNum_eq_tsum, tsum_mul_tsum]
  refine tsum_congr (fun i hi => tsum_congr (fun j hj => ?_))
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Second convolution coefficient identity (triangle side, equal scales). -/
theorem coef_eq2 {K n i : Nat} (hn : n ≤ K) (hi : i ≤ n) :
    ffacAux n (K - n) * cho n i * fact K =
      ffacAux i (K - i) * ffacAux (n - i) (K - (n - i)) := by
  refine Nat.eq_of_mul_eq_mul_right (mul_pos' (fact_pos i) (fact_pos (n - i))) ?_
  have hL : ffacAux n (K - n) * cho n i * fact K * (fact i * fact (n - i)) =
      ffacAux n (K - n) * ((cho n i * (fact i * fact (n - i))) * fact K) := by
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hL, cho_fact n i hi]
  have hL2 : ffacAux n (K - n) * (fact n * fact K) =
      (ffacAux n (K - n) * fact n) * fact K := by
    rw [Nat.mul_assoc]
  rw [hL2, ffacAux_mul_fact, show n + (K - n) = K by omega]
  have hR : ffacAux i (K - i) * ffacAux (n - i) (K - (n - i)) * (fact i * fact (n - i)) =
      (ffacAux i (K - i) * fact i) * (ffacAux (n - i) (K - (n - i)) * fact (n - i)) := by
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hR, ffacAux_mul_fact, ffacAux_mul_fact, show i + (K - i) = K by omega,
    show n - i + (K - (n - i)) = K by omega]

/-- Triangle form of a partial sum at a sum argument (times a constant). -/
theorem expNum_add_tri (C p1 p2 q c : Nat) :
    expNum C (p1 + p2) q * c =
      tsum C (fun n => tsum n (fun i =>
        ffacAux (i + (n - i)) (C - (i + (n - i))) * cho (i + (n - i)) i * c *
          (p1 ^ i * (p2 ^ (n - i) * q ^ (C - (i + (n - i))))))) := by
  rw [expNum_eq_tsum, tsum_mul_const]
  refine tsum_congr (fun n hn => ?_)
  show ffacAux n (C - n) * (p1 + p2) ^ n * q ^ (C - n) * c = _
  rw [add_pow, const_mul_tsum, tsum_mul_const, tsum_mul_const]
  refine tsum_congr (fun i hi => ?_)
  rw [show i + (n - i) = n by omega]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- `S_N(p1/q) S_M(p2/q) ≤ S_{N+M}((p1+p2)/q)`, integer-scaled. -/
theorem prod_le_sum (N M p1 p2 q : Nat) :
    expNum N p1 q * expNum M p2 q * fact (N + M) ≤
      expNum (N + M) (p1 + p2) q * (fact N * fact M) := by
  rw [expNum_mul_box N M p1 p2 q (fact (N + M)),
    expNum_add_tri (N + M) p1 p2 q (fact N * fact M)]
  refine Nat.le_trans (tsum_le_tsum fun i hi => tsum_le_tsum fun j hj =>
    Nat.le_of_eq ?_)
    (box_le_tri (fun i j =>
      ffacAux (i + j) (N + M - (i + j)) * cho (i + j) i * (fact N * fact M) *
        (p1 ^ i * (p2 ^ j * q ^ (N + M - (i + j))))) N M)
  have hq : q ^ (N - i) * q ^ (M - j) = q ^ (N + M - (i + j)) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hq, coef_eq hi hj]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- `S_K((p1+p2)/q) ≤ S_K(p1/q) S_K(p2/q)`, integer-scaled. -/
theorem sum_le_prod (K p1 p2 q : Nat) :
    expNum K (p1 + p2) q * (fact K * q ^ K) ≤ expNum K p1 q * expNum K p2 q := by
  rw [expNum_add_tri K p1 p2 q (fact K * q ^ K),
    show expNum K p1 q * expNum K p2 q = expNum K p1 q * expNum K p2 q * 1 from
      (Nat.mul_one _).symm,
    expNum_mul_box K K p1 p2 q 1]
  refine Nat.le_trans (Nat.le_of_eq ?_)
    (tri_le_box (fun i j =>
      ffacAux i (K - i) * ffacAux j (K - j) * 1 *
        (p1 ^ i * (p2 ^ j * (q ^ (K - i) * q ^ (K - j))))) K)
  refine tsum_congr (fun n hn => tsum_congr (fun i hi => ?_))
  rw [show i + (n - i) = n by omega,
    show ffacAux i (K - i) * ffacAux (n - i) (K - (n - i)) =
      ffacAux n (K - n) * cho n i * fact K from (coef_eq2 hn hi).symm,
    show q ^ (K - i) * q ^ (K - (n - i)) = q ^ K * q ^ (K - n) from by
      rw [← Nat.pow_add, ← Nat.pow_add]
      congr 1
      omega]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_one, Nat.one_mul]

/-! ## Monotonicity and the tail bound -/

/-- Cross-scale fraction transitivity: `a/b ≤ c/d ≤ e/f → a/b ≤ e/f`. -/
theorem div_le_trans {a b c d e f : Nat} (hd : 0 < d)
    (h1 : a * d ≤ c * b) (h2 : c * f ≤ e * d) : a * f ≤ e * b := by
  refine Nat.le_of_mul_le_mul_right ?_ hd
  calc a * f * d = a * d * f := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ c * b * f := Nat.mul_le_mul_right f h1
    _ = c * f * b := by simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ e * d * b := Nat.mul_le_mul_right b h2
    _ = e * b * d := by simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem expNum_step_le (n p q : Nat) :
    (n + 1) * q * expNum n p q ≤ expNum (n + 1) p q := by
  show _ ≤ (n + 1) * q * expNum n p q + p ^ (n + 1)
  omega

/-- `S_n ≤ S_m` for `n ≤ m`, cross-scaled. -/
theorem expNum_mono_N {p q : Nat} {n m : Nat} (h : n ≤ m) :
    expNum n p q * (fact m * q ^ m) ≤ expNum m p q * (fact n * q ^ n) := by
  have key : ∀ d, expNum n p q * (fact (n + d) * q ^ (n + d)) ≤
      expNum (n + d) p q * (fact n * q ^ n) := by
    intro d
    induction d with
    | zero => exact Nat.le_refl _
    | succ k ih =>
      have hf : fact (n + (k + 1)) = (n + k + 1) * fact (n + k) := rfl
      have hp : q ^ (n + (k + 1)) = q ^ (n + k) * q := by
        rw [show n + (k + 1) = (n + k) + 1 by omega, Nat.pow_succ]
      have e1 : expNum n p q * (fact (n + (k + 1)) * q ^ (n + (k + 1))) =
          (n + k + 1) * q * (expNum n p q * (fact (n + k) * q ^ (n + k))) := by
        rw [hf, hp]
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e1]
      have step1 : (n + k + 1) * q * (expNum n p q * (fact (n + k) * q ^ (n + k))) ≤
          (n + k + 1) * q * (expNum (n + k) p q * (fact n * q ^ n)) :=
        Nat.mul_le_mul_left _ ih
      have e2 : (n + k + 1) * q * (expNum (n + k) p q * (fact n * q ^ n)) =
          (n + k + 1) * q * expNum (n + k) p q * (fact n * q ^ n) := by
        simp only [Nat.mul_assoc]
      have step2 : (n + k + 1) * q * expNum (n + k) p q * (fact n * q ^ n) ≤
          expNum (n + k + 1) p q * (fact n * q ^ n) :=
        Nat.mul_le_mul_right _ (expNum_step_le (n + k) p q)
      rw [show n + (k + 1) = n + k + 1 from rfl]
      omega
  have hkey := key (m - n)
  rw [show n + (m - n) = m by omega] at hkey
  exact hkey

/-- Argument monotonicity: `p/q ≤ p'/q'` gives `S_n(p/q) ≤ S_n(p'/q')`. -/
theorem expNum_arg_mono {p q p' q' : Nat} (h : p * q' ≤ p' * q) (n : Nat) :
    expNum n p q * q' ^ n ≤ expNum n p' q' * q ^ n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    show ((k + 1) * q * expNum k p q + p ^ (k + 1)) * q' ^ (k + 1) ≤
      ((k + 1) * q' * expNum k p' q' + p' ^ (k + 1)) * q ^ (k + 1)
    rw [Nat.add_mul ((k + 1) * q * expNum k p q) (p ^ (k + 1)) (q' ^ (k + 1)),
      Nat.add_mul ((k + 1) * q' * expNum k p' q') (p' ^ (k + 1)) (q ^ (k + 1))]
    have h1 : (k + 1) * q * expNum k p q * q' ^ (k + 1) ≤
        (k + 1) * q' * expNum k p' q' * q ^ (k + 1) := by
      have e1 : (k + 1) * q * expNum k p q * q' ^ (k + 1) =
          (k + 1) * (q * q') * (expNum k p q * q' ^ k) := by
        rw [Nat.pow_succ]
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have e2 : (k + 1) * q' * expNum k p' q' * q ^ (k + 1) =
          (k + 1) * (q * q') * (expNum k p' q' * q ^ k) := by
        rw [Nat.pow_succ]
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e1, e2]
      exact Nat.mul_le_mul_left _ ih
    have h2 : p ^ (k + 1) * q' ^ (k + 1) ≤ p' ^ (k + 1) * q ^ (k + 1) := by
      rw [← Nat.mul_pow, ← Nat.mul_pow]
      exact Nat.pow_le_pow_left h (k + 1)
    omega

theorem expNum_zero_arg (n q : Nat) : expNum n 0 q = fact n * q ^ n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show (k + 1) * q * expNum k 0 q + 0 ^ (k + 1) = fact (k + 1) * q ^ (k + 1)
    rw [ih, show (0 : Nat) ^ (k + 1) = 0 by rw [Nat.zero_pow (by omega)],
      show fact (k + 1) = (k + 1) * fact k from rfl, Nat.pow_succ]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega

/-- One step of the decreasing tail potential
`B_M = (E_M (M+1) q + 2 p^(M+1)) / ((M+1)! q^(M+1))`, for `2p ≤ (M+2)q`. -/
theorem tail_potential_step {p q M : Nat} (hM : 2 * p ≤ (M + 2) * q) :
    expNum (M + 1) p q * ((M + 2) * q) + 2 * p ^ (M + 2) ≤
      (expNum M p q * ((M + 1) * q) + 2 * p ^ (M + 1)) * ((M + 2) * q) := by
  have hE : expNum (M + 1) p q = (M + 1) * q * expNum M p q + p ^ (M + 1) := rfl
  have hp2 : p ^ (M + 2) = p * p ^ (M + 1) := by
    rw [show M + 2 = (M + 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
  have hkey : 2 * (p * p ^ (M + 1)) ≤ (M + 2) * q * p ^ (M + 1) := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ hM
  have eL : expNum (M + 1) p q * ((M + 2) * q) + 2 * p ^ (M + 2) =
      expNum M p q * ((M + 1) * q) * ((M + 2) * q) +
        (M + 2) * q * p ^ (M + 1) + 2 * (p * p ^ (M + 1)) := by
    rw [hE, hp2, Nat.add_mul ((M + 1) * q * expNum M p q) (p ^ (M + 1)) ((M + 2) * q)]
    have a1 : (M + 1) * q * expNum M p q * ((M + 2) * q) =
        expNum M p q * ((M + 1) * q) * ((M + 2) * q) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have a2 : p ^ (M + 1) * ((M + 2) * q) = (M + 2) * q * p ^ (M + 1) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega
  have eR : (expNum M p q * ((M + 1) * q) + 2 * p ^ (M + 1)) * ((M + 2) * q) =
      expNum M p q * ((M + 1) * q) * ((M + 2) * q) +
        2 * ((M + 2) * q * p ^ (M + 1)) := by
    rw [Nat.add_mul (expNum M p q * ((M + 1) * q)) (2 * p ^ (M + 1)) ((M + 2) * q)]
    have a3 : 2 * p ^ (M + 1) * ((M + 2) * q) = 2 * ((M + 2) * q * p ^ (M + 1)) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega
  omega

/-- All partial sums beyond `K` stay under the `K`-th tail potential:
`S_M ≤ B_K` for `M ≥ K` when `2p ≤ (K+2)q`. -/
theorem tail_bound {p q K : Nat} (hq : 0 < q) (hK : 2 * p ≤ (K + 2) * q) :
    ∀ M, expNum M p q * (fact (K + 1) * q ^ (K + 1)) ≤
      (expNum K p q * ((K + 1) * q) + 2 * p ^ (K + 1)) * (fact M * q ^ M) := by
  -- denominators are positive
  have hden : ∀ j, 0 < fact j * q ^ j := fun j =>
    mul_pos' (fact_pos j) (Nat.pow_pos hq)
  -- B_(K+d) ≤ B_K by chaining the potential step
  have hB : ∀ d,
      (expNum (K + d) p q * ((K + d + 1) * q) + 2 * p ^ (K + d + 1)) *
          (fact (K + 1) * q ^ (K + 1)) ≤
        (expNum K p q * ((K + 1) * q) + 2 * p ^ (K + 1)) *
          (fact (K + d + 1) * q ^ (K + d + 1)) := by
    intro d
    induction d with
    | zero => exact Nat.le_refl _
    | succ e ih =>
      have hstep := tail_potential_step (p := p) (q := q) (M := K + e)
        (by have : (K + 2) * q ≤ (K + e + 2) * q := Nat.mul_le_mul_right q (by omega)
            omega)
      -- B_(K+e+1) ≤ B_(K+e) cross-scaled, then transitivity with ih
      have hcross : (expNum (K + e + 1) p q * ((K + e + 2) * q) + 2 * p ^ (K + e + 2)) *
          (fact (K + e + 1) * q ^ (K + e + 1)) ≤
          (expNum (K + e) p q * ((K + e + 1) * q) + 2 * p ^ (K + e + 1)) *
            (fact (K + e + 2) * q ^ (K + e + 2)) := by
        have hf : fact (K + e + 2) = (K + e + 2) * fact (K + e + 1) := rfl
        have hp : q ^ (K + e + 2) = q ^ (K + e + 1) * q := by
          rw [show K + e + 2 = (K + e + 1) + 1 by omega, Nat.pow_succ]
        rw [hf, hp]
        have e1 : (expNum (K + e) p q * ((K + e + 1) * q) + 2 * p ^ (K + e + 1)) *
            ((K + e + 2) * fact (K + e + 1) * (q ^ (K + e + 1) * q)) =
            ((expNum (K + e) p q * ((K + e + 1) * q) + 2 * p ^ (K + e + 1)) *
              ((K + e + 2) * q)) * (fact (K + e + 1) * q ^ (K + e + 1)) := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        rw [e1]
        exact Nat.mul_le_mul_right _ (by
          rw [show K + e + 1 + 1 = K + e + 2 by omega] at hstep
          exact hstep)
      rw [show K + (e + 1) = K + e + 1 by omega]
      exact div_le_trans (hden (K + e + 1)) hcross ih
  intro M
  rcases Nat.lt_or_ge M K with hlt | hge
  · -- below K: S_M ≤ S_K ≤ B_K
    have hmono := expNum_mono_N (p := p) (q := q) (Nat.le_of_lt hlt)
    have hSK : expNum K p q * (fact (K + 1) * q ^ (K + 1)) ≤
        (expNum K p q * ((K + 1) * q) + 2 * p ^ (K + 1)) * (fact K * q ^ K) := by
      have e1 : expNum K p q * (fact (K + 1) * q ^ (K + 1)) =
          expNum K p q * ((K + 1) * q) * (fact K * q ^ K) := by
        rw [show fact (K + 1) = (K + 1) * fact K from rfl, Nat.pow_succ]
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e1]
      exact Nat.mul_le_mul_right _ (by omega)
    exact div_le_trans (hden K) hmono hSK
  · -- at or above K: S_M ≤ B_M ≤ B_K
    have hSM : expNum M p q * (fact (M + 1) * q ^ (M + 1)) ≤
        (expNum M p q * ((M + 1) * q) + 2 * p ^ (M + 1)) * (fact M * q ^ M) := by
      have e1 : expNum M p q * (fact (M + 1) * q ^ (M + 1)) =
          expNum M p q * ((M + 1) * q) * (fact M * q ^ M) := by
        rw [show fact (M + 1) = (M + 1) * fact M from rfl, Nat.pow_succ]
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e1]
      exact Nat.mul_le_mul_right _ (by omega)
    have hBM := hB (M - K)
    rw [show K + (M - K) = M by omega] at hBM
    exact div_le_trans (hden (M + 1)) hSM hBM

/-! ## Exponential caps

`capUB p q y w` says `e^(p/q) ≤ y/w` (every partial sum is bounded);
`capLB p q y w` says `e^(p/q) ≥ y/w` (some partial sum already reaches it).
These four-`Nat` relations are the interface the floor-specification
assembly uses; the lemmas below are the surrogates for
`e^(a+b) = e^a e^b` and monotonicity.
-/

def capUB (p q y w : Nat) : Prop := ∀ n, expNum n p q * w ≤ y * (fact n * q ^ n)

def capLB (p q y w : Nat) : Prop := ∃ n, y * (fact n * q ^ n) ≤ expNum n p q * w

theorem capUB_mul {p1 p2 q y1 w1 y2 w2 : Nat} (hq : 0 < q)
    (h1 : capUB p1 q y1 w1) (h2 : capUB p2 q y2 w2) :
    capUB (p1 + p2) q (y1 * y2) (w1 * w2) := by
  intro n
  have hd : 0 < fact n * q ^ n := mul_pos' (fact_pos n) (Nat.pow_pos hq)
  refine Nat.le_of_mul_le_mul_right ?_ hd
  calc expNum n (p1 + p2) q * (w1 * w2) * (fact n * q ^ n)
      = expNum n (p1 + p2) q * (fact n * q ^ n) * (w1 * w2) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ expNum n p1 q * expNum n p2 q * (w1 * w2) :=
        Nat.mul_le_mul_right _ (sum_le_prod n p1 p2 q)
    _ = (expNum n p1 q * w1) * (expNum n p2 q * w2) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (y1 * (fact n * q ^ n)) * (y2 * (fact n * q ^ n)) :=
        Nat.mul_le_mul (h1 n) (h2 n)
    _ = y1 * y2 * (fact n * q ^ n) * (fact n * q ^ n) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem capLB_mul {p1 p2 q y1 w1 y2 w2 : Nat}
    (h1 : capLB p1 q y1 w1) (h2 : capLB p2 q y2 w2) :
    capLB (p1 + p2) q (y1 * y2) (w1 * w2) := by
  obtain ⟨n1, e1⟩ := h1
  obtain ⟨n2, e2⟩ := h2
  refine ⟨n1 + n2, ?_⟩
  have hd : 0 < fact n1 * fact n2 := mul_pos' (fact_pos n1) (fact_pos n2)
  refine Nat.le_of_mul_le_mul_right ?_ hd
  calc y1 * y2 * (fact (n1 + n2) * q ^ (n1 + n2)) * (fact n1 * fact n2)
      = (y1 * (fact n1 * q ^ n1)) * (y2 * (fact n2 * q ^ n2)) * fact (n1 + n2) := by
        rw [show q ^ (n1 + n2) = q ^ n1 * q ^ n2 from Nat.pow_add q n1 n2]
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (expNum n1 p1 q * w1) * (expNum n2 p2 q * w2) * fact (n1 + n2) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul e1 e2)
    _ = expNum n1 p1 q * expNum n2 p2 q * fact (n1 + n2) * (w1 * w2) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ expNum (n1 + n2) (p1 + p2) q * (fact n1 * fact n2) * (w1 * w2) :=
        Nat.mul_le_mul_right _ (prod_le_sum n1 n2 p1 p2 q)
    _ = expNum (n1 + n2) (p1 + p2) q * (w1 * w2) * (fact n1 * fact n2) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Quotient mover: from `e^(a+b) ≤ C/W` and `e^b ≥ G/V`, get `e^a ≤ CV/(WG)`. -/
theorem capUB_cancel {pa pb q C W G V : Nat} (hq : 0 < q)
    (hsum : capUB (pa + pb) q C W) (hb : capLB pb q G V) :
    capUB pa q (C * V) (W * G) := by
  intro n
  obtain ⟨m, hm⟩ := hb
  have hd : 0 < fact m * q ^ m * fact (n + m) :=
    mul_pos' (mul_pos' (fact_pos m) (Nat.pow_pos hq)) (fact_pos (n + m))
  refine Nat.le_of_mul_le_mul_right ?_ hd
  calc expNum n pa q * (W * G) * (fact m * q ^ m * fact (n + m))
      = (G * (fact m * q ^ m)) * (expNum n pa q * W * fact (n + m)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (expNum m pb q * V) * (expNum n pa q * W * fact (n + m)) :=
        Nat.mul_le_mul_right _ hm
    _ = (expNum n pa q * expNum m pb q * fact (n + m)) * (W * V) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (expNum (n + m) (pa + pb) q * (fact n * fact m)) * (W * V) :=
        Nat.mul_le_mul_right _ (prod_le_sum n m pa pb q)
    _ = (expNum (n + m) (pa + pb) q * W) * (fact n * fact m * V) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (C * (fact (n + m) * q ^ (n + m))) * (fact n * fact m * V) :=
        Nat.mul_le_mul_right _ (hsum (n + m))
    _ = C * V * (fact n * q ^ n) * (fact m * q ^ m * fact (n + m)) := by
        rw [show q ^ (n + m) = q ^ n * q ^ m from Nat.pow_add q n m]
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem capUB_one (q : Nat) : capUB 0 q 1 1 := by
  intro n
  rw [expNum_zero_arg]
  omega

theorem capLB_one (q : Nat) : capLB 0 q 1 1 :=
  ⟨0, by rw [expNum_zero_arg]; omega⟩

theorem capUB_pow {p q y w : Nat} (hq : 0 < q) (h : capUB p q y w) :
    ∀ k, capUB (k * p) q (y ^ k) (w ^ k) := by
  intro k
  induction k with
  | zero =>
    show capUB (0 * p) q (y ^ 0) (w ^ 0)
    rw [Nat.zero_mul]
    exact capUB_one q
  | succ j ih =>
    have := capUB_mul hq ih h
    rw [(Nat.succ_mul j p).symm] at this
    rw [Nat.pow_succ, Nat.pow_succ]
    exact this

theorem capLB_pow {p q y w : Nat} (h : capLB p q y w) :
    ∀ k, capLB (k * p) q (y ^ k) (w ^ k) := by
  intro k
  induction k with
  | zero =>
    show capLB (0 * p) q (y ^ 0) (w ^ 0)
    rw [Nat.zero_mul]
    exact capLB_one q
  | succ j ih =>
    have := capLB_mul ih h
    rw [(Nat.succ_mul j p).symm] at this
    rw [Nat.pow_succ, Nat.pow_succ]
    exact this

/-- Transport an upper cap down a smaller argument: `p/q ≤ p'/q'`. -/
theorem capUB_arg {p q p' q' y w : Nat} (hq' : 0 < q') (h : p * q' ≤ p' * q)
    (hub : capUB p' q' y w) : capUB p q y w := by
  intro n
  have hd : 0 < q' ^ n := Nat.pow_pos hq'
  refine Nat.le_of_mul_le_mul_right ?_ hd
  calc expNum n p q * w * q' ^ n
      = (expNum n p q * q' ^ n) * w := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (expNum n p' q' * q ^ n) * w :=
        Nat.mul_le_mul_right _ (expNum_arg_mono h n)
    _ = (expNum n p' q' * w) * q ^ n := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (y * (fact n * q' ^ n)) * q ^ n :=
        Nat.mul_le_mul_right _ (hub n)
    _ = y * (fact n * q ^ n) * q' ^ n := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Transport a lower cap up a larger argument: `p'/q' ≤ p/q`. -/
theorem capLB_arg {p q p' q' y w : Nat} (hq' : 0 < q') (h : p' * q ≤ p * q')
    (hlb : capLB p' q' y w) : capLB p q y w := by
  obtain ⟨n, hn⟩ := hlb
  refine ⟨n, ?_⟩
  have hd : 0 < q' ^ n := Nat.pow_pos hq'
  refine Nat.le_of_mul_le_mul_right ?_ hd
  calc y * (fact n * q ^ n) * q' ^ n
      = (y * (fact n * q' ^ n)) * q ^ n := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (expNum n p' q' * w) * q ^ n :=
        Nat.mul_le_mul_right _ hn
    _ = (expNum n p' q' * q ^ n) * w := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (expNum n p q * q' ^ n) * w :=
        Nat.mul_le_mul_right _ (expNum_arg_mono h n)
    _ = expNum n p q * w * q' ^ n := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Weaken an upper cap to a looser target: `y/w ≤ y'/w'`. -/
theorem capUB_weaken {p q y w y' w' : Nat} (hw : 0 < w)
    (h : capUB p q y w) (hyy : y * w' ≤ y' * w) : capUB p q y' w' := by
  intro n
  refine Nat.le_of_mul_le_mul_right ?_ hw
  calc expNum n p q * w' * w = expNum n p q * w * w' := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ y * (fact n * q ^ n) * w' := Nat.mul_le_mul_right _ (h n)
    _ = y * w' * (fact n * q ^ n) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ y' * w * (fact n * q ^ n) := Nat.mul_le_mul_right _ hyy
    _ = y' * (fact n * q ^ n) * w := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Strengthen a lower cap to a looser target: `y'/w' ≤ y/w`. -/
theorem capLB_weaken {p q y w y' w' : Nat} (hw : 0 < w)
    (h : capLB p q y w) (hyy : y' * w ≤ y * w') : capLB p q y' w' := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  refine Nat.le_of_mul_le_mul_right ?_ hw
  calc y' * (fact n * q ^ n) * w = y' * w * (fact n * q ^ n) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ y * w' * (fact n * q ^ n) := Nat.mul_le_mul_right _ hyy
    _ = y * (fact n * q ^ n) * w' := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ expNum n p q * w * w' := Nat.mul_le_mul_right _ hn
    _ = expNum n p q * w' * w := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Turn one evaluated partial sum plus the geometric tail into a full upper
cap: with `2p ≤ (K+2)q` and
`(E_K (K+1) q + 2 p^(K+1)) w ≤ y (K+1)! q^(K+1)`, conclude `e^(p/q) ≤ y/w`. -/
theorem capUB_of_partial {p q K y w : Nat} (hq : 0 < q) (hK : 2 * p ≤ (K + 2) * q)
    (h : (expNum K p q * ((K + 1) * q) + 2 * p ^ (K + 1)) * w ≤
      y * (fact (K + 1) * q ^ (K + 1))) : capUB p q y w := by
  intro M
  exact div_le_trans (mul_pos' (fact_pos (K + 1)) (Nat.pow_pos hq))
    (tail_bound hq hK M) h

end LnExp
