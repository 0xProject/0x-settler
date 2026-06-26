import LnProof.Kronecker

/-!
# Packed Taylor shifts for the cell walks

The cell checker Taylor-shifts each certificate literal with a
Kronecker-substitution homomorphism: the shifted polynomial is *computed*
inside the decide as a handful of GMP-scale operations on sign-split packed
naturals (`kShiftHorner`, untrusted), then *certified* by one evaluation
identity at `2^B` through `evalPoly_ext`. The packed computation
needs no correctness lemmas: if it produced anything other than the true
shift, the evaluation identity in the checker would fail. The remaining
bound is an ℓ1 bound for true shifts, carried by `aeval`, the
absolute-value evaluation.
-/

namespace LnPoly

/-- Kronecker digit width shared by the cell-walk `checkCoverK` decides and
the cert-vs-literal `evalPoly_ext` identities. It must exceed `log2(2·ℓ1)`
of the certificates; the binding floor is the cell-walk `aeval` bound at
`~2^37772` (the certificate coefficients are `~37k`-bit and decay `~104`
bits per degree, so every monomial term is `~`constant scale), with the
eval-identity `polyL1` floor at `~2^37392`. This clears both with a
`~228`-bit margin, so it is near-minimal rather than arbitrary. -/
def kB : Nat := 38000

/-! ## ℓ1 of a Taylor shift -/

/-- Evaluate the coefficient-magnitude polynomial at a `Nat` point. -/
def aeval : List Int → Nat → Nat
  | [], _ => 0
  | c :: cs, m => c.natAbs + m * aeval cs m

theorem synthDiv_rem (p : List Int) (a : Int) :
    (synthDiv p a).2 = evalPoly p a := by
  have h := synthDiv_eval p a a
  have e : a - a = 0 := by omega
  rw [e, Int.mul_zero] at h
  omega

/-- Triangle inequality for evaluation against `aeval`. -/
theorem evalPoly_natAbs_le : ∀ (p : List Int) (x : Int),
    (evalPoly p x).natAbs ≤ aeval p x.natAbs := by
  intro p
  induction p with
  | nil => intro x; exact Nat.le_refl _
  | cons c cs ih =>
    intro x
    show (c + x * evalPoly cs x).natAbs ≤ c.natAbs + x.natAbs * aeval cs x.natAbs
    have h1 := Int.natAbs_add_le c (x * evalPoly cs x)
    have h2 : (x * evalPoly cs x).natAbs = x.natAbs * (evalPoly cs x).natAbs :=
      Int.natAbs_mul x (evalPoly cs x)
    have h3 := ih x
    have h4 : x.natAbs * (evalPoly cs x).natAbs ≤ x.natAbs * aeval cs x.natAbs :=
      Nat.mul_le_mul_left _ h3
    generalize hg1 : x.natAbs * (evalPoly cs x).natAbs = A at *
    generalize hg2 : x.natAbs * aeval cs x.natAbs = B at *
    omega

/-- `aeval` is monotone in the point. -/
theorem aeval_mono : ∀ (p : List Int) {m n : Nat}, m ≤ n →
    aeval p m ≤ aeval p n := by
  intro p
  induction p with
  | nil => intro m n _; exact Nat.le_refl _
  | cons c cs ih =>
    intro m n h
    show c.natAbs + m * aeval cs m ≤ c.natAbs + n * aeval cs n
    have h1 := ih h
    have h2 : m * aeval cs m ≤ n * aeval cs n :=
      Nat.mul_le_mul h h1
    omega

/-- The synthetic-division step preserves the `aeval` budget: remainder
magnitude plus the quotient's budget fit inside the dividend's budget at
`M = 1 + |a|`. -/
theorem synthDiv_aeval_le : ∀ (p : List Int) (a : Int),
    (evalPoly p a).natAbs + aeval (synthDiv p a).1 (1 + a.natAbs) ≤
      aeval p (1 + a.natAbs) := by
  intro p
  induction p with
  | nil =>
    intro a
    show (0 : Int).natAbs + 0 ≤ 0
    omega
  | cons c cs ih =>
    intro a
    match cs, ih with
    | [], _ =>
      show (c + a * evalPoly ([] : List Int) a).natAbs +
        aeval ([] : List Int) (1 + a.natAbs) ≤ c.natAbs + (1 + a.natAbs) * 0
      show (c + a * 0).natAbs + 0 ≤ c.natAbs + (1 + a.natAbs) * 0
      have e : c + a * 0 = c := by omega
      rw [e]
      omega
    | c2 :: cs', ih =>
      have hrec := ih a
      have hrem := synthDiv_rem (c2 :: cs') a
      show (c + a * evalPoly (c2 :: cs') a).natAbs +
        aeval ((synthDiv (c2 :: cs') a).2 :: (synthDiv (c2 :: cs') a).1)
          (1 + a.natAbs) ≤
        c.natAbs + (1 + a.natAbs) * aeval (c2 :: cs') (1 + a.natAbs)
      show (c + a * evalPoly (c2 :: cs') a).natAbs +
        ((synthDiv (c2 :: cs') a).2.natAbs +
          (1 + a.natAbs) * aeval (synthDiv (c2 :: cs') a).1 (1 + a.natAbs)) ≤
        c.natAbs + (1 + a.natAbs) * aeval (c2 :: cs') (1 + a.natAbs)
      rw [hrem]
      have h1 := Int.natAbs_add_le c (a * evalPoly (c2 :: cs') a)
      have h2 : (a * evalPoly (c2 :: cs') a).natAbs =
          a.natAbs * (evalPoly (c2 :: cs') a).natAbs :=
        Int.natAbs_mul a (evalPoly (c2 :: cs') a)
      have h3 : (1 + a.natAbs) * aeval (c2 :: cs') (1 + a.natAbs) =
          aeval (c2 :: cs') (1 + a.natAbs) +
            a.natAbs * aeval (c2 :: cs') (1 + a.natAbs) := by
        rw [Nat.add_mul, Nat.one_mul]
      have h4 : a.natAbs * ((evalPoly (c2 :: cs') a).natAbs +
          aeval (synthDiv (c2 :: cs') a).1 (1 + a.natAbs)) ≤
          a.natAbs * aeval (c2 :: cs') (1 + a.natAbs) :=
        Nat.mul_le_mul_left _ hrec
      have h5 : a.natAbs * ((evalPoly (c2 :: cs') a).natAbs +
          aeval (synthDiv (c2 :: cs') a).1 (1 + a.natAbs)) =
          a.natAbs * (evalPoly (c2 :: cs') a).natAbs +
            a.natAbs * aeval (synthDiv (c2 :: cs') a).1 (1 + a.natAbs) :=
        Nat.mul_add _ _ _
      have h6 : (1 + a.natAbs) * aeval (synthDiv (c2 :: cs') a).1 (1 + a.natAbs) =
          aeval (synthDiv (c2 :: cs') a).1 (1 + a.natAbs) +
            a.natAbs * aeval (synthDiv (c2 :: cs') a).1 (1 + a.natAbs) := by
        rw [Nat.add_mul, Nat.one_mul]
      generalize hgEa : (evalPoly (c2 :: cs') a).natAbs = Ea at *
      generalize hgQ : aeval (synthDiv (c2 :: cs') a).1 (1 + a.natAbs) = Q at *
      generalize hgC : aeval (c2 :: cs') (1 + a.natAbs) = Cv at *
      generalize hgX1 : a.natAbs * Ea = X1 at *
      generalize hgX2 : a.natAbs * Q = X2 at *
      generalize hgX3 : a.natAbs * Cv = X3 at *
      generalize hgX4 : a.natAbs * (Ea + Q) = X4 at *
      omega

/-- ℓ1 of the Taylor shift is bounded by the absolute evaluation at
`1 + |a|`. -/
theorem polyL1_polyShiftAux : ∀ (fuel : Nat) (p : List Int) (a : Int),
    polyL1 (polyShiftAux fuel p a) ≤ aeval p (1 + a.natAbs) := by
  intro fuel
  induction fuel with
  | zero =>
    intro p a
    show polyL1 ([] : List Int) ≤ aeval p (1 + a.natAbs)
    show 0 ≤ aeval p (1 + a.natAbs)
    omega
  | succ f ih =>
    intro p a
    match p with
    | [] =>
      show (0 : Nat) ≤ 0
      omega
    | c :: cs =>
      show polyL1 ((synthDiv (c :: cs) a).2 ::
        polyShiftAux f (synthDiv (c :: cs) a).1 a) ≤
        aeval (c :: cs) (1 + a.natAbs)
      show (synthDiv (c :: cs) a).2.natAbs +
        polyL1 (polyShiftAux f (synthDiv (c :: cs) a).1 a) ≤
        aeval (c :: cs) (1 + a.natAbs)
      have h1 := ih (synthDiv (c :: cs) a).1 a
      have h2 := synthDiv_aeval_le (c :: cs) a
      have h3 := synthDiv_rem (c :: cs) a
      have h4 : aeval (synthDiv (c :: cs) a).1 (1 + a.natAbs) ≤
          aeval (synthDiv (c :: cs) a).1 (1 + a.natAbs) := Nat.le_refl _
      generalize hg1 : polyL1 (polyShiftAux f (synthDiv (c :: cs) a).1 a) = L at *
      generalize hg2 : aeval (synthDiv (c :: cs) a).1 (1 + a.natAbs) = Q at *
      generalize hg3 : aeval (c :: cs) (1 + a.natAbs) = Cv at *
      omega

theorem polyL1_polyShift (p : List Int) (a : Int) :
    polyL1 (polyShift p a) ≤ aeval p (1 + a.natAbs) :=
  polyL1_polyShiftAux p.length p a

/-! ## Untrusted packed shift computation -/

/-- Sign-split packed polynomial: positive and negative digit strings in
radix `2^B`. Used only as a fast way to *compute* candidate coefficient
lists inside `decide`; nothing about it is trusted. -/
structure KPoly where
  pos : Nat
  neg : Nat

def kAdd (a b : KPoly) : KPoly := ⟨a.pos + b.pos, a.neg + b.neg⟩

def kMul (a b : KPoly) : KPoly :=
  ⟨a.pos * b.pos + a.neg * b.neg, a.pos * b.neg + a.neg * b.pos⟩

def kOfInt (c : Int) : KPoly :=
  ⟨c.toNat, (-c).toNat⟩

/-- Packed `x + a`. -/
def kXA (B : Nat) (a : Int) : KPoly :=
  kAdd (kOfInt a) ⟨2 ^ B, 0⟩

/-- Packed Taylor shift by Horner: `p(x + a)` accumulated as packed
multiply-adds. -/
def kShiftHorner (B : Nat) (a : Int) : List Int → KPoly
  | [] => ⟨0, 0⟩
  | c :: cs => kAdd (kOfInt c) (kMul (kXA B a) (kShiftHorner B a cs))

/-- Signed digit extraction. -/
def unpack (B : Nat) : Nat → KPoly → List Int
  | 0, _ => []
  | len + 1, A =>
    (((A.pos &&& (2 ^ B - 1) : Nat) : Int) - ((A.neg &&& (2 ^ B - 1) : Nat) : Int)) ::
      unpack B len ⟨A.pos >>> B, A.neg >>> B⟩

/-- Square ladder `x^(2^0), x^(2^1), …` of the given depth. -/
def kSquares (x : KPoly) : Nat → List KPoly
  | 0 => [x]
  | d + 1 =>
    match kSquares x d with
    | [] => []
    | s :: rest => kMul s s :: s :: rest

/-- Power from a precomputed square ladder (most significant first). -/
def kPowL : List KPoly → Nat → KPoly
  | [], _ => ⟨1, 0⟩
  | s :: rest, n =>
    let h := kPowL rest (n % 2 ^ rest.length)
    if n / 2 ^ rest.length % 2 = 1 then kMul h s else h

/-- Divide-and-conquer packed Taylor shift:
`P(x+a) = P₀(x+a) + (x+a)^m · P₁(x+a)` with `m = ⌊n/2⌋`. The expensive
full-size multiplications happen only near the top of the recursion, so
the cost is a handful of full-size GMP products. -/
def kShiftDC (B : Nat) (a : Int) (sq : List KPoly) : Nat → List Int → KPoly
  | 0, p => kShiftHorner B a p
  | fuel + 1, p =>
    if p.length ≤ 16 then kShiftHorner B a p
    else
      let m := p.length / 2
      kAdd (kShiftDC B a sq fuel (p.take m))
        (kMul (kPowL sq m) (kShiftDC B a sq fuel (p.drop m)))

/-- The in-kernel shifted-witness candidate. -/
def kShiftWitness (B : Nat) (C : List Int) (a : Int) : List Int :=
  unpack B C.length (kShiftDC B a (kSquares (kXA B a) 9) 16 C)

/-! ## The witness-checked cell walk -/

/-- Certify `0 ≤ P(x)` on `[lo, hi]` by walking cells; each cell's
shifted polynomial is computed packed and certified by one evaluation
identity at `2^B` plus the ℓ1 bounds that make `evalPoly_ext` apply. -/
def checkCoverK (B : Nat) (C : List Int) (lo hi : Int) : List Int → Bool
  | [] => decide (hi < lo)
  | w :: ws =>
    let S := kShiftWitness B C lo
    decide (0 ≤ w) &&
      decide (polyL1 S * 2 < 2 ^ B) &&
      decide (aeval C (1 + lo.natAbs) * 2 < 2 ^ B) &&
      decide (evalPoly S (((2 ^ B : Nat) : Int)) = evalPoly C (lo + ((2 ^ B : Nat) : Int))) &&
      decide (0 ≤ (hornerIv S 0 w).1) &&
      checkCoverK B C (lo + w + 1) hi ws

theorem checkCoverK_sound (B : Nat) (C : List Int) (ws : List Int) :
    ∀ lo hi : Int, checkCoverK B C lo hi ws = true →
      ∀ x : Int, lo ≤ x → x ≤ hi → 0 ≤ evalPoly C x := by
  induction ws with
  | nil =>
    intro lo hi h x h1 h2
    simp only [checkCoverK, decide_eq_true_eq] at h
    omega
  | cons w ws ih =>
    intro lo hi h x h1 h2
    simp only [checkCoverK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hw, hS⟩, hC⟩, he⟩, hcell⟩ := h.1
    have hrest := h.2
    rcases Int.lt_or_le (lo + w) x with hout | hin
    · exact ih (lo + w + 1) hi hrest x (by omega) h2
    · -- the witness agrees with the true shift everywhere
      have hshift : polyL1 (polyShift C lo) * 2 < 2 ^ B := by
        have := polyL1_polyShift C lo
        omega
      have hext := evalPoly_ext (B := B) (kShiftWitness B C lo)
        (polyShift C lo) hS hshift
        (by rw [polyShift_eval, pow2_cast]; exact he)
      have hs := (hornerIv_sound (kShiftWitness B C lo) (lo := 0) (hi := w)
        (x := x - lo) (Int.le_refl 0) (by omega) (by omega)).1
      have hx := hext (x - lo)
      rw [polyShift_eval] at hx
      rw [show lo + (x - lo) = x by omega] at hx
      omega

end LnPoly
