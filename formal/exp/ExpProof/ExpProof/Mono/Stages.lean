import ExpProof.Mono.Octave

/-!
# Horner-stage transports for the `exp` kernel

The reduced argument `t = tTree x` is bounded by `2^127` on the meaningful region (the octave
reduction keeps `|t| < ln2/2 · 2^128`; a sharper `1.2·10^38` form squares below `2^253`). From
those bounds this file transports the downstream kernel stages to closed `Int`/bound forms:

* `v = t²` in Q123 (a nonnegative logical shift, `< 2^120`);
* the even/odd Horner accumulators `ev`, `od` (two-sided constant bounds); the monic leading
  stage is a bare add of `v` at its own basis, and its product with `v` is the only stage with
  no power-of-two headroom — its multiply safety rests on the exact coefficient literal against
  `v < 2^120`;
* `tod = t·Od` in Q88 (a signed shift, transported to `Int`);
* the numerator `ev + tod` and denominator `ev − tod` are both strictly positive;
* `r0 = exp(t)·2^126`, the reciprocal-symmetric quotient, is strictly positive and `< 2^128`.

These are the facts the range/nonneg obligations and the rational-quotient step build on.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-! ## The reduced-argument bound `|t| < 2^127` -/

/-- On the meaningful region the reduced argument is bounded: `-2^127 < int256 (tTree x) < 2^127`.
The octave reduction couples `k` to `x` (`2^192·k ≈ CINV·x`), so the residual `K27·x − LN2·k`
stays inside `±ln2/2·2^235`, leaving `|t| < ln2/2·2^128 < 2^127`. -/
theorem tTree_bound {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    -(2 ^ 127 : Int) < int256 (tTree x) ∧ int256 (tTree x) < 2 ^ 127 := by
  obtain ⟨htlo, hthi⟩ := tTree_sandwich hx hC hC0
  obtain ⟨hklo, hkhi⟩ := kTree_sandwich hx hC hC0
  obtain ⟨hxlo, hxhi⟩ := region_x_bound hC hC0
  -- numeric forms
  have hb96 : (2 : Int) ^ 96 = 79228162514264337593543950336 := by norm_num
  rw [hb96] at hxlo hxhi
  -- constants as decimal
  have hK27 : (0x279d346de4781f921dd7a89933d54d1f72928 : Int) =
      55213970774324510299478046898216203619608872 := by norm_num
  have hLN2 : (0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d : Int) =
      38271408169742254668347313025622401492114385419650052359639581444463709 := by norm_num
  have hCINV : (0x724d54edbacbebbb95c52a0f60 : Int) = 9055943544797870567083544809312 := by
    norm_num
  rw [hK27, hLN2] at htlo hthi
  rw [hCINV] at hklo hkhi
  set t := int256 (tTree x)
  set k := int256 (kTree x)
  set X := int256 x
  -- powers of two as decimals
  have p107 : (2 : Int) ^ 107 = 162259276829213363391578010288128 := by norm_num
  have p127 : (2 : Int) ^ 127 = 170141183460469231731687303715884105728 := by norm_num
  have p199 : (2 : Int) ^ 191 =
      3138550867693340381917894711603833208051177722232017256448 := by norm_num
  have p200 : (2 : Int) ^ 192 =
      6277101735386680763835789423207666416102355444464034512896 := by norm_num
  rw [p107] at htlo hthi
  rw [p199, p200] at hklo hkhi
  rw [p127]
  -- Eliminate `k` by scaling both sandwiches to the common factor `2^192`, then bound `X`.
  -- LN2 (positive) times the k-sandwich:
  have hLN2pos : (0 : Int) < 38271408169742254668347313025622401492114385419650052359639581444463709 := by
    norm_num
  have hklo' : 38271408169742254668347313025622401492114385419650052359639581444463709 *
      (6277101735386680763835789423207666416102355444464034512896 * k) ≤
      38271408169742254668347313025622401492114385419650052359639581444463709 *
      (3138550867693340381917894711603833208051177722232017256448 +
        9055943544797870567083544809312 * X) :=
    mul_le_mul_left_nonneg hklo (le_of_lt hLN2pos)
  have hkhi' : 38271408169742254668347313025622401492114385419650052359639581444463709 *
      (3138550867693340381917894711603833208051177722232017256448 +
        9055943544797870567083544809312 * X) <
      38271408169742254668347313025622401492114385419650052359639581444463709 *
      (6277101735386680763835789423207666416102355444464034512896 * k +
        6277101735386680763835789423207666416102355444464034512896) :=
    by
      have := mul_le_mul_left_nonneg (le_of_lt hkhi) (le_of_lt hLN2pos)
      rcases lt_or_eq_of_le this with h | h
      · exact h
      · exact absurd h.symm (by
          have := Int.mul_lt_mul_of_pos_left hkhi hLN2pos; omega)
  -- 2^192 times the t-sandwich:
  have hp200pos : (0 : Int) < 6277101735386680763835789423207666416102355444464034512896 := by
    norm_num
  have htlo' : 6277101735386680763835789423207666416102355444464034512896 *
      (162259276829213363391578010288128 * t) ≤
      6277101735386680763835789423207666416102355444464034512896 *
      (55213970774324510299478046898216203619608872 * X -
        38271408169742254668347313025622401492114385419650052359639581444463709 * k) :=
    mul_le_mul_left_nonneg htlo (le_of_lt hp200pos)
  have hthi' : 6277101735386680763835789423207666416102355444464034512896 *
      (55213970774324510299478046898216203619608872 * X -
        38271408169742254668347313025622401492114385419650052359639581444463709 * k) <
      6277101735386680763835789423207666416102355444464034512896 *
      (162259276829213363391578010288128 * t + 162259276829213363391578010288128) :=
    by
      have := mul_le_mul_left_nonneg (le_of_lt hthi) (le_of_lt hp200pos)
      rcases lt_or_eq_of_le this with h | h
      · exact h
      · exact absurd h.symm (by
          have := Int.mul_lt_mul_of_pos_left hthi hp200pos; omega)
  constructor
  · nlinarith [htlo', hthi', hklo', hkhi', hxlo, hxhi]
  · nlinarith [htlo', hthi', hklo', hkhi', hxlo, hxhi]

/-- The sharper reduced-argument bound `|t| < 1.2·10^38`: the true envelope is
`ln2/2 · 2^128 ≈ 1.1793·10^38`, and this relaxation still squares below `2^253`, which is what the
Q123 square and the monic-stage multiply safety need. Same sandwich elimination as `tTree_bound`,
closed against the sharper literal. -/
theorem tTree_bound_sharp {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    -(120000000000000000000000000000000000000 : Int) < int256 (tTree x) ∧
      int256 (tTree x) < 120000000000000000000000000000000000000 := by
  obtain ⟨htlo, hthi⟩ := tTree_sandwich hx hC hC0
  obtain ⟨hklo, hkhi⟩ := kTree_sandwich hx hC hC0
  obtain ⟨hxlo, hxhi⟩ := region_x_bound hC hC0
  have hb96 : (2 : Int) ^ 96 = 79228162514264337593543950336 := by norm_num
  rw [hb96] at hxlo hxhi
  have hK27 : (0x279d346de4781f921dd7a89933d54d1f72928 : Int) =
      55213970774324510299478046898216203619608872 := by norm_num
  have hLN2 : (0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d : Int) =
      38271408169742254668347313025622401492114385419650052359639581444463709 := by norm_num
  have hCINV : (0x724d54edbacbebbb95c52a0f60 : Int) = 9055943544797870567083544809312 := by
    norm_num
  rw [hK27, hLN2] at htlo hthi
  rw [hCINV] at hklo hkhi
  set t := int256 (tTree x)
  set k := int256 (kTree x)
  set X := int256 x
  have p107 : (2 : Int) ^ 107 = 162259276829213363391578010288128 := by norm_num
  have p199 : (2 : Int) ^ 191 =
      3138550867693340381917894711603833208051177722232017256448 := by norm_num
  have p200 : (2 : Int) ^ 192 =
      6277101735386680763835789423207666416102355444464034512896 := by norm_num
  rw [p107] at htlo hthi
  rw [p199, p200] at hklo hkhi
  have hLN2pos : (0 : Int) < 38271408169742254668347313025622401492114385419650052359639581444463709 := by
    norm_num
  have hklo' : 38271408169742254668347313025622401492114385419650052359639581444463709 *
      (6277101735386680763835789423207666416102355444464034512896 * k) ≤
      38271408169742254668347313025622401492114385419650052359639581444463709 *
      (3138550867693340381917894711603833208051177722232017256448 +
        9055943544797870567083544809312 * X) :=
    mul_le_mul_left_nonneg hklo (le_of_lt hLN2pos)
  have hkhi' : 38271408169742254668347313025622401492114385419650052359639581444463709 *
      (3138550867693340381917894711603833208051177722232017256448 +
        9055943544797870567083544809312 * X) <
      38271408169742254668347313025622401492114385419650052359639581444463709 *
      (6277101735386680763835789423207666416102355444464034512896 * k +
        6277101735386680763835789423207666416102355444464034512896) :=
    by
      have := mul_le_mul_left_nonneg (le_of_lt hkhi) (le_of_lt hLN2pos)
      rcases lt_or_eq_of_le this with h | h
      · exact h
      · exact absurd h.symm (by
          have := Int.mul_lt_mul_of_pos_left hkhi hLN2pos; omega)
  have hp200pos : (0 : Int) < 6277101735386680763835789423207666416102355444464034512896 := by
    norm_num
  have htlo' : 6277101735386680763835789423207666416102355444464034512896 *
      (162259276829213363391578010288128 * t) ≤
      6277101735386680763835789423207666416102355444464034512896 *
      (55213970774324510299478046898216203619608872 * X -
        38271408169742254668347313025622401492114385419650052359639581444463709 * k) :=
    mul_le_mul_left_nonneg htlo (le_of_lt hp200pos)
  have hthi' : 6277101735386680763835789423207666416102355444464034512896 *
      (55213970774324510299478046898216203619608872 * X -
        38271408169742254668347313025622401492114385419650052359639581444463709 * k) <
      6277101735386680763835789423207666416102355444464034512896 *
      (162259276829213363391578010288128 * t + 162259276829213363391578010288128) :=
    by
      have := mul_le_mul_left_nonneg (le_of_lt hthi) (le_of_lt hp200pos)
      rcases lt_or_eq_of_le this with h | h
      · exact h
      · exact absurd h.symm (by
          have := Int.mul_lt_mul_of_pos_left hthi hp200pos; omega)
  constructor
  · nlinarith [htlo', hthi', hklo', hkhi', hxlo, hxhi]
  · nlinarith [htlo', hthi', hklo', hkhi', hxlo, hxhi]

/-! ## `v = t²` in Q123 -/

/-- The Q123 square `v = ⌊t²/2^133⌋` as a `Nat`: nonnegative, and `< 2^120`. The shift argument
`t·t` fits in a word because `|t| < 1.2·10^38` gives `t² < 2^253`. -/
theorem vTree_eq {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    (vTree x : Int) = (int256 (tTree x))^2 / 2 ^ 133 ∧ vTree x < 2 ^ 120 := by
  obtain ⟨htlo, hthi⟩ := tTree_bound_sharp hx hC hC0
  have htw : tTree x < 2 ^ 256 := by unfold tTree; exact evmSar_lt _ _
  -- the signed square equals the unsigned product of the canonical word with itself
  set t := int256 (tTree x) with htdef
  have hsq_lt : t ^ 2 < 2 ^ 253 := by
    have hp253 : (2:Int)^253 = 14474011154664524427946373126085988481658748083205070504932198000989141204992 := by norm_num
    rw [hp253, sq]
    nlinarith [htlo, hthi]
  have hsq_nn : 0 ≤ t ^ 2 := by positivity
  -- `tTree x · tTree x` as a word equals `t²` (transport), nonneg, `< 2^253`.
  have hmul : int256 (evmMul (tTree x) (tTree x)) = t * t :=
    evmMul_transport htw htw
      (by rw [← sq]; simp only [ipow255]; nlinarith [hsq_nn, hsq_lt])
      (by rw [← sq]; simp only [ipow255]; nlinarith [hsq_lt])
  have hmul_lt : evmMul (tTree x) (tTree x) < 2 ^ 256 := evmMul_lt _ _
  -- its `int256` is nonneg and below `2^253`, so it is the literal Nat value
  have hmul_small : evmMul (tTree x) (tTree x) < 2 ^ 255 := by
    have h := hmul
    unfold int256 at h
    split at h <;> simp only [ipow256] at * <;> nlinarith [hsq_nn, hsq_lt]
  have hmul_nat : (evmMul (tTree x) (tTree x) : Int) = t * t := by
    rw [← hmul]; exact (int256_of_lt hmul_small).symm
  have hmul_nat_lt : evmMul (tTree x) (tTree x) < 2 ^ 253 := by
    have : ((evmMul (tTree x) (tTree x) : Nat) : Int) < 2 ^ 253 := by
      rw [hmul_nat, ← sq]; exact hsq_lt
    exact_mod_cast this
  refine ⟨?_, ?_⟩
  · unfold vTree
    rw [evmShr_eq_div (by norm_num) hmul_lt]
    have he : ((evmMul (tTree x) (tTree x) / 2 ^ 133 : Nat) : Int) =
        (evmMul (tTree x) (tTree x) : Int) / 2 ^ 133 := by
      rw [Int.natCast_ediv]; norm_num
    rw [he, hmul_nat, ← sq]
  · unfold vTree
    rw [evmShr_eq_div (by norm_num) hmul_lt]
    have : evmMul (tTree x) (tTree x) / 2 ^ 133 < 2 ^ 253 / 2 ^ 133 :=
      Nat.div_lt_div_of_lt_of_dvd (by norm_num) hmul_nat_lt
    have he : (2:Nat) ^ 253 / 2 ^ 133 = 2 ^ 120 := by
      rw [Nat.pow_div (by norm_num) (by norm_num)]
    omega

/-! ## Exact word arithmetic when the operands fit -/

/-- `evmAdd` is ordinary addition when the sum fits in a word. -/
theorem evmAdd_eq_nat {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (h : a + b < 2 ^ 256) :
    evmAdd a b = a + b := by
  unfold evmAdd
  rw [u256_of_lt ha, u256_of_lt hb, u256_of_lt h]

/-- `evmMul` is ordinary multiplication when the product fits in a word. -/
theorem evmMul_eq_nat {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (h : a * b < 2 ^ 256) :
    evmMul a b = a * b := by
  unfold evmMul
  rw [u256_of_lt ha, u256_of_lt hb, u256_of_lt h]

/-- One Horner stage upper bound: if `prev < P`, `v < V`, `P · V ≤ 2^256`, and `sh < 256`, then
`evmAdd c (evmShr sh (evmMul prev v)) ≤ c + P * V / 2 ^ sh`, provided the sum fits. -/
theorem stage_le {c prev v P V sh : Nat} (hprev : prev < P) (hv : v < V)
    (hPV : P * V < 2 ^ 256) (hsh : sh < 256)
    (hsum : c + P * V / 2 ^ sh < 2 ^ 256) :
    evmAdd c (evmShr sh (evmMul prev v)) ≤ c + P * V / 2 ^ sh := by
  have hV0 : 0 < V := Nat.pos_of_ne_zero (fun h => by subst h; exact absurd hv (by omega))
  have hprodle : prev * v ≤ P * V := Nat.mul_le_mul (le_of_lt hprev) (le_of_lt hv)
  have hPle : P ≤ P * V := Nat.le_mul_of_pos_right P hV0
  have hVle : V ≤ P * V := Nat.le_mul_of_pos_left V (by omega : 0 < P)
  have hpv : prev * v < 2 ^ 256 := by omega
  have hprev256 : prev < 2 ^ 256 := by omega
  have hv256 : v < 2 ^ 256 := by omega
  have hmul : evmMul prev v = prev * v := evmMul_eq_nat hprev256 hv256 hpv
  have hshr : evmShr sh (evmMul prev v) = prev * v / 2 ^ sh := by
    rw [hmul]; exact evmShr_eq_div hsh hpv
  have hterm : prev * v / 2 ^ sh ≤ P * V / 2 ^ sh := Nat.div_le_div_right hprodle
  rw [hshr]
  have hterm_lt : prev * v / 2 ^ sh < 2 ^ 256 := by omega
  rw [evmAdd_eq_nat (a := c) (b := prev * v / 2 ^ sh) (by omega) hterm_lt (by omega)]
  omega

/-- One Horner stage lower bound: when the stage does not overflow the accumulator dominates its
leading coefficient (the `evmShr` term is nonnegative). The no-overflow hypothesis is supplied via
the matching `stage_le` upper bound at each call site. -/
theorem stage_ge {c prev v sh : Nat} (hc : c < 2 ^ 256)
    (hsum : c + evmShr sh (evmMul prev v) < 2 ^ 256) :
    c ≤ evmAdd c (evmShr sh (evmMul prev v)) := by
  have hsh_lt : evmShr sh (evmMul prev v) < 2 ^ 256 := evmShr_lt _ _
  rw [evmAdd_eq_nat hc hsh_lt hsum]; omega

/-! ## The even/odd Horner accumulators

Each stage `evmAdd c (evmShr sh (evmMul prev v))` is bounded two-sidedly: it never wraps (so it
dominates its leading coefficient `c`), and the truncated tail keeps it below `c + ⌊P·V/2^sh⌋`.
The bounds chain from `v < 2^120` through the five even / four odd stages; the monic leading
stage contributes `ev0 + v` directly, so the first multiply's safety cap is the exact sum
`ev0 + 2^120` rather than a power of two. -/

/-- The truncated stage tail is bounded by `⌊P·V/2^sh⌋`. -/
theorem stage_term_le {prev v P V sh : Nat} (hprev : prev < P) (hv : v < V)
    (hPV : P * V < 2 ^ 256) (hsh : sh < 256) :
    evmShr sh (evmMul prev v) ≤ P * V / 2 ^ sh := by
  have hV0 : 0 < V := Nat.pos_of_ne_zero (fun h => by subst h; exact absurd hv (by omega))
  have hP0 : 0 < P := by omega
  have hprodle : prev * v ≤ P * V := Nat.mul_le_mul (le_of_lt hprev) (le_of_lt hv)
  have hPle : P ≤ P * V := Nat.le_mul_of_pos_right P hV0
  have hVle : V ≤ P * V := Nat.le_mul_of_pos_left V hP0
  have hpv : prev * v < 2 ^ 256 := by omega
  have hmul : evmMul prev v = prev * v := evmMul_eq_nat (by omega) (by omega) hpv
  rw [hmul, evmShr_eq_div hsh hpv]
  exact Nat.div_le_div_right hprodle

/-- Combined two-sided bound for one Horner stage that does not overflow. -/
theorem stage_bounds {c prev v P V sh : Nat} (hprev : prev < P) (hv : v < V)
    (hPV : P * V < 2 ^ 256) (hsh : sh < 256)
    (hsum : c + P * V / 2 ^ sh < 2 ^ 256) :
    c ≤ evmAdd c (evmShr sh (evmMul prev v)) ∧
      evmAdd c (evmShr sh (evmMul prev v)) ≤ c + P * V / 2 ^ sh := by
  have hub := stage_le hprev hv hPV hsh hsum
  have hterm := stage_term_le hprev hv hPV hsh
  refine ⟨?_, hub⟩
  -- abstract the (nonlinear) division so `omega` reasons purely linearly
  generalize hT : P * V / 2 ^ sh = T at hsum hterm
  have hc256 : c < 2 ^ 256 := by omega
  exact stage_ge hc256 (by omega)

/-- The monic leading stage `ev0 + v` is an exact add, capped by the exact sum `ev0 + 2^120`. -/
theorem ev0_lt {v : Nat} (hv : v < 2 ^ 120) :
    evmAdd 0xb9aacfacf3c10b378435f8e22adf48500e v <
      0xb9aacfacf3c10b378435f8e22adf48500e + 2 ^ 120 := by
  rw [evmAdd_eq_nat (by norm_num) (by omega) (by omega)]; omega

theorem ev0_ge {v : Nat} (hv : v < 2 ^ 120) :
    0xb9aacfacf3c10b378435f8e22adf48500e ≤ evmAdd 0xb9aacfacf3c10b378435f8e22adf48500e v := by
  rw [evmAdd_eq_nat (by norm_num) (by omega) (by omega)]; omega

/-- Helper to discharge `2^pe·2^ve/2^sh = 2^e` for the chained stage ceilings. -/
theorem pvd (pe ve sh e : Nat) (hpe : pe + ve = sh + e) :
    (2:Nat) ^ pe * 2 ^ ve / 2 ^ sh = 2 ^ e := by
  rw [← Nat.pow_add, hpe, Nat.pow_add, Nat.mul_div_cancel_left _ (Nat.two_pow_pos sh)]

/-- Two-sided bound on the even Horner accumulator: `0x9c29… ≤ ev < 3·2^126`. The first multiply
`(ev0 + v)·v` is capped by the exact literal sum `(ev0 + 2^120)·2^120 < 2^256` — it has no
power-of-two headroom. -/
theorem evTree_facts {x : Nat} (hv : vTree x < 2 ^ 120) :
    0x9c2948bcaca16a0dd2fe98bb4470c388 ≤ evTree x ∧ evTree x < 3 * 2 ^ 126 := by
  have hev : evTree x =
      evmAdd 0x9c2948bcaca16a0dd2fe98bb4470c388 (evmShr 0x7e (evmMul
      (evmAdd 0x93f11e650dd6c64b96ce79065cdf80f4 (evmShr 0x81 (evmMul
      (evmAdd 0x9064d9657e9a21fc16bb69331b81ae1e (evmShr 0x7b (evmMul
      (evmAdd 0x9a036222841f47c6ed6fc3f7599445 (evmShr 0x95 (evmMul
      (evmAdd 0xb9aacfacf3c10b378435f8e22adf48500e (vTree x)) (vTree x)))) (vTree x)))) (vTree x)))) (vTree x))) := rfl
  rw [hev]
  set v := vTree x with hvdef
  have h0 := ev0_lt hv
  set ev0 := evmAdd 0xb9aacfacf3c10b378435f8e22adf48500e v with hev0
  have h1 : evmAdd 0x9a036222841f47c6ed6fc3f7599445 (evmShr 0x95 (evmMul ev0 v)) < 2 ^ 121 := by
    have := (stage_bounds (c := 0x9a036222841f47c6ed6fc3f7599445) (prev := ev0) (v := v)
      (P := 0xb9aacfacf3c10b378435f8e22adf48500e + 2 ^ 120) (V := 2 ^ 120) (sh := 0x95) h0 hv
      (by norm_num) (by norm_num) (by norm_num)).2
    have hcap : (0x9a036222841f47c6ed6fc3f7599445 : Nat) +
        (0xb9aacfacf3c10b378435f8e22adf48500e + 2 ^ 120) * 2 ^ 120 / 2 ^ 0x95 < 2 ^ 121 := by
      norm_num
    omega
  set ev1 := evmAdd 0x9a036222841f47c6ed6fc3f7599445 (evmShr 0x95 (evmMul ev0 v)) with hev1
  have h2 : evmAdd 0x9064d9657e9a21fc16bb69331b81ae1e (evmShr 0x7b (evmMul ev1 v)) < 2 ^ 129 := by
    have := (stage_bounds (c := 0x9064d9657e9a21fc16bb69331b81ae1e) (prev := ev1) (v := v)
      (P := 2 ^ 121) (V := 2 ^ 120) (sh := 0x7b) h1 hv (by norm_num) (by norm_num)
      (by rw [pvd 121 120 123 118 (by norm_num)]; norm_num)).2
    rw [pvd 121 120 123 118 (by norm_num)] at this; omega
  set ev2 := evmAdd 0x9064d9657e9a21fc16bb69331b81ae1e (evmShr 0x7b (evmMul ev1 v)) with hev2
  have h3 : evmAdd 0x93f11e650dd6c64b96ce79065cdf80f4 (evmShr 0x81 (evmMul ev2 v)) < 2 ^ 129 := by
    have := (stage_bounds (c := 0x93f11e650dd6c64b96ce79065cdf80f4) (prev := ev2) (v := v)
      (P := 2 ^ 129) (V := 2 ^ 120) (sh := 0x81) h2 hv (by norm_num) (by norm_num)
      (by rw [pvd 129 120 129 120 (by norm_num)]; norm_num)).2
    rw [pvd 129 120 129 120 (by norm_num)] at this; omega
  set ev3 := evmAdd 0x93f11e650dd6c64b96ce79065cdf80f4 (evmShr 0x81 (evmMul ev2 v)) with hev3
  have hfin := stage_bounds (c := 0x9c2948bcaca16a0dd2fe98bb4470c388) (prev := ev3) (v := v)
    (P := 2 ^ 129) (V := 2 ^ 120) (sh := 0x7e) h3 hv (by norm_num) (by norm_num)
    (by rw [pvd 129 120 126 123 (by norm_num)]; norm_num)
  rw [pvd 129 120 126 123 (by norm_num)] at hfin
  refine ⟨hfin.1, ?_⟩
  have : (0x9c2948bcaca16a0dd2fe98bb4470c388 : Nat) + 2 ^ 123 < 3 * 2 ^ 126 := by norm_num
  omega

theorem evTree_lt {x : Nat} (hv : vTree x < 2 ^ 120) : evTree x < 3 * 2 ^ 126 :=
  (evTree_facts hv).2
theorem evTree_ge {x : Nat} (hv : vTree x < 2 ^ 120) :
    0x9c2948bcaca16a0dd2fe98bb4470c388 ≤ evTree x := (evTree_facts hv).1

/-- Two-sided bound on the odd Horner accumulator: `0x9c29… ≤ od < 5·2^125`. -/
theorem odTree_facts {x : Nat} (hv : vTree x < 2 ^ 120) :
    0x9c2948bcaca16a0dd2fe98bb4470c388 ≤ odTree x ∧ odTree x < 5 * 2 ^ 125 := by
  have hod : odTree x =
      evmAdd 0x9c2948bcaca16a0dd2fe98bb4470c388 (evmShr 0x80 (evmMul
      (evmAdd 0xaf566247c05753b42892f77b67a6b7c7 (evmShr 0x7a (evmMul
      (evmAdd 0xad4506af99be27419341e181693281 (evmShr 0x84 (evmMul
      (evmAdd 0xc926ddbecdeeb42e68cd16db7ed378 (evmShr 0x7e (evmMul
      0xdc07aff8276bde9a361278df6a10 (vTree x)))) (vTree x)))) (vTree x)))) (vTree x))) := rfl
  rw [hod]
  set v := vTree x with hvdef
  have h0 : evmAdd 0xc926ddbecdeeb42e68cd16db7ed378 (evmShr 0x7e (evmMul 0xdc07aff8276bde9a361278df6a10 v)) < 2 ^ 121 := by
    have := (stage_bounds (c := 0xc926ddbecdeeb42e68cd16db7ed378) (prev := 0xdc07aff8276bde9a361278df6a10) (v := v)
      (P := 2 ^ 112) (V := 2 ^ 120) (sh := 0x7e) (by norm_num) hv (by norm_num) (by norm_num)
      (by rw [pvd 112 120 126 106 (by norm_num)]; norm_num)).2
    rw [pvd 112 120 126 106 (by norm_num)] at this; omega
  set od0 := evmAdd 0xc926ddbecdeeb42e68cd16db7ed378 (evmShr 0x7e (evmMul 0xdc07aff8276bde9a361278df6a10 v)) with hod0
  have h1 : evmAdd 0xad4506af99be27419341e181693281 (evmShr 0x84 (evmMul od0 v)) < 2 ^ 121 := by
    have := (stage_bounds (c := 0xad4506af99be27419341e181693281) (prev := od0) (v := v)
      (P := 2 ^ 121) (V := 2 ^ 120) (sh := 0x84) h0 hv (by norm_num) (by norm_num)
      (by rw [pvd 121 120 132 109 (by norm_num)]; norm_num)).2
    rw [pvd 121 120 132 109 (by norm_num)] at this; omega
  set od1 := evmAdd 0xad4506af99be27419341e181693281 (evmShr 0x84 (evmMul od0 v)) with hod1
  have h2 : evmAdd 0xaf566247c05753b42892f77b67a6b7c7 (evmShr 0x7a (evmMul od1 v)) < 2 ^ 129 := by
    have := (stage_bounds (c := 0xaf566247c05753b42892f77b67a6b7c7) (prev := od1) (v := v)
      (P := 2 ^ 121) (V := 2 ^ 120) (sh := 0x7a) h1 hv (by norm_num) (by norm_num)
      (by rw [pvd 121 120 122 119 (by norm_num)]; norm_num)).2
    rw [pvd 121 120 122 119 (by norm_num)] at this; omega
  set od2 := evmAdd 0xaf566247c05753b42892f77b67a6b7c7 (evmShr 0x7a (evmMul od1 v)) with hod2
  have hfin := stage_bounds (c := 0x9c2948bcaca16a0dd2fe98bb4470c388) (prev := od2) (v := v)
    (P := 2 ^ 129) (V := 2 ^ 120) (sh := 0x80) h2 hv (by norm_num) (by norm_num)
    (by rw [pvd 129 120 128 121 (by norm_num)]; norm_num)
  rw [pvd 129 120 128 121 (by norm_num)] at hfin
  refine ⟨hfin.1, ?_⟩
  have : (0x9c2948bcaca16a0dd2fe98bb4470c388 : Nat) + 2 ^ 121 < 5 * 2 ^ 125 := by norm_num
  omega

theorem odTree_lt {x : Nat} (hv : vTree x < 2 ^ 120) : odTree x < 5 * 2 ^ 125 :=
  (odTree_facts hv).2
theorem odTree_ge {x : Nat} (hv : vTree x < 2 ^ 120) :
    0x9c2948bcaca16a0dd2fe98bb4470c388 ≤ odTree x := (odTree_facts hv).1

end ExpYul
