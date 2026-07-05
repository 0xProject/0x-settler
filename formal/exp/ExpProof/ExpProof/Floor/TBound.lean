import ExpProof.Mono.Octave
import Mathlib.Tactic.IntervalCases

/-!
# The reduced argument stays in the cert domain `[−H129, H129]`

The reduced-argument Taylor caps (`Floor.CapsV`) are certified over `t ∈ [0, H129]` with
`H129 = ⌊ln2/2 · 2¹²⁸⌋`. To instantiate them at the runtime reduced argument `t = tTree x` we
need `|tTree x| ≤ H129` on the meaningful region.

This is an integer-`k` fact: a real linear-program relaxation of the octave/reduced-argument
sandwiches is unbounded (it decouples `k` from `x`), but the *integer*
`k`-rounding sandwich `2²⁰⁰·k ≤ 2¹⁹⁹ + CINV·x < 2²⁰⁰·k + 2²⁰⁰` ties `k` to `x` tightly enough that
the maximum of the reduction argument `K27·x − LN2·k` over the integer region is strictly below
`2¹⁰⁷·(H129 + 1)` (and symmetrically above `−2¹⁰⁷·(H129 + 1)`). `omega` discharges the resulting
linear-integer system — it performs the per-`k`-band case analysis internally.
-/

namespace ExpYul

open FormalYul
open FormalYul.Preservation

set_option maxRecDepth 100000

/-- On the meaningful region the reduced argument lands in the certificate domain:
`-H129 ≤ tTree x ≤ H129` (as signed integers), where `H129 = ⌊ln2/2 · 2¹²⁸⌋`. -/
theorem tTree_in_cert_domain {x : Nat} (hx : x < 2 ^ 256)
    (hC : int256 Cmask < int256 x) (hC0 : int256 x < int256 C0thresh) :
    -(235865763225513294137944142764154484399 : Int) ≤ int256 (tTree x) ∧
      int256 (tTree x) ≤ 235865763225513294137944142764154484399 := by
  obtain ⟨htlo, hthi⟩ := tTree_sandwich hx hC hC0
  obtain ⟨hklo, hkhi⟩ := kTree_sandwich hx hC hC0
  obtain ⟨hxlo, hxhi⟩ := region_x_bound hC hC0
  obtain ⟨hkblo, hkbhi⟩ := kTree_bound hx hC hC0
  -- region endpoints as decimals
  have hCi : int256 Cmask = -41446531673892822312323846185 := int256_Cmask
  have hC0i : int256 C0thresh = 45401140326676417766828703956 := int256_C0thresh
  rw [hCi] at hC
  rw [hC0i] at hC0
  -- constants as decimals
  have hK27 : (0x279d346de4781f921dd7a89933d54d1f72928 : Int) =
      55213970774324510299478046898216203619608872 := by norm_num
  have hLN2 : (0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d : Int) =
      38271408169742254668347313025622401492114385419650052359639581444463709 := by norm_num
  have hCINV : (0x724d54edbacbebbb95c52a0f60 : Int) = 9055943544797870567083544809312 := by
    norm_num
  rw [hK27, hLN2] at htlo hthi
  rw [hCINV] at hklo hkhi
  set t := int256 (tTree x) with htdef
  set k := int256 (kTree x) with hkdef
  set X := int256 x with hXdef
  -- powers of two as decimals
  have p106 : (2 : Int) ^ 106 = 81129638414606681695789005144064 := by norm_num
  have p199 : (2 : Int) ^ 191 =
      3138550867693340381917894711603833208051177722232017256448 := by norm_num
  have p200 : (2 : Int) ^ 192 =
      6277101735386680763835789423207666416102355444464034512896 := by norm_num
  have pH : (235865763225513294137944142764154484399 : Int) =
      235865763225513294137944142764154484399 := rfl
  rw [p106] at htlo hthi
  rw [p199, p200] at hklo hkhi
  clear_value k
  -- For each fixed integer octave index `k ∈ [−61, 65]` the band of consistent `x` together with
  -- the reduction sandwich pins `t` to the cert domain; `omega` closes each band (the coupling is
  -- linear in `x` and `t` once `k` is a literal).
  clear htdef hXdef hkdef hCi hC0i hK27 hLN2 hCINV pH p106 p199 p200 hx hxlo hxhi
  interval_cases k <;> constructor <;> omega

end ExpYul
