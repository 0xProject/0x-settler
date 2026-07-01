import ExpProof.Mono.WordMono

namespace ExpYul

open FormalYul.Preservation

/-! Runtime constants used by the generated exp kernel normal form. -/

abbrev Cmask : Nat := 0xffffffffffffffffffffffffffffffffffffffff7a143b87dbdabf5ee0a0efd7
abbrev C0thresh : Nat := 0x8e383a2cdfa1b74a9422d2e1

abbrev kRoundShift : Nat := 0xc8
abbrev kHalfShift : Nat := 0xc7
abbrev cInvQ200 : Nat := 0x724d54edbacbebbb95c52a0f6076

abbrev k27Q235 : Nat := 0x279d346de4781f921dd7a89933d54d1f72928
abbrev ln2Q235 : Nat := 0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d
abbrev tArgShift : Nat := 0x6b
abbrev squareShift : Nat := 0x80

abbrev ev0 : Nat := 0xb9aacfad41060587203a79af0ebc
abbrev ev1 : Nat := 0x9a036222e11aee18465042f8ea64c8
abbrev ev2 : Nat := 0x9064d965e1c4863b73604e0ddbec53f9
abbrev ev3 : Nat := 0x93f11e65781741b92fa7fc4f4fffcca2
abbrev ev4 : Nat := 0x4e14a45e8ec305e233e11b4174e214ac
abbrev evShift0 : Nat := 0x1d
abbrev evShift1 : Nat := 0x82
abbrev evShift2 : Nat := 0x80
abbrev evShift3 : Nat := 0x86
abbrev evShift4 : Nat := 0x84

abbrev od0 : Nat := 0xdc07aff85e5bb5629d0fb64a84bb
abbrev od1 : Nat := 0xc926ddbf3830ca5561cc01585402d0
abbrev od2 : Nat := 0xad4506b00b1246c7e5b4fd33e1201b
abbrev od3 : Nat := 0xaf5662483c4ce783a9ef5fe025f42e9e
abbrev od4 : Nat := 0x270a522f476182f119f08da0ba710a56
abbrev odShift1 : Nat := 0x83
abbrev odShift2 : Nat := 0x89
abbrev odShift3 : Nat := 0x7f
abbrev odShift4 : Nat := 0x87

abbrev todShift : Nat := 0x80
abbrev expQShift : Nat := 0x7e
abbrev wadWord : Nat := 0xde0b6b3a7640000
abbrev marginWord : Nat := 0x9fe769d0fa58e9f

theorem int256_Cmask : int256 Cmask = -41446531673892822312323846185 := by
  unfold Cmask int256
  norm_num

theorem Cmask_lt : Cmask < 2 ^ 256 := by
  unfold Cmask
  norm_num

theorem int256_C0thresh : int256 C0thresh = 44014845965556527147994239713 := by
  unfold C0thresh int256
  norm_num

end ExpYul
