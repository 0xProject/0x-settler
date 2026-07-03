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
abbrev squareShift : Nat := 0x85

abbrev ev0 : Nat := 0xb9aacfacf3c10b378435f8e22adf48500e
abbrev ev1 : Nat := 0x9a036222841f47c6ed6fc3f7602053
abbrev ev2 : Nat := 0x9064d9657e9a21fc16bb69331c5c3057
abbrev ev3 : Nat := 0x93f11e650dd6c64b96ce79065cdf809e
abbrev ev4 : Nat := 0x9c2948bcaca16a0dd2fe98bb4470c3c4
abbrev evShift1 : Nat := 0x95
abbrev evShift2 : Nat := 0x7b
abbrev evShift3 : Nat := 0x81
abbrev evShift4 : Nat := 0x7e

abbrev od0 : Nat := 0xdc07aff8276bde9a361278df6a10
abbrev od1 : Nat := 0xc926ddbecdeeb42e68cd16db7da8c1
abbrev od2 : Nat := 0xad4506af99be27419341e1816ff351
abbrev od3 : Nat := 0xaf566247c05753b42892f77b67a6b7c6
abbrev od4 : Nat := 0x9c2948bcaca16a0dd2fe98bb4470c3c4
abbrev odShift1 : Nat := 0x7e
abbrev odShift2 : Nat := 0x84
abbrev odShift3 : Nat := 0x7a
abbrev odShift4 : Nat := 0x80

abbrev todShift : Nat := 0x81
abbrev expQShift : Nat := 0x7e
abbrev foldShift : Nat := 0x6c
abbrev wadWord : Nat := 0x3782dace9d9
abbrev marginWord : Nat := 0x2161b482a02

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
