import ExpProof.Mono.WordMono

namespace ExpYul

open FormalYul.Preservation

/-! Runtime constants used by the generated exp kernel normal form. -/

abbrev Cmask : Nat := 0xffffffffffffffffffffffffffffffffffffffff7a143b87dbdabf5ee0a0efd7
abbrev C0thresh : Nat := 0x907595ccd30708cabec8a9db

abbrev kRoundShift : Nat := 0xc0
abbrev kHalfShift : Nat := 0xbf
abbrev cInvQ192 : Nat := 0x724d54edbacbebbb95c52a0f60

abbrev k27Q235 : Nat := 0x279d346de4781f921dd7a89933d54d1f72928
abbrev ln2Q235 : Nat := 0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d
abbrev tArgShift : Nat := 0x6b
abbrev squareShift : Nat := 0x85

abbrev ev0 : Nat := 0xb9aacfacf3c10b378435f8e22adf48500e
abbrev ev1 : Nat := 0x9a036222841f47c6ed6fc3f7599445
abbrev ev2 : Nat := 0x9064d9657e9a21fc16bb69331b81ae1e
abbrev ev3 : Nat := 0x93f11e650dd6c64b96ce79065cdf80f4
abbrev ev4 : Nat := 0x9c2948bcaca16a0dd2fe98bb4470c388
abbrev evShift1 : Nat := 0x95
abbrev evShift2 : Nat := 0x7b
abbrev evShift3 : Nat := 0x81
abbrev evShift4 : Nat := 0x7e

abbrev od0 : Nat := 0xdc07aff8276bde9a361278df6a10
abbrev od1 : Nat := 0xc926ddbecdeeb42e68cd16db7ed378
abbrev od2 : Nat := 0xad4506af99be27419341e181693281
abbrev od3 : Nat := 0xaf566247c05753b42892f77b67a6b7c7
abbrev od4 : Nat := 0x9c2948bcaca16a0dd2fe98bb4470c388
abbrev odShift1 : Nat := 0x7e
abbrev odShift2 : Nat := 0x84
abbrev odShift3 : Nat := 0x7a
abbrev odShift4 : Nat := 0x80

abbrev todShift : Nat := 0x81
abbrev foldShift : Nat := 0x44
abbrev scaleQ68 : Nat := 0xde0b6b3a764000000000000000000000
abbrev marginWord : Nat := 0x3

theorem scaleQ68_eq : (scaleQ68 : Int) = 3814697265625 * 2 ^ 86 := by
  unfold scaleQ68; norm_num

theorem scaleQ68_lt_2128 : scaleQ68 < 2 ^ 128 := by unfold scaleQ68; norm_num

theorem int256_Cmask : int256 Cmask = -41446531673892822312323846185 := by
  unfold Cmask int256
  norm_num

theorem Cmask_lt : Cmask < 2 ^ 256 := by
  unfold Cmask
  norm_num

theorem int256_C0thresh : int256 C0thresh = 44707993146116472457411471835 := by
  unfold C0thresh int256
  norm_num

end ExpYul
