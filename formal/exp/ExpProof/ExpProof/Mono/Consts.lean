import ExpProof.Mono.WordMono

namespace ExpYul

open FormalYul.Preservation

/-! Runtime constants used by the generated exp kernel normal form. -/

abbrev Cmask : Nat := 0xffffffffffffffffffffffffffffffffffffffff7a143b87dbdabf5ee0a0efd7
abbrev C0thresh : Nat := 0x92b2f16cc66c5a4ae96e80d4

abbrev kRoundShift : Nat := 0xc0
abbrev kHalfShift : Nat := 0xbf
abbrev cInvQ192 : Nat := 0x724d54edbacbebbb95c52a0f60

abbrev k27Q235 : Nat := 0x279d346de4781f921dd7a89933d54d1f72928
abbrev ln2Q235 : Nat := 0x58b90bfbe8e7bcd5e4f1d9cc01f97b57a079a193394c5b16c5068badc5d
abbrev tArgShift : Nat := 0x6a
abbrev squareShift : Nat := 0x87

abbrev ev0 : Nat := 0xb9aacfacf3c10b378435f8e22adf48500e
abbrev ev1 : Nat := 0x9a036222841f47c6ed6fc3f7599445
abbrev ev2 : Nat := 0x9064d9657e9a21fc16bb69331b81ae1e
abbrev ev3 : Nat := 0x93f11e650dd6c64b96ce79065cdf80f4
abbrev ev4 : Nat := 0x1385291795942d41ba5fd317688e18710
abbrev evShift1 : Nat := 0x95
abbrev evShift2 : Nat := 0x7b
abbrev evShift3 : Nat := 0x81
abbrev evShift4 : Nat := 0x7d

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
abbrev foldShift : Nat := 0x43
abbrev scaleQ67 : Nat := 0x6f05b59d3b2000000000000000000000
abbrev scaleMaxClz : Nat := 0x81
abbrev marginWord : Nat := 0x1
abbrev xHiMulExpRay : Nat := 0x0116d70f49dec622d4bda70c52
abbrev xLoZeroMulExpRay : Nat := 0xfffffffffffffffffffffffffffffffffffffffee270ddd64709e8aac2676ec3

theorem scaleQ67_eq : (scaleQ67 : Int) = 3814697265625 * 2 ^ 85 := by
  unfold scaleQ67; norm_num

theorem scaleQ67_lt_2127 : scaleQ67 < 2 ^ 127 := by unfold scaleQ67; norm_num

theorem int256_Cmask : int256 Cmask = -41446531673892822312323846185 := by
  unfold Cmask int256
  norm_num

theorem Cmask_lt : Cmask < 2 ^ 256 := by
  unfold Cmask
  norm_num

theorem int256_C0thresh : int256 C0thresh = 45401140326676417766828703956 := by
  unfold C0thresh int256
  norm_num

theorem int256_xHiMulExpRay : int256 xHiMulExpRay = 86296823979713191022445399122 := by
  unfold xHiMulExpRay int256
  norm_num

theorem int256_xLoZeroMulExpRay :
    int256 xLoZeroMulExpRay = -88376265521393026950697095485 := by
  unfold xLoZeroMulExpRay int256
  norm_num

theorem xHiMulExpRay_lt : xHiMulExpRay < 2 ^ 256 := by
  unfold xHiMulExpRay
  norm_num

theorem xLoZeroMulExpRay_lt : xLoZeroMulExpRay < 2 ^ 256 := by
  unfold xLoZeroMulExpRay
  norm_num

end ExpYul
