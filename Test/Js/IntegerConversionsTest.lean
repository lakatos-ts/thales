import Js

open Js.Number.FloatOps

/-! The two abstract operations that turn a Number into an integer, pinned on
both evaluation paths against Node 26 (`x | 0` for ToInt32, and the argument a
formatter's range check sees for ToIntegerOrInfinity).

`integerOrInfinity?` answers `none` for **either** infinity, so what these
pins say about `Infinity` and `-Infinity` is only that both are out of range;
the caller that needs to tell them apart has the Number itself. -/

/-! ## ToInt32, 7.1.6 -/

example : tsToInt32 0.0 = 0 := by decide
example : tsToInt32 (-0.0) = 0 := by decide
example : tsToInt32 Js.floatNaN = 0 := by decide
example : tsToInt32 Js.floatInf = 0 := by decide
example : tsToInt32 (-Js.floatInf) = 0 := by decide
example : tsToInt32 (-1.0) = -1 := by decide
example : tsToInt32 3.7 = 3 := by decide
example : tsToInt32 (-3.7) = -3 := by decide
#guard tsToInt32 0.0 == 0
#guard tsToInt32 (-0.0) == 0
#guard tsToInt32 Js.floatNaN == 0
#guard tsToInt32 Js.floatInf == 0
#guard tsToInt32 (-Js.floatInf) == 0
#guard tsToInt32 4294967298 == 2
#guard tsToInt32 2147483648 == -2147483648
#guard tsToInt32 (-1.0) == -1
#guard tsToInt32 3.7 == 3
#guard tsToInt32 (-3.7) == -3
#guard tsToInt32 1e20 == 1661992960
#guard tsToInt32 4294967295 == -1
#guard tsToInt32 (-4294967294) == 2
#guard tsToInt32 9007199254740992 == 0
#guard tsToInt32 (-2147483649) == 2147483647

/-! ## ToIntegerOrInfinity, 7.1.5 -/

example : integerOrInfinity? Js.floatNaN = some 0 := by decide
example : integerOrInfinity? 0.0 = some 0 := by decide
example : integerOrInfinity? (-0.0) = some 0 := by decide
example : integerOrInfinity? Js.floatInf = none := by decide
example : integerOrInfinity? (-Js.floatInf) = none := by decide
example : integerOrInfinity? 2.5 = some 2 := by decide
example : integerOrInfinity? (-2.5) = some (-2) := by decide
example : integerOrInfinity? 100.0 = some 100 := by decide
#guard integerOrInfinity? Js.floatNaN == some 0
#guard integerOrInfinity? 0.0 == some 0
#guard integerOrInfinity? (-0.0) == some 0
#guard integerOrInfinity? Js.floatInf == none
#guard integerOrInfinity? (-Js.floatInf) == none
#guard integerOrInfinity? 2.5 == some 2
#guard integerOrInfinity? (-2.5) == some (-2)
#guard integerOrInfinity? 100.0 == some 100
-- The magnitude is exact at every size: this is a hundred quintillion, not a
-- saturated `UInt64`.
#guard integerOrInfinity? 1e20 == some 100000000000000000000

/-! ## ToLength, 7.1.20

ToIntegerOrInfinity clamped into `[0, 2^53 - 1]`. This is the one
conversion that tells the infinities apart: `+∞` is the limit itself and
`-∞` is `+0`, as test262's `clamps-to-integer-limit` rows for `pop`,
`push`, `splice`, and `unshift` observe through the `length` written back. -/

example : tsToLength Js.floatNaN = 0 := by decide
example : tsToLength (-0.0) = 0 := by decide
example : tsToLength (-1.0) = 0 := by decide
example : tsToLength (-Js.floatInf) = 0 := by decide
example : tsToLength 2.5 = 2 := by decide
example : tsToLength 9007199254740991.0 = 9007199254740991 := by decide
example : tsToLength 9007199254740992.0 = 9007199254740991 := by decide
example : tsToLength Js.floatInf = 9007199254740991 := by decide
#guard tsToLength Js.floatNaN == 0
#guard tsToLength (-0.0) == 0
#guard tsToLength (-1.0) == 0
#guard tsToLength (-Js.floatInf) == 0
#guard tsToLength 2.5 == 2
#guard tsToLength 9007199254740991.0 == 9007199254740991
#guard tsToLength 9007199254740992.0 == 9007199254740991
#guard tsToLength Js.floatInf == 9007199254740991

/-! ## `Math.clz32` and `Math.imul`, the two members built on ToUint32 -/

example : tsClz32 0.0 = 32 := by decide
example : tsClz32 1.0 = 31 := by decide
example : tsClz32 2147483648 = 0 := by decide
example : tsImul 2 4 = 8 := by decide
example : tsImul (-1.0) 8 = -8 := by decide

-- test262 `clz32/int32bit.js`, `nan.js`, `infinity.js`, `Math.clz32.js`
#guard tsClz32 (-0.0) == 32
#guard tsClz32 Js.floatNaN == 32
#guard tsClz32 Js.floatInf == 32
#guard tsClz32 (-Js.floatInf) == 32
#guard tsClz32 4294967295 == 0
#guard tsClz32 4294967296 == 32
#guard tsClz32 4294967297 == 31
#guard tsClz32 65535 == 16
#guard tsClz32 65536 == 15
#guard tsClz32 65537 == 15
#guard tsClz32 255 == 24
#guard tsClz32 256 == 23
#guard tsClz32 257 == 23
#guard tsClz32 (-4294967295) == 31
#guard tsClz32 (-4294967296) == 32
#guard tsClz32 (-4294967297) == 0
#guard tsClz32 (-65535) == 0
#guard tsClz32 (-255) == 0
#guard tsClz32 0.5 == 32
#guard tsClz32 1e20 == 1

-- test262 `imul/results.js`
#guard tsImul (-2.0) (-2.0) == 4
#guard tsImul 4294967295 5 == -5
#guard tsImul 4294967294 5 == -10
#guard tsImul (-0.0) 7 == 0
#guard tsImul 0.1 7 == 0
#guard tsImul 0.9 7 == 0
#guard tsImul 1.1 7 == 7
#guard tsImul 1.9 7 == 7
#guard tsImul 1073741824 7 == -1073741824
#guard tsImul 1073741824 1073741824 == 0
#guard tsImul (-1073741824) 7 == 1073741824
#guard tsImul (-1073741824) (-1073741824) == 0
#guard tsImul 2147483648 7 == -2147483648
#guard tsImul 2147483648 2147483648 == 0
#guard tsImul (-2147483648) 7 == -2147483648
#guard tsImul 2147483647 7 == 2147483641
#guard tsImul 2147483647 2147483647 == 1
#guard tsImul 65536 65536 == 0
#guard tsImul Js.floatNaN 7 == 0
#guard tsImul Js.floatInf 7 == 0
#guard tsImul (-4294967297) 3 == -3
#guard tsImul 1e20 1 == 1661992960
