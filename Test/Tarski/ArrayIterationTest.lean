import Tarski.Eval
import Tarski.Format

/-! The `Array` members a callback enters, and the two statics.

`every`, `some`, `find`, `findIndex`, `forEach`, `map`, and `filter` are
one walk in the evaluator — `visitElements` over a `VisitKind` — because
23.1.3's seven algorithms differ only in what they do with the call's
result and in whether a hole is visited at all. Both halves of that are
pinned below, as are `reduce` and `reduceRight`'s two ways of finding an
initial accumulator, `flat`'s depth, `sort`'s stability and its
`undefined`-last rule, and `Array.from`/`Array.of`'s shared allocation.

There is no elision in this AST (`[1, , 2]` is #394's), so a hole is
always made here by a write past the end or by `Array(n)`. -/

open Tarski

/-- What the binary would print, so a case reads as its own stdout. -/
private def outcome (p : Program) : String :=
  match runScript p with
  | none => "<diverges>"
  | some (.error (.throw v), h) => s!"uncaught: {describeThrown h v}"
  | some (.error _, _) => "<abrupt>"
  | some (.ok none, _) => "<empty>"
  | some (.ok (some v), _) => formatValue v

/-- A program that is one expression. -/
private def expr (e : Expr) : Program := [.exprStmt e]

/-- An array literal of number literals. -/
private def nums (xs : List Float) : Expr := .arrayLit (xs.map (.numLit ·))

/-- `<recv>.<name>(<args>)`. -/
private def callOn (recv : Expr) (name : String) (args : List Expr) : Expr :=
  .call (.member recv name) args

/-- A one-parameter arrow with a concise body. -/
private def fn1 (x : String) (body : Expr) : Expr :=
  .arrow [{ target := x, default := none }] (.expr body)

/-- A two-parameter arrow with a concise body. -/
private def fn2 (x y : String) (body : Expr) : Expr :=
  .arrow [{ target := x, default := none }, { target := y, default := none }] (.expr body)

/-- `const xs = Array(<n>);` — the only way to spell a hole here. -/
private def holes (n : Float) : Expr := .call (.ident "Array") [.numLit n]

/-- `class A extends Array {}` -/
private def declareA : Stmt :=
  .classDecl "A" { name := some "A", superClass := some (.ident "Array"), elements := [] }

/-! ## `forEach`

The callback sees `(value, index, array)` and a `thisArg` of its own; a
hole is skipped; the length is read once at the start, so an element the
callback appends is never visited. -/

#guard outcome
    [ .varDecl .«let» [{ target := "seen", init := some (.strLit "") }],
      .exprStmt (callOn (.arrayLit [.strLit "a", .strLit "b"]) "forEach"
        [fn2 "v" "i" (.assign (.ident "seen")
          (.binary .add (.binary .add (.ident "seen") (.ident "v")) (.ident "i")))]),
      .exprStmt (.ident "seen") ]
  == "a0b1"

-- The third argument is the array itself.
#guard outcome
    [ .varDecl .«let» [{ target := "same", init := some (.boolLit false) }],
      .varDecl .«const» [{ target := "xs", init := some (nums [1.0]) }],
      .exprStmt (callOn (.ident "xs") "forEach"
        [.arrow [{ target := "v", default := none }, { target := "i", default := none },
                 { target := "a", default := none }]
          (.expr (.assign (.ident "same") (.binary .strictEq (.ident "a") (.ident "xs"))))]),
      .exprStmt (.ident "same") ]
  == "true"

-- A hole is skipped, so the callback runs once and not twice.
#guard outcome
    [ .varDecl .«let» [{ target := "n", init := some (.numLit 0.0) }],
      .varDecl .«const» [{ target := "xs", init := some (holes 2.0) }],
      .exprStmt (.assign (.index (.ident "xs") (.numLit 0.0)) (.numLit 1.0)),
      .exprStmt (callOn (.ident "xs") "forEach"
        [fn1 "v" (.assign (.ident "n") (.binary .add (.ident "n") (.numLit 1.0)))]),
      .exprStmt (.ident "n") ]
  == "1"

-- An element the callback appends is past the length the walk read.
#guard outcome
    [ .varDecl .«let» [{ target := "n", init := some (.numLit 0.0) }],
      .varDecl .«const» [{ target := "xs", init := some (nums [1.0]) }],
      .exprStmt (callOn (.ident "xs") "forEach"
        [fn1 "v" (.logical .and
          (.assign (.ident "n") (.binary .add (.ident "n") (.numLit 1.0)))
          (callOn (.ident "xs") "push" [.numLit 2.0]))]),
      .exprStmt (.ident "n") ]
  == "1"

-- An element the callback deletes before its turn is skipped.
#guard outcome
    [ .varDecl .«let» [{ target := "n", init := some (.numLit 0.0) }],
      .varDecl .«const» [{ target := "xs", init := some (nums [1.0, 2.0]) }],
      .exprStmt (callOn (.ident "xs") "forEach"
        [fn1 "v" (.logical .and
          (.assign (.ident "n") (.binary .add (.ident "n") (.numLit 1.0)))
          (.delete (.index (.ident "xs") (.numLit 1.0))))]),
      .exprStmt (.ident "n") ]
  == "1"

#guard outcome (expr (callOn (nums [1.0]) "forEach" [fn1 "v" (.ident "v")])) == "undefined"
#guard outcome (expr (callOn (.arrayLit []) "forEach" [.numLit 1.0]))
  == "uncaught: TypeError: not a function"
-- The callback is checked even when there is nothing to visit.
#guard outcome (expr (callOn (.arrayLit []) "map" [.numLit 1.0]))
  == "uncaught: TypeError: not a function"

/-! ## `map` and `filter`

Both allocate through ArraySpeciesCreate — `map` at the receiver's
length, `filter` at 0 — so a subclass of `Array` gets a subclass
instance. `map` writes at the source's index, which is what keeps a hole
a hole; `filter` writes at a running index of its own, which is what
drops one. -/

#guard outcome
    (expr (callOn (callOn (nums [1.0, 2.0]) "map" [fn1 "x" (.binary .mul (.ident "x")
      (.numLit 3.0))]) "join" []))
  == "3,6"
#guard outcome
    [ declareA,
      .exprStmt (.binary .instanceof
        (callOn (.new (.ident "A") [.numLit 1.0]) "map" [fn1 "x" (.ident "x")]) (.ident "A")) ]
  == "true"
-- A hole is not visited and so not defined in the result.
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (holes 2.0) }],
      .exprStmt (.assign (.index (.ident "xs") (.numLit 1.0)) (.numLit 1.0)),
      .exprStmt (callOn (callOn (.ident "xs") "map" [fn1 "x" (.ident "x")])
        "hasOwnProperty" [.numLit 0.0]) ]
  == "false"
-- The result's length is the source's, holes and all.
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (holes 3.0) }],
      .exprStmt (.member (callOn (.ident "xs") "map" [fn1 "x" (.ident "x")]) "length") ]
  == "3"

#guard outcome
    (expr (callOn (callOn (nums [1.0, 2.0, 3.0]) "filter"
      [fn1 "x" (.binary .gt (.ident "x") (.numLit 1.0))]) "join" []))
  == "2,3"
#guard outcome (expr (.member (callOn (nums [1.0, 2.0]) "filter" [fn1 "x" (.boolLit false)])
  "length")) == "0"
-- The element the predicate saw is what is kept, even if the callback
-- has since changed the source.
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (nums [1.0, 2.0]) }],
      .exprStmt (callOn (callOn (.ident "xs") "filter"
        [fn1 "x" (.logical .and
          (.assign (.index (.ident "xs") (.numLit 1.0)) (.numLit 9.0))
          (.boolLit true))]) "join" []) ]
  == "1,9"

/-! ## `every`, `some`, `find`, and `findIndex`

The first two stop early and answer a boolean; the empty array's two
answers are the identities of `&&` and `||`. `find` and `findIndex` are
the two that visit a hole, as `undefined`. -/

#guard outcome (expr (callOn (.arrayLit []) "every" [fn1 "x" (.boolLit false)])) == "true"
#guard outcome (expr (callOn (.arrayLit []) "some" [fn1 "x" (.boolLit true)])) == "false"
#guard outcome
    (expr (callOn (nums [1.0, 2.0]) "every" [fn1 "x" (.binary .gt (.ident "x") (.numLit 0.0))]))
  == "true"
#guard outcome
    (expr (callOn (nums [1.0, 2.0]) "some" [fn1 "x" (.binary .gt (.ident "x") (.numLit 1.0))]))
  == "true"
-- `every` stops at the first falsy result: two elements, one call.
#guard outcome
    [ .varDecl .«let» [{ target := "n", init := some (.numLit 0.0) }],
      .exprStmt (callOn (nums [1.0, 2.0]) "every"
        [fn1 "x" (.logical .and
          (.assign (.ident "n") (.binary .add (.ident "n") (.numLit 1.0)))
          (.boolLit false))]),
      .exprStmt (.ident "n") ]
  == "1"
#guard outcome
    (expr (callOn (nums [1.0, 2.0, 3.0]) "find" [fn1 "x" (.binary .gt (.ident "x")
      (.numLit 1.0))]))
  == "2"
#guard outcome
    (expr (callOn (nums [1.0]) "find" [fn1 "x" (.boolLit false)])) == "undefined"
#guard outcome
    (expr (callOn (nums [1.0, 2.0, 3.0]) "findIndex" [fn1 "x" (.binary .gt (.ident "x")
      (.numLit 1.0))]))
  == "1"
#guard outcome (expr (callOn (nums [1.0]) "findIndex" [fn1 "x" (.boolLit false)])) == "-1"
-- A hole *is* visited, as `undefined`, which is the whole difference
-- between these two and the five above.
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (holes 2.0) }],
      .exprStmt (.assign (.index (.ident "xs") (.numLit 1.0)) (.numLit 1.0)),
      .exprStmt (callOn (.ident "xs") "findIndex"
        [fn1 "x" (.binary .strictEq (.ident "x") .undefLit)]) ]
  == "0"

/-! ## `findLast` and `findLastIndex`

`find` and `findIndex` counting down (23.1.3.11, .12): every index is
visited, a hole as `undefined`, from the last to the first, and the walk
stops at the first truthy answer. -/

#guard outcome
    (expr (callOn (nums [1.0, 2.0, 3.0]) "findLast" [fn1 "x" (.binary .lt (.ident "x")
      (.numLit 3.0))]))
  == "2"
#guard outcome
    (expr (callOn (nums [1.0]) "findLast" [fn1 "x" (.boolLit false)])) == "undefined"
#guard outcome
    (expr (callOn (nums [1.0, 2.0, 3.0]) "findLastIndex" [fn1 "x" (.binary .lt (.ident "x")
      (.numLit 3.0))]))
  == "1"
#guard outcome (expr (callOn (nums [1.0]) "findLastIndex" [fn1 "x" (.boolLit false)])) == "-1"
-- The order is descending, and the walk stops at the first hit.
#guard outcome
    [ .varDecl .«let» [{ target := "seen", init := some (.strLit "") }],
      .exprStmt (callOn (nums [1.0, 2.0, 3.0]) "findLast"
        [fn1 "x" (.logical .and
          (.assign (.ident "seen") (.binary .add (.ident "seen") (.ident "x")))
          (.binary .strictEq (.ident "x") (.numLit 2.0)))]),
      .exprStmt (.ident "seen") ]
  == "32"
-- A hole is visited, as `undefined`.
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (holes 2.0) }],
      .exprStmt (.assign (.index (.ident "xs") (.numLit 0.0)) (.numLit 1.0)),
      .exprStmt (callOn (.ident "xs") "findLastIndex"
        [fn1 "x" (.binary .strictEq (.ident "x") .undefLit)]) ]
  == "1"
-- The predicate is checked before any element, so an empty array still
-- refuses a non-function.
#guard outcome (expr (callOn (.arrayLit []) "findLast" [.numLit 1.0]))
  == "uncaught: TypeError: not a function"
-- Generic over an array-like, with `(value, index, object)` as the
-- arguments.
#guard outcome
    (expr (.call (.member (.member (.member (.ident "Array") "prototype") "findLast") "call")
      [.objectLit [.init "length" (.numLit 2.0), .init "0" (.strLit "a"),
        .init "1" (.strLit "b")],
       fn2 "v" "i" (.binary .strictEq (.ident "i") (.numLit 1.0))]))
  == "b"

/-! ## `reduce` and `reduceRight`

With an initial value the fold starts there; without one it starts at the
first — or last — *present* element, and an array with none at all is the
refusal. -/

#guard outcome
    (expr (callOn (nums [1.0, 2.0, 3.0]) "reduce"
      [fn2 "a" "b" (.binary .add (.ident "a") (.ident "b"))]))
  == "6"
#guard outcome
    (expr (callOn (nums [1.0, 2.0]) "reduce"
      [fn2 "a" "b" (.binary .add (.ident "a") (.ident "b")), .numLit 10.0]))
  == "13"
#guard outcome (expr (callOn (.arrayLit []) "reduce"
  [fn2 "a" "b" (.ident "a"), .numLit 0.0])) == "0"
#guard outcome (expr (callOn (.arrayLit []) "reduce" [fn2 "a" "b" (.ident "a")]))
  == "uncaught: TypeError: Reduce of empty array with no initial value"
-- One present element and no initial value: the accumulator is that
-- element and the callback never runs.
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (holes 2.0) }],
      .exprStmt (.assign (.index (.ident "xs") (.numLit 1.0)) (.numLit 1.0)),
      .exprStmt (callOn (.ident "xs") "reduce"
        [.arrow [{ target := "a", default := none }, { target := "b", default := none }]
          (.block [.throwStmt (.new (.ident "Error") [])])]) ]
  == "1"
#guard outcome
    (expr (callOn (nums [1.0, 2.0, 3.0]) "reduceRight"
      [fn2 "a" "b" (.binary .add (.binary .add (.ident "a") (.strLit "")) (.ident "b"))]))
  == "321"
#guard outcome (expr (callOn (.arrayLit []) "reduceRight" [fn2 "a" "b" (.ident "a")]))
  == "uncaught: TypeError: Reduce of empty array with no initial value"

/-! ## `flat` and `flatMap`

23.1.3.13's depth is 1 by default and `+∞` for an infinity; a negative
depth and 0 both copy. A hole is dropped whatever the depth is, the walk
asking HasProperty first. -/

-- `[1, [2, [3]]].flat()` is `[1, 2, [3]]`: one level, so the inner array
-- is still an array. At `Infinity` it is not.
#guard outcome
    (expr (.member (callOn (.arrayLit [.numLit 1.0, .arrayLit [.numLit 2.0, nums [3.0]]])
      "flat" []) "length"))
  == "3"
#guard outcome
    (expr (.call (.member (.ident "Array") "isArray")
      [.index (callOn (.arrayLit [.numLit 1.0, .arrayLit [.numLit 2.0, nums [3.0]]]) "flat" [])
        (.numLit 2.0)]))
  == "true"
#guard outcome
    (expr (.call (.member (.ident "Array") "isArray")
      [.index (callOn (.arrayLit [.numLit 1.0, .arrayLit [.numLit 2.0, nums [3.0]]]) "flat"
        [.ident "Infinity"]) (.numLit 2.0)]))
  == "false"
#guard outcome
    (expr (.member (callOn (.arrayLit [.numLit 1.0, .arrayLit [.numLit 2.0, nums [3.0]]])
      "flat" [.ident "Infinity"]) "length"))
  == "3"
#guard outcome
    (expr (.member (callOn (.arrayLit [.numLit 1.0, nums [2.0]]) "flat" [.numLit 0.0]) "length"))
  == "2"
#guard outcome
    (expr (.member (callOn (.arrayLit [.numLit 1.0, nums [2.0]]) "flat"
      [.unary .neg (.numLit 1.0)]) "length"))
  == "2"
-- A hole is dropped, so the result is shorter than the source.
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (holes 2.0) }],
      .exprStmt (.assign (.index (.ident "xs") (.numLit 1.0)) (.numLit 1.0)),
      .exprStmt (.member (callOn (.ident "xs") "flat" []) "length") ]
  == "1"
#guard outcome
    (expr (callOn (callOn (nums [1.0, 2.0]) "flatMap"
      [fn1 "x" (.arrayLit [.ident "x", .binary .mul (.ident "x") (.numLit 2.0)])]) "join" []))
  == "1,2,2,4"
-- One level only: a nested array the mapper returns is not flattened.
#guard outcome
    (expr (.member (callOn (nums [1.0]) "flatMap" [fn1 "x" (.arrayLit [nums [1.0]])]) "length"))
  == "1"
#guard outcome (expr (callOn (.arrayLit []) "flatMap" [.numLit 1.0]))
  == "uncaught: TypeError: not a function"

/-! ## `sort`

A stable merge sort over the present elements, `undefined` last whatever
the comparator says, holes moved to the very end and then deleted. The
comparator is checked **before** ToObject, which is 23.1.3.30 step 1. -/

#guard outcome (expr (callOn (callOn (nums [10.0, 9.0, 1.0]) "sort" []) "join" []))
  == "1,10,9"
#guard outcome
    (expr (callOn (callOn (nums [3.0, 1.0, 2.0]) "sort"
      [fn2 "a" "b" (.binary .sub (.ident "a") (.ident "b"))]) "join" []))
  == "1,2,3"
-- `undefined` sorts last, ahead of the holes.
#guard outcome
    (expr (callOn (callOn (.arrayLit [.undefLit, .numLit 2.0, .numLit 1.0]) "sort" []) "join" []))
  == "1,2,"
-- A hole ends up at the end and is deleted: the length stands, the key
-- does not.
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (holes 3.0) }],
      .exprStmt (.assign (.index (.ident "xs") (.numLit 1.0)) (.numLit 2.0)),
      .exprStmt (.assign (.index (.ident "xs") (.numLit 2.0)) (.numLit 1.0)),
      .exprStmt (callOn (.ident "xs") "sort" []),
      .exprStmt (.logical .and
        (.binary .strictEq (.member (.ident "xs") "length") (.numLit 3.0))
        (.unary .not (callOn (.ident "xs") "hasOwnProperty" [.numLit 2.0]))) ]
  == "true"
-- Stability: two records with the same first component keep their order.
#guard outcome
    (expr (callOn (callOn
      (.arrayLit [.arrayLit [.numLit 1.0, .strLit "a"], .arrayLit [.numLit 0.0, .strLit "b"],
                  .arrayLit [.numLit 1.0, .strLit "c"]])
      "sort" [fn2 "p" "q" (.binary .sub (.index (.ident "p") (.numLit 0.0))
        (.index (.ident "q") (.numLit 0.0)))]) "join" []))
  == "0,b,1,a,1,c"
-- The comparator is checked ahead of ToObject, so this is its refusal
-- and not the one a nullish receiver would make.
#guard outcome
    (expr (.call (.member (.member (.member (.ident "Array") "prototype") "sort") "call")
      [.undefLit, .numLit 1.0]))
  == "uncaught: TypeError: The comparison function must be either a function or undefined"
#guard outcome (expr (callOn (nums [1.0, 2.0]) "sort" [.numLit 1.0]))
  == "uncaught: TypeError: The comparison function must be either a function or undefined"
-- A comparator answering NaN is +0, so the order stands.
#guard outcome
    (expr (callOn (callOn (nums [2.0, 1.0]) "sort" [fn2 "a" "b" (.ident "NaN")]) "join" []))
  == "2,1"
-- It answers the receiver itself.
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (nums [1.0]) }],
      .exprStmt (.binary .strictEq (callOn (.ident "xs") "sort" []) (.ident "xs")) ]
  == "true"

/-! ## `Array.from` and `Array.of`

Both allocate through the `this` they were called on when it is a
constructor and through ArrayCreate when it is not, which is what
`Array.from.call(A, …)` observes. `Array.from` takes the iterable path
when GetMethod(items, @@iterator) answers a method (23.1.2.1 step 3) and
reads an array-like by index otherwise. -/

#guard outcome
    (expr (callOn (.call (.member (.ident "Array") "from")
      [.objectLit [.init "length" (.numLit 2.0)], fn2 "_" "i" (.ident "i")]) "join" []))
  == "0,1"

/-- `Symbol.iterator` as a computed key. -/
private def iterKey : PropKey := .computed (.member (.ident "Symbol") "iterator")

/-- The issue's iterable, with a close counter: `{ [Symbol.iterator]() {
let i = 0; return { next: () => ({ value: i, done: i++ >= 3 }), return()
{ closed = closed + 1; return {}; } }; } }`. -/
private def counter : Expr :=
  .objectLit
    [ .method .method iterKey []
        [ .varDecl .«let» [{ target := "i", init := some (.numLit 0.0) }],
          .returnStmt (some (.objectLit
            [ .init "next" (.arrow [] (.expr (.objectLit
                [ .init "value" (.ident "i"),
                  .init "done" (.binary .ge (.update .inc false (.ident "i")) (.numLit 3.0)) ]))),
              .method .method "return" []
                [ .exprStmt (.compoundAssign .add (.ident "closed") (.numLit 1.0)),
                  .returnStmt (some (.objectLit [])) ] ])) ] ]

/-- `let closed = 0; const it = <counter>;` -/
private def withCounter : List Stmt :=
  [ .varDecl .«let» [{ target := "closed", init := some (.numLit 0.0) }],
    .varDecl .«const» [{ target := "it", init := some counter }] ]

-- The iterable path (#66): an iterable that is not array-like is walked
-- through its iterator, and the mapper sees each value with its index.
#guard outcome
    (withCounter ++ [.exprStmt (.member (.call (.member (.ident "Array") "from") [.ident "it"]) "length")])
  == "3"
#guard outcome
    (withCounter ++
      [.exprStmt (callOn (.call (.member (.ident "Array") "from")
        [.ident "it", fn2 "v" "i" (.binary .add (.binary .mul (.ident "v") (.numLit 10.0)) (.ident "i"))])
        "join" [])])
  == "0,11,22"
-- A mapper that throws closes the iterator (step 4.d.iv's
-- IfAbruptCloseIterator); an exhausted iterator is not closed.
#guard outcome
    (withCounter ++
      [ .tryStmt
          [.exprStmt (.call (.member (.ident "Array") "from")
            [.ident "it", fn1 "v" (.call (.ident "fail") [])])]
          (some { param := none, body := [] }) none,
        .exprStmt (.ident "closed") ])
  == "1"
#guard outcome
    (withCounter ++
      [ .exprStmt (.call (.member (.ident "Array") "from") [.ident "it"]),
        .exprStmt (.ident "closed") ])
  == "0"
-- On the iterable path the constructor is called with no arguments
-- (step 4.a), so `Array.from.call(Object, [])` is a plain object and not
-- a `Number` wrapper around 0.
#guard outcome
    (expr (.binary .strictEq
      (.member (.call (.member (.member (.ident "Array") "from") "call") [.ident "Object", .arrayLit []])
        "constructor")
      (.ident "Object")))
  == "true"
-- GetMethod: a nullish `@@iterator` means the array-like path, and a
-- non-callable one is a TypeError before anything is read by index.
#guard outcome
    (expr (callOn (.call (.member (.ident "Array") "from")
      [.objectLit [.init "length" (.numLit 1.0), .init "0" (.numLit 7.0), .init iterKey .nullLit]])
      "join" []))
  == "7"
#guard outcome
    (expr (.call (.member (.ident "Array") "from")
      [.objectLit [.init "length" (.numLit 1.0), .init iterKey (.numLit 1.0)]]))
  == "uncaught: TypeError: [object Object] is not iterable"
-- There is no HasProperty in 23.1.2.1's loop, so a hole arrives as
-- `undefined` rather than staying one.
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (holes 2.0) }],
      .exprStmt (callOn (.call (.member (.ident "Array") "from") [.ident "xs"])
        "hasOwnProperty" [.numLit 0.0]) ]
  == "true"
#guard outcome
    (expr (.call (.member (.ident "Array") "from")
      [.objectLit [.init "length" (.numLit 1.0)], .numLit 1.0]))
  == "uncaught: TypeError: not a function"
#guard outcome
    (expr (.call (.member (.ident "Array") "from") [.undefLit]))
  == "uncaught: TypeError: Cannot convert undefined or null to object"
-- A string has an `@@iterator`, so it is walked by code point and not
-- read by code unit as the array-like it is boxed into would be: a
-- surrogate pair is one element.
#guard outcome
    (expr (.call (.member (.call (.member (.ident "Array") "from") [.strLit "ab"]) "join") []))
  == "a,b"
#guard outcome
    (expr (.member (.call (.member (.ident "Array") "from") [.strLit "😀"]) "length"))
  == "1"
-- A constructor `this` builds the result.
#guard outcome
    [ declareA,
      .exprStmt (.binary .instanceof
        (.call (.member (.member (.ident "Array") "from") "call")
          [.ident "A", .objectLit [.init "length" (.numLit 1.0)]]) (.ident "A")) ]
  == "true"
-- A non-constructor `this` gets a plain array.
#guard outcome
    (expr (.binary .instanceof
      (.call (.member (.member (.ident "Array") "from") "call")
        [.undefLit, .objectLit [.init "length" (.numLit 1.0)]]) (.ident "Array")))
  == "true"

-- `Array.of(7)` is one element where `Array(7)` is seven holes.
#guard outcome (expr (.member (.call (.member (.ident "Array") "of") [.numLit 7.0]) "length"))
  == "1"
#guard outcome (expr (.member (.call (.ident "Array") [.numLit 7.0]) "length")) == "7"
#guard outcome
    (expr (callOn (.call (.member (.ident "Array") "of") [.numLit 1.0, .numLit 2.0]) "join" []))
  == "1,2"
#guard outcome
    [ declareA,
      .exprStmt (.binary .instanceof
        (.call (.member (.member (.ident "Array") "of") "call") [.ident "A", .numLit 1.0])
        (.ident "A")) ]
  == "true"
#guard outcome
    (expr (.binary .instanceof
      (.call (.member (.member (.ident "Array") "of") "call") [.undefLit, .numLit 1.0])
      (.ident "Array")))
  == "true"
