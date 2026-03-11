(* list -- singly-linked linear lists *)

#include "share/atspre_staload.hats"

(* ============================================================
   Types
   ============================================================ *)

#pub datatype list_t(t@ype, int) =
  | {a:t@ype} list_nil(a, 0) of ()
  | {a:t@ype}{n:nat} list_cons(a, n+1) of (a, list_t(a, n))

#pub typedef list(a:t@ype) = [n:nat] list_t(a, n)

(* ============================================================
   Construction
   ============================================================ *)

#pub fun {a:t@ype} nil (): list_t(a, 0)

#pub fun {a:t@ype} cons {n:nat}
  (x: a, xs: list_t(a, n)): list_t(a, n+1)

implement {a} nil () = list_nil()

implement {a} cons (x, xs) = list_cons(x, xs)

(* ============================================================
   Length
   ============================================================ *)

#pub fun {a:t@ype} length {n:nat}
  (xs: list_t(a, n)): int(n)

implement {a} length {n} (xs) = let
  fun loop {i:nat} .<i>.
    (xs: list_t(a, i)): int(i) =
    case+ xs of
    | list_nil() => 0
    | list_cons(_, tl) => 1 + loop(tl)
in loop(xs) end

(* ============================================================
   Reverse
   ============================================================ *)

#pub fun {a:t@ype} reverse {n:nat}
  (xs: list_t(a, n)): list_t(a, n)

implement {a} reverse (xs) = let
  fun loop {i:nat}{j:nat} .<j>.
    (acc: list_t(a, i), rest: list_t(a, j)): list_t(a, i+j) =
    case+ rest of
    | list_nil() => acc
    | list_cons(x, tl) => loop(list_cons(x, acc), tl)
in loop(list_nil(), xs) end

(* ============================================================
   Head and tail
   ============================================================ *)

#pub fun {a:t@ype} head {n:pos}
  (xs: list_t(a, n)): a

#pub fun {a:t@ype} tail {n:pos}
  (xs: list_t(a, n)): list_t(a, n-1)

implement {a} head (xs) =
  case+ xs of list_cons(x, _) => x

implement {a} tail (xs) =
  case+ xs of list_cons(_, tl) => tl

(* ============================================================
   Map and fold
   ============================================================ *)

#pub fun {a:t@ype}{b:t@ype} map {n:nat}
  (xs: list_t(a, n), f: a -<cloref1> b): list_t(b, n)

implement {a}{b} map {n} (xs, f) = let
  fun loop {i:nat} .<i>.
    (xs: list_t(a, i), f: (a) -<cloref1> b): list_t(b, i) =
    case+ xs of
    | list_nil() => list_nil()
    | list_cons(x, tl) => list_cons(f(x), loop(tl, f))
in loop(xs, f) end

#pub fun {a:t@ype}{b:t@ype} foldl {n:nat}
  (xs: list_t(a, n), init: b, f: (b, a) -<cloref1> b): b

implement {a}{b} foldl {n} (xs, init, f) = let
  fun loop {i:nat} .<i>.
    (xs: list_t(a, i), acc: b, f: (b, a) -<cloref1> b): b =
    case+ xs of
    | list_nil() => acc
    | list_cons(x, tl) => loop(tl, f(acc, x), f)
in loop(xs, init, f) end

(* ============================================================
   Append
   ============================================================ *)

#pub fun {a:t@ype} append {m:nat}{n:nat}
  (xs: list_t(a, m), ys: list_t(a, n)): list_t(a, m+n)

implement {a} append {m}{n} (xs, ys) = let
  fun loop {i:nat} .<i>.
    (xs: list_t(a, i), ys: list_t(a, n)): list_t(a, i+n) =
    case+ xs of
    | list_nil() => ys
    | list_cons(x, tl) => list_cons(x, loop(tl, ys))
in loop(xs, ys) end

(* ============================================================
   Is_nil
   ============================================================ *)

#pub fun {a:t@ype} is_nil {n:nat}
  (xs: list_t(a, n)): bool(n == 0)

implement {a} is_nil (xs) =
  case+ xs of
  | list_nil() => true
  | list_cons(_, _) => false

(* ============================================================
   Linear list (for holding linear values like arrays)
   ============================================================ *)

#pub datavtype list_vt(vt@ype+, int) =
  | {a:vt@ype} list_vt_nil(a, 0) of ()
  | {a:vt@ype}{n:nat} list_vt_cons(a, n+1) of (a, list_vt(a, n))

#pub vtypedef listv(a:vt@ype) = [n:nat] list_vt(a, n)
