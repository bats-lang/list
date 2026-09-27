(* list -- singly-linked linear lists *)

#include "share/atspre_staload.hats"

(* ============================================================
   Type

   A list is linear: bats has no GC, so every cell is freed by
   whoever holds the list last (free, or a consuming ~ pattern).
   Operations that walk a list borrow it (!); operations that
   rebuild one (reverse, append, tail) consume it and reuse or free
   its cells.
   ============================================================ *)

#pub datavtype list_vt(vt@ype+, int) =
  | {a:vt@ype} list_vt_nil(a, 0) of ()
  | {a:vt@ype}{n:nat} list_vt_cons(a, n+1) of (a, list_vt(a, n))

#pub vtypedef listv(a:vt@ype) = [n:nat] list_vt(a, n)

(* ============================================================
   Construction and freeing
   ============================================================ *)

#pub fun {a:vt@ype} nil (): list_vt(a, 0)

#pub fun {a:vt@ype} cons {n:nat}
  (x: a, xs: list_vt(a, n)): list_vt(a, n+1)

(* Frees every cell. The elements are values (t@ype); a list of
   linear elements is consumed with ~ patterns instead. *)
#pub fun {a:t@ype} free {n:nat}
  (xs: list_vt(a, n)): void

implement {a} nil () = list_vt_nil()

implement {a} cons (x, xs) = list_vt_cons(x, xs)

implement {a} free {n} (xs) = let
  fun loop {i:nat} .<i>.
    (xs: list_vt(a, i)): void =
    case+ xs of
    | ~list_vt_nil() => ()
    | ~list_vt_cons(_, tl) => loop(tl)
in loop(xs) end

(* ============================================================
   Length and is_nil
   ============================================================ *)

#pub fun {a:vt@ype} length {n:nat}
  (xs: !list_vt(a, n)): int(n)

#pub fun {a:vt@ype} is_nil {n:nat}
  (xs: !list_vt(a, n)): bool(n == 0)

implement {a} length {n} (xs) = let
  fun loop {i:nat}{k:nat} .<i>.
    (xs: !list_vt(a, i), k: int(k)): int(i+k) =
    case+ xs of
    | list_vt_nil() => k
    | list_vt_cons(_, tl) => loop(tl, k + 1)
in loop(xs, 0) end

implement {a} is_nil (xs) =
  case+ xs of
  | list_vt_nil() => true
  | list_vt_cons(_, _) => false

(* ============================================================
   Reverse (in place: the cells are reused)
   ============================================================ *)

#pub fun {a:vt@ype} reverse {n:nat}
  (xs: list_vt(a, n)): list_vt(a, n)

implement {a} reverse (xs) = let
  fun loop {i:nat}{j:nat} .<j>.
    (acc: list_vt(a, i), rest: list_vt(a, j)): list_vt(a, i+j) =
    case+ rest of
    | ~list_vt_nil() => acc
    | @list_vt_cons(_, tl) => let
        val next = tl
        val () = tl := acc
        prval () = fold@(rest)
      in loop(rest, next) end
in loop(list_vt_nil(), xs) end

(* ============================================================
   Head and tail
   ============================================================ *)

#pub fun {a:t@ype} head {n:pos}
  (xs: !list_vt(a, n)): a

(* Frees the first cell. *)
#pub fun {a:t@ype} tail {n:pos}
  (xs: list_vt(a, n)): list_vt(a, n-1)

implement {a} head (xs) =
  case+ xs of list_vt_cons(x, _) => x

implement {a} tail (xs) =
  case+ xs of ~list_vt_cons(_, tl) => tl

(* ============================================================
   Map and fold

   The function is a closure on the caller's stack, passed by
   reference, so nothing is allocated for it:
     var f = lam@ (x: int): int =<clo1> x * 10
     val ys = map<int><int>(xs, f)
   ============================================================ *)

#pub fun {a:t@ype}{b:vt@ype} map {n:nat}
  (xs: !list_vt(a, n), f: &(a) -<clo1> b): list_vt(b, n)

#pub fun {a:t@ype}{b:vt@ype} foldl {n:nat}
  (xs: !list_vt(a, n), init: b, f: &(b, a) -<clo1> b): b

implement {a}{b} map {n} (xs, f) = let
  fun loop {i:nat} .<i>.
    (xs: !list_vt(a, i), f: &(a) -<clo1> b): list_vt(b, i) =
    case+ xs of
    | list_vt_nil() => list_vt_nil()
    | list_vt_cons(x, tl) => let
        val y = f(x)
      in list_vt_cons(y, loop(tl, f)) end
in loop(xs, f) end

implement {a}{b} foldl {n} (xs, init, f) = let
  fun loop {i:nat} .<i>.
    (xs: !list_vt(a, i), acc: b, f: &(b, a) -<clo1> b): b =
    case+ xs of
    | list_vt_nil() => acc
    | list_vt_cons(x, tl) => loop(tl, f(acc, x), f)
in loop(xs, init, f) end

(* ============================================================
   Append (consumes both lists; the cells of xs are reused)
   ============================================================ *)

#pub fun {a:vt@ype} append {m:nat}{n:nat}
  (xs: list_vt(a, m), ys: list_vt(a, n)): list_vt(a, m+n)

implement {a} append {m}{n} (xs, ys) = let
  fun loop {i:nat} .<i>.
    (xs: list_vt(a, i), ys: list_vt(a, n)): list_vt(a, i+n) =
    case+ xs of
    | ~list_vt_nil() => ys
    | @list_vt_cons(_, tl) => let
        val () = tl := loop(tl, ys)
        prval () = fold@(xs)
      in xs end
in loop(xs, ys) end

(* ============================================================
   Tests (bats test)
   ============================================================ *)

$UNITTEST.run begin

(* [k, k + 1, k + 2] (a helper, not a test: tests take no arguments) *)
fn from3 (k: int): list_vt(int, 3) = cons<int>(k, cons<int>(k + 1, cons<int>(k + 2, nil<int>())))

fn test_length (): bool = let
  val xs = from3(1)
  val e = nil<int>()
  val ok = (length<int>(xs) = 3) && (length<int>(e) = 0)
  val () = free<int>(xs)
  val () = free<int>(e)
in ok end

fn test_head_tail (): bool = let
  val xs = from3(1)
  val h = head<int>(xs)
  val t = tail<int>(xs)
  val h2 = head<int>(t)
  val () = free<int>(t)
in (h = 1) && (h2 = 2) end

fn test_reverse (): bool = let
  val r = reverse<int>(from3(1))
  val h = head<int>(r)
  val t = tail<int>(tail<int>(r))
  val l = head<int>(t)
  val () = free<int>(t)
in (h = 3) && (l = 1) end

fn test_map (): bool = let
  val xs = from3(1)
  var f = lam@ (x: int): int =<clo1> x * 10
  val m = map<int><int>(xs, f)
  val () = free<int>(xs)
  val h = head<int>(m)
  val t = tail<int>(m)
  val h2 = head<int>(t)
  val () = free<int>(t)
in (h = 10) && (h2 = 20) end

(* foldl is left to right: ((0 - 1) - 2) - 3 *)
fn test_foldl (): bool = let
  val xs = from3(1)
  var f = lam@ (acc: int, x: int): int =<clo1> acc - x
  val s = foldl<int><int>(xs, 0, f)
  val () = free<int>(xs)
in s = ~6 end

fn test_append (): bool = let
  val a = append<int>(from3(1), cons<int>(4, nil<int>()))
  val n = length<int>(a)
  val t = tail<int>(tail<int>(tail<int>(a)))
  val l = head<int>(t)
  val () = free<int>(t)
in (n = 4) && (l = 4) end

fn test_is_nil (): bool = let
  val e = nil<int>()
  val xs = from3(1)
  val ok = is_nil<int>(e) && ~is_nil<int>(xs)
  val () = free<int>(e)
  val () = free<int>(xs)
in ok end

end
