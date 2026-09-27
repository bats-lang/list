#include "share/atspre_staload.hats"
#use list as L

(* Builds linear lists, walks them and consumes them, freeing every
   cell (it runs under valgrind: no cell may be lost). Exits 1 on a
   wrong length or sum. *)
fun upto {n:nat} .<n>. (n: int n): $L.list_vt(int, n) =
  if n = 0 then $L.list_vt_nil() else $L.list_vt_cons(n, upto(n - 1))

fun sum {n:nat} .<n>. (xs: !$L.list_vt(int, n)): int =
  case+ xs of
  | $L.list_vt_nil() => 0
  | $L.list_vt_cons(x, tl) => x + sum(tl)

fun consume {n:nat} .<n>. (xs: $L.list_vt(int, n), acc: int): int =
  case+ xs of
  | ~$L.list_vt_nil() => acc
  | ~$L.list_vt_cons(_, tl) => consume(tl, acc + 1)

implement main0 () = let
  val xs = upto(100)
  val s = sum(xs)
  val k = consume(xs, 0)
  val e = consume($L.list_vt_nil{int}(), 0)
  val ok = s = 5050 && k = 100 && e = 0
  val () = (if ok then () else println! ("FAIL: sum ", s, " count ", k))
in if ok then () else exit(1) end
