#include "share/atspre_staload.hats"
#use list as L

(* Exercises the list API (reverse, map, append, foldl, tail) and frees
   every list it builds; it runs under valgrind, so no cell and no
   closure may be lost. Exits 1 on a mismatch. *)
fn from3 (): $L.list_vt(int, 3) =
  $L.cons<int>(1, $L.cons<int>(2, $L.cons<int>(3, $L.nil<int>())))

implement main0 () = let
  val xs = from3()
  var times10 = lam@ (x: int): int =<clo1> x * 10
  val m = $L.map<int><int>(xs, times10)
  val r = $L.reverse<int>(xs)
  val r3 = $L.head<int>(r)
  val mt = $L.tail<int>(m)
  val m2 = $L.head<int>(mt)
  val () = $L.free<int>(mt)
  val a = $L.append<int>(from3(), $L.map<int><int>(r, times10))
  var minus = lam@ (acc: int, x: int): int =<clo1> acc - x
  val f = $L.foldl<int><int>(a, 0, minus)
  val n = $L.length<int>(a)
  val e = $L.nil<int>()
  val ok = n = 6 && r3 = 3 && m2 = 20 && f = ~66
    && $L.is_nil<int>(e) && ~$L.is_nil<int>(a)
  val () = $L.free<int>(a)
  val () = $L.free<int>(r)
  val () = $L.free<int>(e)
  val () = (if ok then () else println! ("FAIL: fold ", f))
in if ok then () else exit(1) end
