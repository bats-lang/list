#include "share/atspre_staload.hats"
#use list as L

(* Exercises the list_t API. list_t is a datatype: its cells are never
   freed, so this test does not run under valgrind (list_vt is the
   linear list; see tests/dynamic/linear). Exits 1 on a mismatch. *)
implement main0 () = let
  val xs = $L.cons<int>(1, $L.cons<int>(2, $L.cons<int>(3, $L.nil<int>())))
  val r = $L.reverse<int>(xs)
  val m = $L.map<int><int>(xs, lam (x) =<cloref1> x * 10)
  val a = $L.append<int>(xs, m)
  val f = $L.foldl<int><int>(a, 0, lam (acc, x) =<cloref1> acc - x)
  val ok = $L.length<int>(a) = 6 && $L.head<int>(r) = 3
    && $L.head<int>($L.tail<int>(m)) = 20 && f = ~66
    && $L.is_nil<int>($L.nil<int>()) && ~$L.is_nil<int>(xs)
  val () = (if ok then () else println! ("FAIL: fold ", f))
in if ok then () else exit(1) end
