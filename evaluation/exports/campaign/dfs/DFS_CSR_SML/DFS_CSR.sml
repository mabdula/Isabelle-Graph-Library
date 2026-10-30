structure Machine : sig
  val sub_nat : int * int -> int
  val div_nat : int * int -> int
  val mod_nat : int * int -> int
  val upd : int * 'a * 'a array -> 'a array
end = struct
  fun sub_nat (m, n) = if m < n then 0 else m - n
  fun div_nat (m, n) = if n = 0 then 0 else Int.quot (m, n)
  fun mod_nat (m, n) = if n = 0 then m else Int.rem (m, n)
  fun upd (i, x, a) = (Array.update (a, i, x); a)
end


structure DFS_CSR : sig
  type return
  type ('a, 'b, 'c, 'd) dFS_it_imp_state_ext
  val dfs_edges_run :
    Int.int ->
      Int.int array ->
        Int.int array ->
          Int.int ->
            Int.int -> (unit -> (return * (Int.int array * Int.int ref)))
end = struct

datatype typerepa = Typerep of string * typerepa list;

datatype 'a itself = Type;

fun typerep_nata t = Typerep ("Nat.nat", []);

type 'a typerep = {typerep : 'a itself -> typerepa};
val typerep = #typerep : 'a typerep -> 'a itself -> typerepa;

type 'a countable = {};

type 'a heap = {countable_heap : 'a countable, typerep_heap : 'a typerep};
val countable_heap = #countable_heap : 'a heap -> 'a countable;
val typerep_heap = #typerep_heap : 'a heap -> 'a typerep;

val countable_nat = {} : Int.int countable;

val typerep_nat = {typerep = typerep_nata} : Int.int typerep;

val heap_nat = {countable_heap = countable_nat, typerep_heap = typerep_nat} :
  Int.int heap;

fun typerep_boola t = Typerep ("HOL.bool", []);

val countable_bool = {} : bool countable;

val typerep_bool = {typerep = typerep_boola} : bool typerep;

val heap_bool = {countable_heap = countable_bool, typerep_heap = typerep_bool} :
  bool heap;

datatype num = One | Bit0 of num | Bit1 of num;

datatype return = Reachable | NotReachable;

datatype ('a, 'b, 'c, 'd) dFS_it_imp_state_ext =
  DFS_it_imp_state_ext of 'a * 'b * 'c * 'd;

fun refa A_ x = (fn () => ref x);

fun src_imp x = (fn (fa, _) => (fn a => (fn () => Array.sub (fa, a)))) x;

fun tgt_imp x = (fn (_, a) => (fn b => (fn () => Array.sub (a, b)))) x;

fun edge_adv x = (fn _ => fn i => (fn () => (Int.+ (i, (1 : Int.int))))) x;

fun edge_cur x = (fn _ => (fn a => (fn () => a))) x;

fun csr_has_imp A_ =
  (fn (ba, (_, ca)) => fn v => fn () =>
    let
      val i = (fn () => Array.sub (ca, v)) ();
      val e = (fn () => Array.sub (ba, Int.+ (v, (1 : Int.int)))) ();
    in
      Int.< (i, e)
    end);

fun csr_copy_imp n ba ca i =
  (if Int.< (i, n)
    then (fn () => let
                     val s = (fn () => Array.sub (ba, i)) ();
                     val _ = (fn () => Machine.upd (i, s, ca)) ();
                   in
                     csr_copy_imp n ba ca (Int.+ (i, (1 : Int.int))) ()
                   end)
    else (fn () => ()));

fun csr_move_imp A_ =
  (fn (_, (_, ca)) => fn v => fn () =>
    let
      val i = (fn () => Array.sub (ca, v)) ();
      val _ = (fn () => Machine.upd (v, Int.+ (i, (1 : Int.int)), ca)) ();
    in
      ()
    end);

fun edge_has_next x =
  (fn (fa, _) => fn i => fn () => let
                                    val l = (fn () => Array.length fa) ();
                                  in
                                    Int.< (i, l)
                                  end)
    x;

fun csr_current_imp A_ =
  (fn (_, (ea, ca)) => fn v => fn () =>
    let
      val x = (fn () => Array.sub (ca, v)) ();
    in
      (fn () => Array.sub (ea, x)) ()
    end);

fun csr_cursor_init n ba =
  (fn () => let
              val ca = (fn () => Array.array (n, (0 : Int.int))) ();
              val _ = csr_copy_imp n ba ca (0 : Int.int) ();
            in
              ca
            end);

fun ars_pop_imp A_ =
  (fn (_, sr) => fn () =>
    let
      val sp = (fn () => ! sr) ();
    in
      (fn () => sr := (Machine.sub_nat (sp, (1 : Int.int)))) ()
    end);

fun ars_top_imp A_ =
  (fn (aa, sr) => fn () =>
    let
      val sp = (fn () => ! sr) ();
    in
      (fn () => Array.sub (aa, Machine.sub_nat (sp, (1 : Int.int)))) ()
    end);

fun ars_push_imp A_ =
  (fn (aa, sr) => fn x => fn () =>
    let
      val sp = (fn () => ! sr) ();
      val _ = (fn () => Machine.upd (sp, x, aa)) ();
    in
      (fn () => sr := (Int.+ (sp, (1 : Int.int)))) ()
    end);

fun csr_fill_heads c b e si =
  (fn () =>
    let
      val ba = edge_has_next c si ();
    in
      (if ba
        then (fn f_ => fn () => f_ ((edge_cur c si) ()) ())
               (fn ea =>
                 (fn f_ => fn () => f_ ((src_imp c ea) ()) ())
                   (fn k =>
                     (fn f_ => fn () => f_ ((tgt_imp c ea) ()) ())
                       (fn x =>
                         (fn f_ => fn () => f_
                           (((fn () => Array.sub (b, Int.+ (k, (1 : Int.int)))))
                           ()) ())
                           (fn p =>
                             (fn f_ => fn () => f_
                               (((fn () => Machine.upd
                                  (Int.+ (k, (1 : Int.int)),
                                  Int.+ (p, (1 : Int.int)), b)))
                               ()) ())
                               (fn _ =>
                                 (fn f_ => fn () => f_
                                   (((fn () => Machine.upd (p, x, e))) ()) ())
                                   (fn _ =>
                                     (fn f_ => fn () => f_ ((edge_adv c si) ())
                                       ())
                                       (csr_fill_heads c b e)))))))
        else (fn () => ()))
        ()
    end);

fun csr_init_heads c si m =
  (fn () =>
    let
      val b = edge_has_next c si ();
    in
      (if b then (fn f_ => fn () => f_ ((edge_cur c si) ()) ())
                   (fn e =>
                     (fn f_ => fn () => f_ ((tgt_imp c e) ()) ())
                       (fn a => (fn () => Array.array (m, a))))
        else (fn () => Array.fromList []))
        ()
    end);

fun ars_empty_imp A_ cap d =
  (fn () => let
              val aa = (fn () => Array.array (cap, d)) ();
              val sr = refa heap_nat (0 : Int.int) ();
            in
              (aa, sr)
            end);

fun csr_prefix_sums_heads n b j acc =
  (if Int.<= (j, n)
    then (fn () =>
           let
             val c = (fn () => Array.sub (b, j)) ();
           in
             let
               val acca = Int.+ (c, acc);
             in
               (fn f_ => fn () => f_ (((fn () => Machine.upd (j, acca, b))) ())
                 ())
                 (fn _ =>
                   csr_prefix_sums_heads n b (Int.+ (j, (1 : Int.int))) acca)
             end
               ()
           end)
    else (fn () => ()));

fun csr_count_heads n c b m si =
  (fn () =>
    let
      val ba = edge_has_next c si ();
    in
      (if ba
        then (fn f_ => fn () => f_ ((edge_cur c si) ()) ())
               (fn e =>
                 (fn f_ => fn () => f_ ((src_imp c e) ()) ())
                   (fn k =>
                     (fn f_ => fn () => f_
                       ((if Int.<= (Int.+ (k, (2 : Int.int)), n)
                          then (fn f_ => fn () => f_
                                 (((fn () => Array.sub (b,
                                    Int.+ (k, (2 : Int.int)))))
                                 ()) ())
                                 (fn d =>
                                   (fn f_ => fn () => f_
                                     (((fn () => Machine.upd
(Int.+ (k, (2 : Int.int)), Int.+ (d, (1 : Int.int)), b)))
                                     ()) ())
                                     (fn _ => (fn () => ())))
                          else (fn () => ()))
                       ()) ())
                       (fn _ =>
                         (fn f_ => fn () => f_ ((edge_adv c si) ()) ())
                           (csr_count_heads n c b (Int.+ (m, (1 : Int.int)))))))
        else (fn () => m))
        ()
    end);

fun csr_build_heads n c si =
  (fn () =>
    let
      val b =
        (fn () => Array.array (Int.+ (n, (1 : Int.int)), (0 : Int.int))) ();
      val m = csr_count_heads n c b (0 : Int.int) si ();
      val _ = csr_prefix_sums_heads n b (1 : Int.int) (0 : Int.int) ();
      val e = csr_init_heads c si m ();
      val _ = csr_fill_heads c b e si ();
    in
      (b, e)
    end);

fun ars_is_empty_imp A_ =
  (fn (_, sr) => fn () => let
                            val sp = (fn () => ! sr) ();
                          in
                            ((sp : Int.int) = (0 : Int.int))
                          end);

fun imp_stack (DFS_it_imp_state_ext (imp_stack, imp_seen, imp_its, more)) =
  imp_stack;

fun imp_seen (DFS_it_imp_state_ext (imp_stack, imp_seen, imp_its, more)) =
  imp_seen;

fun imp_its (DFS_it_imp_state_ext (imp_stack, imp_seen, imp_its, more)) =
  imp_its;

fun bool_array_set_insert_imp x xi =
  (fn () => let
              val _ = (fn () => Machine.upd (x, true, xi)) ();
            in
              ()
            end);

fun bool_array_set_isin_imp A_ xi x = (fn () => Array.sub (xi, x));

fun dfs_csr_loop t sti =
  (fn () =>
    let
      val e = ars_is_empty_imp heap_nat (imp_stack sti) ();
    in
      (if e then (fn () => NotReachable)
        else (fn f_ => fn () => f_ ((ars_top_imp heap_nat (imp_stack sti)) ())
               ())
               (fn v =>
                 (if ((v : Int.int) = t) then (fn () => Reachable)
                   else (fn f_ => fn () => f_
                          ((csr_has_imp heap_nat (imp_its sti) v) ()) ())
                          (fn b =>
                            (if b then (fn f_ => fn () => f_
 ((csr_current_imp heap_nat (imp_its sti) v) ()) ())
 (fn u =>
   (fn f_ => fn () => f_ ((csr_move_imp heap_nat (imp_its sti) v) ()) ())
     (fn _ =>
       (fn f_ => fn () => f_
         ((bool_array_set_isin_imp heap_bool (imp_seen sti) u) ()) ())
         (fn sn =>
           (if sn then dfs_csr_loop t sti
             else (fn f_ => fn () => f_
                    ((ars_push_imp heap_nat (imp_stack sti) u) ()) ())
                    (fn _ =>
                      (fn f_ => fn () => f_
                        ((bool_array_set_insert_imp u (imp_seen sti)) ()) ())
                        (fn _ => dfs_csr_loop t sti))))))
                              else (fn f_ => fn () => f_
                                     ((ars_pop_imp heap_nat (imp_stack sti)) ())
                                     ())
                                     (fn _ => dfs_csr_loop t sti))))))
        ()
    end);

fun dfs_csr s t sti =
  (fn () => let
              val _ = ars_push_imp heap_nat (imp_stack sti) s ();
              val _ = bool_array_set_insert_imp s (imp_seen sti) ();
            in
              dfs_csr_loop t sti ()
            end);

fun dfs_edges_run n fa ta s t =
  (fn () =>
    let
      val a = csr_build_heads n (fa, ta) (0 : Int.int) ();
    in
      let
        val (ba, ea) = a;
      in
        (fn f_ => fn () => f_ ((csr_cursor_init n ba) ()) ())
          (fn ca =>
            (fn f_ => fn () => f_ ((ars_empty_imp heap_nat n (0 : Int.int)) ())
              ())
              (fn si =>
                (fn f_ => fn () => f_ (((fn () => Array.array (n, false))) ())
                  ())
                  (fn vi =>
                    (fn f_ => fn () => f_
                      ((dfs_csr s t
                         (DFS_it_imp_state_ext (si, vi, (ba, (ea, ca)), ())))
                      ()) ())
                      (fn r => (fn () => (r, si))))))
      end
        ()
    end);

end; (*struct DFS_CSR*)
