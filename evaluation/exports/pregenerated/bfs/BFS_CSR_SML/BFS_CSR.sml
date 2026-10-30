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


structure BFS_CSR : sig
  val bfs_path : Int.int array -> Int.int array -> Int.int -> (unit -> Int.int)
  val bfs_csr_run :
    Int.int ->
      Int.int array ->
        Int.int array ->
          Int.int array ->
            (unit -> (bool array * (Int.int array * Int.int array)))
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_nat = {equal = (fn a => fn b => ((a : Int.int) = b))} : Int.int equal;

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

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_nat = {zero = (0 : Int.int)} : Int.int zero;

fun typerep_boola t = Typerep ("HOL.bool", []);

val countable_bool = {} : bool countable;

val typerep_bool = {typerep = typerep_boola} : bool typerep;

val heap_bool = {countable_heap = countable_bool, typerep_heap = typerep_bool} :
  bool heap;

datatype num = One | Bit0 of num | Bit1 of num;

datatype ('a, 'b, 'c, 'd, 'e) bFS_state_imp_ext =
  BFS_state_imp_ext of 'a * 'c * 'b * Int.int * 'd * 'e;

fun id x = (fn xa => xa) x;

fun eq A_ a b = equal A_ a b;

fun src_imp x = (fn (fa, _) => (fn a => (fn () => Array.sub (fa, a)))) x;

fun tgt_imp x = (fn (_, a) => (fn b => (fn () => Array.sub (a, b)))) x;

fun edge_adv x = (fn _ => fn i => (fn () => (Int.+ (i, (1 : Int.int))))) x;

fun edge_cur x = (fn _ => (fn a => (fn () => a))) x;

fun iterate_range_strict A_ arr start enda fi acc =
  (if Int.< (start, enda)
    then (fn () =>
           let
             val current = (fn () => Array.sub (arr, start)) ();
             val x = fi current acc ();
           in
             iterate_range_strict A_ arr (Int.+ (start, (1 : Int.int))) enda fi
               x ()
           end)
    else (fn () => acc));

fun csr_fold_imp A_ =
  (fn (ba, ea) => fn v => fn f => fn acc => fn () =>
    let
      val i = (fn () => Array.sub (ba, v)) ();
      val j = (fn () => Array.sub (ba, Int.+ (v, (1 : Int.int)))) ();
    in
      iterate_range_strict A_ ea i j f acc ()
    end);

fun edge_has_next x =
  (fn (fa, _) => fn i => fn () => let
                                    val l = (fn () => Array.length fa) ();
                                  in
                                    Int.< (i, l)
                                  end)
    x;

fun bool_array_set_insert_imp x xi =
  (fn () => let
              val _ = (fn () => Machine.upd (x, true, xi)) ();
            in
              ()
            end);

fun bfs_set_srcs_visited imp_vis (fronti, (frontp, buffer_fronti)) =
  (fn () =>
    let
      val _ =
        iterate_range_strict heap_nat fronti (0 : Int.int) frontp
          (fn v => fn _ => bool_array_set_insert_imp v imp_vis) () ();
    in
      imp_vis
    end);

fun bfs_src_to_cf x = (fn () => x);

fun bfs_set_dists A_ di (fronti, (frontp, buffer_fronti)) n =
  iterate_range_strict heap_nat fronti (0 : Int.int) frontp
    (fn v => (fn a => (fn () => Machine.upd (v, n, a)))) di;

fun parent_array_init_imp (ra, k) pa =
  iterate_range_strict heap_nat ra (0 : Int.int) k
    (fn v => fn _ => fn () => let
                                val _ = (fn () => Machine.upd (v, v, pa)) ();
                              in
                                ()
                              end)
    ();

fun par_init_imp (fronti, (frontp, buffer_fronti)) pa =
  parent_array_init_imp (fronti, frontp) pa;

fun bfs_init empty_vis src_imp imp_some_dist imp_some_par =
  (fn () =>
    let
      val v = bfs_set_srcs_visited empty_vis src_imp ();
      val _ = par_init_imp src_imp imp_some_par ();
      val cf = bfs_src_to_cf src_imp ();
      val dists = bfs_set_dists heap_nat imp_some_dist cf (0 : Int.int) ();
    in
      BFS_state_imp_ext (dists, cf, v, (0 : Int.int), imp_some_par, ())
    end);

fun parent_array_get_path_imp pa ra k s =
  (fn () =>
    let
      val _ = (fn () => Machine.upd (k, s, ra)) ();
      val u = (fn () => Array.sub (pa, s)) ();
    in
      (if ((u : Int.int) = s) then (fn () => (Int.+ (k, (1 : Int.int))))
        else parent_array_get_path_imp pa ra (Int.+ (k, (1 : Int.int))) u)
        ()
    end);

fun bfs_path pa ra v = parent_array_get_path_imp pa ra (0 : Int.int) v;

fun visited
  (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) =
  visited;

fun parent
  (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) =
  parent;

fun dists
  (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) =
  dists;

fun current_dist_update current_dista
  (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) =
  BFS_state_imp_ext
    (dists, current, visited, current_dista current_dist, parent, more);

fun visited_update visiteda
  (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) =
  BFS_state_imp_ext
    (dists, current, visiteda visited, current_dist, parent, more);

fun current_update currenta
  (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) =
  BFS_state_imp_ext
    (dists, currenta current, visited, current_dist, parent, more);

fun parent_update parenta
  (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) =
  BFS_state_imp_ext
    (dists, current, visited, current_dist, parenta parent, more);

fun dists_update distsa
  (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) =
  BFS_state_imp_ext
    (distsa dists, current, visited, current_dist, parent, more);

fun current_dist
  (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) =
  current_dist;

fun current
  (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) =
  current;

fun bfs_cf_is_empty (B1_, B2_) (fronti, (frontp, buffer_fronti)) =
  (fn () => (eq B2_ frontp (zero B1_)));

fun parent_array_extend_imp pa u v =
  (fn () => let
              val _ = (fn () => Machine.upd (v, u, pa)) ();
            in
              ()
            end);

fun bool_array_set_isin_imp A_ xi x = (fn () => Array.sub (xi, x));

fun bfs_csr_inner_loop gi visi pari u (front, frontpt) =
  csr_fold_imp heap_nat gi u
    (fn v => fn (fronta, frontpta) => fn () =>
      let
        val b = bool_array_set_isin_imp heap_bool visi v ();
      in
        (if not b
          then (fn f_ => fn () => f_
                 (((fn () => Machine.upd (frontpta, v, fronta))) ()) ())
                 (fn frontb =>
                   (fn f_ => fn () => f_ ((bool_array_set_insert_imp v visi) ())
                     ())
                     (fn _ =>
                       (fn f_ => fn () => f_ ((parent_array_extend_imp pari u v)
                         ()) ())
                         (fn _ =>
                           (fn () =>
                             (frontb, Int.+ (frontpta, (1 : Int.int)))))))
          else (fn () => (fronta, frontpta)))
          ()
      end)
    (front, frontpt);

fun bfs_csr_outer_loop gi visi pari (old_front, old_frontp) (front, frontpt) =
  iterate_range_strict heap_nat old_front (0 : Int.int) old_frontp
    (bfs_csr_inner_loop gi visi pari) (front, frontpt);

fun bfs_csr_round gi (fronti, (frontp, buffer_fronti)) imp_vis pari =
  (fn () =>
    let
      val a =
        bfs_csr_outer_loop gi imp_vis pari (fronti, frontp)
          (buffer_fronti, (0 : Int.int)) ();
    in
      let
        val (front, frontpt) = a;
      in
        (fn () => ((front, (frontpt, fronti)), (imp_vis, pari)))
      end
        ()
    end);

fun bfs_csr_loop gi state =
  (fn () =>
    let
      val b = bfs_cf_is_empty (zero_nat, equal_nat) (current state) ();
    in
      (if b then (fn () => state)
        else (fn f_ => fn () => f_
               ((bfs_csr_round gi (current state) (visited state)
                  (parent state))
               ()) ())
               (fn (currenta, (visiteda, parenta)) =>
                 let
                   val d = current_dist state;
                 in
                   (fn f_ => fn () => f_
                     ((bfs_set_dists heap_nat (dists state) currenta
                        (Int.+ (d, (1 : Int.int))))
                     ()) ())
                     (fn dist =>
                       bfs_csr_loop gi
                         (parent_update (fn _ => parenta)
                           (current_dist_update
                             (fn _ => Int.+ (d, (1 : Int.int)))
                             (current_update (fn _ => currenta)
                               (visited_update (fn _ => visiteda)
                                 (dists_update (fn _ => dist) state))))))
                 end))
        ()
    end);

fun bfs_csr_visited_dists_parents gi empty_vis src_imp imp_some_dist
  imp_some_par =
  (fn () =>
    let
      val init = bfs_init empty_vis src_imp imp_some_dist imp_some_par ();
      val final = bfs_csr_loop gi init ();
    in
      (visited final, (dists final, parent final))
    end);

fun copy_prefix_imp A_ k sa da i =
  (if Int.< (i, k)
    then (fn () => let
                     val x = (fn () => Array.sub (sa, i)) ();
                     val _ = (fn () => Machine.upd (i, x, da)) ();
                   in
                     copy_prefix_imp A_ k sa da (Int.+ (i, (1 : Int.int))) ()
                   end)
    else (fn () => ()));

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

fun bfs_csr_run n fa ta sa =
  (fn () =>
    let
      val gi = csr_build_heads n (fa, ta) (0 : Int.int) ();
      val k = (fn () => Array.length sa) ();
      val fr =
        (fn () => Array.array (Int.+ (n, (1 : Int.int)), (0 : Int.int))) ();
      val _ = copy_prefix_imp heap_nat k sa fr (0 : Int.int) ();
      val bf =
        (fn () => Array.array (Int.+ (n, (1 : Int.int)), (0 : Int.int))) ();
      val vi = (fn () => Array.array (n, false)) ();
      val da = (fn () => Array.tabulate (n, id)) ();
      val x = (fn () => Array.tabulate (n, id)) ();
    in
      bfs_csr_visited_dists_parents gi vi (fr, (k, bf)) da x ()
    end);

end; (*struct BFS_CSR*)
