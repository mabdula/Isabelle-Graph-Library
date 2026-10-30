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
  val bfs_path :
    Int.int array ->
      Int.int array -> Int.int array -> Int.int -> (unit -> Int.int)
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

fun pos_adv x = (fn _ => fn i => (fn () => (Int.+ (i, (1 : Int.int))))) x;

fun pos_cur x = (fn _ => (fn a => (fn () => a))) x;

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

fun bset_memb v a = (fn () => Array.sub (a, v));

fun bset_ins v a = (fn () => Machine.upd (v, true, a));

fun bfs_set_srcs_visited imp_vis (fronti, (frontp, buffer_fronti)) =
  iterate_range_strict heap_nat fronti (0 : Int.int) frontp
    (fn v => fn vis => fn () =>
      let
        val b = bset_memb v vis ();
      in
        (if not b then bset_ins v vis else (fn () => vis)) ()
      end)
    imp_vis;

fun bfs_src_to_cf x = (fn () => x);

fun bfs_set_dists A_ di (fronti, (frontp, buffer_fronti)) n =
  iterate_range_strict heap_nat fronti (0 : Int.int) frontp
    (fn v => (fn a => (fn () => Machine.upd (v, n, a)))) di;

fun bfs_init empty_vis src_imp imp_some_dist imp_some_par =
  (fn () =>
    let
      val v = bfs_set_srcs_visited empty_vis src_imp ();
      val cf = bfs_src_to_cf src_imp ();
      val dists = bfs_set_dists heap_nat imp_some_dist cf (0 : Int.int) ();
    in
      BFS_state_imp_ext (dists, cf, v, (0 : Int.int), imp_some_par, ())
    end);

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

fun visited
  (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) =
  visited;

fun current
  (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) =
  current;

fun parent
  (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) =
  parent;

fun dists
  (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) =
  dists;

fun bfs_cf_is_empty (B1_, B2_) (fronti, (frontp, buffer_fronti)) =
  (fn () => (eq B2_ frontp (zero B1_)));

fun bfs_csr_nbs A_ gi v fi acci =
  let
    val (ba, ea) = gi;
  in
    (fn () =>
      let
        val l = (fn () => Array.length ba) ();
      in
        (if Int.< (Int.+ (v, (1 : Int.int)), l)
          then (fn f_ => fn () => f_ (((fn () => Array.sub (ba, v))) ()) ())
                 (fn i =>
                   (fn f_ => fn () => f_
                     (((fn () => Array.sub (ba, Int.+ (v, (1 : Int.int))))) ())
                     ())
                     (fn j => iterate_range_strict A_ ea i j (fi v) acci))
          else (fn () => acci))
          ()
      end)
  end;

fun bfs_inner_loop gi pari u (front, (frontpt, vis)) =
  bfs_csr_nbs heap_nat gi u
    (fn ua => fn v => fn (fronta, (frontpta, visa)) => fn () =>
      let
        val b = bset_memb v visa ();
      in
        (if not b
          then (fn f_ => fn () => f_
                 (((fn () => Machine.upd (frontpta, v, fronta))) ()) ())
                 (fn frontb =>
                   (fn f_ => fn () => f_ ((bset_ins v visa) ()) ())
                     (fn visb =>
                       (fn f_ => fn () => f_
                         (((fn () => Machine.upd (v, ua, pari))) ()) ())
                         (fn _ =>
                           (fn () =>
                             (frontb,
                               (Int.+ (frontpta, (1 : Int.int)), visb))))))
          else (fn () => (fronta, (frontpta, visa))))
          ()
      end)
    (front, (frontpt, vis));

fun bfs_outer_loop gi pari (old_front, old_frontp) (front, (frontpt, vis)) =
  iterate_range_strict heap_nat old_front (0 : Int.int) old_frontp
    (bfs_inner_loop gi pari) (front, (frontpt, vis));

fun bfs_round gi (fronti, (frontp, buffer_fronti)) imp_vis pari =
  (fn () =>
    let
      val a =
        bfs_outer_loop gi pari (fronti, frontp)
          (buffer_fronti, ((0 : Int.int), imp_vis)) ();
    in
      let
        val (front, (frontpt, vis)) = a;
      in
        (fn () => ((front, (frontpt, fronti)), (vis, pari)))
      end
        ()
    end);

fun bfs_loop gi state =
  (fn () =>
    let
      val b = bfs_cf_is_empty (zero_nat, equal_nat) (current state) ();
    in
      (if b then (fn () => state)
        else (fn f_ => fn () => f_
               ((bfs_round gi (current state) (visited state) (parent state))
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
                       bfs_loop gi
                         (parent_update (fn _ => parenta)
                           (current_dist_update
                             (fn _ => Int.+ (d, (1 : Int.int)))
                             (current_update (fn _ => currenta)
                               (visited_update (fn _ => visiteda)
                                 (dists_update (fn _ => dist) state))))))
                 end))
        ()
    end);

fun bfs_path_rev di pari ra v k =
  (fn () =>
    let
      val _ = (fn () => Machine.upd (k, v, ra)) ();
      val dv = (fn () => Array.sub (di, v)) ();
    in
      (if ((dv : Int.int) = (0 : Int.int))
        then (fn () => (Int.+ (k, (1 : Int.int))))
        else (fn f_ => fn () => f_ (((fn () => Array.sub (pari, v))) ()) ())
               (fn u => bfs_path_rev di pari ra u (Int.+ (k, (1 : Int.int)))))
        ()
    end);

fun bfs_path di pari ra v = bfs_path_rev di pari ra v (0 : Int.int);

fun pos_head x = (fn (_, a) => (fn b => (fn () => Array.sub (a, b)))) x;

fun pos_tail x = (fn (fa, _) => (fn a => (fn () => Array.sub (fa, a)))) x;

fun bset_empty n = (fn () => Array.array (n, false));

fun bfs_visited_dists_parents gi empty_vis src_imp imp_some_dist imp_some_par =
  (fn () =>
    let
      val init = bfs_init empty_vis src_imp imp_some_dist imp_some_par ();
      val final = bfs_loop gi init ();
    in
      (visited final, (dists final, parent final))
    end);

fun copy_prefix_imp A_ sa fa k i =
  (if Int.< (i, k)
    then (fn () => let
                     val x = (fn () => Array.sub (sa, i)) ();
                     val _ = (fn () => Machine.upd (i, x, fa)) ();
                   in
                     copy_prefix_imp A_ sa fa k (Int.+ (i, (1 : Int.int))) ()
                   end)
    else (fn () => ()));

fun bfs_csr_prefix n b j acc =
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
                 (fn _ => bfs_csr_prefix n b (Int.+ (j, (1 : Int.int))) acca)
             end
               ()
           end)
    else (fn () => ()));

fun pos_has_next x =
  (fn (fa, _) => fn i => fn () => let
                                    val l = (fn () => Array.length fa) ();
                                  in
                                    Int.< (i, l)
                                  end)
    x;

fun bfs_csr_count n c b m si =
  (fn () =>
    let
      val ba = pos_has_next c si ();
    in
      (if ba
        then (fn f_ => fn () => f_ ((pos_cur c si) ()) ())
               (fn e =>
                 (fn f_ => fn () => f_ ((pos_tail c e) ()) ())
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
                         (fn f_ => fn () => f_ ((pos_adv c si) ()) ())
                           (bfs_csr_count n c b (Int.+ (m, (1 : Int.int)))))))
        else (fn () => m))
        ()
    end);

fun bfs_csr_init c si m =
  (fn () =>
    let
      val b = pos_has_next c si ();
    in
      (if b then (fn f_ => fn () => f_ ((pos_cur c si) ()) ())
                   (fn e =>
                     (fn f_ => fn () => f_ ((pos_head c e) ()) ())
                       (fn a => (fn () => Array.array (m, a))))
        else (fn () => Array.fromList []))
        ()
    end);

fun bfs_csr_fill c b e si =
  (fn () =>
    let
      val ba = pos_has_next c si ();
    in
      (if ba
        then (fn f_ => fn () => f_ ((pos_cur c si) ()) ())
               (fn ea =>
                 (fn f_ => fn () => f_ ((pos_tail c ea) ()) ())
                   (fn k =>
                     (fn f_ => fn () => f_ ((pos_head c ea) ()) ())
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
                                     (fn f_ => fn () => f_ ((pos_adv c si) ())
                                       ())
                                       (bfs_csr_fill c b e)))))))
        else (fn () => ()))
        ()
    end);

fun bfs_csr_build n c si =
  (fn () =>
    let
      val b =
        (fn () => Array.array (Int.+ (n, (1 : Int.int)), (0 : Int.int))) ();
      val m = bfs_csr_count n c b (0 : Int.int) si ();
      val _ = bfs_csr_prefix n b (1 : Int.int) (0 : Int.int) ();
      val e = bfs_csr_init c si m ();
      val _ = bfs_csr_fill c b e si ();
    in
      (b, e)
    end);

fun bfs_csr_run n fa ta sa =
  (fn () =>
    let
      val gi = bfs_csr_build n (fa, ta) (0 : Int.int) ();
      val k = (fn () => Array.length sa) ();
      val fr =
        (fn () => Array.array (Int.+ (n, (1 : Int.int)), (0 : Int.int))) ();
      val _ = copy_prefix_imp heap_nat sa fr k (0 : Int.int) ();
      val bf =
        (fn () => Array.array (Int.+ (n, (1 : Int.int)), (0 : Int.int))) ();
      val vi = bset_empty n ();
      val da = (fn () => Array.tabulate (n, id)) ();
      val x = (fn () => Array.tabulate (n, id)) ();
    in
      bfs_visited_dists_parents gi vi (fr, (k, bf)) da x ()
    end);

end; (*struct BFS_CSR*)
