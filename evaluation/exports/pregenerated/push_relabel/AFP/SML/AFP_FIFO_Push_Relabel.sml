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


structure AFP_FIFO_Push_Relabel : sig
  val compute_flow_val_impl :
    Int.int ->
      Int.int -> (Int.int list) array -> Int.int array -> (unit -> Int.int)
  val fifo_push_relabel_init_impl :
    (Int.int * Int.int -> Int.int) -> Int.int -> (unit -> (Int.int array))
  val fifo_push_relabel_run_impl :
    Int.int ->
      Int.int ->
        Int.int ->
          (Int.int list) array -> Int.int array -> (unit -> (Int.int array))
  val fifo_push_relabel_impl :
    (Int.int * Int.int -> Int.int) ->
      Int.int ->
        Int.int -> Int.int -> (Int.int list) array -> (unit -> (Int.int array))
end = struct

datatype typerepa = Typerep of string * typerepa list;

datatype 'a itself = Type;

fun typerep_inta t = Typerep ("Int.int", []);

type 'a typerep = {typerep : 'a itself -> typerepa};
val typerep = #typerep : 'a typerep -> 'a itself -> typerepa;

type 'a countable = {};

type 'a heap = {countable_heap : 'a countable, typerep_heap : 'a typerep};
val countable_heap = #countable_heap : 'a heap -> 'a countable;
val typerep_heap = #typerep_heap : 'a heap -> 'a typerep;

val countable_int = {} : Int.int countable;

val typerep_int = {typerep = typerep_inta} : Int.int typerep;

val heap_int = {countable_heap = countable_int, typerep_heap = typerep_int} :
  Int.int heap;

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_int = {plus = (fn a => fn b => Int.+ (a, b))} : Int.int plus;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_int = {zero = (0 : Int.int)} : Int.int zero;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

val ord_int =
  {less_eq = (fn a => fn b => Int.<= (a, b)),
    less = (fn a => fn b => Int.< (a, b))}
  : Int.int ord;

fun typerep_nata t = Typerep ("Nat.nat", []);

val countable_nat = {} : Int.int countable;

val typerep_nat = {typerep = typerep_nata} : Int.int typerep;

val heap_nat = {countable_heap = countable_nat, typerep_heap = typerep_nat} :
  Int.int heap;

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_nat = {one = (1 : Int.int)} : Int.int one;

val plus_nat = {plus = (fn a => fn b => Int.+ (a, b))} : Int.int plus;

val zero_nat = {zero = (0 : Int.int)} : Int.int zero;

type 'a minus = {minus : 'a -> 'a -> 'a};
val minus = #minus : 'a minus -> 'a -> 'a -> 'a;

val minus_nat = {minus = (fn a => fn b => Machine.sub_nat (a, b))} :
  Int.int minus;

val ord_nat =
  {less_eq = (fn a => fn b => Int.<= (a, b)),
    less = (fn a => fn b => Int.< (a, b))}
  : Int.int ord;

fun typerep_lista A_ t = Typerep ("List.list", [typerep A_ Type]);

fun countable_list A_ = {} : ('a list) countable;

fun typerep_list A_ = {typerep = typerep_lista A_} : ('a list) typerep;

fun heap_list A_ =
  {countable_heap = countable_list (countable_heap A_),
    typerep_heap = typerep_list (typerep_heap A_)}
  : ('a list) heap;

datatype num = One | Bit0 of num | Bit1 of num;

fun fold f [] s = s
  | fold f (x :: xs) s = fold f xs (f x s);

fun rev xs = fold (fn a => fn b => a :: b) xs [];

fun the (SOME x2) = x2;

fun fst (x1, x2) = x1;

fun snd (x1, x2) = x2;

fun min A_ a b = (if less_eq A_ a b then a else b);

fun imp_for i u f s =
  (if Int.<= (u, i) then (fn () => s)
    else (fn () => let
                     val x = f i s ();
                   in
                     imp_for (Int.+ (i, (1 : Int.int))) u f x ()
                   end));

fun mtx_get A_ m mtx e =
  (fn () => Array.sub (mtx, Int.+ (Int.* (fst e, m), snd e)));

fun cf_get_impl n = mtx_get heap_int n;

fun mtx_set A_ m mtx e v =
  (fn () => Machine.upd (Int.+ (Int.* (fst e, m), snd e), v, mtx));

fun cf_set_impl n = mtx_set heap_int n;

fun mtx_tabulate (A1_, A2_, A3_) (B1_, B2_) n m c =
  (fn () =>
    let
      val ma = (fn () => Array.array (Int.* (n, m), zero B1_)) ();
      val a =
        imp_for (0 : Int.int) (Int.* (n, m))
          (fn k => fn (i, (j, maa)) =>
            (fn f_ => fn () => f_ (((fn () => Machine.upd (k, c (i, j), maa)))
              ()) ())
              (fn _ =>
                let
                  val ja = Int.+ (j, (1 : Int.int));
                in
                  (if Int.< (ja, m) then (fn () => (i, (ja, maa)))
                    else (fn () =>
                           (plus A2_ i (one A1_), ((0 : Int.int), maa))))
                end))
          (zero A3_, ((0 : Int.int), ma)) ();
    in
      let
        val (_, (_, aa)) = a;
      in
        (fn () => aa)
      end
        ()
    end);

fun cf_init_impl c n =
  mtx_tabulate (one_nat, plus_nat, zero_nat) (zero_int, heap_int) n n c;

fun clc_get_rlx_impl x = (fn ai => fn bi => let
      val (_, a2) = ai;
    in
      (fn () => Array.sub (a2, bi))
    end)
                           x;

fun cnt_incr_impl (A1_, A2_, A3_) a k =
  (fn () =>
    let
      val freq = (fn () => Array.sub (a, k)) ();
      val x = (fn () => Machine.upd (k, plus A2_ freq (one A1_), a)) ();
    in
      x
    end);

fun cnt_decr_impl (A1_, A2_, A3_) a k =
  (fn () =>
    let
      val freq = (fn () => Array.sub (a, k)) ();
      val x = (fn () => Machine.upd (k, minus A1_ freq (one A2_), a)) ();
    in
      x
    end);

fun clc_set_impl x =
  (fn ai => fn bia => fn bi =>
    let
      val (a1, a2) = ai;
    in
      (fn () =>
        let
          val xa = (fn () => Array.sub (a2, bia)) ();
          val x_a = cnt_decr_impl (minus_nat, one_nat, heap_nat) a1 xa ();
          val x_b = (fn () => Machine.upd (bia, bi, a2)) ();
          val x_c = (fn () => Array.sub (x_b, bia)) ();
          val x_d = cnt_incr_impl (one_nat, plus_nat, heap_nat) x_a x_c ();
        in
          (x_d, x_b)
        end)
    end)
    x;

fun gap_impl n =
  (fn ai => fn bia => fn bi =>
    imp_for (0 : Int.int) n
      (fn xa => fn sigma => fn () =>
        let
          val x_b = clc_get_rlx_impl sigma xa ();
        in
          (if Int.< (bi, x_b) andalso Int.< (x_b, ai)
            then clc_set_impl sigma xa (Int.+ (ai, (1 : Int.int)))
            else (fn () => sigma))
            ()
        end)
      bia);

fun imp_nfoldli [] c f s = (fn () => s)
  | imp_nfoldli (x :: ls) c f s =
    (fn () =>
      let
        val b = c s ();
      in
        (if b then (fn f_ => fn () => f_ ((f x s) ()) ()) (imp_nfoldli ls c f)
          else (fn () => s))
          ()
      end);

fun is_Nil a = (case a of [] => true | _ :: _ => false);

fun x_add_impl (A1_, A2_) x u delta =
  (fn () => let
              val xu = (fn () => Array.sub (x, u)) ();
              val xa = (fn () => Machine.upd (u, plus A1_ xu delta, x)) ();
            in
              xa
            end);

fun am_is_in_V_impl A_ am u =
  (fn () => let
              val amu = (fn () => Array.sub (am, u)) ();
            in
              not (is_Nil amu)
            end);

fun l_init_impl n s cardV =
  (fn () => let
              val l = (fn () => Array.array (n, (0 : Int.int))) ();
              val x = (fn () => Machine.upd (s, cardV, l)) ();
            in
              x
            end);

fun heap_WHILET b f s =
  (fn () =>
    let
      val bv = b s ();
    in
      (if bv then (fn f_ => fn () => f_ ((f s) ()) ()) (heap_WHILET b f)
        else (fn () => s))
        ()
    end);

fun clc_get_impl x = (fn ai => fn bi => let
  val (_, a2) = ai;
in
  (fn () => Array.sub (a2, bi))
end)
                       x;

fun cnt_init_impl n c =
  (fn () =>
    let
      val a =
        (fn () => Array.array (Int.* ((2 : Int.int), n), (0 : Int.int))) ();
      val aa =
        (fn () => Machine.upd ((0 : Int.int),
          Machine.sub_nat (c, (1 : Int.int)), a))
          ();
      val x = (fn () => Machine.upd (c, (1 : Int.int), aa)) ();
    in
      x
    end);

fun clc_init_impl s n = (fn xi => fn () => let
     val x = l_init_impl n s xi ();
     val x_a = cnt_init_impl n xi ();
   in
     (x_a, x)
   end);

fun clc_has_gap_impl x =
  (fn ai => fn bi => let
                       val (a1, _) = ai;
                     in
                       (fn () => let
                                   val xa = (fn () => Array.sub (a1, bi)) ();
                                 in
                                   ((xa : Int.int) = (0 : Int.int))
                                 end)
                     end)
    x;

fun min_adj_label_impl n =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val x = (fn () => Array.sub (ai, bi)) ();
      val x_a =
        imp_nfoldli x (fn _ => (fn () => true))
          (fn xb => fn sigma =>
            (fn f_ => fn () => f_ ((cf_get_impl n bib (bi, xb)) ()) ())
              (fn x_c =>
                (if not ((x_c : Int.int) = (0 : Int.int))
                  then (fn f_ => fn () => f_ (((fn () => Array.sub (bia, xb)))
                         ()) ())
                         (fn x_e =>
                           (fn () =>
                             (case sigma of NONE => SOME x_e
                               | SOME x_f => SOME (min ord_nat x_e x_f))))
                  else (fn () => sigma))))
          NONE ();
    in
      the x_a
    end);

fun min_adj_label_clc_impl n =
  (fn ai => fn bib => fn bia => fn bi => let
   val (_, a2) = bia;
 in
   min_adj_label_impl n ai bib a2 bi
 end);

fun clc_relabel_impl n =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val x = min_adj_label_clc_impl n ai bib bia bi ();
    in
      clc_set_impl bia bi (Int.+ (x, (1 : Int.int))) ()
    end);

fun compute_flow_val_impl s n =
  (fn ai => fn bi => fn () =>
    let
      val x = (fn () => Array.sub (ai, s)) ();
    in
      imp_nfoldli x (fn _ => (fn () => true))
        (fn xb => fn sigma =>
          (fn f_ => fn () => f_ ((cf_get_impl n bi (xb, s)) ()) ())
            (fn x_c => (fn () => (Int.+ (sigma, x_c)))))
        (0 : Int.int) ()
    end);

val q_empty_impl : 'a list * 'b list = ([], []);

fun q_enqueue_impl x = (fn xa => fn (l, r) => (l, xa :: r)) x;

fun fifo_push_impl s t n =
  (fn ai => fn bib => fn bia => fn (a1, a2) => fn () =>
    let
      val x = (fn () => Array.sub (ai, a1)) ();
      val x_a = (fn () => Array.sub (ai, a2)) ();
      val x_b = cf_get_impl n bib (a1, a2) ();
      val x_c = cf_get_impl n bib (a2, a1) ();
    in
      let
        val x_d = min ord_int x x_b;
      in
        (fn f_ => fn () => f_
          ((x_add_impl (plus_int, heap_int) ai a1 (Int.~ x_d)) ()) ())
          (fn x_f =>
            (fn f_ => fn () => f_ ((x_add_impl (plus_int, heap_int) x_f a2 x_d)
              ()) ())
              (fn x_g =>
                (fn f_ => fn () => f_
                  ((cf_set_impl n bib (a1, a2) (Int.- (x_b, x_d))) ()) ())
                  (fn x_h =>
                    (fn f_ => fn () => f_
                      ((cf_set_impl n x_h (a2, a1) (Int.+ (x_c, x_d))) ()) ())
                      (fn x_i =>
                        (fn () =>
                          (if not ((a2 : Int.int) = s) andalso
                                (not ((a2 : Int.int) = t) andalso
                                  ((x_a : Int.int) = (0 : Int.int)))
                            then ((x_g, x_i), q_enqueue_impl a2 bia)
                            else ((x_g, x_i), bia)))))))
      end
        ()
    end);

fun q_dequeue_impl x =
  (fn a =>
    (case a of ([], r) => let
                            val xa :: l = rev r;
                          in
                            (xa, (l, []))
                          end
      | (xa :: l, r) => (xa, (l, r))))
    x;

fun q_is_empty_impl x = (fn (l, r) => is_Nil l andalso is_Nil r) x;

fun fifo_init_C_impl n =
  (fn xi =>
    imp_for (0 : Int.int) n
      (fn xd => fn sigma => fn () =>
        let
          val x_d = am_is_in_V_impl heap_nat xi xd ();
        in
          (if x_d then Int.+ (sigma, (1 : Int.int)) else sigma)
        end)
      (0 : Int.int));

fun fifo_q_init_impl s t =
  (fn xi => fn () =>
    let
      val x_a = (fn () => Array.sub (xi, s)) ();
    in
      imp_nfoldli x_a (fn _ => (fn () => true))
        (fn xc => fn sigma =>
          (fn () =>
            (if not ((xc : Int.int) = t) then q_enqueue_impl xc sigma
              else sigma)))
        q_empty_impl ()
    end);

fun fifo_dis_loop_impl s t n =
  (fn ai => fn bid => fn bic => fn bib => fn bia => fn bi => fn () =>
    let
      val x = (fn () => Array.sub (ai, bi)) ();
    in
      imp_nfoldli x
        (fn ((a1a, _), (_, _)) =>
          (fn f_ => fn () => f_ (((fn () => Array.sub (a1a, bi))) ()) ())
            (fn x_b => (fn () => (not ((x_b : Int.int) = (0 : Int.int))))))
        (fn xb => fn ((a1a, a2a), (a1b, a2b)) =>
          (fn f_ => fn () => f_ ((cf_get_impl n a2a (bi, xb)) ()) ())
            (fn x_c =>
              (if not ((x_c : Int.int) = (0 : Int.int))
                then (fn f_ => fn () => f_ ((clc_get_impl a1b bi) ()) ())
                       (fn x_e =>
                         (fn f_ => fn () => f_ ((clc_get_impl a1b xb) ()) ())
                           (fn x_f =>
                             (if ((x_e : Int.int) = (Int.+ (x_f,
              (1 : Int.int))))
                               then (fn f_ => fn () => f_
                                      ((fifo_push_impl s t n a1a a2a a2b
 (bi, xb))
                                      ()) ())
                                      (fn (a1c, a2c) =>
(fn () => let
            val (a1d, a2d) = a1c;
          in
            ((a1d, a2d), (a1b, a2c))
          end))
                               else (fn () => ((a1a, a2a), (a1b, a2b))))))
                else (fn () => ((a1a, a2a), (a1b, a2b))))))
        ((bid, bic), (bib, bia)) ()
    end);

fun pp_init_xcf2_impl s n =
  (fn ai => fn bi => fn () =>
    let
      val x = (fn () => Array.array (n, (0 : Int.int))) ();
      val x_a = (fn () => Array.sub (ai, s)) ();
    in
      imp_nfoldli x_a (fn _ => (fn () => true))
        (fn xc => fn (a1, a2) =>
          (fn f_ => fn () => f_ ((cf_get_impl n a2 (s, xc)) ()) ())
            (fn x_d =>
              (fn f_ => fn () => f_
                ((x_add_impl (plus_int, heap_int) a1 s (Int.~ x_d)) ()) ())
                (fn x_e =>
                  (fn f_ => fn () => f_
                    ((x_add_impl (plus_int, heap_int) x_e xc x_d) ()) ())
                    (fn x_f =>
                      (fn f_ => fn () => f_
                        ((cf_set_impl n a2 (s, xc) (0 : Int.int)) ()) ())
                        (fn x_g =>
                          (fn f_ => fn () => f_ ((cf_set_impl n x_g (xc, s) x_d)
                            ()) ())
                            (fn x_h => (fn () => (x_f, x_h))))))))
        (x, bi) ()
    end);

fun fifo_gap_relabel_impl n =
  (fn ai => fn bid => fn bic => fn bib => fn bia => fn bi =>
    let
      val x = q_enqueue_impl bi bia;
    in
      (fn () =>
        let
          val x_a = clc_get_impl bib bi ();
          val x_b = clc_relabel_impl n bid bic bib bi ();
          val x_c = clc_has_gap_impl x_b x_a ();
        in
          (if x_c
            then (fn f_ => fn () => f_ ((gap_impl n ai x_b x_a) ()) ())
                   (fn x_d => (fn () => (x_d, x)))
            else (fn () => (x_b, x)))
            ()
        end)
    end);

fun fifo_push_relabel_init_impl c n = cf_init_impl c n;

fun fifo_fifo_discharge_impl s t n =
  (fn ai => fn bid => fn bic => fn bib => fn bia => fn bi =>
    let
      val (a1, a2) = q_dequeue_impl bi;
    in
      (fn () =>
        let
          val a = fifo_dis_loop_impl s t n bid bic bib bia a2 a1 ();
        in
          let
            val ((a1b, a2b), (a1c, a2c)) = a;
          in
            (fn f_ => fn () => f_ (((fn () => Array.sub (a1b, a1))) ()) ())
              (fn x_b =>
                (if not ((x_b : Int.int) = (0 : Int.int))
                  then (fn f_ => fn () => f_
                         ((fifo_gap_relabel_impl n ai bid a2b a1c a2c a1) ())
                         ())
                         (fn (a1d, a2d) => (fn () => ((a1b, a2b), (a1d, a2d))))
                  else (fn () => ((a1b, a2b), (a1c, a2c)))))
          end
            ()
        end)
    end);

fun fifo_push_relabel_run_impl s t n =
  (fn ai => fn bi => fn () =>
    let
      val x = fifo_init_C_impl n ai ();
      val a = pp_init_xcf2_impl s n ai bi ();
    in
      let
        val (a1, a2) = a;
      in
        (fn f_ => fn () => f_ ((clc_init_impl s n x) ()) ())
          (fn x_b =>
            (fn f_ => fn () => f_ ((fifo_q_init_impl s t ai) ()) ())
              (fn x_c =>
                (fn f_ => fn () => f_
                  ((heap_WHILET
                     (fn (a1a, a2a) => (fn () => let
           val (_, _) = a1a;
           val (_, a2c) = a2a;
         in
           not (q_is_empty_impl a2c)
         end))
                     (fn ((a1b, a2b), (aa, b)) =>
                       fifo_fifo_discharge_impl s t n x ai a1b a2b aa b)
                     ((a1, a2), (x_b, x_c)))
                  ()) ())
                  (fn (a1a, a2a) => (fn () => let
        val (_, a2b) = a1a;
        val (_, _) = a2a;
      in
        a2b
      end))))
      end
        ()
    end);

fun fifo_push_relabel_impl c s t n =
  (fn xi => fn () => let
                       val x = fifo_push_relabel_init_impl c n ();
                     in
                       fifo_push_relabel_run_impl s t n xi x ()
                     end);

end; (*struct AFP_FIFO_Push_Relabel*)
