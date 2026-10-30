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


structure DFS_RBT : sig
  type color
  type 'a tree
  type ('a, 'b, 'c) dFS_state_ext
  val rbt_dfs_impl :
    ((Int.int * (Int.int * color) tree) * color) tree ->
      Int.int ->
        (Int.int, (Int.int * color) tree, unit) dFS_state_ext ->
          (Int.int, (Int.int * color) tree, unit) dFS_state_ext
  val rbt_from_list :
    (Int.int * Int.int) list ->
      ((Int.int * (Int.int * color) tree) * color) tree
  val rbt_dfs_initial_state :
    Int.int -> (Int.int, (Int.int * color) tree, unit) dFS_state_ext
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_nat = {equal = (fn a => fn b => ((a : Int.int) = b))} : Int.int equal;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

val ord_nat =
  {less_eq = (fn a => fn b => Int.<= (a, b)),
    less = (fn a => fn b => Int.< (a, b))}
  : Int.int ord;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_nat = {ord_preorder = ord_nat} : Int.int preorder;

val order_nat = {preorder_order = preorder_nat} : Int.int order;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_nat = {order_linorder = order_nat} : Int.int linorder;

datatype color = Red | Black;

fun equal_colora Red Black = false
  | equal_colora Black Red = false
  | equal_colora Black Black = true
  | equal_colora Red Red = true;

val equal_color = {equal = equal_colora} : color equal;

fun eq A_ a b = equal A_ a b;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

datatype 'a tree = Leaf | Node of 'a tree * 'a * 'a tree;

datatype return = Reachable | NotReachable;

datatype cmp_val = LT | EQ | GT;

datatype ('a, 'b, 'c) dFS_state_ext =
  DFS_state_ext of 'a list * 'b * return * 'c;

fun cmp (A1_, A2_) x y =
  (if less ((ord_preorder o preorder_order o order_linorder) A2_) x y then LT
    else (if eq A1_ x y then EQ else GT));

fun baliL (Node (Node (t1, (a, Red), t2), (b, Red), t3)) c t4 =
  Node (Node (t1, (a, Black), t2), (b, Red), Node (t3, (c, Black), t4))
  | baliL (Node (Leaf, (a, Red), Node (t2, (b, Red), t3))) c t4 =
    Node (Node (Leaf, (a, Black), t2), (b, Red), Node (t3, (c, Black), t4))
  | baliL (Node (Node (v, (vc, Black), vb), (a, Red), Node (t2, (b, Red), t3)))
    c t4 =
    Node (Node (Node (v, (vc, Black), vb), (a, Black), t2), (b, Red),
           Node (t3, (c, Black), t4))
  | baliL Leaf a t2 = Node (Leaf, (a, Black), t2)
  | baliL (Node (Leaf, (v, Black), vb)) a t2 =
    Node (Node (Leaf, (v, Black), vb), (a, Black), t2)
  | baliL (Node (Leaf, va, Leaf)) a t2 =
    Node (Node (Leaf, va, Leaf), (a, Black), t2)
  | baliL (Node (Leaf, va, Node (v, (ve, Black), vd))) a t2 =
    Node (Node (Leaf, va, Node (v, (ve, Black), vd)), (a, Black), t2)
  | baliL (Node (Node (vc, (vf, Black), ve), (v, Black), vb)) a t2 =
    Node (Node (Node (vc, (vf, Black), ve), (v, Black), vb), (a, Black), t2)
  | baliL (Node (Node (vc, (vf, Black), ve), va, Leaf)) a t2 =
    Node (Node (Node (vc, (vf, Black), ve), va, Leaf), (a, Black), t2)
  | baliL (Node (Node (vc, (vf, Black), ve), va, Node (v, (vh, Black), vg))) a
    t2 =
    Node (Node (Node (vc, (vf, Black), ve), va, Node (v, (vh, Black), vg)),
           (a, Black), t2)
  | baliL (Node (v, (vc, Black), vb)) a t2 =
    Node (Node (v, (vc, Black), vb), (a, Black), t2);

fun baliR t1 a (Node (t2, (b, Red), Node (t3, (c, Red), t4))) =
  Node (Node (t1, (a, Black), t2), (b, Red), Node (t3, (c, Black), t4))
  | baliR t1 a (Node (Node (t2, (b, Red), t3), (c, Red), Leaf)) =
    Node (Node (t1, (a, Black), t2), (b, Red), Node (t3, (c, Black), Leaf))
  | baliR t1 a
    (Node (Node (t2, (b, Red), t3), (c, Red), Node (v, (vc, Black), vb))) =
    Node (Node (t1, (a, Black), t2), (b, Red),
           Node (t3, (c, Black), Node (v, (vc, Black), vb)))
  | baliR t1 a Leaf = Node (t1, (a, Black), Leaf)
  | baliR t1 a (Node (v, (vc, Black), vb)) =
    Node (t1, (a, Black), Node (v, (vc, Black), vb))
  | baliR t1 a (Node (Leaf, va, Leaf)) =
    Node (t1, (a, Black), Node (Leaf, va, Leaf))
  | baliR t1 a (Node (Node (vb, (ve, Black), vd), va, Leaf)) =
    Node (t1, (a, Black), Node (Node (vb, (ve, Black), vd), va, Leaf))
  | baliR t1 a (Node (Leaf, va, Node (vc, (vf, Black), ve))) =
    Node (t1, (a, Black), Node (Leaf, va, Node (vc, (vf, Black), ve)))
  | baliR t1 a
    (Node (Node (vb, (vh, Black), vg), va, Node (vc, (vf, Black), ve))) =
    Node (t1, (a, Black),
           Node (Node (vb, (vh, Black), vg), va, Node (vc, (vf, Black), ve)));

fun paint c Leaf = Leaf
  | paint c (Node (l, (a, uu), r)) = Node (l, (a, c), r);

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun upd (A1_, A2_) x y Leaf = Node (Leaf, ((x, y), Red), Leaf)
  | upd (A1_, A2_) x y (Node (l, ((a, b), Black), r)) =
    (case cmp (A1_, A2_) x a of LT => baliL (upd (A1_, A2_) x y l) (a, b) r
      | EQ => Node (l, ((x, y), Black), r)
      | GT => baliR l (a, b) (upd (A1_, A2_) x y r))
  | upd (A1_, A2_) x y (Node (l, ((a, b), Red), r)) =
    (case cmp (A1_, A2_) x a
      of LT => Node (upd (A1_, A2_) x y l, ((a, b), Red), r)
      | EQ => Node (l, ((x, y), Red), r)
      | GT => Node (l, ((a, b), Red), upd (A1_, A2_) x y r));

val empty : ('a * color) tree = Leaf;

fun lookup (A1_, A2_) Leaf x = NONE
  | lookup (A1_, A2_) (Node (l, ((a, b), uu), r)) x =
    (case cmp (A1_, A2_) x a of LT => lookup (A1_, A2_) l x | EQ => SOME b
      | GT => lookup (A1_, A2_) r x);

fun update (A1_, A2_) x y t = paint Black (upd (A1_, A2_) x y t);

fun bheight Leaf = (0 : Int.int)
  | bheight (Node (l, (x, c), r)) =
    (if equal_colora c Black then Int.+ (bheight l, (1 : Int.int))
      else bheight l);

fun the (SOME x2) = x2;

fun seen (DFS_state_ext (stack, seen, return, more)) = seen;

fun sel Leaf = (raise Fail "undefined")
  | sel (Node (l, (a, Black), r)) = a
  | sel (Node (l, (a, Red), r)) = a;

fun joinR l x r =
  (if Int.<= (bheight l, bheight r) then Node (l, (x, Red), r)
    else (case l
           of Node (la, (xa, Red), ra) => Node (la, (xa, Red), joinR ra x r)
           | Node (la, (xa, Black), ra) => baliR la xa (joinR ra x r)));

fun joinL l x r =
  (if Int.<= (bheight r, bheight l) then Node (l, (x, Red), r)
    else (case r
           of Node (la, (xa, Red), ra) => Node (joinL l x la, (xa, Red), ra)
           | Node (la, (xa, Black), ra) => baliL (joinL l x la) xa ra));

fun join l x r =
  (if Int.< (bheight r, bheight l) then paint Black (joinR l x r)
    else (if Int.< (bheight l, bheight r) then paint Black (joinL l x r)
           else Node (l, (x, Black), r)));

fun stack (DFS_state_ext (stack, seen, return, more)) = stack;

fun split_rbt (A1_, A2_) x Leaf = (Leaf, (false, Leaf))
  | split_rbt (A1_, A2_) x (Node (l, (a, uu), r)) =
    (case cmp (A1_, A2_) x a
      of LT => let
                 val (l1, (b, l2)) = split_rbt (A1_, A2_) x l;
               in
                 (l1, (b, join l2 a r))
               end
      | EQ => (l, (true, r))
      | GT => let
                val (r1, (b, r2)) = split_rbt (A1_, A2_) x r;
              in
                (join l a r1, (b, r2))
              end);

fun insert_rbt (A1_, A2_) x t = let
                                  val (l, (_, a)) = split_rbt (A1_, A2_) x t;
                                in
                                  join l x a
                                end;

fun add_edge (A1_, A2_) g u v =
  (case lookup (A1_, A2_) g u
    of NONE => let
                 val vset = insert_rbt (A1_, A2_) v empty;
                 val digraph = update (A1_, A2_) u vset g;
               in
                 digraph
               end
    | SOME _ => let
                  val vset = the (lookup (A1_, A2_) g u);
                  val vseta = insert_rbt (A1_, A2_) v vset;
                  val digraph = update (A1_, A2_) u vseta g;
                in
                  digraph
                end);

fun equal_tree A_ Leaf (Node (x21, x22, x23)) = false
  | equal_tree A_ (Node (x21, x22, x23)) Leaf = false
  | equal_tree A_ (Node (x21, x22, x23)) (Node (y21, y22, y23)) =
    equal_tree A_ x21 y21 andalso (eq A_ x22 y22 andalso equal_tree A_ x23 y23)
  | equal_tree A_ Leaf Leaf = true;

fun return_update returna (DFS_state_ext (stack, seen, return, more)) =
  DFS_state_ext (stack, seen, returna return, more);

fun stack_update stacka (DFS_state_ext (stack, seen, return, more)) =
  DFS_state_ext (stacka stack, seen, return, more);

fun neighbourhood (A1_, A2_) g v =
  (case lookup (A1_, A2_) g v of NONE => empty | SOME vset => vset);

fun seen_update seena (DFS_state_ext (stack, seen, return, more)) =
  DFS_state_ext (stack, seena seen, return, more);

fun split_min_rbt (A1_, A2_) (Node (l, (a, uu), r)) =
  (if equal_tree (equal_prod A1_ equal_color) l Leaf then (a, r)
    else let
           val (m, la) = split_min_rbt (A1_, A2_) l;
         in
           (m, join la a r)
         end);

fun join2_rbt (A1_, A2_) l r =
  (if equal_tree (equal_prod A1_ equal_color) r Leaf then l
    else let
           val (a, b) = split_min_rbt (A1_, A2_) r;
         in
           join l a b
         end);

fun diff_rbt (A1_, A2_) t1 t2 =
  (if equal_tree (equal_prod A1_ equal_color) t1 Leaf then Leaf
    else (if equal_tree (equal_prod A1_ equal_color) t2 Leaf then t1
           else let
                  val Node (l2, (a, _), r2) = t2;
                  val (l1, (_, r1)) = split_rbt (A1_, A2_) a t1;
                  val l = diff_rbt (A1_, A2_) l1 l2;
                  val aa = diff_rbt (A1_, A2_) r1 r2;
                in
                  join2_rbt (A1_, A2_) l aa
                end));

fun dfs_impl (A1_, A2_) f t dfs_state =
  (case stack dfs_state of [] => return_update (fn _ => NotReachable) dfs_state
    | v :: stack_tl =>
      (if eq A1_ v t then return_update (fn _ => Reachable) dfs_state
        else (if not (equal_tree (equal_prod A1_ equal_color)
                       (diff_rbt (A1_, A2_) (neighbourhood (A1_, A2_) f v)
                         (seen dfs_state))
                       empty)
               then let
                      val u =
                        sel (diff_rbt (A1_, A2_) (neighbourhood (A1_, A2_) f v)
                              (seen dfs_state));
                      val stacka = u :: stack dfs_state;
                      val seena = insert_rbt (A1_, A2_) u (seen dfs_state);
                    in
                      dfs_impl (A1_, A2_) f t
                        (seen_update (fn _ => seena)
                          (stack_update (fn _ => stacka) dfs_state))
                    end
               else let
                      val stacka = stack_tl;
                    in
                      dfs_impl (A1_, A2_) f t
                        (stack_update (fn _ => stacka) dfs_state)
                    end)));

val map_empty : (('a * ('a * color) tree) * color) tree = Leaf;

fun from_list (A1_, A2_) xs =
  foldl (fn g => fn (a, b) => add_edge (A1_, A2_) g a b) map_empty xs;

fun rbt_dfs_impl x = dfs_impl (equal_nat, linorder_nat) x;

fun rbt_from_list x = from_list (equal_nat, linorder_nat) x;

fun dfs_initial_state (A1_, A2_) s =
  DFS_state_ext ([s], insert_rbt (A1_, A2_) s empty, NotReachable, ());

fun rbt_dfs_initial_state x = dfs_initial_state (equal_nat, linorder_nat) x;

end; (*struct DFS_RBT*)
