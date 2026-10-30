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


structure BFS_RBT : sig
  type color
  type 'a tree
  type ('a, 'b, 'c) bFS_state_ext
  val bFS_dag_rbt :
    ((Int.int * (Int.int * color) tree) * color) tree ->
      (Int.int * color) tree ->
        ((Int.int * (Int.int * color) tree) * color) tree
  val graph_rbt :
    (Int.int * Int.int) list ->
      ((Int.int * (Int.int * color) tree) * color) tree
  val parent_rbt :
    ((Int.int * Int.int) * color) tree -> Int.int -> Int.int option
  val build_rbt_sources : Int.int list -> (Int.int * color) tree
  val bFS_check_reachable_rbt :
    ((Int.int * (Int.int * color) tree) * color) tree ->
      (Int.int * color) tree -> Int.int -> bool
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

datatype cmp_val = LT | EQ | GT;

datatype ('a, 'b, 'c) bFS_state_ext = BFS_state_ext of 'a * 'b * 'b * 'c;

fun id x = (fn xa => xa) x;

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

fun isin (A1_, A2_) Leaf x = false
  | isin (A1_, A2_) (Node (l, (a, uu), r)) x =
    (case cmp (A1_, A2_) x a of LT => isin (A1_, A2_) l x | EQ => true
      | GT => isin (A1_, A2_) r x);

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

fun member A_ [] y = false
  | member A_ (x :: xs) y = eq A_ x y orelse member A_ xs y;

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

fun ins (A1_, A2_) x Leaf = Node (Leaf, (x, Red), Leaf)
  | ins (A1_, A2_) x (Node (l, (a, Black), r)) =
    (case cmp (A1_, A2_) x a of LT => baliL (ins (A1_, A2_) x l) a r
      | EQ => Node (l, (a, Black), r) | GT => baliR l a (ins (A1_, A2_) x r))
  | ins (A1_, A2_) x (Node (l, (a, Red), r)) =
    (case cmp (A1_, A2_) x a of LT => Node (ins (A1_, A2_) x l, (a, Red), r)
      | EQ => Node (l, (a, Red), r)
      | GT => Node (l, (a, Red), ins (A1_, A2_) x r));

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if member A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

val empty : ('a * color) tree = Leaf;

fun lookup (A1_, A2_) Leaf x = NONE
  | lookup (A1_, A2_) (Node (l, ((a, b), uu), r)) x =
    (case cmp (A1_, A2_) x a of LT => lookup (A1_, A2_) l x | EQ => SOME b
      | GT => lookup (A1_, A2_) r x);

fun update (A1_, A2_) x y t = paint Black (upd (A1_, A2_) x y t);

fun insert (A1_, A2_) x t = paint Black (ins (A1_, A2_) x t);

fun map_filter f [] = []
  | map_filter f (x :: xs) =
    (case f x of NONE => map_filter f xs | SOME y => y :: map_filter f xs);

fun bheight Leaf = (0 : Int.int)
  | bheight (Node (l, (x, c), r)) =
    (if equal_colora c Black then Int.+ (bheight l, (1 : Int.int))
      else bheight l);

fun snd (x1, x2) = x2;

fun fst (x1, x2) = x1;

fun nbs A_ (B1_, B2_) edges v =
  foldr (insert (B1_, B2_))
    (remdups B1_
      (map_filter (fn x => (if eq A_ (fst x) v then SOME (snd x) else NONE))
        edges))
    Leaf;

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

fun equal_tree A_ Leaf (Node (x21, x22, x23)) = false
  | equal_tree A_ (Node (x21, x22, x23)) Leaf = false
  | equal_tree A_ (Node (x21, x22, x23)) (Node (y21, y22, y23)) =
    equal_tree A_ x21 y21 andalso (eq A_ x22 y22 andalso equal_tree A_ x23 y23)
  | equal_tree A_ Leaf Leaf = true;

fun visited_update visiteda (BFS_state_ext (parents, current, visited, more)) =
  BFS_state_ext (parents, current, visiteda visited, more);

fun parents_update parentsa (BFS_state_ext (parents, current, visited, more)) =
  BFS_state_ext (parentsa parents, current, visited, more);

fun current_update currenta (BFS_state_ext (parents, current, visited, more)) =
  BFS_state_ext (parents, currenta current, visited, more);

fun neighbourhood (A1_, A2_) =
  (fn g => fn v =>
    (case lookup (A1_, A2_) g v of NONE => Leaf | SOME vset => vset));

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

fun union_rbt (A1_, A2_) t1 t2 =
  (if equal_tree (equal_prod A1_ equal_color) t1 Leaf then t2
    else (if equal_tree (equal_prod A1_ equal_color) t2 Leaf then t1
           else let
                  val Node (l1, (a, _), r1) = t1;
                  val (l2, (_, r2)) = split_rbt (A1_, A2_) a t2;
                  val l = union_rbt (A1_, A2_) l1 l2;
                  val b = union_rbt (A1_, A2_) r1 r2;
                in
                  join l a b
                end));

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

fun fold_rbt f Leaf acc = acc
  | fold_rbt f (Node (l, (x, Black), r)) acc =
    f x (fold_rbt f l (fold_rbt f r acc))
  | fold_rbt f (Node (l, (x, Red), r)) acc =
    f x (fold_rbt f l (fold_rbt f r acc));

fun fold_vset x = fold_rbt x;

fun next_frontier (A1_, A2_) g frontier vis =
  fold_vset
    (fn u => fn nf =>
      union_rbt (A1_, A2_) nf
        (diff_rbt (A1_, A2_) (neighbourhood (A1_, A2_) g u) vis))
    frontier Leaf;

fun fold_adjmap x = fold_rbt x;

fun add_neighbs (A1_, A2_) g u vs =
  (if equal_tree (equal_prod A1_ equal_color) vs Leaf then g
    else (case lookup (A1_, A2_) g u of NONE => update (A1_, A2_) u vs g
           | SOME vsa => update (A1_, A2_) u (union_rbt (A1_, A2_) vsa vs) g));

fun expand_tree (A1_, A2_) g bFS_tree frontier vis =
  fold_adjmap
    (fn u => fn nf =>
      add_neighbs (A1_, A2_) nf u
        (diff_rbt (A1_, A2_) (neighbourhood (A1_, A2_) g u) vis))
    frontier bFS_tree;

fun visited (BFS_state_ext (parents, current, visited, more)) = visited;

fun parents (BFS_state_ext (parents, current, visited, more)) = parents;

fun current (BFS_state_ext (parents, current, visited, more)) = current;

fun bfs_impl (A1_, A2_) g bFS_state =
  (if not (equal_tree (equal_prod A1_ equal_color) (current bFS_state) Leaf)
    then let
           val visiteda =
             union_rbt (A1_, A2_) (visited bFS_state) (current bFS_state);
           val parentsa =
             expand_tree (A1_, A2_) g (parents bFS_state) (current bFS_state)
               visiteda;
           val currenta =
             next_frontier (A1_, A2_) g (current bFS_state) visiteda;
         in
           bfs_impl (A1_, A2_) g
             (current_update (fn _ => currenta)
               (visited_update (fn _ => visiteda)
                 (parents_update (fn _ => parentsa) bFS_state)))
         end
    else bFS_state);

fun vertices A_ edges = remdups A_ (map fst edges @ map snd edges);

fun a_graph (A1_, A2_) edges =
  foldr (fn x => update (A1_, A2_) x (nbs A1_ (A1_, A2_) edges x))
    (vertices A1_ edges) empty;

fun bfs_initial_state A_ srcs = BFS_state_ext (empty, srcs, Leaf, ());

fun bFS_dag_rbt g srcs =
  parents
    (bfs_impl (equal_nat, linorder_nat) g
      (bfs_initial_state linorder_nat srcs));

fun graph_rbt es = a_graph (equal_nat, linorder_nat) es;

fun parent_rbt p v = lookup (equal_nat, linorder_nat) p v;

fun build_rbt_sources lista =
  foldr (insert (equal_nat, linorder_nat)) lista empty;

fun bFS_check_reachable_rbt g srcs t =
  isin (equal_nat, linorder_nat)
    (visited
      (bfs_impl (equal_nat, linorder_nat) g
        (bfs_initial_state linorder_nat srcs)))
    t;

end; (*struct BFS_RBT*)
