theory RBT_Map_Extension
  imports "HOL-Data_Structures.RBT_Map"
begin

fun update_all where
"update_all f Leaf = Leaf"|
"update_all f (B l (x, y) r) = B (update_all f l) (x, f x y) (update_all f r)"|
"update_all f (R l (x, y) r) = R (update_all f l) (x, f x y) (update_all f r)"

definition rbt_red :: "('a::linorder \<times> 'b) rbt \<Rightarrow> bool" where
"rbt_red t = (invc t \<and> invh t \<and> sorted1 (inorder t))"

lemma rbt_red_subtrees: 
  "rbt_red (B l m r) \<Longrightarrow> rbt_red l" 
  "rbt_red (B l m r) \<Longrightarrow> rbt_red r" 
  "rbt_red (R l m r) \<Longrightarrow> rbt_red l" 
  "rbt_red (R l m r) \<Longrightarrow> rbt_red r" 
  by (auto simp add: rbt_red_def sorted_wrt_append)

lemma domain_subtrees:
"rbt_red (B l (x, y) r) \<Longrightarrow>
 dom (lookup  (B l (x, y) r)) = dom (lookup l) \<union> {x} \<union> dom (lookup r)"
"rbt_red (R l (x, y) r) \<Longrightarrow>
 dom (lookup  (R l (x, y) r)) = dom (lookup l) \<union> {x} \<union> dom (lookup r)"
  by(auto simp add: sorted_wrt_append lookup_map_of map_of_sorted_snoc[of _ x]  sorted_mid_iff
                    dom_def rbt_red_def map_of_sorted_Cons[of x])

lemma bheight_no_change: "bheight (update_all f tree) = bheight tree"
  by(induction f tree rule: update_all.induct) auto

lemma key_inorder_no_change: "map fst (inorder (update_all f tree)) = map fst (inorder tree)"
  by(induction f tree rule: update_all.induct) auto

lemma color_no_change: "color (update_all f tree) = color tree"
  by(induction f tree rule: update_all.induct) auto

lemma  update_all: 
    "\<And> map f. rbt_red map \<Longrightarrow> (\<And> x. x \<in> dom (lookup map) 
                  \<Longrightarrow> lookup (update_all f map) x =
                      Some (f x (the (lookup map x))))" 
    "\<And> map f g. rbt_red map \<Longrightarrow> (\<And> x. x \<in> dom (lookup map)  \<Longrightarrow>
                     f x (the (lookup map x)) = g x (the (lookup map x))) \<Longrightarrow>
          update_all f map = update_all g map " 
   "\<And> map f. rbt_red  map \<Longrightarrow> rbt_red (update_all f map)" 
   "\<And> map f. rbt_red map \<Longrightarrow> dom (lookup (update_all f map))
                              = dom (lookup map)"
proof(goal_cases)
  case (1 map f a)
  then show ?case 
  proof(induction f map rule: update_all.induct)
    case (2 f l x y r)
    note IH = this
    show ?case
      using IH(3) domain_subtrees IH(4,3) 
      by(auto intro: IH(1,2) rbt_red_subtrees)
  next
    case (3 f l x y r)
     note IH = this
    then show ?case 
      using IH(3) domain_subtrees IH(4,3) 
      by(auto intro: IH(1,2) rbt_red_subtrees)
  qed auto
next
  case (2 map f g)
  then show ?case 
  proof(induction f map rule: update_all.induct)
    case (2 f l x y r)
    note IH = this
    have help1: "f x y = g x y \<Longrightarrow> a = x \<Longrightarrow> lookup l x = Some ya \<Longrightarrow> f x ya = g x ya" for a ya 
      using  sorted_mid_iff  rbt_red_subtrees(1)[OF "2.prems"(1)]
            "2.prems"(1)[simplified rbt_red_def inorder.simps sorted_mid_iff]
      by(subst (asm) lookup_map_of, force simp add: rbt_red_def, subst (asm) map_of_None2) force+
    have help2: "f a (the (lookup r a)) = g a (the (lookup r a)) \<Longrightarrow> x < a \<Longrightarrow> lookup l a = Some y \<Longrightarrow> f a y = g a y" for y a
      using  sorted_mid_iff  rbt_red_subtrees(1)[OF "2.prems"(1)]
            "2.prems"(1)[simplified rbt_red_def inorder.simps sorted_mid_iff]
      by (simp add: lookup_map_of rbt_red_def,
         (subst (asm) map_of_None2[OF  sorted_snoc_le[OF ASSUMPTION_I, of _ x]]; auto)) 
    have coincide_left:"a \<in> dom (lookup l) \<Longrightarrow> f a (the (lookup l a)) = g a (the (lookup l a))" for a
      using IH(4)[simplified domain_subtrees(1)[OF IH(3)], of a, simplified lookup.simps]
      by(cases "cmp a x") (auto simp add: dom_def intro: help1 help2)
    have coincide_x: "f x y = g x y"
      using IH(4)[of x] by(auto simp add: dom_def)
    have helper: "a < x \<Longrightarrow> f a (the (lookup l a)) = g a (the (lookup l a)) \<Longrightarrow> lookup r a = Some y \<Longrightarrow> f a y = g a y" for a y
       apply(subst (asm) (3) lookup_map_of, simp add: rbt_red_subtrees(2)[OF  IH(3), simplified rbt_red_def])
       using sym[OF  list.simps(9)[of fst "(x, y)" "Tree2.inorder r", simplified fst_conv]]
             IH(3)[simplified rbt_red_def Tree2.inorder.simps(2)  map_append ]
       by(subst (asm) map_of_sorted_Cons[of x])
         (auto simp add:  map_of_sorted_Cons[of x] sorted_wrt_append)
     have coincide_right:"a \<in> dom (lookup r) \<Longrightarrow> f a (the (lookup r a)) = g a (the (lookup r a))" for a   
      using IH(4)[simplified domain_subtrees(1)[OF IH(3)], of a, simplified lookup.simps]
             IH(3)[simplified rbt_red_def Tree2.inorder.simps(2)  map_append ]
            IH(4)[simplified dom_def lookup.simps(2), of a]
      by (cases "cmp a x") (auto simp add: lookup_map_of map_of_None sorted_wrt_append dom_def intro: helper)
    show ?case
    using coincide_x coincide_left domain_subtrees IH(4,3) coincide_right
      by(force intro!: IH(2)  IH(1) intro: rbt_red_subtrees)
  next
    case (3 f l x y r)
    note IH = this
    have help1: "f x y = g x y \<Longrightarrow> a = x \<Longrightarrow> lookup l x = Some ya \<Longrightarrow> f x ya = g x ya" for a ya
      using  sorted_mid_iff  rbt_red_subtrees(3)[OF "3.prems"(1)]
            "3.prems"(1)[simplified rbt_red_def inorder.simps sorted_mid_iff]
      by (subst (asm) lookup_map_of, force simp add: rbt_red_def, subst (asm) map_of_None2) force+
    have help2: "f a (the (lookup r a)) = g a (the (lookup r a)) \<Longrightarrow> x < a \<Longrightarrow> lookup l a = Some y \<Longrightarrow> f a y = g a y" for a y
      using  sorted_mid_iff  rbt_red_subtrees(3)[OF "3.prems"(1)]
            "3.prems"(1)[simplified rbt_red_def inorder.simps sorted_mid_iff]
      by ( simp add: lookup_map_of rbt_red_def,
         (subst (asm) map_of_None2[OF  sorted_snoc_le[OF ASSUMPTION_I, of _ x]]; auto)) 
    have coincide_left:"a \<in> dom (lookup l) \<Longrightarrow> f a (the (lookup l a)) = g a (the (lookup l a))" for a
      using IH(4)[simplified domain_subtrees(2)[OF IH(3)], of a, simplified lookup.simps]
      by(cases "cmp a x")(auto simp add: dom_def intro: help1 help2)
    have coincide_x: "f x y = g x y"
      using IH(4)[of x] by(auto simp add: dom_def)
    have helper: "a < x \<Longrightarrow> f a (the (lookup l a)) = g a (the (lookup l a)) \<Longrightarrow> lookup r a = Some y \<Longrightarrow> f a y = g a y" for a y 
     apply(subst (asm) (3) lookup_map_of, simp add: rbt_red_subtrees(4)[OF  IH(3), simplified rbt_red_def])
       using sym[OF  list.simps(9)[of fst "(x, y)" "Tree2.inorder r", simplified fst_conv]]
             IH(3)[simplified rbt_red_def Tree2.inorder.simps(2)  map_append ]
       by(subst (asm) map_of_sorted_Cons[of x])
         (auto simp add:  map_of_sorted_Cons[of x] sorted_wrt_append)     

   have coincide_right:"a \<in> dom (lookup r) \<Longrightarrow> f a (the (lookup r a)) = g a (the (lookup r a))" for a
      using IH(4)[simplified domain_subtrees(2)[OF IH(3)], of a, simplified lookup.simps]      
            IH(3)[simplified rbt_red_def Tree2.inorder.simps(2)  map_append ]
            IH(4)[simplified dom_def lookup.simps(2), of a]
      by (cases "cmp a x")(auto simp add: dom_def lookup_map_of map_of_None sorted_wrt_append intro: helper)
    show ?case
    using coincide_x coincide_left domain_subtrees IH(4,3) coincide_right
      by(force intro!: IH(2)  IH(1) intro: rbt_red_subtrees)
  qed auto
next
  case (3 map f)
  then show ?case 
  proof(induction f map rule: update_all.induct)
    case (2 f l x y r)
    note IH = this
    show ?case 
        using IH(1,2) rbt_red_subtrees(1,2)[OF IH(3)] IH(3)  
        by (auto simp add: rbt_red_def  bheight_no_change key_inorder_no_change)
  next
    case (3 f l x y r)
    note IH = this
    show ?case 
        using IH(1,2) rbt_red_subtrees(3,4)[OF IH(3)] IH(3)  
        by (auto simp add: rbt_red_def  bheight_no_change key_inorder_no_change color_no_change)
  qed (auto simp add: rbt_red_def)
next
  case (4 map f)
  show ?case 
    by(induction f map rule: update_all.induct) fastforce+
qed

fun get_max where
"get_max f Leaf = undefined"|
"get_max f (Node Leaf ((x, y),_::color ) Leaf) = f x y"|
"get_max f (Node (Node l1 ((x1, y1), c1) r1) ((x, y),_::color ) Leaf) =
                max (f x y) (get_max f (Node l1 ((x1, y1), c1) r1))" |
"get_max f (Node Leaf ((x, y),_::color ) (Node l2 ((x2, y2), c2) r2)) =
                max  (f x y) (get_max f (Node l2 ((x2, y2), c2) r2))" |
"get_max f (Node (Node l1 ((x1, y1), c1) r1) ((x, y),_::color ) (Node l2 ((x2, y2), c2) r2)) =
                max (max (get_max f (Node l1 ((x1, y1), c1) r1)) (f x y)) 
                          (get_max f (Node l2 ((x2, y2), c2) r2))"

lemma finite_tree_dom: "finite  (dom (lookup tree))"
  unfolding dom_def
  apply(induction tree)
  subgoal by simp
  subgoal for left mid right
    apply(cases mid, simp)
    subgoal for kv c
      apply(cases kv)
      by(auto intro: finite_subset[of _ " {a. \<exists>y. lookup left a = Some y} \<union> {_}
                                 \<union> {a. \<exists>y. lookup right a = Some y}"])
    done
  done

lemma sufficientE: "P \<Longrightarrow> (P \<Longrightarrow> Q) \<Longrightarrow> Q" by simp
lemma append_single_elem: "xs@x#ys = (xs @ [x])@ ys" by auto

lemma image_of_domain_decomp:
     "rbt_red (Node lef ((x, y), c) righ) \<Longrightarrow>
         {f ya (the (lookup (Node lef ((x, y), c) righ) ya)) |ya.
     ya \<in> dom (lookup (Node lef ((x, y), c) righ))} =
     {f ya (the (lookup  lef ya)) |ya. ya \<in> dom (lookup  lef)}
     \<union> {f x y} \<union>
     {f ya (the (lookup righ ya)) |ya. ya \<in> dom (lookup righ)}"
proof(rule, goal_cases)
  case 1
  then show ?case 
    by (auto split: if_split simp add: rbt_red_def dom_def)
next
  case 2
  have help1: "\<lbrakk>rbt_red \<langle>lef, ((x, y), c), righ\<rangle>; lookup lef ya = Some yb \<rbrakk>\<Longrightarrow>
       \<exists>yaa. (x < yaa \<longrightarrow>
              f ya yb = f yaa (the (lookup righ yaa)) \<and> yaa \<in> dom (lookup \<langle>lef, ((x, y), c), righ\<rangle>)) \<and>
             (\<not> x < yaa \<longrightarrow>
              (yaa < x \<longrightarrow>
               f ya yb = f yaa (the (lookup lef yaa)) \<and> yaa \<in> dom (lookup \<langle>lef, ((x, y), c), righ\<rangle>)) \<and>
              (yaa = x \<longrightarrow> f ya yb = f x y \<and> x \<in> dom (lookup \<langle>lef, ((x, y), c), righ\<rangle>)))" for ya yb
      by(auto intro: exI[of _ ya] sufficientE[of "_ < x"] case_split[of " _ \<ge> x"] 
           simp add: lookup_map_of map_of_sorted_snoc[of _ x] sorted_wrt_append rbt_red_def dom_def)
    have help2: "\<lbrakk>rbt_red \<langle>lef, ((x, y), c), righ\<rangle> ; lookup righ ya = Some yb\<rbrakk> \<Longrightarrow>
    \<exists>yaa. (x < yaa \<longrightarrow> f ya yb = f yaa (the (lookup righ yaa)) \<and> yaa \<in> dom (lookup \<langle>lef, ((x, y), c), righ\<rangle>)) \<and>
          (\<not> x < yaa \<longrightarrow>
           (yaa < x \<longrightarrow> f ya yb = f yaa (the (lookup lef yaa)) \<and> yaa \<in> dom (lookup \<langle>lef, ((x, y), c), righ\<rangle>)) \<and>
           (yaa = x \<longrightarrow> f ya yb = f x y \<and> x \<in> dom (lookup \<langle>lef, ((x, y), c), righ\<rangle>)))" for ya yb
      by (auto intro: exI[of _ ya] linorder_class.linorder_cases[of ya x] 
            simp add: lookup_map_of map_of_sorted_Cons[of x]  map_of_None rbt_red_def sorted_wrt_append)
    from 2 show ?case
    by (fastforce intro: help1 help2)
qed

lemma get_max_correct:
"rbt_red tree \<Longrightarrow> dom (lookup tree) \<noteq> {} \<Longrightarrow>
           get_max f tree = Max {f y (the (lookup tree y)) |y. y \<in> dom (lookup tree)}"
proof(induction f tree rule: get_max.induct)
  case (1 f)
  then show ?case by auto
next
  case (2 f x y uu)
  have "get_max f \<langle>\<langle>\<rangle>, ((x, y), uu), \<langle>\<rangle>\<rangle>
       = f x y" by simp
  also have "... = Max {f x y}"by simp
  also have "... = Max {f ya (the (lookup \<langle>\<langle>\<rangle>, ((x, y), uu), \<langle>\<rangle>\<rangle> ya)) |ya.
         ya \<in> dom (lookup \<langle>\<langle>\<rangle>, ((x, y), uu), \<langle>\<rangle>\<rangle>)}"
    by(force intro!: arg_cong[of _ _ Max] simp add: dom_def)
  ultimately show ?case by argo
next
  case (3 f l1 x1 y1 c1 r1 x y c)
  have " get_max f \<langle>\<langle>l1, ((x1, y1), c1), r1\<rangle>, ((x, y), c), \<langle>\<rangle>\<rangle> 
        = max (f x y) (get_max f \<langle>l1, ((x1, y1), c1), r1\<rangle>)" by simp
  also have "... = max (f x y) (Max {f y (the (lookup \<langle>l1, ((x1, y1), c1), r1\<rangle> y)) |y.
         y \<in> dom (lookup \<langle>l1, ((x1, y1), c1), r1\<rangle>)})"
    using 3(2)
    by(intro arg_cong[of _ _ "max _"], intro 3(1), cases c, auto intro: rbt_red_subtrees(1,3)
      dest: cong[of _ "(\<lambda>x. None)"  x1, OF _ refl])
  also have "... = Max (Set.insert (f x y) {f y (the (lookup \<langle>l1, ((x1, y1), c1), r1\<rangle> y)) |y.
         y \<in> dom (lookup \<langle>l1, ((x1, y1), c1), r1\<rangle>)})"
    by(intro sym[OF linorder_class.Max_insert])
      (auto simp add:  finite_tree_dom dest: cong[of _ "(\<lambda>x. None)"  x1, OF _ refl])
  also have "... = Max {f ya (the (lookup \<langle>\<langle>l1, ((x1, y1), c1), r1\<rangle>, ((x, y), c), \<langle>\<rangle>\<rangle> ya)) |ya.
         ya \<in> dom (lookup \<langle>\<langle>l1, ((x1, y1), c1), r1\<rangle>, ((x, y), c), \<langle>\<rangle>\<rangle>)}"
    apply(rule arg_cong[of _ _ Max], subst (2) image_of_domain_decomp)
    using 3(2) by force+
  ultimately show ?case by argo
next
  case (4 f x y c l2 x2 y2 c2 r2)
  have " get_max f  \<langle>\<langle>\<rangle>, ((x, y), c), \<langle>l2, ((x2, y2), c2), r2\<rangle>\<rangle>
        = max (f x y) (get_max f \<langle>l2, ((x2, y2), c2), r2\<rangle>)" by simp
  also have "... = max (f x y) (Max {f y (the (lookup \<langle>l2, ((x2, y2), c2), r2\<rangle> y)) |y.
         y \<in> dom (lookup \<langle>l2, ((x2, y2), c2), r2\<rangle>)})"
    using 4(2)
    by(intro arg_cong[of _ _ "max _"], intro 4(1), cases c, auto intro: rbt_red_subtrees(2,4)
      dest: cong[of _ "(\<lambda>x. None)"  x2, OF _ refl])
  also have "... = Max (Set.insert (f x y) {f y (the (lookup \<langle>l2, ((x2, y2), c2), r2\<rangle> y)) |y.
         y \<in> dom (lookup \<langle>l2, ((x2, y2), c2), r2\<rangle>)})"
    by(intro sym[OF linorder_class.Max_insert])
      (auto simp add:  finite_tree_dom dest: cong[of _ "(\<lambda>x. None)"  x2, OF _ refl])
  also have "... = Max {f ya (the (lookup \<langle>\<langle>\<rangle>, ((x, y), c), \<langle>l2, ((x2, y2), c2), r2\<rangle>\<rangle> ya)) |ya.
         ya \<in> dom (lookup \<langle>\<langle>\<rangle>, ((x, y), c), \<langle>l2, ((x2, y2), c2), r2\<rangle>\<rangle>)}"
    apply(rule arg_cong[of _ _ Max], subst (2) image_of_domain_decomp)
    using 4(2) by force+
  ultimately show ?case by argo 
next
  case (5 f l1 x1 y1 c1 r1 x y ux l2 x2 y2 c2 r2)
  have " get_max f  \<langle>\<langle>l1, ((x1, y1), c1), r1\<rangle>, ((x, y), ux), \<langle>l2, ((x2, y2), c2), r2\<rangle>\<rangle>
        = max (max (get_max f \<langle>l1, ((x1, y1), c1), r1\<rangle>) (f x y))
             (get_max f \<langle>l2, ((x2, y2), c2), r2\<rangle>)" by simp
  also have "... = max (max (Max {f y (the (lookup \<langle>l1, ((x1, y1), c1), r1\<rangle> y)) |y.
                   y \<in> dom (lookup \<langle>l1, ((x1, y1), c1), r1\<rangle>)})
          (f x y))
     (Max {f y (the (lookup \<langle>l2, ((x2, y2), c2), r2\<rangle> y)) |y.
           y \<in> dom (lookup \<langle>l2, ((x2, y2), c2), r2\<rangle>)})"
    using 5(3) 
     by((subst 5(2) | subst 5(1)) ;
        auto intro: color.exhaust[of ux] rbt_red_subtrees
              dest: cong[of _ "(\<lambda>x. None)"  x2, OF _ refl] 
                    cong[of _ "(\<lambda>x. None)"  x1, OF _ refl] 
          simp add: 5(2))+
   also have "... = Max ({f y (the (lookup \<langle>l1, ((x1, y1), c1), r1\<rangle> y)) |y.
                                y \<in> dom (lookup \<langle>l1, ((x1, y1), c1), r1\<rangle>)}
                          \<union> {f x y} \<union>
                         {f y (the (lookup \<langle>l2, ((x2, y2), c2), r2\<rangle> y)) |y.
                                y \<in> dom (lookup \<langle>l2, ((x2, y2), c2), r2\<rangle>)})"
     by(subst linorder_class.Max_Un, 
        (auto dest: cong[of _ "(\<lambda>x. None)"  x2, OF _ refl] cong[of _ "(\<lambda>x. None)"  x1, OF _ refl]
          simp add: finite_tree_dom )[4])+ 
       simp
  also have "... = Max {f ya (the (lookup \<langle>\<langle>l1, ((x1, y1), c1), r1\<rangle>, ((x, y), ux), \<langle>l2, ((x2, y2), c2), r2\<rangle>\<rangle> ya)) |ya.
         ya \<in> dom (lookup \<langle>\<langle>l1, ((x1, y1), c1), r1\<rangle>, ((x, y), ux), \<langle>l2, ((x2, y2), c2), r2\<rangle>\<rangle>)}"
    apply(rule arg_cong[of _ _ Max], subst (3) image_of_domain_decomp)
    using 5(3) by force+
  ultimately show ?case by argo
qed

locale Map_iterator =
  fixes invar lookup update_all
  assumes update_all:
    "\<And> rep f. invar rep \<Longrightarrow> (\<And> x. x \<in> dom (lookup rep) 
                  \<Longrightarrow> lookup (update_all f rep) x =
                      Some (f x (the (lookup rep x))))"
    "\<And> rep f g. invar rep \<Longrightarrow> (\<And> x. x \<in> dom (lookup rep)  \<Longrightarrow>
                     f x (the (lookup rep x)) = g x (the (lookup rep x))) \<Longrightarrow>
          update_all f rep = update_all g rep "
   "\<And> rep f. invar rep \<Longrightarrow> invar (update_all f rep)"
   "\<And> rep f. invar rep \<Longrightarrow> dom (lookup (update_all f rep))
                              = dom (lookup rep)"
end