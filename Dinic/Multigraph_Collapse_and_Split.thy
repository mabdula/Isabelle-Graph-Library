theory Multigraph_Collapse_and_Split
  imports (*Directed_Set_Graphs.Multigraph*) "HOL-Eisbach.Eisbach"
          Flow_Theory.Blocking_Flow
begin

locale split_weight_single_spec = 
  fixes   add::"'w \<Rightarrow> 'w \<Rightarrow> 'w" ("_ w+ _")
  and   subtr::"'w \<Rightarrow> 'w \<Rightarrow> 'w" ("_ w- _")
  and   zero::"'w" ("w0")
  and    wleq::"'w \<Rightarrow> 'w \<Rightarrow> bool" ("_ w\<le> _")
  and   wless::"'w \<Rightarrow> 'w \<Rightarrow> bool" ("_ w< _")
  and   weq::"'w \<Rightarrow> 'w \<Rightarrow> bool"   ("_ w= _")
 (* and   iterate::"('x \<Rightarrow> ('map \<times> 'w) \<Rightarrow> ('map \<times> 'w))
           \<Rightarrow> 'x_set \<Rightarrow>  ('map \<times> 'w) \<Rightarrow> 'map"*)
  and update::"'map \<Rightarrow> 'x \<Rightarrow> 'w \<Rightarrow> 'map"
  and lookup::"'map \<Rightarrow> 'x \<Rightarrow> 'w option"
  and map_empty::'map
begin

fun split where 
"split u [] W mp= mp"|
"split u (x#xs) W mp= 
   (if W w= w0 then mp
    else if W w\<le> u x then update mp x W
    else split u xs (W w-  u x) (update mp x (W w- (W w- u x))))"

end

locale split_weight_single =
  split_weight_single_spec where
add = "add::'w \<Rightarrow> 'w \<Rightarrow> 'w"  for add ("_ w+ _")
+ assumes  w_add_assoc:"\<And>a b c. ((a w+ b) w+ c) = (a w+ (b w+ c))"
and     w_add_comm: "\<And>a b. (a w+ b) = (b w+ a)"
and     w0_let_ntr: "\<And>a. (w0 w+ a) = a"
and     less_def:   "\<And>x y::'w. (x w< y) = (x w\<le> y \<and> \<not> y w\<le> x)"
and     less_refl: "\<And>x::'w. x w\<le> x" 
and     less_trans: "\<And>x y z::'w. x w\<le> y \<Longrightarrow> y w\<le> z \<Longrightarrow> x w\<le> z"
        (*"\<And>x y. x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
        "\<And>a b::'w. (a \<le> b) = (\<exists>c. b = a w+ c)"
        "\<And>a b::'w. a \<le> b \<Longrightarrow> b w- a w+ a = b"
        "\<And>a b c. a - b - c = a - (b + c)"*)
begin

lemma split_lemma:
  assumes "foldr add (map u xs) w0 w= W"
  shows   "(foldr (\<lambda> x w. (the (lookup (split u xs W map_empty) x)) w+ w) xs w0)
                w= W"
          "\<And> x. x \<in> set xs
            \<Longrightarrow> (the (lookup (split u xs W map_empty) x)) w\<le> u x"
  sorry





  oops

split_weight_spec +
assumes w_add_assoc:"\<And>a b c. ((a w+ b) w+ c) = (a w+ (b w+ c))"
and     w_add_comm: "\<And>a b. a w+ b = b w+ a"
and     w0_let_ntr: "\<And>a. w0 w+ a = a"
and     less_def:   "\<And>x y::'w. (x < y) = (x \<le> y \<and> \<not> y \<le> x)"
and     less_refl: "\<And>x::'w. x \<le> x" 
and     less_trans: "\<And>x y z::'w. x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
        (*"\<And>x y. x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
        "\<And>a b::'w. (a \<le> b) = (\<exists>c. b = a w+ c)"
        "\<And>a b::'w. a \<le> b \<Longrightarrow> b w- a w+ a = b"
        "\<And>a b c. a - b - c = a - (b + c)"*)








  oops






fun find_f where
"find_f g acc [] f = f"|
"find_f g acc [e] f= (\<lambda> d. if d = e then acc else f d)"|
"find_f g acc (e#es) f= (if acc \<le> g e then (\<lambda> d. if d = e then acc else f d)
                        else find_f g (acc - g e) es (\<lambda> d. if d = e then acc - (acc -  g e) else f d))"

lemma e_not_in_no_change:"e \<notin> set es \<Longrightarrow> find_f g acc es f e = f e"
  by(induction g acc es f arbitrary: e rule: find_f.induct )
     auto

lemma find_f_init_cong:
  assumes "\<And> e. e \<in> set es \<Longrightarrow> f e = f' e"
  shows  "e \<in> set es \<Longrightarrow> find_f g acc es f e = find_f g acc es f' e"
  using assms
proof(induction g acc es f arbitrary: f' e rule: find_f.induct )
  case (1 g acc f)
  then show ?case by simp
  next
  case (2 g acc e f)
  then show ?case by simp
next
  case (3 g acc d v va f )
  show ?case 
    apply (subst find_f.simps(3))+
    apply(cases "acc \<le> g d")
    subgoal
      apply(subst if_P[of "acc \<le> g d"])
       apply simp
      apply(subst if_P[of "acc \<le> g d"])
       apply simp
      using 3(2,3) by auto
    subgoal
      apply(subst if_not_P[of "acc \<le> g d"])
       apply simp
      apply(subst if_not_P[of "acc \<le> g d"])
       apply simp
      apply(cases "e \<in> set (v #va)")
      subgoal
      apply(rule 3(1))
          apply simp
         apply simp
        apply simp
        using 3(2,3) by simp
      subgoal
        apply(subst e_not_in_no_change)
         apply simp
        apply(subst e_not_in_no_change)
         apply simp
        using 3(2,3) by simp
      done
    done
qed
  
  
lemma 
  assumes "A \<subseteq> \<Union> (g ` (set es))" "es \<noteq> []" "distinct es"
  shows       "\<exists> f. (\<forall> e \<in> set es. f e \<subseteq> g e) \<and> \<Union> (f ` (set es)) = A"
proof-
  define f where "f = find_f g A es (\<lambda> e. {})"
  have prop1:"\<Union> (f ` set es) = A"
    using assms(1,2,3)
    unfolding f_def
  proof(induction es arbitrary: A)
    case Nil
    then show ?case by simp
  next
    case (Cons e es)
    note IH = this
    show ?case 
    proof(cases es)
      case Nil
      show ?thesis 
        apply(subst Nil, subst find_f.simps, subst Nil)
        by simp
    next
      case (Cons d list)
      show ?thesis 
        apply(subst Cons)
        apply(subst find_f.simps)
        apply(cases "A \<subseteq> g e")
        subgoal
          apply(subst if_P[of "A \<subseteq> g e"])
           apply simp
          apply(subst set_simps(2))
          apply(subst Union_image_insert)
          using IH(4) by simp
        subgoal
          apply(subst if_not_P[of "A \<subseteq> g e"])
           apply simp
          apply(subst set_simps(2))
          apply(subst Union_image_insert)
          apply(subst e_not_in_no_change[of e "d#list" g "A - g e"])
          using IH(4) Cons apply simp
          apply(subst if_P[of "e = e"])
           apply simp
          unfolding Cons[symmetric]
         apply(subst image_cong[OF refl  find_f_init_cong[of
               es "(\<lambda>d. if d = e then A - (A - g e) else {})" "\<lambda> x.  {}" _ g "A - g e"], of "set es" "\<lambda> x. x"]
        )
          apply(subst if_not_P)
          using IH(4) Cons apply force
            apply simp        
          apply simp
          apply(subst IH(1)) (*interesting*)
          using IH(2) apply force
          using Cons apply simp
          using IH(4) apply simp (*interesting*)
          by auto
        done
    qed
  qed
  have prop2:"e\<in>set es \<Longrightarrow> f e \<subseteq> g e" for e
    unfolding f_def
    using assms(1,2,3)
  proof(induction es arbitrary: A)
    case Nil
    then show ?case by simp
  next
    case (Cons d es)
    note IH = this
    show ?case 
    proof(cases es)
      case Nil
      then show ?thesis 
        using IH(2,3) 
        unfolding Nil
        apply(subst find_f.simps)
        by simp
    next
      case (Cons a list)
      show ?thesis 
        unfolding Cons
        apply(subst find_f.simps)
        apply(cases "A \<subseteq> g d")
        subgoal
          apply(subst if_P[of "A \<subseteq> g d"])
           apply simp
          by auto
        subgoal
          apply(subst if_not_P[of "A \<subseteq> g d"])
           apply simp
          apply(cases "d = e")
          subgoal
            apply(subst e_not_in_no_change)
            using IH(5) Cons apply simp
            apply(subst if_P)
             apply simp (*interesting*)
            by auto
          subgoal
            unfolding Cons[symmetric]
            apply(subst find_f_init_cong[of
               es "(\<lambda>da. if da = d then A - (A - g d) else {})" "\<lambda> x.  {}" _ g "A - g d"])
            apply(subst if_not_P)
            using IH(5) Cons apply auto[1]
            apply simp
            using IH(2) Cons apply simp
            apply(rule IH(1))
            using IH(2) Cons apply simp (*interesting*)
            using IH(3) apply force
            using Cons apply simp
            using IH(5) apply simp
            done
          done
        done
    qed
  qed
  show ?thesis
    apply(rule exI[of _ f])
    using prop1 prop2 by simp
 (* have "(\<And> e. e\<in>set es \<Longrightarrow> f' e \<subseteq> g e) \<Longrightarrow> \<Union> (f' ` set es) = A 
           \<Longrightarrow> (\<And> e. e \<in> set es \<Longrightarrow> f' e \<subseteq> f e) \<Longrightarrow> \<exists> e \<in> set es. f' e \<subset> f e \<Longrightarrow> False" for f'
   *)
qed



typ "'a set"

typ nat

context canonically_ordered_monoid_add begin end
context ordered_cancel_comm_monoid_diff  begin end

context comm_monoid_diff begin
end             
context cancel_comm_monoid_add begin
end
context comm_monoid_add begin end
context cancel_ab_semigroup_add begin end (* problem*)
context ordered_ab_semigroup_add_imp_le begin end
context ordered_cancel_ab_semigroup_add begin end
context ordered_ab_semigroup_add begin end


class comm_monoid_monus = 
  canonically_ordered_monoid_add + 
   minus +
  assumes add_diff_cancel_left' [simp]: "a  \<le> b \<Longrightarrow> (b -a) + a = b"
  assumes diff_diff_add [algebra_simps, algebra_split_simps,
                         field_simps, field_split_simps]:
                            "a - b - c = a - (b + c)"
  assumes diff_leq_minuend: "a - b \<le> a"
  assumes zero_diff [simp]: "0 - a = 0"
begin

lemma "a - (a - b) \<le> b" 
  unfolding le_iff_add
  find_theorems "(_::'a) - _"
  find_theorems "_ \<le> (_::'a)"

(*
lemma 
  assumes "c +b = a" "(\<And> d. d + b = a \<Longrightarrow> c \<le> d)" 
  shows"c = a -b"
proof-
  have "c \<le> a - b" 
    using add_commute assms(1,2) local.add_diff_cancel_left' local.le_iff_add
    by blast
  moreover have "c \<ge> a - b"
    sledgehammer
 
  find_theorems "(_::'a) \<le> _"
*)
end

instantiation set:: (type) comm_monoid_monus 
begin

definition "plus_set = Set.union"
definition "zero_set = {}"

instance proof
  show "\<And>(a::'a set) b c. a + b + c = a + (b + c)"
       "\<And>(a::'a set) b. a + b = b + a"
       "\<And>(a::'a set). 0 + a = a"
       "\<And>a b. (a \<subseteq> b) = (\<exists>c. b = a + c)"
       "\<And>a b. a \<subseteq> b \<Longrightarrow> b - a + a = b"
       "\<And>(a::'a set) b c. a - b - c = a - (b + c)"
       "\<And>(a::'a set). 0 - a = 0"
       "\<And>(a::'a set) b. a - b \<subseteq> a"
    by(auto simp add: plus_set_def zero_set_def)
qed
end

instantiation nat:: comm_monoid_monus 
begin

instance proof
  show "\<And>(a::nat) b. a \<le> b \<Longrightarrow> b - a + a = b"
       "\<And>(a::nat) b c. a - b - c = a - (b + c)"
       "\<And>(a::nat). 0 - a = 0"
       "\<And>a b::nat. a - b \<le> a"
    by(auto simp add: plus_set_def zero_set_def)
qed
end
(*
definition pos_real_rel::"real \<Rightarrow> real \<Rightarrow> bool" where
"pos_real_rel x y = ( \<bar> x \<bar> = \<bar> y \<bar>)"

quotient_type pos_real = real / pos_real_rel
 morphisms Rep_Integ Abs_Integ
 by(auto intro!: equivpI reflpI sympI transpI simp add: pos_real_rel_def)

find_theorems "_::pos_real"
typ real
term Abs_pos_real
term Rep_pos_real
*)
(*
datatype real_wrapper = wrap real 

fun the_real where "the_real (wrap x) = x"

instantiation real_wrapper::  comm_monoid_monus 
begin

definition "zero_real_wrapper = wrap 0"

definition "minus_real_wrapper (x::real_wrapper) (y::real_wrapper) =
            wrap ( max (0::real) (the_real x  - the_real y))"

definition "less_eq_real_wrapper (x::real_wrapper) (y::real_wrapper) =
           (the_real x  \<le>  the_real y )"

definition "less_real_wrapper (x::real_wrapper) (y::real_wrapper) =
           ( the_real x  < the_real y)"

definition "plus_real_wrapper (x::real_wrapper) (y::real_wrapper) =
            wrap ( max (0::real) (the_real x  + the_real y ))"

instance proof
  show "\<And>(a::real_wrapper) b c. a + b + c = a + (b + c)"
       "\<And>(a::real_wrapper) b. a + b = b + a"
       "\<And>(a::real_wrapper). 0 + a = a"
    apply(auto simp add: plus_real_wrapper_def zero_real_wrapper_def)
   *)

datatype ereal_wrapper = wrap ereal

fun the_ereal where
"the_ereal (wrap x) = x"
text \<open>An interpretation of ereal wrappers as commutative monoid with monus.
This is suitable for shortest paths.\<close>
instantiation ereal_wrapper:: comm_monoid_monus 
begin

definition "plus_ereal_wrapper (x::ereal_wrapper) y
           = wrap (min (the_ereal x) (the_ereal y))"
definition "zero_ereal_wrapper = wrap PInfty"
definition "minus_ereal_wrapper (x::ereal_wrapper) y =
           (if the_ereal x < the_ereal y then x else wrap PInfty)"
definition "less_eq_ereal_wrapper (x::ereal_wrapper) y =
             (the_ereal x \<ge> the_ereal y)"
definition "less_ereal_wrapper (x::ereal_wrapper) y =
             (the_ereal x > the_ereal y)"

instance proof
  show "(a \<le> b) = (\<exists>c. b = a + c)" for a b::ereal_wrapper
    by(auto simp add:  plus_ereal_wrapper_def 
                       less_eq_ereal_wrapper_def less_ereal_wrapper_def
              intro: the_ereal.elims intro!: exI[of _ b])
  show "a \<le> b \<Longrightarrow> b - a + a = b" for a b::ereal_wrapper
    by(cases a, all \<open>cases b\<close>)
      (auto simp add: plus_ereal_wrapper_def minus_ereal_wrapper_def
                         less_ereal_wrapper_def less_eq_ereal_wrapper_def)
 show " 0 + a = a" for a::ereal_wrapper
    by(cases a)
      (auto simp add: plus_ereal_wrapper_def zero_ereal_wrapper_def)
  show 
"\<And>(a::ereal_wrapper) b c. a + b + c = a + (b + c)"
"\<And>(a::ereal_wrapper) b. a + b = b + a"
"\<And>a::ereal_wrapper. 0 - a = 0"
"\<And>(x::ereal_wrapper) y. (x < y) = (x \<le> y \<and> \<not> y \<le> x)"
"\<And>x::ereal_wrapper. x \<le> x"
"\<And>(x::ereal_wrapper) y z. x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
"\<And>(x::ereal_wrapper) y. x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
"\<And>(a::ereal_wrapper) b c. a - b - c = a - (b + c)"
"\<And>a b::ereal_wrapper. a - b \<le> a"
    using  min.commute 
    by(auto simp add: zero_ereal_wrapper_def minus_ereal_wrapper_def
                      plus_ereal_wrapper_def min.assoc 
                      less_eq_ereal_wrapper_def less_ereal_wrapper_def
               intro: the_ereal.elims )
qed
end

typedef pos_real = "{x::real | x. x \<ge> 0}"
  morphisms real_of_pos_real pos_real
  by auto
print_theorems

find_theorems "_::pos_real"

code_datatype pos_real 
setup_lifting type_definition_pos_real


lift_definition plus::"pos_real \<Rightarrow> pos_real \<Rightarrow> pos_real" 
    is "\<lambda> x y. ( x +  y)"
  by simp

lift_definition one::"pos_real" 
    is "1"
  by simp

lift_definition zero::"pos_real" 
    is "0"
  by simp

lemmas [code abstype] = pos_real.real_of_pos_real_inverse
real_of_pos_real_inject plus_def one_def zero_def

declare [[coercion_enabled]]

instantiation pos_real::numeral
begin


definition "plus_pos_real (x::pos_real) y
  = plus x y"

instance proof
  show "\<And> (a::pos_real) b c. a + b + c = a + (b + c)"
    apply(auto simp add: plus_pos_real_def) 
    sorry
qed
end

value "(1::pos_real)"
lemma "(1::pos_real) = undefined" 