theory General_ML_Tools
imports Main
begin
ML \<open>
  infix 0 THEN_ELSE' SOLVED_THEN_ELSE
  infix 1 THEN_ALL_NEW_FWD

  signature BASIC_RF2_UTIL = sig

    (** Util **)  
    val yield_singleton2: ('a list -> 'b -> ('c * 'd list) * 'e) -> 'a -> 'b -> ('c * 'd) * 'e
    val map_option: ('a -> 'b) -> 'a option -> 'b option

    val last: 'a list -> 'a
    val butlast: 'a list -> 'a list 
    
    val img_ord: ('a -> 'b) -> 'b ord -> 'a ord
    
    
    (* Extract first element for which given predicate holds from list *)
    val extract_first: ('a -> bool) -> 'a list -> ('a * 'a list) option
    
    (* groups list by relation, preserve order *)
    val group_by: ('a * 'a -> bool) -> 'a list -> 'a list list
    
    
    (** Terms **)  
    val is_Abs: term -> bool
    val is_App: term -> bool
    val has_Var: term -> bool

    val split_binop: (term -> term*term) -> term -> term list
    val list_binop_right: (term*term -> term) -> term list -> term
    val list_binop_right': term -> (term*term -> term) -> term list -> term
    
    val list_conjs: term list -> term
    
    (** Tactics **)
    val rprems_tac: Proof.context -> int -> tactic
    val rprem_tac: int -> Proof.context -> int -> tactic
    val elim_tac: Proof.context -> thm list -> int -> tactic
    val elim_determ_tac: Proof.context -> thm list -> int -> tactic
    val intro_tac: Proof.context -> thm list -> int -> tactic
    val intro_determ_tac: Proof.context -> thm list -> int -> tactic
    (*val intro1_tac: Proof.context -> thm list -> int -> tactic
    val intro1_determ_tac: Proof.context -> thm list -> int -> tactic*)
    val fo_resolve_tac: thm list -> Proof.context -> int -> tactic
 
    (* With NO_MATCH *)
    val simp_only_tac: thm list -> Proof.context -> int -> tactic
    val full_simp_only_tac: thm list -> Proof.context -> int -> tactic
    val asm_simp_only_tac: thm list -> Proof.context -> int -> tactic
    val asm_full_simp_only_tac: thm list -> Proof.context -> int -> tactic
    
    
    (* Eta contraction *)
    val eta_tac: int -> tactic
    
    
    (** Tacticals **)
    (*** Forward versions of common tacticals. Useful for goals with schematics. *)
    val INTERVAL_FWD: (int -> tactic) -> int -> int -> tactic
    val THEN_ALL_NEW_FWD: (int -> tactic) * (int -> tactic) -> (int -> tactic)
    val REPEAT_ALL_NEW_FWD: (int -> tactic) -> (int -> tactic)
    val ALL_GOALS_FWD': (int -> tactic) -> (int -> tactic)
    val ALL_GOALS_FWD: (int -> tactic) -> tactic

    (*** Subgoal-aware repeat *)    
    val REPEAT_DETERM': (int -> tactic) -> (int -> tactic)
    val REPEAT': (int -> tactic) -> (int -> tactic)

    val REPEAT_DETERM1': (int -> tactic) -> (int -> tactic)
    val REPEAT1': (int -> tactic) -> (int -> tactic)
        
    (* Narrow down to this subgoal *)
    val SELECT_GOAL' : (int -> tactic) -> int -> tactic
    
    (*** Fail, if specified subgoal does not exist *)
    val IF_EXGOAL: (int -> tactic) -> (int -> tactic)
    (*** Condition on subgoal. Eta-contracts term.  *)
    val COND': (term -> bool) -> (int -> tactic)
    (*** Condition on subgoal's conclusion. Eta-contracts term. *)
    val CONCL_COND': (term -> bool) -> (int -> tactic)
      
    (* Tactic that depends on subgoal term structure. Eta-contracts term. *)
    val WITH_subgoal: (term -> int -> tactic) -> int -> tactic
    (* Tactic that depends on subgoal's conclusion term structure. Eta-contracts term. *)
    val WITH_concl: (term -> int -> tactic) -> int -> tactic
    (* Tactic that depends on subgoal's premises term structure. Eta-contracts terms. *)
    val WITH_prems: (term list -> int -> tactic) -> int -> tactic
    
    
    val THEN_ELSE': (int -> tactic) * ((int -> tactic) * (int -> tactic)) -> (int -> tactic)
    val APPEND_LIST': (int -> tactic) list -> int -> tactic
    
    (* Guard tac2 by tac1: If tac1 succeeds, also execute tac2. Otherwise succeed. *)
    val GUARD': (int -> tactic) -> (int -> tactic) -> (int -> tactic)
    
    (* Execute the or else part depending on whether first tactic solved goal *)
    val SOLVED_THEN_ELSE: tactic * (tactic * tactic) -> tactic
    
    (* Execute second tactic if first tactic did not solve the goal *)
    val IF_NOT_SOLVED': (int -> tactic) -> (int -> tactic) -> (int -> tactic) 
    
    (* Succeed with unchanged goal if tactic succeeds, fail otherwise *)
    val CAN: tactic -> tactic
    val CAN': (int -> tactic) -> (int -> tactic)
    
    
  end

  signature RF2_UTIL = sig
    include BASIC_RF2_UTIL
    (** Isabelle-ML Extensions **)

    
    (** Simplified Term Structure *)
    val tstruct: term -> string
    
    (** Core type inference *)
    val infer_types_simple: Proof.context -> term -> term
    
    (** Theorem Handling **)
    
    (* Destruct unconditional definition theorem, i.e., lhs=rhs or lhs\<equiv>rhs *)
    val dest_def_thm: thm -> term * term 
    
    (* Adjust bound names in split theorem to match on LHS and RHS. 
      This is a workaround: Names should match by default!
    *)
    val adjust_split_thm_names: Proof.context -> thm -> thm
    
    (* Terms *)
    (* Match pattern against term, and return list of values for non-dummy
      variables. A variable is considered dummy if its name starts with 
      an underscore (_)*)
    val fo_matchp: theory -> cterm -> term -> term list option
    val fo_matches: theory -> cterm -> term -> bool

    (* Rename all variables in a term to a uniform naming scheme. 
      Used to compare theorems, even if variables have different names.
      NOTE: Still needs `aconv` for comparison, as Abs is not renamed.
    *)
    val anorm_typ: typ -> typ
    val anorm_term: term -> term
    val anorm_thm: Proof.context -> thm -> thm
    val anorm_thm_global: thm -> thm
    
    (* Order a list of items such that more specific items come
       before less specific ones. The term to be compared is
       extracted by a function that is given as parameter.
    *)
    val subsume_sort: ('a -> term) -> Proof.context -> 'a list -> 'a list
    val subsume_sort_global: ('a -> term) -> theory -> 'a list -> 'a list
    val subsume_sort_gen: ('a -> term) -> Context.generic 
      -> 'a list -> 'a list
    
    
    (** More on subgoals  *)
    (*
    val fix_params: term -> term
    val dest_goal: term -> term list * term
    val goal_concl: term -> term
    val goal_prems: term -> term list
    *)
    
    (** Conversions *)
    (* Debugging *)
    val trace_conv: conv

    (* Apply conversion to Q x\<^sub>1...x\<^sub>n in \<And>x\<^sub>1 ... x\<^sub>n. ... \<Longrightarrow> PROP (Q x\<^sub>1...x\<^sub>n) *)    
    val HHF_concl_conv: (Proof.context -> conv) -> Proof.context -> conv
    (* Apply conversion to all P\<^sub>i x\<^sub>1...x\<^sub>n in \<And>x\<^sub>1 ... x\<^sub>n. P\<^sub>1 x\<^sub>1...x\<^sub>n \<Longrightarrow> ... \<Longrightarrow> P\<^sub>m x\<^sub>1...x\<^sub>n \<Longrightarrow> PROP (Q x\<^sub>1...x\<^sub>n) *)    
    val HHF_prems_conv: (Proof.context -> conv) -> Proof.context -> conv
    (* Apply conversion to Q x\<^sub>1...x\<^sub>n in \<And>x\<^sub>1 ... x\<^sub>n. ... \<Longrightarrow> Trueprop (Q x\<^sub>1...x\<^sub>n) *)
    val HOL_concl_conv: (Proof.context -> conv) -> Proof.context -> conv

    (* Convert nth premise *)    
    val nth_prem_conv: int -> conv -> conv
    
    (* Prove premises of theorem by given tactics. Warning: Simultaneous semantics, 
      will fail/misbehave if tactic instantiates schematic that occurs in later premise to be proved *)
    val prove_prems: Proof.context -> thm -> (Proof.context -> int -> tactic) option list -> thm
        
    
    (* Apply conversion to direct subterms, fail if conversion fails for a subterm *)
    val sub_conv':  (Proof.context -> conv) -> Proof.context -> conv
    
    (* Conversion that transforms a term, and then uses a tactic to prove equality *)
    val cfg_trace_f_tac_conv: bool Config.T
    val f_tac_conv: Proof.context -> (term -> term) -> tactic -> conv

    (* Conversion wrt. congruence rules. The rules must have the form a\<equiv>b \<Longrightarrow> c\<equiv>d. *)
    val cong_rls_conv: thm list -> conv -> conv
    
    
    (* Roughly the simplified attribute *)
    val simplified: thm list -> Proof.context -> thm -> thm
    
    (* Simplifier Conversions *)  
    val rewrite: thm list -> Proof.context -> conv  
    val asm_rewrite: thm list -> Proof.context -> conv  
    val full_rewrite: thm list -> Proof.context -> conv  
    val asm_full_rewrite: thm list -> Proof.context -> conv  
    

    (* Parsing props with patterns *)
    val read_prop_pattern: Proof.context -> string -> term
    val args_prop_pattern: term context_parser

    (* Parse mode and return specified value *)    
    val parse_mode': string * 'a -> 'a parser
    (* Parse one of specified modes *)
    val parse_multimode: (string * 'a) list -> Token.T list -> 'a * Token.T list
    (* Parse one of specified modes, default to specified value *)
    val parse_multimode_dflt: 'a -> (string * 'a) list -> Token.T list -> 'a * Token.T list
  end

  structure RF2_Util : RF2_UTIL = struct

    fun yield_singleton2 f x c = let val ((r1,r2),c) = f [x] c in ((r1,the_single r2),c) end
    
    fun map_option _ NONE = NONE
      | map_option f (SOME x) = SOME (f x)

    fun last [] = raise Match
      | last [a] = a
      | last (_::xs) = last xs
      
    fun butlast xs = let
      fun aux _ [] = raise Match
        | aux acc [_] = rev acc
        | aux acc (x::xs) = aux (x::acc) xs
    in
      aux [] xs
    end  
      
    fun img_ord f ordb = ordb o apply2 f
    
    fun extract_first _ [] = (NONE)
      | extract_first P (x::xs) = 
          if P x then SOME (x,xs) 
          else map_option (apsnd (curry op :: x)) (extract_first P xs)
    
    (*
      groups a list by a relation: 
        Each element is combined with all succeeding related elements, otherwise, th order 
        of the list is preserved.
        
        group_by op= [1,2,3,2,3,4] = [[1],[2,2],[3,3],[4]]
    *)
    fun group_by _ [] = []
      | group_by p (x::xs) = let
          fun rel y = p (x,y)
          val xs1 = filter rel xs
          val xs2 = filter_out rel xs
        in
          (x::xs1) :: group_by p xs2
        end
  
    fun is_Abs (Abs _) = true
      | is_Abs _ = false
  
    fun is_App (_$_) = true
      | is_App _ = false

    fun has_Var (Var _) = true
      | has_Var (Abs (_,_,t)) = has_Var t
      | has_Var (t1$t2) = has_Var t1 orelse has_Var t2
      | has_Var _ = false
          
    
    fun split_binop dest t = case try dest t of 
      NONE => [t]
    | SOME (l,r) => split_binop dest l @ split_binop dest r  
    
    fun list_binop_right _ [] = error "list_binop with empty list"
      | list_binop_right _ [x] = x
      | list_binop_right mk (x::xs) = mk (x, list_binop_right mk xs)

    fun list_binop_right' i _ [] = i
      | list_binop_right' _ mk xs = list_binop_right mk xs
            
    val list_conjs = list_binop_right' @{const True} HOLogic.mk_conj
      
    
    (* Resolve with premises. Copied and adjusted from Goal.assume_rule_tac. *)
    fun rprems_tac ctxt = Goal.norm_hhf_tac ctxt THEN' CSUBGOAL (fn (goal, i) =>
      let
        fun non_atomic (Const (@{const_name Pure.imp}, _) $ _ $ _) = true
          | non_atomic (Const (@{const_name Pure.all}, _) $ _) = true
          | non_atomic _ = false;

        val ((_, goal'), ctxt') = Variable.focus_cterm NONE goal ctxt;
        val goal'' = Drule.cterm_rule 
          (singleton (Variable.export ctxt' ctxt)) goal';
        val Rs = filter (non_atomic o Thm.term_of) 
          (Drule.strip_imp_prems goal'');

        val ethms = Rs |> map (fn R =>
          (Simplifier.norm_hhf ctxt (Thm.trivial R)));
      in eresolve_tac ctxt ethms i end
      );

    (* Resolve with premise. Copied and adjusted from Goal.assume_rule_tac. *)
    fun rprem_tac n ctxt = Goal.norm_hhf_tac ctxt THEN' CSUBGOAL (fn (goal, i) =>
      let
        val ((_, goal'), ctxt') = Variable.focus_cterm NONE goal ctxt;
        val goal'' = Drule.cterm_rule 
          (singleton (Variable.export ctxt' ctxt)) goal';

        val R = nth (Drule.strip_imp_prems goal'') (n - 1)
        val rl = Simplifier.norm_hhf ctxt (Thm.trivial R)
      in
        eresolve_tac ctxt [rl] i
      end
      );
  
      
    val eta_tac = CONVERSION (Thm.eta_conversion)  
      
        
    fun dest_def_thm thm = case Thm.prop_of thm of
      (@{const Trueprop}$(Const (@{const_name "HOL.eq"},_)$lhs$rhs)) => (lhs,rhs)
    | (Const (@{const_name Pure.eq},_)$lhs$rhs) => (lhs,rhs)  
    | _ => raise THM("dest_def_thm",1,[thm])

    fun adjust_split_thm_names ctxt thm = let
        
      val (lhs,rhs) = Thm.prop_of thm
        |> HOLogic.dest_Trueprop
        |> HOLogic.dest_eq
      
      fun dest_alls (Const (@{const_name All},_)$(Abs (x,_,t))) = x::dest_alls t
        | dest_alls _ = []
      
      val namess = HOLogic.dest_conj rhs |> map dest_alls
      
      fun eta_long_var (t as Var (_,T)) names = let
        val Ts = binder_types T
        val args = names ~~ Ts |> map Free
      in 
        list_comb (t,args) |> fold_rev lambda args
      end
      | eta_long_var _ _ = raise Match
      
      
      val lhsvars = dest_comb lhs |> snd |> strip_comb |> snd |> butlast
      
      val substs = lhsvars ~~ namess
        |> map (fn (x,names) => (dest_Var x,Thm.cterm_of ctxt (eta_long_var x names)))
        |> Vars.make
        
      val thm = Thm.instantiate (TVars.empty,substs) thm
    in
      thm
    end      
    
    
    
    fun fo_matchp thy cpat t = let
      fun ignore (Var ((name,_),_)) = String.isPrefix "_" name
        | ignore _ = true;

      val pat = Thm.term_of cpat;
      val pvars = fold_aterms (
        fn t => fn l => if is_Var t andalso not (ignore t)
          then t::l else l
      ) pat [] |> rev
      val inst = Pattern.first_order_match thy (pat,t) 
        (Vartab.empty,Vartab.empty);
    in SOME (map (Envir.subst_term inst) pvars) end 
    handle Pattern.MATCH => NONE;

    val fo_matches = is_some ooo fo_matchp


    fun anorm_typ ty = let
      val instT = Term.add_tvarsT ty []
      |> map_index (fn (i,(n,s)) => (n,TVar (("t"^string_of_int i,0),s)))
      val ty = Term.typ_subst_TVars instT ty;
    in ty end;

    fun anorm_term t = let
      val instT = Term.add_tvars t []
      |> map_index (fn (i,(n,s)) => (n,TVar (("t"^string_of_int i,0),s)))
      val t = Term.subst_TVars instT t;
      val inst = Term.add_vars t []
      |> map_index (fn (i,(n,s)) => (n,Var (("v"^string_of_int i,0),s)))
      val t = Term.subst_Vars inst t;
    in t end;

    fun anorm_thm ctxt thm = let
      val cT = Thm.ctyp_of ctxt
      val ct = Thm.cterm_of ctxt
      
      val t = Thm.full_prop_of thm
      
      val instT = Term.add_tvars t []
      |> map_index (fn (i,(n,s)) => ((n,s),cT (TVar (("t"^string_of_int i,0),s))))
      |> TVars.make

      val thm = Thm.instantiate (instT,Vars.empty) thm
      
      val t = Thm.full_prop_of thm
      val inst = Term.add_vars t []
      |> map_index (fn (i,(n,T)) => ((n,T),ct (Var (("v"^string_of_int i,0),T))))
      |> Vars.make
      
      val thm = Thm.instantiate (TVars.empty, inst) thm
        |> Conv.fconv_rule Drule.beta_eta_conversion
        
    in thm end;
    
    fun anorm_thm_global thm = anorm_thm (Proof_Context.init_global (Thm.theory_of_thm thm)) thm
    
    fun subsume_sort_global f thy items = let
      val rhss = map (Envir.beta_eta_contract o f) items
      fun freqf thy net rhs = Net.match_term net rhs 
        |> filter (fn p => Pattern.matches thy (p,rhs))
        |> length

      val net = fold 
        (fn rhs => Net.insert_term_safe (op =) (rhs,rhs)) rhss Net.empty 

      val freqs = map (freqf thy net) rhss

      val res = freqs ~~ items 
        |> sort (rev_order o int_ord o apply2 fst)
        |> map snd
  
    in res end

    fun subsume_sort f = subsume_sort_global f o Proof_Context.theory_of
    fun subsume_sort_gen f = subsume_sort_global f o Context.theory_of

    (*
    fun fix_params (Const (@{const_name Pure.all},_)$Abs(x,T,t)) = let
            val vt = Free (singleton (Term.rename_wrt_term t) (x,T))
            val t = subst_bound (vt,t)
          in
            fix_params t
          end
      | fix_params t = t
    
    
    fun dest_goal t = let val t = fix_params t in (Logic.strip_imp_prems t, Logic.strip_imp_concl t) end
    val goal_concl = fix_params #> Logic.strip_imp_concl
    val goal_prems = fix_params #> Logic.strip_imp_prems
    *)
    
    (* Apply tactic to subgoals in interval, in a forward manner, skipping over
      emerging subgoals *)
    fun INTERVAL_FWD tac l u st =
      if l>u then all_tac st 
      else (tac l THEN (fn st' => let
          val ofs = Thm.nprems_of st' - Thm.nprems_of st;
        in
          if ofs < ~1 then raise THM (
            "INTERVAL_FWD: Tac solved more than one goal",~1,[st,st'])
          else INTERVAL_FWD tac (l+1+ofs) (u+ofs) st'
        end)) st;
    
    (* Apply tac2 to all subgoals emerged from tac1, in forward manner. *)
    fun (tac1 THEN_ALL_NEW_FWD tac2) i st =
      (tac1 i 
        THEN (fn st' => INTERVAL_FWD tac2 i (i + Thm.nprems_of st' - Thm.nprems_of st) st')
      ) st;

    fun REPEAT_ALL_NEW_FWD tac =
      tac THEN_ALL_NEW_FWD (TRY o (fn i => REPEAT_ALL_NEW_FWD tac i));
    
    
    (* Repeat tac on subgoal. Determinize each step. 
       Stop if tac fails or subgoal is solved. *)
    fun REPEAT_DETERM' tac i st = let
      val n = Thm.nprems_of st 
    in
      REPEAT_DETERM (COND (has_fewer_prems n) no_tac (tac i)) st
    end

    fun REPEAT' tac i st = let
      val n = Thm.nprems_of st 
    in
      REPEAT (COND (has_fewer_prems n) no_tac (tac i)) st
    end

    fun REPEAT_DETERM1' tac i st = let
      val n = Thm.nprems_of st 
    in
      REPEAT_DETERM1 (COND (has_fewer_prems n) no_tac (tac i)) st
    end

    fun REPEAT1' tac i st = let
      val n = Thm.nprems_of st 
    in
      REPEAT1 (COND (has_fewer_prems n) no_tac (tac i)) st
    end
    
    fun SELECT_GOAL' tac = SELECT_GOAL (ALLGOALS tac)
    
    (* Apply tactic to all goals in a forward manner.
      Newly generated goals are ignored.
    *)
    fun ALL_GOALS_FWD' tac i st =
      (tac i THEN (fn st' => 
        let
          val i' = i + Thm.nprems_of st' + 1 - Thm.nprems_of st;
        in
          if i' <= Thm.nprems_of st' then
            ALL_GOALS_FWD' tac i' st'
          else
            all_tac st'
        end
      )) st;

    fun ALL_GOALS_FWD tac = ALL_GOALS_FWD' tac 1;
    
    fun IF_EXGOAL tac i st = if i <= Thm.nprems_of st then
      tac i st
    else no_tac st;
    
    fun COND' P = IF_EXGOAL (fn i => fn st => 
      (if P (Thm.prop_of st |> curry Logic.nth_prem i |> Envir.eta_contract) then
      all_tac st else no_tac st) 
      handle TERM _ => no_tac st
      | Pattern.MATCH => no_tac st
    )

    fun CONCL_COND' P = IF_EXGOAL (fn i => fn st => 
      (if P (Thm.prop_of st |> (fn t => Logic.concl_of_goal t i) |> Envir.eta_contract) then
      all_tac st else no_tac st) 
      handle TERM _ => no_tac st
      | Pattern.MATCH => no_tac st
    )

    
    (* TODO/FIXME: There seem to be no guarantees when eta-long forms are introduced by unification.
      So, we have to expect eta-long forms everywhere, which may be a problem when matching terms
      syntactically.
    *)
    fun WITH_subgoal tac = 
      (*CONVERSION Thm.eta_conversion THEN' *)
      IF_EXGOAL (fn i => fn st => tac (nth (Thm.prems_of st) (i - 1) |> Envir.eta_contract) i st)

    fun WITH_concl tac = 
      (*CONVERSION Thm.eta_conversion THEN' *)
      IF_EXGOAL (fn i => fn st => 
        tac (Logic.concl_of_goal (Thm.prop_of st) i |> Envir.eta_contract) i st
      )
    
    fun WITH_prems tac = 
      (*CONVERSION Thm.eta_conversion THEN' *)
      IF_EXGOAL (fn i => fn st => 
        tac (Logic.prems_of_goal (Thm.prop_of st) i |> map Envir.eta_contract) i st
      )
    
    fun APPEND_LIST' tacs = fold_rev (curry (op APPEND')) tacs (K no_tac);
    
    fun (tac1 THEN_ELSE' (tac2,tac3)) x = tac1 x THEN_ELSE (tac2 x,tac3 x);  
        
    fun GUARD' tac1 tac2 = tac1 THEN_ELSE' (tac2, K all_tac)
    
    fun (tac1 SOLVED_THEN_ELSE (tac2,tac3)) st =
      tac1 st 
      |> Seq.maps (fn st' => 
           if Thm.nprems_of st' < Thm.nprems_of st then tac2 st' (* Solved goal *)
           else tac3 st' (* Did not solve goal *)
         )
         
    fun IF_NOT_SOLVED' tac1 tac2 i st =
      tac1 i st 
      |> Seq.maps (fn st' => 
          if Thm.nprems_of st' < Thm.nprems_of st then Seq.single st' (* Solved goal *)
          else tac2 i st' (* Apply tac2 to (first) unsolved goal *)
          )  
    
    fun CAN tac st =
      case Seq.pull (tac st) of NONE => Seq.empty | _ => Seq.single st

    fun CAN' tac i = CAN (tac i)  
                
    fun elim_tac ctxt thms = REPEAT_ALL_NEW (ematch_tac ctxt thms)
    fun elim_determ_tac ctxt thms = REPEAT_ALL_NEW (DETERM o ematch_tac ctxt thms)
    
    fun intro_tac ctxt thms = REPEAT_ALL_NEW (match_tac ctxt thms)
    fun intro_determ_tac ctxt thms = REPEAT_ALL_NEW (DETERM o match_tac ctxt thms)
    
    (*fun intro1_tac ctxt thms = REPEAT1 o (match_tac ctxt thms)
    fun intro1_determ_tac ctxt thms = REPEAT_DETERM1' (match_tac ctxt thms)
    *)
        
    (* Resolve with rule. Use first-order unification.
      From cookbook, added exception handling *)
    fun fo_rtac thm = Subgoal.FOCUS (fn {context = ctxt, concl, ...} => 
    let
      val concl_pat = Drule.strip_imp_concl (Thm.cprop_of thm)
      val insts = Thm.first_order_match (concl_pat, concl)
    in
      resolve_tac ctxt [Drule.instantiate_normalize insts thm] 1
    end handle Pattern.MATCH => no_tac )

    fun gen_simp_only_tac tac thms ctxt = 
      tac (put_simpset HOL_basic_ss ctxt addsimprocs [@{simproc NO_MATCH}] addsimps thms)
    
    val simp_only_tac = gen_simp_only_tac simp_tac
    val asm_simp_only_tac = gen_simp_only_tac asm_simp_tac
    val full_simp_only_tac = gen_simp_only_tac full_simp_tac
    val asm_full_simp_only_tac = gen_simp_only_tac asm_full_simp_tac
    
    fun fo_resolve_tac thms ctxt = 
      FIRST' (map (fn thm => fo_rtac thm ctxt) thms);
    
    local
      fun par b s = if b then "("^s^")" else s
    
      fun psi_aux p env = let
        fun r (Const (n,_)) = Long_Name.base_name n
          | r (Var (n,_)) = Term.string_of_vname n
          | r (Free (n,_)) = n
          | r (Bound i) = nth env i
          | r (Abs (x,_,t)) = par p (let val x = singleton (Name.variant_list env) x in "\<lambda>"^x^". "^psi_aux false (x::env) t end)
          | r (t as _$_) = let
              val (f,args) = strip_comb t
              val f = psi_aux true env f
              val args = map (psi_aux true env) args |> space_implode " "
              val s = f^" "^args
            in par p s end    
      in
        r
      end
    in    
      val tstruct = psi_aux false []
    end

    
    (* Proposed by Makarius. 
      Lammich: added the schematic mode (no idea how general or core this is after all).
    *)
    fun infer_types_simple ctxt = let
      val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
    in
      singleton (Type_Infer_Context.infer_types ctxt) 
      #> singleton (Type_Infer.fixate ctxt false)
    end
    
    fun trace_conv ct = (tracing (@{make_string} ct); Conv.all_conv ct);
    
    fun HHF_concl_conv cnv = Conv.params_conv ~1 
      (fn ctxt => Conv.concl_conv ~1 (cnv ctxt));

    fun HHF_prems_conv cnv = Conv.params_conv ~1 
      (fn ctxt => Conv.prems_conv ~1 (cnv ctxt));
      
    fun HOL_concl_conv cnv = HHF_concl_conv (HOLogic.Trueprop_conv o cnv)
      
    fun nth_prem_conv 1 cv = Conv.implies_conv cv Conv.all_conv
      | nth_prem_conv n cv = Conv.implies_concl_conv (nth_prem_conv (n-1) cv)
    
        
    fun prove_prems ctxt thm tacs = let
      
      fun mk_cnv [] = Conv.all_conv
        | mk_cnv (NONE::xs) = Conv.implies_concl_conv (mk_cnv xs)
        | mk_cnv (SOME _::xs) = Conv.implies_conv (Object_Logic.atomize ctxt) (mk_cnv xs)
    
      (* Atomize relevant premises *)  
      val thm = Conv.fconv_rule (mk_cnv tacs) thm
        
      fun prove t tac = Goal.prove ctxt [] [] t (fn {context=ctxt, ...} => 
        ALLGOALS (
          REPEAT_DETERM' (match_tac ctxt @{thms allI impI}) (* TODO: Maybe apply atomize-rules in reverse *)
          THEN' tac ctxt
        ) 
      )
      
      fun proves [] _ = []
        | proves _ [] = []
        | proves (_::ps) (NONE::tacs) = asm_rl :: proves ps tacs
        | proves (p::ps) (SOME tac :: tacs) = prove p tac :: proves ps tacs
        
      (* Prove premises *)  
      val pthms = proves (Thm.prems_of thm) tacs
      
      val thm = thm OF pthms
    in
      thm
    end  
    
        
        
    local open Conv in

      fun sub_conv' conv ctxt ct = (case Thm.term_of ct of
        Abs _ => abs_conv (conv o snd) ctxt
      | _$_ => comb_conv (conv ctxt)  
      | _ => all_conv
      ) ct

    end          
        
        
            
    val cfg_trace_f_tac_conv = 
      Attrib.setup_config_bool @{binding trace_f_tac_conv} (K false)

    fun f_tac_conv ctxt f tac ct = let
    
      fun do_trace msg = if Config.get ctxt cfg_trace_f_tac_conv then tracing (msg ()) else ()
    
      val t = Thm.term_of ct
      val t' = f t
      val goal = Logic.mk_equals (t,t')
      val _ = do_trace (fn () => Syntax.string_of_term ctxt goal)

      val goal = Thm.cterm_of ctxt goal

      val thm = Goal.prove_internal ctxt [] goal (K tac) handle (exn as THM (msg,_,thms)) => (
        do_trace (fn () => Pretty.block [ Pretty.str "f_tac_conv, proof failed: ", Pretty.str msg, 
          Pretty.big_list "thms" (map (Thm.pretty_thm ctxt) thms)
            ] |> Pretty.string_of);
       Exn.reraise exn  
      )
    in
      thm
    end

    fun cong_rl_conv (conv:conv) rule ct = let
      val rule = Thm.incr_indexes (Thm.maxidx_of_cterm ct + 1) rule;
      val lhs = Thm.cprop_of rule |> Thm.dest_implies |> snd |> Thm.dest_equals_lhs;
      val rule = Thm.rename_boundvars (Thm.term_of lhs) (Thm.term_of ct) rule;
      val rule =
        Thm.instantiate (Thm.match (lhs, ct)) rule
          handle Pattern.MATCH => raise CTERM ("cong_rl_conv", [lhs, ct]);
      
      val lhs' = Thm.cprop_of rule |> Thm.dest_implies |> fst |> Thm.dest_equals_lhs;
          
    in rule OF [conv lhs'] end
    
    fun cong_rls_conv rules conv = 
      Conv.first_conv (map (cong_rl_conv conv) rules)

    
    fun simplified [] ctxt = asm_full_simplify ctxt
      | simplified thms ctxt = asm_full_simplify (Raw_Simplifier.clear_simpset ctxt addsimps thms)
        
      
    fun gen_rewrite f thms ctxt = f (put_simpset HOL_basic_ss ctxt addsimps thms)
    
    
    val rewrite = gen_rewrite Simplifier.rewrite
    val asm_rewrite = gen_rewrite Simplifier.asm_rewrite
    val full_rewrite = gen_rewrite Simplifier.full_rewrite
    val asm_full_rewrite = gen_rewrite Simplifier.asm_full_rewrite

    
    fun read_prop_pattern ctxt = Syntax.read_prop (Proof_Context.set_mode Proof_Context.mode_pattern ctxt)
    val args_prop_pattern = let open Args in Scan.peek (named_term o read_prop_pattern o Context.proof_of) end
    
     
    fun parse_mode' (name,res) = Args.parens (Args.$$$ name >> (K res))
  
    fun parse_multimode nrs = Scan.first (map parse_mode' nrs)
    fun parse_multimode_dflt dflt nrs = Scan.optional (parse_multimode nrs) dflt
         
  end

  structure Basic_RF2_Util = RF2_Util : BASIC_RF2_UTIL
  open Basic_RF2_Util
  
  
\<close>

method_setup rprems = \<open>(Scan.lift (Scan.option Parse.nat) >> (fn i => fn ctxt => 
  SIMPLE_METHOD' (
    case i of
      NONE => rprems_tac ctxt
    | SOME i => rprem_tac i ctxt
  )))\<close>
  \<open>resolve with premises\<close>

method_setup fo_rule = \<open>Attrib.thms >> (SIMPLE_METHOD' oo fo_resolve_tac)\<close>

method_setup mrule = \<open>
  (Attrib.thms >> (fn thms => fn ctxt => SIMPLE_METHOD' (match_tac ctxt thms)))
  \<close> \<open>match with intro rules\<close>

method_setup merule = \<open>
  (Attrib.thms >> (fn thms => fn ctxt => SIMPLE_METHOD' (ematch_tac ctxt thms)))
  \<close> \<open>match with elim rules\<close>
    
method_setup mdrule = \<open>
  (Attrib.thms >> (fn thms => fn ctxt => SIMPLE_METHOD' (dmatch_tac ctxt thms)))
  \<close> \<open>match with dest rules\<close>


method_setup instantiate = \<open>Scan.lift Args.var --| Scan.lift @{keyword "="} -- Args.term_pattern >> (
  fn (v,t) => fn ctxt => let
    val ct = Thm.cterm_of ctxt t |> @{print}
    fun tac st = Drule.infer_instantiate ctxt [(v,ct)] st
      |> Seq.single
    
  in
    SIMPLE_METHOD (tac)
  end)
\<close>

(* @{get_named_theorems name} : Proof.context -> thm list *)
ML \<open>
  local
    fun print name = "(fn ctxt => Named_Theorems.get ctxt " ^ ML_Syntax.print_string name ^ ")"
  in
    val _ = Theory.setup
    (ML_Antiquotation.inline_embedded \<^binding>\<open>get_named_theorems\<close>
      (Args.context -- Scan.lift Parse.embedded_position >>
        (fn (ctxt, name) => print (Named_Theorems.check ctxt name))));
  
  end
\<close>

(* @{pattern \<dots>} : term and @{pat_prop \<dots>} : term  *)
setup \<open>
  ML_Antiquotation.inline_embedded \<^binding>\<open>pattern\<close>
    (Args.term_pattern >> (ML_Syntax.atomic o ML_Syntax.print_term))
    
  #>  
  ML_Antiquotation.inline_embedded \<^binding>\<open>pat_prop\<close>
    (RF2_Util.args_prop_pattern >> (ML_Syntax.atomic o ML_Syntax.print_term))
\<close>

(*
method_setup with_notes = \<open>
  let
    fun note args ctxt =
      ctxt |> Proof_Context.note_thmss ""
         (Attrib.map_facts_refs (map (Attrib.attribute_cmd ctxt)) (Proof_Context.get_fact ctxt) args) |> snd
  
    fun modify args m thms (ctxt,st) = let 
      val ctxt = note args ctxt
    in
      m thms (ctxt,st)
    end
         
  in
    (Scan.lift Parse_Spec.name_facts -- (Scan.lift (Parse.$$$ "in") |-- Method.text_closure) >>
      (fn (args, text) => fn ctxt => modify args (Method.evaluate_runtime text ctxt)))
      
  end      
\<close> \<open>Locally note facts for method\<close>
*)

(*
method_setup use' = \<open>
    (Attrib.thms -- (Scan.lift (Parse.$$$ "in") |-- Method.text_closure) >>
      (fn (_, text) => fn ctxt => fn thms => Method.evaluate_runtime text ctxt thms))
\<close> "indicate context for method expression"
*)



experiment
begin
  named_theorems foo
  ML_val \<open>@{get_named_theorems foo} @{context}\<close>

(*  lemma "a o b = (\<lambda>x. a(b(x)))"
    apply (use' comp_def[simp] [[simp_trace]] in simp)
    done
*)    
  
end


ML_val \<open>
  fun assert_eq a b = if a=b then () else error("assert_eq " ^ @{make_string} a ^ " <> "^ @{make_string} b)

  val _ = assert_eq (group_by op= [1,3,2,3,4]) [[1],[3,3],[2],[4]]
  val _ = assert_eq  (group_by op= [1,2,3,2,3,4]) [[1],[2,2],[3,3],[4]]
  
  val _ = assert_eq  (group_by op= []) []
  
\<close>









end
