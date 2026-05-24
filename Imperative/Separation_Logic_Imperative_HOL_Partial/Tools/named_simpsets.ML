(*
Named simpsets. Derived from named_theorems.ML
*)

signature NAMED_SIMPSETS =
sig
  val get: Proof.context -> string -> simpset
  val clear: string -> Context.generic -> Context.generic
  val map: string -> (simpset -> simpset) -> Context.generic -> Context.generic
  val map_ctxt: string -> (Proof.context -> Proof.context) -> Context.generic -> Context.generic
  
  val put: string -> Proof.context -> Proof.context
  
  val get_all: Proof.context -> simpset Name_Space.table
  
  
  val add_simp: string -> thm -> Context.generic -> Context.generic
  val del_simp: string -> thm -> Context.generic -> Context.generic

  val add_cong: string -> thm -> Context.generic -> Context.generic
  val del_cong: string -> thm -> Context.generic -> Context.generic

  val add_procs: string -> simproc list -> Context.generic -> Context.generic
  val del_procs: string -> simproc list -> Context.generic -> Context.generic
  
    
  val add_split: string -> thm -> Context.generic -> Context.generic
  val del_split: string -> thm -> Context.generic -> Context.generic
    
  val add_attr: string -> attribute
  val del_attr: string -> attribute
  
  val add_cong_attr: string -> attribute
  val del_cong_attr: string -> attribute
  
  val add_split_attr: string -> attribute
  val del_split_attr: string -> attribute
  
  val check: Proof.context -> xstring * Position.T -> string

  val declare: binding -> simpset option -> local_theory -> local_theory
  val declare_cmd: binding -> (xstring * Position.T) option -> local_theory -> local_theory
  
  (* Convenience *)
  val simp_tac: string -> thm list -> Proof.context -> int -> tactic
  val asm_simp_tac: string -> thm list -> Proof.context -> int -> tactic
  val full_simp_tac: string -> thm list -> Proof.context -> int -> tactic
  val asm_full_simp_tac: string -> thm list -> Proof.context -> int -> tactic

  val rewrite: string -> thm list -> Proof.context -> conv  
  val asm_rewrite: string -> thm list -> Proof.context -> conv  
  val full_rewrite: string -> thm list -> Proof.context -> conv  
  val asm_full_rewrite: string -> thm list -> Proof.context -> conv  

  val simplify: string -> thm list -> Proof.context -> thm -> thm  
  val asm_simplify: string -> thm list -> Proof.context -> thm -> thm
  val full_simplify: string -> thm list -> Proof.context -> thm -> thm
  val asm_full_simplify: string -> thm list -> Proof.context -> thm -> thm

  
  val named_ss_mod: Method.modifier parser
      
end;

structure Named_Simpsets: NAMED_SIMPSETS =
struct

(* context data *)

structure Data = Generic_Data
(
  type T = simpset Name_Space.table;
  val empty: T = Name_Space.empty_table "named-simpset";
  val merge : T * T -> T = Name_Space.join_tables (K merge_ss);
);


val content = Name_Space.get o Data.get

val get = content o Context.Proof;
  
val get_all = Data.get o Context.Proof


fun put name ctxt = put_simpset (get ctxt name) ctxt

fun map name f context =
  (content context name; Data.map (Name_Space.map_table_entry name f) context);

fun map_ctxt name f context = map name (simpset_map (Context.proof_of context) f) context


(* maintain content *)

fun clear name = map_ctxt name clear_simpset;

fun add_simp name thm = map_ctxt name (Simplifier.add_simp thm)
fun del_simp name thm = map_ctxt name (Simplifier.del_simp thm)

fun add_cong name thm = map_ctxt name (Simplifier.add_cong thm)
fun del_cong name thm = map_ctxt name (Simplifier.del_cong thm)

fun add_procs name procs = map_ctxt name (fn ctxt => ctxt addsimprocs procs)
fun del_procs name procs = map_ctxt name (fn ctxt => ctxt delsimprocs procs)


fun add_split name thm = map_ctxt name (Splitter.add_split thm)
fun del_split name thm = map_ctxt name (Splitter.del_split thm)

val add_attr = Thm.declaration_attribute o add_simp;
val del_attr = Thm.declaration_attribute o del_simp;

val add_cong_attr = Thm.declaration_attribute o add_cong;
val del_cong_attr = Thm.declaration_attribute o del_cong;

val add_split_attr = Thm.declaration_attribute o add_split;
val del_split_attr = Thm.declaration_attribute o del_split;


(* check *)

fun check ctxt = let val context = Context.Proof ctxt in Name_Space.check context (Data.get context) #> #1 end


(* declaration *)

fun new_entry binding init = let
  fun decl _ context = let
    val sstab = Data.get context
    val ss = the_default (Raw_Simplifier.clear_simpset (Context.proof_of context) |> simpset_of) init
    val (_,sstab) = Name_Space.define context true (binding,ss) sstab
  in Data.put sstab context end  
  
in
  Local_Theory.declaration {syntax=false, pervasive=true, pos=Position.none} decl
end    


fun declare binding init lthy =
  let
    val lthy' = lthy |> new_entry binding init
  in (lthy') end;

  
fun declare_cmd binding init_src lthy = let
  val init = Option.map (get lthy o check lthy) init_src
in
  declare binding init lthy
end
  
  
val named_simpset_attr = 
  (Args.context -- Scan.lift Args.name_position) 
  :|-- (fn (ctxt,raw_binding) => let val name = check ctxt raw_binding in
       (Scan.lift (Args.$$$ "simp") |-- Attrib.add_del (add_attr name) (del_attr name))
    || (Scan.lift (Args.$$$ "cong") |-- Attrib.add_del (add_cong_attr name) (del_cong_attr name))
    || (Scan.lift (Args.$$$ "split") |-- Attrib.add_del (add_split_attr name) (del_split_attr name))
    || Attrib.add_del (add_attr name) (del_attr name)
  end
  )
  
val _ = Theory.setup
  (Attrib.setup \<^binding>\<open>named_ss\<close> named_simpset_attr "Modify named simpsets")

val put_named_simpset_attr =
  (Args.context -- Scan.lift Args.name_position) >> (fn (ctxt,raw_binding) => let
    val name = check ctxt raw_binding
    val attr = Thm.declaration_attribute (fn _ => Context.map_proof (put name))
  in attr
  end)     
  
val _ = Theory.setup
  (Attrib.setup \<^binding>\<open>put_named_ss\<close> put_named_simpset_attr "Activate named simpset")
  
  
local

(* TODO: Redundancy from simplifier.ML, which does not export these values! *)
val no_asmN = "no_asm";
val no_asm_useN = "no_asm_use";
val no_asm_simpN = "no_asm_simp";

fun conv_mode x =
  ((Args.parens (Args.$$$ no_asmN) >> K simplify ||
    Args.parens (Args.$$$ no_asm_simpN) >> K asm_simplify ||
    Args.parens (Args.$$$ no_asm_useN) >> K full_simplify ||
    Scan.succeed asm_full_simplify) |> Scan.lift) x;

fun simp_aux ctxt ((f,NONE),thms) = 
  f ((if null thms then I else Raw_Simplifier.clear_simpset)
        ctxt addsimps thms)    
  | simp_aux ctxt ((f,SOME raw_name),thms) = let
      val name = check ctxt raw_name
      val ctxt = put name ctxt addsimps thms
    in
      f ctxt
    end
        
in

val simplified = 
  conv_mode 
  -- Scan.option (Scan.lift (Parse.$$$ "uses" |-- Args.name_position)) 
  -- Attrib.thms >>
  (fn (fnt as (_,thms)) => 
    Thm.rule_attribute thms (fn context =>
      simp_aux (Context.proof_of context) fnt));

val _ = Theory.setup
   (Attrib.setup \<^binding>\<open>simplified\<close> simplified "simplified rule");
      
end;
  
  
  
(* ML antiquotation *)

val _ = Theory.setup
  (ML_Antiquotation.inline \<^binding>\<open>named_simpset\<close>
    (Args.context -- Scan.lift (Args.name_position) >>
      (fn (ctxt, name) => ML_Syntax.print_string (check ctxt name))));


(* Method modifiers *)            
val named_ss_mod = Args.$$$ "named_ss" |-- Parse.position Parse.name --| Args.colon 
  >> (fn raw_binding => {
    init = (fn ctxt => put (check ctxt raw_binding) ctxt ),
    attribute = Simplifier.simp_add, 
    pos = \<^here>
  })


(* Convenience *)      
      
  fun simp_tac ns thms ctxt = Simplifier.simp_tac (put ns ctxt addsimps thms)
  fun asm_simp_tac ns thms ctxt = Simplifier.asm_simp_tac (put ns ctxt addsimps thms)
  fun full_simp_tac ns thms ctxt = Simplifier.full_simp_tac (put ns ctxt addsimps thms)
  fun asm_full_simp_tac ns thms ctxt = Simplifier.asm_full_simp_tac (put ns ctxt addsimps thms)
  
  fun simplify ns thms ctxt = Simplifier.simplify (put ns ctxt addsimps thms)
  fun asm_simplify ns thms ctxt = Simplifier.asm_simplify (put ns ctxt addsimps thms)
  fun full_simplify ns thms ctxt = Simplifier.full_simplify (put ns ctxt addsimps thms)
  fun asm_full_simplify ns thms ctxt = Simplifier.asm_full_simplify (put ns ctxt addsimps thms)

  fun rewrite ns thms ctxt = Simplifier.rewrite (put ns ctxt addsimps thms)
  fun asm_rewrite ns thms ctxt = Simplifier.asm_rewrite (put ns ctxt addsimps thms)
  fun full_rewrite ns thms ctxt = Simplifier.full_rewrite (put ns ctxt addsimps thms)
  fun asm_full_rewrite ns thms ctxt = Simplifier.asm_full_rewrite (put ns ctxt addsimps thms)
      
                  
end;
