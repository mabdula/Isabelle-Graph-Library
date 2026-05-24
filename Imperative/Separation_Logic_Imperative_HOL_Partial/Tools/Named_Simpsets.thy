(*
  Named simpsets, analogously to named theorems.
  
  Author: Peter Lammich
  
  TODO: 
  
    Declare attributes with name of named simpset, instead of one global named_ss attribute!
  
    Initialize from merge of simpsets (?) This goes into direction of "locale expressions", don't overshoot here!
    
    Isar-Syntax for adding/removing simprocs
    
  
*)
section \<open>Named Simpsets\<close>
theory Named_Simpsets
imports General_ML_Tools
keywords "named_simpset" :: thy_decl and "print_named_simpset" :: diag
begin


  subsection \<open>Setup\<close>
  ML_file "named_simpsets.ML"
  
  ML \<open>
  val _ =
    Outer_Syntax.local_theory \<^command_keyword>\<open>named_simpset\<close>
      "declare named simpset"
      (Parse.binding -- Scan.option (\<^keyword>\<open>=\<close> |-- Parse.position Parse.embedded) >> uncurry Named_Simpsets.declare_cmd);
  \<close>
          
  ML \<open>      
  val _ = let      
    fun print_named_simpset_cmd name_src bang ctxt = let
      val name = Named_Simpsets.check ctxt name_src
    in
      Named_Simpsets.put name ctxt
      |> Simplifier.pretty_simpset bang
      |> Pretty.writeln
    end
        
  in
    Outer_Syntax.command \<^command_keyword>\<open>print_named_simpset\<close>
      "print named simpset"
      (Parse.position Parse.name -- Parse.opt_bang >> (fn (name_src,b) =>
        Toplevel.keep (print_named_simpset_cmd name_src b o Toplevel.context_of)))
        
  end                
  \<close>
  
  local_setup \<open> I
    #> Named_Simpsets.declare @{binding HOL_ss} (SOME HOL_ss)
    #> Named_Simpsets.declare @{binding HOL_basic_ss} (SOME HOL_basic_ss)
    #> Named_Simpsets.declare @{binding Main_ss} (SOME (simpset_of @{context}))
  \<close>

  (* TODO/FIXME/XXX: Is this the intended way how to add an attribute to simp?*)
  setup \<open>Simplifier.method_setup (Named_Simpsets.named_ss_mod :: Splitter.split_modifiers)\<close>
      
  named_simpset HOL_basic_ss_nomatch = HOL_basic_ss
  declaration \<open>fn _ => Named_Simpsets.map_ctxt @{named_simpset HOL_basic_ss_nomatch} (fn ctxt => ctxt addsimprocs [@{simproc NO_MATCH}])\<close>
  
  named_simpset HOL_ss_nomatch = HOL_ss
  declaration \<open>fn _ => Named_Simpsets.map_ctxt @{named_simpset HOL_ss_nomatch} (fn ctxt => ctxt addsimprocs [@{simproc NO_MATCH}])\<close>

  
  subsection \<open>Convenience\<close>
  ML \<open>
    (* simp-only tactics. Note the inclusion of NO_MATCH simproc. *)
    val simp_only_tac = Named_Simpsets.simp_tac @{named_simpset HOL_basic_ss_nomatch}
    val asm_simp_only_tac = Named_Simpsets.asm_simp_tac @{named_simpset HOL_basic_ss_nomatch}
    val full_simp_only_tac = Named_Simpsets.full_simp_tac @{named_simpset HOL_basic_ss_nomatch}
    val asm_full_simp_only_tac = Named_Simpsets.asm_full_simp_tac @{named_simpset HOL_basic_ss_nomatch}
  
    val scan_simp_only_options = RF2_Util.parse_multimode_dflt asm_full_simp_only_tac [
      ("no_asm",simp_only_tac),
      ("no_asm_simp",asm_simp_only_tac),
      ("no_asm_use",full_simp_only_tac)
    ]
    
    val rewrite_nm = Named_Simpsets.rewrite @{named_simpset HOL_basic_ss_nomatch}
    val asm_rewrite_nm = Named_Simpsets.asm_rewrite @{named_simpset HOL_basic_ss_nomatch}
    val full_rewrite_nm = Named_Simpsets.full_rewrite @{named_simpset HOL_basic_ss_nomatch}
    val asm_full_rewrite_nm = Named_Simpsets.asm_full_rewrite @{named_simpset HOL_basic_ss_nomatch}
    
  \<close>
  
  method_setup simp_onm = \<open>Scan.lift scan_simp_only_options -- Attrib.thms >> (fn (m,thms) => 
    SIMPLE_METHOD' o (CHANGED oo m thms)
  )\<close>
  
  
  subsection \<open>Examples\<close>

  experiment
  begin
    subsubsection \<open>Isar Interface\<close>
    
    (* Start with cleared simpset *)
    named_simpset bar
    
    (* Start with other named simpset *)
    named_simpset foo = HOL_ss

    (* Print Content *)
    print_named_simpset bar
    print_named_simpset foo
    
    (* Predefined simpsets *)
    print_named_simpset HOL_basic_ss
    print_named_simpset HOL_ss
    print_named_simpset Main_ss          (* Simpset of theory HOL.Main *)
    
    
    
        
    (* Adding and deleting simp rules *)
    declare nth_append[named_ss bar]
    declare nth_append[named_ss bar del]
    declare nth_append[named_ss bar add]
    
    (* Same for split and cong *)
    declare if_split[named_ss bar split add]
    declare if_split[named_ss bar split del]
    declare if_split[named_ss bar split]
    
    declare if_cong[named_ss bar cong add]
    declare if_cong[named_ss bar cong del]
    declare if_cong[named_ss bar cong]
    
    (* Using Named Simpsets *)
    lemma "([1,2,3]@[4])!1 = 2"
      apply (simp named_ss bar:)
      by simp
    
    lemma "([1,2,3]@[4])!1 = 2"
      supply [[put_named_ss bar]]
      apply simp
      apply (simp named_ss Main_ss:)
      done

    lemma "([1,2,3]@[4])!1 = 2"
      apply (use [[put_named_ss bar]] in simp)
      by simp
          

    (* Convenience: simp_onm *)
    lemma "P 1 1 \<Longrightarrow> Q 1 1" for P Q :: "nat \<Rightarrow> nat \<Rightarrow> bool"
      apply (simp_onm (no_asm) One_nat_def)
      apply (simp_onm (no_asm_use) One_nat_def)
      oops  
  
    subsubsection \<open>ML Interface\<close>
    
    local_setup \<open>Named_Simpsets.declare @{binding foo2} NONE\<close>
    local_setup \<open>Named_Simpsets.declare @{binding foo3} (SOME HOL_ss)\<close>
    
    ML_val \<open>
      val ctxt = @{context}
    
      val ctxt = Named_Simpsets.put @{named_simpset foo} ctxt

      
      val _ = Named_Simpsets.map_ctxt
    \<close>
      
    
      
  end

  (* TODO: FIXME 
    Does not work with qualified properly.
    Note: inside experiment context, the below works. Must be some omission in taming the locale stack.
  *)

  context begin
    qualified named_simpset Named_Simpset_qualified_bug = HOL_ss
    
    print_named_simpset Named_Simpset_qualified_bug (** Works *)
    lemma foobar[named_ss Named_Simpset_qualified_bug]: "True" oops (** Does not work. Undefined name *)
    
  end
  
    
end
