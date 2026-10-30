(*
  Author: Adem Rimpapa
*)

theory UnionFind_Specs
  imports Main AI_Provenance.Provenance
begin

provenance human

(* The Union-Find structure consists of a ground set/universe s and the union-find structure uf. It
abstracts to a set of sets, representing a partition of the universe.

The universe s is given in a form suitable for the implementation (of type 'i), e.g. a number n 
for the universe {0..<n}, and abstracts to the set s.
The initial union-find structure uf_init s is the partition of the universe set s into singletons. *)

locale UnionFind_Specs =
  fixes uf_invar :: "'u \<Rightarrow> 'i \<Rightarrow> bool"
  fixes set_of_sets :: "'u \<Rightarrow> 'a set set"
  fixes merge :: "'u \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'u"
  fixes in_same_set :: "'u \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes uf_init :: "'i \<Rightarrow> 'u"
  fixes set :: "'i \<Rightarrow> 'a set"
  assumes set_of_sets_union: "uf_invar uf s \<Longrightarrow> \<Union> (set_of_sets uf) = set s"
  assumes set_of_sets_disjoint: "uf_invar uf s \<Longrightarrow> pairwise disjnt (set_of_sets uf)"
  assumes set_of_sets_nonempty: "uf_invar uf s \<Longrightarrow> {} \<notin> set_of_sets uf"
  assumes in_same_set_correct: "uf_invar uf s \<Longrightarrow> x \<in> set s \<Longrightarrow> y \<in> set s \<Longrightarrow>
    (in_same_set uf x y = (\<exists>A \<in> set_of_sets uf. x \<in> A \<and> y \<in> A))"
  assumes merge_invar: "uf_invar uf s \<Longrightarrow> x \<in> set s \<Longrightarrow> y \<in> set s \<Longrightarrow> uf_invar (merge uf x y) s"
  assumes merge_correct: "uf_invar uf s \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> A \<in> set_of_sets uf \<Longrightarrow> B \<in> set_of_sets uf \<Longrightarrow>
    set_of_sets (merge uf x y) = (set_of_sets uf - {A, B}) \<union> {A \<union> B}"
  assumes uf_init_invar: "uf_invar (uf_init s) s"
  assumes uf_init_correct: "set_of_sets (uf_init s) = (\<lambda>x. {x}) ` set s"

end
