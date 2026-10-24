theory Test
  imports Provenance
begin

lemma unmarked: "PROP A \<Longrightarrow> PROP A"
  by assumption

section \<open>Human part\<close>
provenance human

lemma a: "PROP A \<Longrightarrow> PROP A"
  by assumption

lemma \<^marker>\<open>provenance ai\<close> a_exception: "PROP A \<Longrightarrow> PROP A"
proof -
  assume "PROP A"
  then show "PROP A" .
qed

lemma long: "PROP A \<Longrightarrow> PROP B \<Longrightarrow> PROP A"
proof -
  assume a: "PROP A" and b: "PROP B"
  have \<^marker>\<open>provenance ai\<close> c: "PROP A"
  proof -
    from a show "PROP A" .
  qed
  have d: "PROP A"
    by \<^marker>\<open>provenance ai\<close> (rule a)
  have e: "PROP A"
    apply \<^marker>\<open>provenance ai\<close> (rule a)
    done
  show "PROP A" by (rule c)
qed

section \<open>AI part\<close>
provenance ai

lemma b: "PROP A \<Longrightarrow> PROP B \<Longrightarrow> PROP A"
  by assumption

definition "c \<equiv> \<lambda>x::prop. x"

section \<open>Collaborative part\<close>
provenance ai_human

lemma d: "PROP A \<Longrightarrow> PROP A"
  by assumption

end
