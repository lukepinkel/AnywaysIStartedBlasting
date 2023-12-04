theory FiltersAndIdeals
  imports Main
begin



definition is_finite_inter_closed::"'X set set \<Rightarrow> bool" where
  "is_finite_inter_closed A \<equiv> (\<forall>a1 a2. a1 \<in> A \<longrightarrow> a2 \<in> A  \<longrightarrow> a1 \<inter> a2 \<in> A)"


definition is_up_closed::"'X::order set \<Rightarrow> bool" where
  "is_up_closed A \<equiv> (\<forall>a b. a \<in> A \<longrightarrow> a \<le> b \<longrightarrow> b \<in> A)"

definition is_ne::"'X set \<Rightarrow> bool" where
  "is_ne A \<equiv> A \<noteq> {}"

definition has_finite_inter_prop::"'X set set \<Rightarrow> bool" where
  "has_finite_inter_prop A \<equiv> (\<forall>B \<in> Pow(A). finite B \<longrightarrow>  (\<Inter>B \<noteq> {}))"

definition is_downdirected::"'X set set \<Rightarrow> bool" where
  "is_downdirected A \<equiv> (\<forall>a1 \<in> A. \<forall>a2 \<in> A. \<exists>a3 \<in> A. a3 \<subseteq> (a1 \<inter> a2))"

(*
typedef 'X filtersubbase = "{E::'X set set. has_finite_inter_prop E}"
  using has_finite_inter_prop_def by fastforce

typedef 'X filterbase = "{B::'X set set. (is_downdirected B) \<and> (is_ne B)}"
  by (metis all_not_in_conv empty_subsetI is_downdirected_def is_ne_def mem_Collect_eq)

typedef 'a filter = "{(F::'a set set). (is_finite_inter_closed F) \<and> (is_up_closed F) \<and> (is_ne F)}"
  by (metis (mono_tags) Int_Inter_eq(2) InterI boolean_algebra.conj_zero_left equals0I is_finite_inter_closed_def is_ne_def is_up_closed_def mem_Collect_eq)

class filtersubbase = 
  fixes E::"'a set set"
  assumes fip:"has_finite_inter_prop E"

class filterbase=
  fixes B::"'a set set"
  assumes ne:"is_ne B"
  assumes ddir:"is_downdirected B"

class filter =
  fixes F :: "'a set set" 
  assumes ne:"is_ne F"
  assumes fcapclosed: "is_finite_inter_closed F"
  assumes upclosed:   "is_upclosed F" 

hide_type Filter.filter

instantiation filter :: (type) complete_lattice
begin

definition less_eq_filter  where  "F1 \<le> F2 \<longleftrightarrow> (\<forall>A \<in> F1. (\<exists>B. ((B\<in>F2) \<and>  (B \<subseteq> A))))"


instance
proof
  fix F1 F2 F3::"'a filter"  and EF::"'a filter set"
qed
end *)

declare [[show_types]]

definition union_of :: "('a set set \<Rightarrow> bool) \<Rightarrow> ('a set \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
  (infixr "union'_of" 60)
  where "P union_of Q \<equiv> \<lambda>S. \<exists>\<U>. P \<U> \<and> \<U> \<subseteq> Collect Q \<and> \<Union>\<U> = S"

definition inter_of :: "('a set set \<Rightarrow> bool) \<Rightarrow> ('a set \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
  (infixr "inter'_of" 60)
  where "P inter_of Q \<equiv> \<lambda>S. \<exists>\<U>. P \<U> \<and> \<U> \<subseteq> Collect Q \<and> \<Inter>\<U> = S"

definition arbitrary:: "'a set set \<Rightarrow> bool" where "arbitrary \<U> \<equiv> True"

lemma union_of_inc: "\<lbrakk>P {S}; Q S\<rbrakk> \<Longrightarrow> (P union_of Q) S"
  by (auto simp: union_of_def)

lemma inter_of_inc:
   "\<lbrakk>P {S}; Q S\<rbrakk> \<Longrightarrow> (P inter_of Q) S"
  by (auto simp: inter_of_def)

lemma union_of_mono:
   "\<lbrakk>(P union_of Q) S; \<And>x. Q x \<Longrightarrow> Q' x\<rbrakk> \<Longrightarrow> (P union_of Q') S"
  by (auto simp: union_of_def)

lemma inter_of_mono:
   "\<lbrakk>(P inter_of Q) S; \<And>x. Q x \<Longrightarrow> Q' x\<rbrakk> \<Longrightarrow> (P inter_of Q') S"
  by (auto simp: inter_of_def)

lemma all_union_of:
     "(\<forall>S. (P union_of Q) S \<longrightarrow> R S) \<longleftrightarrow> (\<forall>T. P T \<and> T \<subseteq> Collect Q \<longrightarrow> R(\<Union>T))"
  by (auto simp: union_of_def)

lemma all_inter_of:
     "(\<forall>S. (P inter_of Q) S \<longrightarrow> R S) \<longleftrightarrow> (\<forall>T. P T \<and> T \<subseteq> Collect Q \<longrightarrow> R(\<Inter>T))"
  by (auto simp: inter_of_def)
             
lemma inter_ofE:
     "\<lbrakk>(P inter_of Q) S; \<And>T. \<lbrakk>P T; T \<subseteq> Collect Q\<rbrakk> \<Longrightarrow> R(\<Inter>T)\<rbrakk> \<Longrightarrow> R S"
  by (auto simp: inter_of_def)

lemma union_of_empty:
     "P {} \<Longrightarrow> (P union_of Q) {}"
  by (auto simp: union_of_def)

lemma inter_of_empty:
     "P {} \<Longrightarrow> (P inter_of Q) UNIV"
  by (auto simp: inter_of_def)

text\<open> The arbitrary and finite cases\<close>

lemma arbitrary_union_of_alt:
   "(arbitrary union_of Q) S \<longleftrightarrow> (\<forall>x \<in> S. \<exists>U. Q U \<and> x \<in> U \<and> U \<subseteq> S)"
 (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (force simp: union_of_def arbitrary_def)
next
  assume ?rhs
  then have "{U. Q U \<and> U \<subseteq> S} \<subseteq> Collect Q" "\<Union>{U. Q U \<and> U \<subseteq> S} = S"
    by auto
  then show ?lhs
    unfolding union_of_def arbitrary_def by blast
qed

lemma arbitrary_union_of_empty [simp]: "(arbitrary union_of P) {}"
  by (force simp: union_of_def arbitrary_def)

lemma arbitrary_inter_of_empty [simp]:
  "(arbitrary inter_of P) UNIV"
  by (force simp: inter_of_def arbitrary_def)

lemma arbitrary_union_of_inc:
  "P S \<Longrightarrow> (arbitrary union_of P) S"
  by (force simp: union_of_inc arbitrary_def)

lemma arbitrary_inter_of_inc:
  "P S \<Longrightarrow> (arbitrary inter_of P) S"
  by (force simp: inter_of_inc arbitrary_def)

lemma arbitrary_union_of_complement:
   "(arbitrary union_of P) S \<longleftrightarrow> (arbitrary inter_of (\<lambda>S. P(- S))) (- S)"  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain \<U> where "\<U> \<subseteq> Collect P" "S = \<Union>\<U>"
    by (auto simp: union_of_def arbitrary_def)
  then show ?rhs
    unfolding inter_of_def arbitrary_def
    by (rule_tac x="uminus ` \<U>" in exI) auto
next
  assume ?rhs
  then obtain \<U> where "\<U> \<subseteq> {S. P (- S)}" "\<Inter>\<U> = - S"
    by (auto simp: union_of_def inter_of_def arbitrary_def)
  then show ?lhs
    unfolding union_of_def arbitrary_def
    by (rule_tac x="uminus ` \<U>" in exI) auto
qed

lemma arbitrary_inter_of_complement:
   "(arbitrary inter_of P) S \<longleftrightarrow> (arbitrary union_of (\<lambda>S. P(- S))) (- S)"
  by (simp add: arbitrary_union_of_complement)

lemma arbitrary_union_of_idempot [simp]:
  "arbitrary union_of arbitrary union_of P = arbitrary union_of P"
proof -
  have 1: "\<exists>\<U>'\<subseteq>Collect P. \<Union>\<U>' = \<Union>\<U>" if "\<U> \<subseteq> {S. \<exists>\<V>\<subseteq>Collect P. \<Union>\<V> = S}" for \<U>
  proof -
    let ?\<W> = "{V. \<exists>\<V>. \<V>\<subseteq>Collect P \<and> V \<in> \<V> \<and> (\<exists>S \<in> \<U>. \<Union>\<V> = S)}"
    have *: "\<And>x U. \<lbrakk>x \<in> U; U \<in> \<U>\<rbrakk> \<Longrightarrow> x \<in> \<Union>?\<W>"
      using that
      apply simp
      apply (drule subsetD, assumption, auto)
      done
    show ?thesis
    apply (rule_tac x="{V. \<exists>\<V>. \<V>\<subseteq>Collect P \<and> V \<in> \<V> \<and> (\<exists>S \<in> \<U>. \<Union>\<V> = S)}" in exI)
      using that by (blast intro: *)
  qed
  have 2: "\<exists>\<U>'\<subseteq>{S. \<exists>\<U>\<subseteq>Collect P. \<Union>\<U> = S}. \<Union>\<U>' = \<Union>\<U>" if "\<U> \<subseteq> Collect P" for \<U>
    by (metis (mono_tags, lifting) union_of_def arbitrary_union_of_inc that)
  show ?thesis
    unfolding union_of_def arbitrary_def by (force simp: 1 2)
qed

lemma arbitrary_inter_of_idempot:
   "arbitrary inter_of arbitrary inter_of P = arbitrary inter_of P" (is "?lhs = ?rhs")
proof -
  have "- ?lhs = - ?rhs"
    unfolding arbitrary_inter_of_complement by simp
  then show ?thesis
    by simp
qed

lemma arbitrary_union_of_Union:
   "(\<And>S. S \<in> \<U> \<Longrightarrow> (arbitrary union_of P) S) \<Longrightarrow> (arbitrary union_of P) (\<Union>\<U>)"
  by (metis union_of_def arbitrary_def arbitrary_union_of_idempot mem_Collect_eq subsetI)

lemma arbitrary_union_of_Un:
   "\<lbrakk>(arbitrary union_of P) S; (arbitrary union_of P) T\<rbrakk>
           \<Longrightarrow> (arbitrary union_of P) (S \<union> T)"
  using arbitrary_union_of_Union [of "{S,T}"] by auto

lemma arbitrary_inter_of_Inter:
   "(\<And>S. S \<in> \<U> \<Longrightarrow> (arbitrary inter_of P) S) \<Longrightarrow> (arbitrary inter_of P) (\<Inter>\<U>)"
  by (metis inter_of_def arbitrary_def arbitrary_inter_of_idempot mem_Collect_eq subsetI)

lemma arbitrary_inter_of_Int:
   "\<lbrakk>(arbitrary inter_of P) S; (arbitrary inter_of P) T\<rbrakk>
           \<Longrightarrow> (arbitrary inter_of P) (S \<inter> T)"
  using arbitrary_inter_of_Inter [of "{S,T}"] by auto

lemma arbitrary_union_of_Int_eq:
  "(\<forall>S T. (arbitrary union_of P) S \<and> (arbitrary union_of P) T
               \<longrightarrow> (arbitrary union_of P) (S \<inter> T))
   \<longleftrightarrow> (\<forall>S T. P S \<and> P T \<longrightarrow> (arbitrary union_of P) (S \<inter> T))"  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (simp add: arbitrary_union_of_inc)
next
  assume R: ?rhs
  show ?lhs
  proof clarify
    fix S :: "'a set" and T :: "'a set"
    assume "(arbitrary union_of P) S" and "(arbitrary union_of P) T"
    then obtain \<U> \<V> where *: "\<U> \<subseteq> Collect P" "\<Union>\<U> = S" "\<V> \<subseteq> Collect P" "\<Union>\<V> = T"
      by (auto simp: union_of_def)
    then have "(arbitrary union_of P) (\<Union>C\<in>\<U>. \<Union>D\<in>\<V>. C \<inter> D)"
     using R by (blast intro: arbitrary_union_of_Union)
   then show "(arbitrary union_of P) (S \<inter> T)"
     by (simp add: Int_UN_distrib2 *)
 qed
qed

lemma arbitrary_inter_of_Un_eq:
   "(\<forall>S T. (arbitrary inter_of P) S \<and> (arbitrary inter_of P) T
               \<longrightarrow> (arbitrary inter_of P) (S \<union> T)) \<longleftrightarrow>
        (\<forall>S T. P S \<and> P T \<longrightarrow> (arbitrary inter_of P) (S \<union> T))"
  apply (simp add: arbitrary_inter_of_complement)
  using arbitrary_union_of_Int_eq [of "\<lambda>S. P (- S)"]
  by (metis (no_types, lifting) arbitrary_def double_compl union_of_inc)

lemma finite_union_of_empty [simp]: "(finite union_of P) {}"
  by (simp add: union_of_empty)

lemma finite_inter_of_empty [simp]: "(finite inter_of P) UNIV"
  by (simp add: inter_of_empty)

lemma finite_union_of_inc:
   "P S \<Longrightarrow> (finite union_of P) S"
  by (simp add: union_of_inc)

lemma finite_inter_of_inc:
   "P S \<Longrightarrow> (finite inter_of P) S"
  by (simp add: inter_of_inc)

lemma finite_union_of_complement:
  "(finite union_of P) S \<longleftrightarrow> (finite inter_of (\<lambda>S. P(- S))) (- S)"
  unfolding union_of_def inter_of_def
  apply safe
   apply (rule_tac x="uminus ` \<U>" in exI, fastforce)+
  done

lemma finite_inter_of_complement:
   "(finite inter_of P) S \<longleftrightarrow> (finite union_of (\<lambda>S. P(- S))) (- S)"
  by (simp add: finite_union_of_complement)

lemma finite_union_of_idempot [simp]:
  "finite union_of finite union_of P = finite union_of P"
proof -
  have "(finite union_of P) S" if S: "(finite union_of finite union_of P) S" for S
  proof -
    obtain \<U> where "finite \<U>" "S = \<Union>\<U>" and \<U>: "\<forall>U\<in>\<U>. \<exists>\<U>. finite \<U> \<and> (\<U> \<subseteq> Collect P) \<and> \<Union>\<U> = U"
      using S unfolding union_of_def by (auto simp: subset_eq)
    then obtain f where "\<forall>U\<in>\<U>. finite (f U) \<and> (f U \<subseteq> Collect P) \<and> \<Union>(f U) = U"
      by metis
    then show ?thesis
      unfolding union_of_def \<open>S = \<Union>\<U>\<close>
      by (rule_tac x = "snd ` Sigma \<U> f" in exI) (fastforce simp: \<open>finite \<U>\<close>)
  qed
  moreover
  have "(finite union_of finite union_of P) S" if "(finite union_of P) S" for S
    by (simp add: finite_union_of_inc that)
  ultimately show ?thesis
    by force
qed

lemma finite_inter_of_idemp [simp]:
  "finite inter_of finite inter_of  P = finite inter_of  P"
proof -
  have "(finite inter_of P) S" if S: "(finite inter_of finite inter_of P) S" for S
  proof -
    obtain \<U> where "finite \<U>" "S = \<Inter>\<U>" and \<U>: "\<forall>U\<in>\<U>. \<exists>\<U>. finite \<U> \<and> (\<U> \<subseteq> Collect P) \<and> \<Inter>\<U> = U"
      using S unfolding inter_of_def by (auto simp: subset_eq)
    then obtain f where "\<forall>U\<in>\<U>. finite (f U) \<and> (f U \<subseteq> Collect P) \<and> \<Inter>(f U) = U"
      by metis
    then show ?thesis
      unfolding inter_of_def \<open>S = \<Inter>\<U>\<close>
      by (rule_tac x = "snd ` Sigma \<U> f" in exI) (fastforce simp: \<open>finite \<U>\<close>)
  qed
  moreover
  have "(finite inter_of finite inter_of P) S" if "(finite inter_of P) S" for S
    by (simp add: finite_inter_of_inc that)
  ultimately show ?thesis
    by force
qed

definition thesenuts::"'X set \<Rightarrow> 'X set  \<Rightarrow> bool" where
  "thesenuts A X  \<equiv> (finite A \<and> A \<noteq> {} \<and> A \<subseteq> X)"

lemma finite_intersections_in_set:
  fixes X::"'X set"
  assumes A0:"C \<noteq> {}" and
          A1:"C \<in> Pow(Pow (X))" and
          A2: "\<And>a1 a2. a1 \<in> C \<Longrightarrow> a2 \<in> C \<Longrightarrow> a1 \<inter> a2 \<in> C"and 
          A3:"finite E" and
          A4:"E \<noteq> {}"  and
          A5:"E \<subseteq> C"
  shows "(\<Inter>E) \<in> C"
proof -
  from A3 A4 A5 show ?thesis
  proof (induct E rule: finite_ne_induct)
    case (singleton x)
    with assms show ?case
      by simp
    next
    case (insert x F)
    then have "(\<Inter>(insert x F)) \<in> C" using assms
    proof-
      have P0:"x \<in> C"
        using insert.prems by auto
      have P1: "F \<subseteq> C"
        using insert.prems by auto
      with A2 have P2:"x \<inter> (\<Inter>F) \<in> C"
        by (simp add: P0 insert.hyps(4))
      from insert.hyps have P3:"(\<Inter>F) \<in> C"
        using P1 by blast
      have  P4:"\<Inter>(insert x F) = x \<inter> (\<Inter>F)" by simp
      then show "(\<Inter>(insert x F)) \<in> C"
        by (simp add: P2)
    qed
    show ?case
      using \<open>\<Inter> (insert (x::'X set) (F::'X set set)) \<in> (C::'X set set)\<close> by auto
qed
qed


definition FCapClosed::"'X set set \<Rightarrow> prop" where
  "FCapClosed A \<equiv> (\<And>a1 a2. a1 \<in> A \<Longrightarrow> a2 \<in> A \<Longrightarrow> a1 \<inter> a2 \<in> A)"

locale system_of_sets = 
  fixes X::"'X set" and A::"'X set set"
  assumes set_of_subsets[intro]:"A \<in> Pow(Pow X)"

locale pi_system = system_of_sets + 
  assumes f_int_closed[intro]:"\<And>a1 a2. a1 \<in> A  \<Longrightarrow>  a2 \<in> A \<Longrightarrow>  a1 \<inter> a2 \<in> A "

lemma (in pi_system) inter_finite[intro]:
  assumes "finite I" "I \<noteq> {}" "\<And>i. i \<in> I \<Longrightarrow>  E i \<in> A"
  shows "(\<Inter>i\<in>I. E i) \<in> A"      
  using assms by (induct rule: finite_ne_induct) auto

inductive_set 
  fmn::"'X set set \<Rightarrow> 'X set set" for A::"'X set set"
  where 
    fcc[intro]:"\<lbrakk>a1 \<in> fmn A; a2 \<in> fmn A\<rbrakk> \<Longrightarrow> a1 \<inter> a2 \<in> fmn A"
 
print_theorems


definition FinPow::"'X set \<Rightarrow> 'X set set" where
  "FinPow(X) = {A \<in> Pow(X). finite(A)}"

lemma finpow1: 
  assumes "A \<in> FinPow(X)"
  shows "\<exists>n::nat. card(A) =n"
  by simp

end