theory FiltersAgain3
  imports Main "./Posets"
begin
hide_type Filter.filter
no_notation Cons (infixr "#" 65)
declare [[show_types]]

definition is_inhabited::"'X set  \<Rightarrow> bool" where
   "is_inhabited X \<equiv> X \<noteq> {}"

definition is_pisystem::"'X set set \<Rightarrow> bool" where
   "is_pisystem X \<equiv> (\<forall>a b. a \<in> X  \<longrightarrow> b \<in> X \<longrightarrow> a \<inter> b  \<in> X)"

definition is_pibase::"'X set set \<Rightarrow> bool" where
   "is_pibase X \<equiv> (\<forall>a b. a \<in> X  \<longrightarrow> b \<in> X \<longrightarrow>(\<exists>c  \<in> X. c \<subseteq> a \<inter> b ))"

definition is_fcsystem::"'X set set \<Rightarrow> bool" where
   "is_fcsystem X \<equiv> (\<forall>F. F \<noteq> {} \<longrightarrow> finite F \<longrightarrow> F  \<subseteq> X \<longrightarrow> \<Inter>F \<in> X)"

definition is_fcbase::"'X set set \<Rightarrow> bool" where
   "is_fcbase X \<equiv> (\<forall>F. finite F \<longrightarrow> F  \<subseteq> X \<longrightarrow> (\<exists>c \<in> X. c \<subseteq> \<Inter>F))"

definition is_upclosed::"'X::order set \<Rightarrow> bool" where
   "is_upclosed X \<equiv> (\<forall>a b. a \<le> b \<longrightarrow>  a \<in> X \<longrightarrow>  b \<in> X)"

definition is_filter::"'X set set \<Rightarrow> bool" where 
  "is_filter F \<equiv> (is_pisystem F \<and> is_upclosed F \<and> is_inhabited F)"

definition is_proper::"'X set set \<Rightarrow> bool" where
   "is_proper F \<equiv> {} \<notin> F"

definition is_properfilter::"'X set set \<Rightarrow> bool" where
   "is_properfilter F \<equiv> is_filter F \<and> is_proper F"

definition filter_set::"'X set set set" where
   "filter_set = {F. is_filter F}"

definition proper_filterset::"'X set set set" where
   "proper_filterset = {F. is_properfilter F}"

definition meshes::"('X set set) \<Rightarrow> ('X set set) \<Rightarrow> bool"  (infixl "#" 50)  where
   "(A # B) \<equiv> (\<forall>a \<in> A. \<forall>b \<in> B.  (a\<inter>b \<noteq> {}))"

definition grill::"'X set set \<Rightarrow> 'X set set" where
  "grill A = {x::('X set). {x}#A}"  

definition proper_finite_meet_closure::"'X set set \<Rightarrow> 'X set set" where
    "proper_finite_meet_closure A = {a. \<exists>f\<in>Pow(A). finite f \<and>  f \<noteq> {} \<and>  \<Inter>f=a}"

definition finite_meet_closure::"'X set set \<Rightarrow> 'X set set" where
    "finite_meet_closure A = {a. \<exists>f\<in>Pow(A). finite f  \<and>  \<Inter>f=a}"

definition upclosure::"'X::order set \<Rightarrow> 'X::order set" where
    "upclosure A = {x. \<exists>a \<in> A. a \<le> x}"

definition filter_generated_by::"'X set set set \<Rightarrow> 'X set set" where
  "filter_generated_by A = upclosure(proper_finite_meet_closure(\<Union>A))"

definition is_filtergrill::"'X set set \<Rightarrow> bool" where
  "is_filtergrill A \<equiv> (\<exists>F::('X set set). (is_filter F) \<and> (A = grill F))"

definition is_prime::"'X set set \<Rightarrow> bool" where
  "is_prime A \<equiv> (\<forall>a. \<forall>b. a \<union> b \<in> A \<longrightarrow> (a \<in> A \<or> b \<in> A))"

definition is_grillage::"'X set set \<Rightarrow> bool" where
  "is_grillage A \<equiv> (is_prime A  \<and> is_upclosed A \<and> is_inhabited A)"

definition is_chain::"'X::ord set \<Rightarrow> bool" where
  "is_chain A \<equiv> (\<forall>a1 \<in> A. \<forall>a2 \<in> A. (a1 \<le> a2 \<or> a2 \<le> a1))"

definition is_ultrafilter::"'X set set \<Rightarrow> bool" where
  "is_ultrafilter U \<equiv> (is_properfilter U \<and> IsMaximal2 U proper_filterset)"

definition is_prime_alt::"'X set set \<Rightarrow> bool" where
  "is_prime_alt U \<equiv> (\<forall>a. ((a \<in> U) \<and> \<not>((UNIV-a) \<in> U)) \<or> (\<not>(a \<in> U) \<and> ((UNIV-a) \<in> U)))"

definition finer_filters::"'X set set \<Rightarrow> 'X set set set" where
  "finer_filters F = {U. is_properfilter U \<and> (F \<subseteq> U)}"
    
abbreviation fmc::"'X set set \<Rightarrow> 'X set set" where
  "fmc A \<equiv> finite_meet_closure A"

abbreviation pfmc::"'X set set \<Rightarrow> 'X set set" where
  "pfmc A \<equiv> proper_finite_meet_closure A"

abbreviation fgenby::"'X set set set \<Rightarrow> 'X set set" where
  "fgenby A \<equiv> filter_generated_by A"






lemma finite_meet_closure_to_proper:
  "(proper_finite_meet_closure A) \<union> {UNIV} = finite_meet_closure A" 
proof-
  let ?C1="(proper_finite_meet_closure A)" let ?C2="finite_meet_closure A"
  have B0:"?C1 \<subseteq> ?C2"
  proof
    fix c1 assume P0:"c1 \<in> ?C1"
    obtain f where P1:"f \<in> Pow(A) \<and>  finite f \<and>  f \<noteq> {} \<and>  \<Inter>f=c1" by (smt (verit, best) P0 CollectD proper_finite_meet_closure_def)
    show "c1 \<in> ?C2"  using P1 finite_meet_closure_def by blast
  qed
  have B1:"UNIV \<in> ?C2 "using finite_meet_closure_def by auto
  have B2:"?C1 \<union> {UNIV} \<subseteq> ?C2" by (simp add: B0 B1)
  have B3:"?C2 \<subseteq> ?C1 \<union> {UNIV}"
    by (smt (verit, del_insts) UnCI proper_finite_meet_closure_def finite_meet_closure_def complete_lattice_class.Inf_empty insert_iff mem_Collect_eq subsetI)
  show ?thesis using B2 B3 by blast
qed

lemma fmc_extensive:
  "A \<subseteq> finite_meet_closure A"
proof-
  have B0:"\<forall>a \<in> A. finite {a} \<and> {a} \<in> Pow(A) \<and> a=\<Inter>{a}" by simp
  have B1:"\<forall>a \<in> A. \<exists>f \<in> Pow(A). finite f \<and> \<Inter>f=a"using B0 by blast
  with B1 show ?thesis  by (simp add: finite_meet_closure_def subsetI)
qed

lemma pfmc_extensive:
  "A \<subseteq> proper_finite_meet_closure A"
proof-
  have B0:"\<forall>a \<in> A. finite {a} \<and> {a} \<noteq> {}  \<and> {a} \<in> Pow(A) \<and> a=\<Inter>{a}" by simp
  have B1:"\<forall>a \<in> A. \<exists>f \<in> Pow(A). f \<noteq> {} \<and> finite f \<and> \<Inter>f=a"using B0 by blast
  with B0 B1 show ?thesis by (smt (verit, del_insts) CollectI proper_finite_meet_closure_def subsetI)
qed

lemma upc_extensive:
  "A \<subseteq> upclosure A"
  using upclosure_def by fastforce

lemma fmc_isotone:
  "A \<subseteq> B \<longrightarrow> finite_meet_closure A \<subseteq> finite_meet_closure B"
  by (smt (verit) Pow_iff finite_meet_closure_def mem_Collect_eq subset_eq)
  
lemma pfmc_isotone:
  "A \<subseteq> B \<longrightarrow> proper_finite_meet_closure A \<subseteq> proper_finite_meet_closure B"
  by (smt (verit) CollectD CollectI PowD PowI proper_finite_meet_closure_def order_trans subsetI)


lemma upc_isotone:
  "A \<subseteq> B \<longrightarrow> upclosure A \<subseteq> upclosure B"
  by (smt (verit, best) Collect_mono subsetD upclosure_def)
  

lemma fmc_idempotent:
  "finite_meet_closure A = finite_meet_closure (finite_meet_closure A)"
proof-
  let ?C1="finite_meet_closure A"
  let ?C2="finite_meet_closure ?C1"
  have B0:"A \<subseteq> ?C1" by (simp add: fmc_extensive)
  have B1:"?C1 \<subseteq> ?C2" by (simp add: fmc_extensive)
  have B2:"?C2 \<subseteq> ?C1"
  proof
    fix a assume A0:"a \<in> ?C2"
    obtain f where A1:"f= (\<lambda>a. SOME E. E \<in> Pow(A) \<and> finite E \<and> a=\<Inter>E)" by simp
    obtain B where A2:"B \<in> (Pow ?C1) \<and> finite B \<and> a=(\<Inter>B)" by (smt (verit, best) A0 finite_meet_closure_def mem_Collect_eq)
    have B20:"\<forall>b \<in> B. \<exists>E \<in> Pow (A). finite E \<and> b = \<Inter>E"
      by (smt (verit, ccfv_threshold) A2 CollectD Union_Pow_eq Union_iff finite_meet_closure_def)
    have B30:"\<forall>b \<in> B. (b=(\<Inter>(f b)))" by (metis (mono_tags, lifting) A1 B20 someI)
    have B40:"a=(\<Inter>b\<in>B. (\<Inter>(f b)))" using A2 B30 by auto
    let ?D="\<Union>b \<in> B. (f b)"
    have B50:"\<forall>b \<in> B. finite (f b)" by (metis (mono_tags, lifting) A1 B20 verit_sko_ex_indirect2)
    have B60:"\<forall>b \<in> B. (f b) \<in> Pow A"  by (metis (mono_tags, lifting) A1 B20 verit_sko_ex_indirect2)
    have B70:"?D \<in> Pow(A)" using B60 by blast
    have B80:"finite ?D" using A2 B50 by blast
    have B90:"a=\<Inter>?D" using B40 by blast
    show B110:"a \<in> ?C1" using B70 B80 B90 finite_meet_closure_def by blast
  qed
  show ?thesis using B1 B2 by auto
qed

lemma pfmc_idempotent:
 "proper_finite_meet_closure A = proper_finite_meet_closure (proper_finite_meet_closure A)"
proof-
  let ?C1="proper_finite_meet_closure A"
  let ?C2="proper_finite_meet_closure ?C1"
  have B0:"A \<subseteq> ?C1" by (simp add: pfmc_extensive)
  have B1:"?C1 \<subseteq> ?C2" by (simp add: pfmc_extensive)
  have B2:"?C2 \<subseteq> ?C1"
  proof
    fix a assume A0:"a \<in> ?C2"
    obtain f where A1:"f= (\<lambda>a. SOME E. E \<in> Pow(A) \<and> E \<noteq> {} \<and> finite E \<and> a=\<Inter>E)" by simp
    obtain B where A2:"B \<in> (Pow ?C1) \<and> finite B \<and> B \<noteq> {} \<and> a=(\<Inter>B)" by (smt (verit, best) A0 proper_finite_meet_closure_def mem_Collect_eq)
    have B20:"\<forall>b \<in> B. \<exists>E \<in> Pow (A). finite E \<and> E \<noteq> {}  \<and> b = \<Inter>E" by (smt (verit, ccfv_threshold) A2 CollectD Union_Pow_eq Union_iff proper_finite_meet_closure_def)
    have B30:"\<forall>b \<in> B. (b=(\<Inter>(f b)))" by (metis (mono_tags, lifting) A1 B20 someI)
    have B40:"a=(\<Inter>b\<in>B. (\<Inter>(f b)))" using A2 B30 by auto
    let ?D="\<Union>b \<in> B. (f b)"
    have B50:"\<forall>b \<in> B. finite (f b)"
    proof
      fix b assume A3:"b \<in> B"
      have B500:"\<exists>E \<in> Pow A. E \<noteq> {} \<and> finite E \<and> b= (\<Inter>E)" by (metis A3 B20)
      show "finite (f b)" by (metis (mono_tags, lifting) A1 B500 someI_ex)
    qed
    have B60:"\<forall>b \<in> B. (f b) \<in> Pow A" by (smt (verit, ccfv_SIG) A1 B20 verit_sko_ex_indirect2)
    have B70:"?D \<in> Pow(A)" using B60 by blast
    have B80:"finite ?D" using A2 B50 by blast
    have B90:"a=\<Inter>?D" using B40 by blast
    have B110:"?D \<noteq> {}" by (smt (verit, del_insts) A1 A2 B20 SUP_bot_conv(1) equals0I someI_ex)
    show B120:"a \<in> ?C1" using B110 B70 B80 B90 proper_finite_meet_closure_def by blast
  qed
  show ?thesis using B1 B2 by auto
qed


lemma upc_is_idempotent:
  "upclosure (upclosure A) = upclosure A"
proof-
  let ?A1="upclosure A" let ?A2="upclosure ?A1"
  have LtR:"?A1 \<subseteq> ?A2" by (simp add: upc_extensive) 
  have RtL:"?A2 \<subseteq> ?A1" by (smt (verit) CollectD CollectI order_trans subsetI upclosure_def)
  with LtR RtL show ?thesis by fastforce
qed


lemma fmc_is_pseudoclosure:
  "pseudo_closure finite_meet_closure"
  by (simp add: extensive_def fmc_extensive fmc_isotone isotone_def pseudo_closure_def)

lemma fmc_is_closure:
  "closure finite_meet_closure"
  by (metis closure_def fmc_idempotent fmc_is_pseudoclosure idempotent_def)

lemma pfmc_is_pseudoclosure:
  "pseudo_closure proper_finite_meet_closure"
  by (simp add: extensive_def isotone_def pfmc_extensive pfmc_isotone pseudo_closure_def)

lemma pfmc_is_closure:
  "closure proper_finite_meet_closure"
  using closure_def idempotent_def pfmc_idempotent pfmc_is_pseudoclosure by auto

lemma upc_is_pseudoclosure:
  "pseudo_closure upclosure"
  by (simp add: extensive_def isotone_def pseudo_closure_def upc_extensive upc_isotone)

lemma upc_is_closure:
  "closure upclosure"
  by (simp add: closure_def idempotent_def upc_is_idempotent upc_is_pseudoclosure)


lemma upclosure_is_upclosed:
  "is_upclosed (upclosure A)"
  using is_upclosed_def upc_is_idempotent upclosure_def by fastforce



lemma imp_in_upclosure:
  "\<And>a. a \<in> A \<longrightarrow> a \<in> (upclosure A)"
  using upc_extensive by force 

lemma in_upclosure_imp:
  "\<And>a. a \<in> (upclosure A) \<longrightarrow>(\<exists>b \<in> A. a \<supseteq> b )" by (simp add: upclosure_def)

lemma finite_intersections_in_set:
  fixes X::"'X set"
  assumes A2: "\<And>a1 a2. a1 \<in> C \<Longrightarrow> a2 \<in> C \<Longrightarrow> a1 \<inter> a2 \<in> C"and 
          A3:"finite E" and A4:"E \<noteq> {}" and A5:"E \<subseteq> C"
  shows "(\<Inter>E) \<in> C"
proof -
  from A3 A4 A5 show ?thesis
  proof (induct E rule: finite_ne_induct)
    case (singleton x) with assms show ?case by simp
    next case (insert x F)
    then have "(\<Inter>(insert x F)) \<in> C" using assms
    proof-
      have P0:"x \<in> C" using insert.prems by auto
      have P1: "F \<subseteq> C" using insert.prems by auto
      with A2 have P2:"x \<inter> (\<Inter>F) \<in> C" by (simp add: P0 insert.hyps(4))
      from insert.hyps have P3:"(\<Inter>F) \<in> C" using P1 by blast
      have  P4:"\<Inter>(insert x F) = x \<inter> (\<Inter>F)" by simp
      then show "(\<Inter>(insert x F)) \<in> C"  by (simp add: P2)
    qed
    show ?case
      using \<open>\<Inter> (insert x F) \<in> C\<close> by auto
  qed
qed


lemma finite_intersections_base:
  fixes X::"'X set"
  assumes A2: "\<And>a1 a2. a1 \<in> C \<Longrightarrow> a2 \<in> C \<Longrightarrow> (\<exists>a3 \<in> C. a1 \<inter> a2 \<supseteq> a3)"and 
          A3:"finite E" and A4:"E \<noteq> {}" and A5:"E \<subseteq> C"
  shows " (\<exists>a3 \<in> C. (\<Inter>E) \<supseteq> a3)"
proof -
  from A3 A4 A5 show ?thesis
  proof (induct E rule: finite_ne_induct)
    case (singleton x) with assms show ?case  by fastforce
    next case (insert x F)
    then have "\<exists>a3 \<in> C. (\<Inter>(insert x F)) \<supseteq> a3" using assms
    proof-
      have P0:"x \<in> C" using insert.prems by auto
      have P1: "F \<subseteq> C" using insert.prems by auto
      have P2:"\<exists>a \<in> C. (\<Inter>F) \<supseteq> a"  by (simp add: P1 insert.hyps(4))
      have P3:"\<exists>b \<in> C. (x \<inter> (\<Inter>F)) \<supseteq> b"  by (metis A2 Int_subset_iff P0 P2 inf.order_iff)
      have P4:"\<exists>a3 \<in> C. (\<Inter>(insert x F)) \<supseteq> a3" using P3 by auto
      then show "\<exists>a3 \<in> C. (\<Inter>(insert x F)) \<supseteq> a3"  by (simp add: P4)
    qed
    show ?case
      using \<open>\<exists>a3\<in>C. a3 \<subseteq> \<Inter> (insert x F)\<close> by blast
  qed
qed

lemma finite_union_in_set:
  fixes X::"'X set"
  assumes A1:"C \<in> Pow(Pow (X))" and A2: "\<And>a1 a2. a1 \<in> C \<Longrightarrow> a2 \<in> C \<Longrightarrow> a1 \<union>  a2 \<in> C"and 
          A3:"finite E" and A4:"E \<noteq> {}"  and A5:"E \<subseteq> C"
  shows "(\<Union>E) \<in> C"
proof -
  from A3 A4 A5 show ?thesis
  proof (induct E rule: finite_ne_induct)
    case (singleton x)  with assms show ?case by simp
    next case (insert x F)
    then have "(\<Union>(insert x F)) \<in> C" using assms
    proof-
      have P0:"x \<in> C"  using insert.prems by auto
      have P1: "F \<subseteq> C" using insert.prems by auto
      with A2 have P2:"x \<union> (\<Union>F) \<in> C" by (simp add: P0 insert.hyps(4))
      from insert.hyps have P3:"(\<Union>F) \<in> C" using P1 by blast
      have  P4:"\<Union>(insert x F) = x \<union> (\<Union>F)" by simp
      then show "(\<Union>(insert x F)) \<in> C" by (simp add: P2)
    qed
    show ?case
      using \<open>\<Union> (insert (x::'X set) (F::'X set set)) \<in> (C::'X set set)\<close> by auto
  qed
qed

lemma finite_intersections_in_set_app:
  assumes A0:"A \<noteq> {} \<and> A \<noteq> {{}}" shows "is_pisystem A \<longleftrightarrow> is_fcsystem A"
proof-
  let ?L="is_pisystem A" let ?R="is_fcsystem A"
  have RiL:"?R \<longrightarrow> ?L"
    by (metis (no_types, opaque_lifting) Inf_insert cInf_singleton empty_iff empty_subsetI is_fcsystem_def finite.emptyI finite_insert insert_subset is_pisystem_def)
  have LiR:"?L\<longrightarrow> ?R"
  proof
    assume P0:?L 
    have P1:"\<And>a1 a2. a1 \<in> A \<Longrightarrow> a2 \<in> A \<Longrightarrow> a1 \<inter> a2 \<in> A" using P0 is_pisystem_def by blast
    have P2: "\<And>F. ((F \<noteq> {}  \<and> finite F \<and> F  \<subseteq> A) \<longrightarrow>( \<Inter>F \<in> A))"
    proof
      fix F assume P3:"F \<noteq> {} \<and> finite F \<and> F \<subseteq> A"
      show "(\<Inter>F) \<in> A"
        by (simp add: P1 P3 finite_intersections_in_set)
    qed
    show ?R by (simp add: P2 is_fcsystem_def)
  qed
  with RiL LiR show ?thesis by blast
qed

lemma finite_intersections_base_app:
  assumes A0:"A \<noteq> {} \<and> A \<noteq> {{}}" shows "is_pibase A \<longleftrightarrow> is_fcbase A"
proof-
  let ?L="is_pibase A" let ?R="is_fcbase A"
  have RiL:"?R \<longrightarrow> ?L"
  proof
    assume ?R
    show ?L
    proof-
      have RiL_P0:"(\<forall>a \<in> A. \<forall>b \<in> A. (\<exists>c  \<in> A. c \<subseteq> a \<inter> b ))"
      proof
        fix a assume RiL_A0:"a \<in> A"
        show "\<forall>b \<in> A. (\<exists>c  \<in> A. c \<subseteq> a \<inter> b )"
        proof
          fix b assume RiL_A1:"b \<in> A"
          let ?F="{a, b}"
          have RiL_B0:"finite ?F" by simp
          have RiL_B1:"?F \<subseteq> A" by (simp add: RiL_A0 RiL_A1) 
          obtain c where RiL_B2:"c \<in> A \<and> c \<subseteq> \<Inter>?F"
            by (meson RiL_B0 RiL_B1 \<open>is_fcbase (A::'a set set)\<close> is_fcbase_def)
          have RiL_B3:"\<Inter>?F = a \<inter> b"  by simp
          show "(\<exists>c  \<in> A. c \<subseteq> a \<inter> b )" using RiL_B2 by auto
        qed
      qed
      show ?thesis  using RiL_P0 is_pibase_def by blast
    qed
  qed
  have LiR:"?L\<longrightarrow> ?R"
  proof
    assume P0:?L 
    have P1:"\<And>a1 a2. a1 \<in> A \<Longrightarrow> a2 \<in> A \<Longrightarrow>(\<exists>c  \<in> A. c \<subseteq> a1 \<inter> a2 )" using P0 is_pibase_def by auto
    have P2: "\<And>F. ((F \<noteq> {}  \<and> finite F \<and> F  \<subseteq> A) \<longrightarrow>(\<exists>c. c \<in> A \<and> c \<subseteq> \<Inter>F))" by (metis P1 finite_intersections_base)
    show ?R  by (metis Inter_greatest P2 assms empty_iff is_fcbase_def order_class.order_eq_iff subset_iff)
  qed
  with RiL LiR show ?thesis by blast
qed
 

lemma fmc_is_fm_closed:
  "is_fcsystem (fmc A)"
  by (smt (verit, del_insts) Pow_def finite_meet_closure_def fmc_idempotent is_fcsystem_def mem_Collect_eq)


lemma pfmc_is_fm_closed:
  "is_fcsystem (pfmc A)"
  by (metis (mono_tags, lifting) CollectI PowI is_fcsystem_def pfmc_idempotent proper_finite_meet_closure_def)

lemma fcsystem_then_fcbase:
  assumes "A \<noteq> {}"
  shows "is_fcsystem A \<longrightarrow> is_fcbase A"
  by (metis assms complete_lattice_class.Inf_empty is_fcbase_def is_fcsystem_def subset_antisym subset_eq top_greatest)


lemma pisystem_then_pibase:
  assumes "A \<noteq> {}"
  shows "is_pisystem A \<longrightarrow> is_pibase A"
  by (metis assms empty_subsetI fcsystem_then_fcbase finite_intersections_base_app finite_intersections_in_set_app insertI1 is_pibase_def)

lemma filter_iff_pisystem_with_univ:
  "is_filter F \<longleftrightarrow>  (is_pisystem F \<and> is_upclosed F \<and>  (UNIV \<in>  F))"
  by (metis FiltersAgain3.is_filter_def empty_iff equals0I is_inhabited_def is_upclosed_def top_greatest)


lemma filter_iff_fcsystem_with_univ:
  "is_filter F \<longleftrightarrow> (is_fcsystem F \<and>  is_upclosed F \<and>  (UNIV \<in>  F))"
  by (metis UNIV_not_empty empty_iff filter_iff_pisystem_with_univ finite_intersections_in_set_app singletonD)

lemma filter_iff_fcsystem_inhabted:
  "is_filter F \<longleftrightarrow> (is_fcsystem F \<and> is_upclosed F \<and> is_inhabited F)"
proof-
  let ?lhs="is_filter F" let ?rhs="(is_fcsystem F \<and> is_upclosed F \<and> is_inhabited F)"
  have LtR:"?lhs \<longrightarrow> ?rhs"
  proof
    assume A0:"?lhs"
    have B0:"is_fcsystem F \<and> is_upclosed F"
      using A0 filter_iff_fcsystem_with_univ by auto 
    have B1:"UNIV \<in> F"
      using A0 filter_iff_pisystem_with_univ by blast
    have B2:"F \<noteq> {}" using B1 by auto
    show "?rhs"
      using A0 B0 is_filter_def by blast
  qed
  have RtL:"?rhs \<longrightarrow> ?lhs"
  proof
    assume A1:"?rhs"
    have B0:"is_fcsystem F \<and> is_upclosed F \<and> F \<noteq> {}"
      using A1 is_inhabited_def by blast 
    have B1:"\<exists>x. x \<in> F" using B0 by auto
    obtain x where A2:"x \<in> F" using B1 by auto
    have B2:"x \<subseteq> UNIV"  by simp
    have B3:"UNIV \<in> F"
      using A1 A2 B2 is_upclosed_def by blast 
    show "?lhs"
      by (simp add: A1 B3 filter_iff_fcsystem_with_univ)
  qed
  with LtR RtL show ?thesis by blast
qed

lemma filter_porder_expression:
  assumes A0:"is_filter F1 \<and> is_filter F2"
  shows "F1 \<subseteq> F2 \<longleftrightarrow> (\<forall>f1 \<in> F1. \<exists>f2 \<in> F2. f1 \<supseteq> f2)"
  by (meson assms in_mono filter_iff_fcsystem_inhabted subsetI is_upclosed_def)




lemma filter_intersection_is_filter:
  assumes A0:"\<forall>F \<in> EF. (is_filter F)"
  shows "is_filter (\<Inter>EF)"
proof-
  let ?I="\<Inter>EF"
  have B0:"\<forall>F \<in> EF. (is_fcsystem F \<and> is_upclosed F \<and> is_inhabited F \<and> F \<noteq> {} \<and> is_pisystem F \<and> UNIV \<in> F)"
    using is_filter_def assms filter_iff_fcsystem_with_univ by auto
  have P0:"UNIV \<in> ?I"
    using is_filter_def assms filter_iff_fcsystem_with_univ by auto
  have P1:"is_pisystem ?I" 
    by (meson B0 Inter_iff is_pisystem_def)
  have P2:"is_upclosed ?I"
    by (meson B0 Inter_iff is_upclosed_def)
  with P0 P1 P2 show ?thesis
    by (simp add: B0 P1 P2 filter_iff_pisystem_with_univ)
qed

lemma degenerate_filter1:
  "is_filter (Pow UNIV)"
  by (simp add: filter_iff_fcsystem_with_univ is_fcsystem_def is_upclosed_def)

lemma degenerate_filter2:
  assumes "is_filter F"
  shows "\<not>(is_proper F) \<longleftrightarrow> F=(Pow UNIV) "
  by (metis Pow_UNIV UNIV_I UNIV_eq_I assms empty_subsetI filter_iff_fcsystem_with_univ is_proper_def is_upclosed_def)


lemma fil_inter0:
  assumes A0:"\<forall>i \<in> I. (is_filter (EF(i)))" and A1:"EF`I \<noteq> {} \<and> EF`I \<noteq> {{}}"
  shows "Inf (EF`(I)) = {H. \<exists>U. (H=(\<Union>(U`(I))) \<and> (\<forall>i \<in> I. U(i) \<in> EF(i)))}"
proof-
  let ?L="Inf (EF`(I))" let ?R="{H. \<exists>U. (H=(\<Union>(U`(I))) \<and> (\<forall>i \<in> I. U(i) \<in> EF(i)))}"
  have LtR:"?L \<subseteq> ?R"
  proof
    fix a assume A2:"a \<in> ?L"
    define U::"'a \<Rightarrow> 'b set" where A3:"U = (\<lambda>i. a)"
    have B0:"\<forall>i \<in> I. a \<in> EF(i)" using A2 by auto
    have B1:"a=\<Union>(U`(I))" using A1 A3 by auto
    have B2:"\<forall>i \<in> I. (U(i)) \<in> (EF(i))"  using A3 B0 by fastforce 
    show "a \<in> ?R" using B1 B2 by blast
  qed
  have RtL:"?R \<subseteq> ?L"
  proof
    fix a assume A4:"a \<in> ?R"
    have B3:"\<forall>i \<in> I. \<exists>fi \<in>  (EF(i)). fi \<subseteq> a" using A4 by blast
    have B4:"\<forall>i \<in> I. a \<in> (EF(i))"
      by (meson A0 B3 filter_iff_fcsystem_with_univ is_upclosed_def)
    show "a \<in> ?L" using B4 by blast
  qed
  from LtR RtL have Eq:"?R = ?L" by blast
  with Eq show ?thesis by simp
qed

lemma fil_inter1:
  assumes A0:"\<forall>F \<in> \<F>. (is_filter F)" and A1:"\<F> \<noteq> {} \<and> \<F> \<noteq> {{}}"
  shows "Inf \<F>  = {H. \<exists>U. (H=(\<Union>U)) \<and> (\<forall>F \<in> \<F>. \<exists>u \<in> U. u \<in> F)}"
proof-
  let ?L="Inf \<F>" let ?R=" {H. \<exists>U. (H=(\<Union>U)) \<and> (\<forall>F \<in> \<F>. \<exists>u \<in> U. u \<in> F)}"
  have LtR:"?L \<subseteq> ?R"
  proof
    fix a assume A2:"a \<in> ?L"
    define U where A3:"U = {a}" 
    have B0:"\<forall>F \<in> \<F>. a \<in> F" using A2 by auto
    have B1: "a = \<Union>U" using A1 A3 by auto
    have B2:"\<forall>F \<in> \<F>. \<exists>u \<in> U. u \<in> F"
      by (simp add: A3 B0)
    show "a \<in> ?R" using B1 B2 by blast
  qed
  have RtL:"?R \<subseteq> ?L"
  proof
    fix a assume A4:"a \<in> ?R"
    have B3:"\<forall>F \<in> \<F>. \<exists>f \<in> F. f \<subseteq> a" using A4 by blast
    have B4:"\<forall>F \<in> \<F>. a \<in> F" by (meson A0 B3 filter_iff_fcsystem_with_univ is_upclosed_def)
    show "a \<in> ?L" using B4 by blast
  qed
  from LtR RtL have Eq:"?R = ?L" by blast
  with Eq show ?thesis by simp
qed

lemma fil_inter2:
  assumes A0:"\<forall>i \<in> I. (is_filter (EF(i)))" and A1:"EF`I \<noteq> {} \<and> EF`I \<noteq> {{}}"
  shows "Inf1 (EF`(I)) filter_set = (Inf (EF`(I))) "
proof-
  let ?INF="Inf (EF`(I))"
  have B0:"\<forall>F \<in> filter_set. (\<forall>Fi \<in> EF`(I). F \<subseteq> Fi) \<longrightarrow> F \<subseteq> ?INF"
  proof
    fix F::"'b set set" assume AB00:"F \<in> filter_set"
    show "(\<forall>Fi \<in> EF`(I). F \<subseteq> Fi) \<longrightarrow> F \<subseteq> ?INF"
    proof
      assume AB01:"\<forall>Fi \<in> EF`(I). F \<subseteq> Fi"
      show "F \<subseteq> ?INF" using AB01 by blast
    qed
  qed
  have B1:"\<forall>Fi \<in> EF`(I). ?INF \<subseteq> Fi " by blast
  have B2:"?INF \<in> filter_set"
    by (simp add: A0 filter_intersection_is_filter filter_set_def)
  have B3:"?INF \<in> LowerBoundsIn (EF`(I)) filter_set"
    by (simp add: B1 B2 lower_bounds_are_lower_bounds2)
  have B4:"IsInf2 ?INF (EF`I) filter_set"  by (simp add: B0 B3 IsInf2_def)
  with A0 A1 B4 show ?thesis
    by (simp add: B2 Inter_lower chumba_wumba1_inf complete_lattice_class.Inf_greatest)
qed



lemma filter_un0:
  assumes A0:"\<forall>F \<in> EF. (is_filter F)" and A1:"EF \<noteq> {} \<and> EF \<noteq> {{}}"
  shows "(is_upclosed (\<Union>EF)) \<and> (UNIV \<in> (\<Union>EF))"
proof-
  let ?S="\<Union>EF"
  have P0:"is_upclosed ?S"
    by (meson A0 Union_iff filter_iff_fcsystem_with_univ is_upclosed_def)
  have P3:"UNIV \<in> ?S"
    by (meson A0 A1 Union_iff ex_in_conv filter_iff_fcsystem_with_univ)
  with P0 P3 show ?thesis by blast
qed

lemma filter_un1:
  assumes A0:"\<forall>i \<in> I. (is_filter (EF(i)))" and A1:"EF`I \<noteq> {} \<and> EF`I \<noteq> {{}}" and A2:"I \<noteq> {}"
  shows "Sup (EF`(I)) \<subseteq>  {H. \<exists>U. (H=(\<Inter>(U`(I))) \<and> (\<forall>i \<in> I. U(i) \<in> EF(i)))}"
proof
  let ?L="Sup (EF`(I))" let ?R=" {H. \<exists>U. (H=(\<Inter>(U`(I))) \<and> (\<forall>i \<in> I. U(i) \<in> EF(i)))}"
  fix a assume A3:"a \<in> ?L"  
  obtain j where A4:"a \<in> (EF(j)) \<and> j \<in> I" using A3 by blast
  define U where A5:"U=(\<lambda>i. if i \<noteq> j then UNIV else a)"
  have B0:"\<forall>i \<in> I. i \<noteq> j \<longrightarrow> U(i) = UNIV" by (simp add: A5) 
  have B1:"\<forall>i \<in> I. i=j \<longrightarrow> U(i) = a"  by (simp add: A5) 
  have B2:"\<forall>i \<in> I. (U(i)) \<in> {UNIV, a}" using B0 B1 by blast
  have B3:"(U`(I)) \<subseteq> {UNIV, a}" using B2 by blast
  have B4:"\<forall>i \<in> I. (i=j) \<or> (i \<noteq> j)"  by simp
  have B5:"\<forall>i \<in> I. (U(i) = UNIV) \<or> (U(i) = a)" using B0 B1 by blast
  have B6:"a = UNIV \<inter> a" by simp
  have B7:"\<exists>j \<in> I. a = (U(j))" using B1 \<open>a \<in> EF j \<and> j \<in> I\<close> by blast
  have B8:"{a} \<subseteq> U`(I)"  using B7 by blast
  have B9:"a = (\<Inter>(U`(I)))" using B5 B8 by fastforce
  have B10:"\<forall>i \<in> I. (U(i)) \<in> (EF(i))"
    using A0 A4 A5 filter_iff_fcsystem_with_univ by fastforce
  show "a \<in> ?R" using B10 B9 by blast
qed

lemma filter_un2:
  assumes A0:"\<forall>i \<in> I. (is_filter (EF(i)))" and A1:"EF`I \<noteq> {} \<and> EF`I \<noteq> {{}}" and A2:"I \<noteq> {}"
  shows "\<forall>a \<in>  Sup (EF`(I)). (\<exists>U. (a=(\<Inter>(U`(I))) \<and> (\<forall>i \<in> I. U(i) \<in> EF(i))))"
proof
  let ?S="Sup (EF`(I))"
  let ?P="(\<lambda>H.  (\<exists>U. (H=(\<Inter>(U`(I))) \<and> (\<forall>i \<in> I. U(i) \<in> EF(i)))))"
  fix a assume A3:"a \<in> ?S "
  have B0:"?S \<subseteq> {H. ?P H}" by (simp add: A0 A1 A2 filter_un1)
  have B1:"a \<in> {H. ?P H} " using A3 B0 by blast
  show "?P a"  using B1 by blast
qed

lemma fc_base_lem1:
  assumes A0:"is_fcbase B"
  shows "\<forall>a1 \<in> B. \<forall>a2 \<in> B.  (\<exists>a3 \<in> B. a3 \<subseteq> a1 \<inter> a2)"
proof
  fix a1 assume A1:"a1 \<in> B"
  show "\<forall>a2 \<in> B. (\<exists>a3 \<in> B. a3 \<subseteq> a1 \<inter> a2)"
  proof
    fix a2 assume A2:"a2 \<in> B"
    let ?F="{a1, a2}"
    have B0:"finite ?F" by simp
    have B1:"?F \<subseteq> B" by (simp add: A1 A2)
    have B2:"a1 \<inter> a2 = \<Inter>?F" by simp
    show "\<exists>a3 \<in> B. a3 \<subseteq> a1 \<inter> a2" by (metis B0 B1 B2 assms is_fcbase_def)
  qed
qed

lemma filter_base_gen_filter:
  assumes A0:"is_fcbase B" shows "is_filter (upclosure B)"
proof-
  let ?F="upclosure B"
  have P0:"is_pisystem ?F"
  proof-
    have P00: "\<forall>a0 \<in> ?F. \<forall>a1 \<in> ?F. a0 \<inter> a1 \<in> ?F"
    proof
      fix a0 assume P00_A0:"a0 \<in> ?F"
      obtain b0 where P00_B0:"(b0 \<in> B) \<and> (b0 \<subseteq> a0)"
        using P00_A0 upclosure_def by auto 
      show "\<forall>a1 \<in> ?F. a0 \<inter> a1 \<in> ?F"
      proof
        fix a1 assume P00_A1:"a1 \<in> ?F"
        obtain b1 where P00_B1:"(b1 \<in> B) \<and> (b1 \<subseteq> a1)"
          using P00_A1 upclosure_def by auto 
        let ?b01="b0 \<inter> b1"
        obtain b where P00_B2:"(b \<in> B) \<and> (b \<subseteq> ?b01)"
          using P00_B0 P00_B1 assms fc_base_lem1 by blast
        have P00_B3:"b \<subseteq> a0 \<inter> a1"  using P00_B0 P00_B1 P00_B2 by blast
        show "a0 \<inter> a1 \<in> ?F" by (metis (no_types, lifting) P00_B2 P00_B3 mem_Collect_eq upclosure_def)
      qed
    qed
    with P00 show ?thesis  by (simp add: is_pisystem_def)
  qed
  have P1:"is_upclosed ?F"
    by (simp add: upclosure_is_upclosed)
  have P2:"is_inhabited ?F"
    by (metis assms bot.extremum_uniqueI empty_iff finite.emptyI is_fcbase_def is_inhabited_def upc_extensive) 
  with P0 P1 P2 show ?thesis
    by (simp add: FiltersAgain3.is_filter_def)
qed
      
lemma fil_union4:
  assumes A0:"\<forall>i \<in> I. (is_filter (EF(i)))" and A1:"EF`I \<noteq> {} \<and> EF`I \<noteq> {{}}"
  shows "is_fcbase (pfmc (Sup (EF`I)))"
proof-
  let ?IM="Sup (EF`I)" let ?B="pfmc ?IM"
  have B0:"is_fcsystem ?B"
    using pfmc_is_fm_closed by blast
  have B1:"is_fcbase ?B"
    by (metis A1 B0 Pow_empty fcsystem_then_fcbase pfmc_extensive subset_Pow_Union subset_empty subset_singletonD)
  with B1 show ?thesis by simp
qed

lemma fil_union5:
  assumes A0:"\<forall>i \<in> I. (is_filter (EF(i)))" and A1:"EF`I \<noteq> {} \<and> EF`I \<noteq> {{}}"
  shows "is_filter (upclosure( pfmc (Sup (EF`(I))) ))"
  using A0 A1 fil_union4 filter_base_gen_filter by blast

lemma fil_union5b:
  assumes A0:"\<forall>i \<in> I. (is_filter (EF(i)))" and A1:"EF`I \<noteq> {} \<and> EF`I \<noteq> {{}}"
  shows "is_filter (fgenby( EF`I ))"
  by (metis A0 A1 fil_union5 filter_generated_by_def)

lemma fil_union5c:
  fixes \<F>::"'X set set set"
  assumes A0:"\<forall>F \<in> \<F>. is_filter F" and A1:"\<F> \<noteq> {} \<and> \<F> \<noteq> {{}}"
  shows "is_filter (fgenby(\<F> ))"
  by (metis A0 A1 UNIV_witness bex_empty bot.extremum_uniqueI fcsystem_then_fcbase filter_base_gen_filter filter_generated_by_def filter_un0 pfmc_extensive pfmc_is_fm_closed)

lemma fil_union6:
  assumes A0:"\<forall>i \<in> I. (is_filter (EF(i)))" and A1:"EF`I \<noteq> {} \<and> EF`I \<noteq> {{}}"
  shows "\<forall>i \<in> I. ((EF(i)) \<subseteq> upclosure( pfmc (Sup (EF`(I))) ))"
  using pfmc_extensive upc_extensive by fastforce


lemma fil_union7:
  assumes A0:"\<forall>i \<in> I. (is_filter (EF(i)))" and A1:"EF`I \<noteq> {} \<and> EF`I \<noteq> {{}}" and A2:"is_filter G"
  shows "(\<forall>i \<in> I. ((EF(i)) \<subseteq> G)) \<longrightarrow> ( upclosure( pfmc (Sup (EF`(I))))  \<subseteq> G)"
proof
  let ?L="(\<forall>i \<in> I. ((EF(i)) \<subseteq> G))"
  let ?IM="EF`(I)"
  let ?UN="Sup ?IM"
  let ?S="upclosure(pfmc ?UN)"
  let ?R="?S \<subseteq> G"
  assume L0:?L
  show ?R
  proof
    fix a assume LtR_A0:"a \<in> ?S"
    obtain b where LtR_A1:"b \<in> (pfmc ?UN) \<and> a \<supseteq> b "
      using LtR_A0 upclosure_def by auto
    obtain F where LtR_A2:"(F \<in> Pow(?UN)) \<and> (finite F) \<and> b=(\<Inter>F)"
      by (smt (verit) CollectD LtR_A1 proper_finite_meet_closure_def)
    have LtR_B0:"F \<subseteq> ?UN" using LtR_A2 by blast
    have LtR_B1:"\<forall>f \<in> F. \<exists>i \<in> I. f \<in> EF(i)" using LtR_B0 by auto
    have LtR_B2:"\<forall>f \<in> F.  f \<in> G" using L0 LtR_B1 by fastforce
    have LtR_B3:"F \<subseteq> G" by (simp add: LtR_B2 subsetI)
    have LtR_B4:"(\<Inter>F) \<in> G"
      by (metis A2 Inter_empty LtR_A2 LtR_B3 filter_iff_fcsystem_inhabted filter_iff_pisystem_with_univ is_fcsystem_def)
    have LtR_B5:"(\<Inter>F) =b"using LtR_A2 by blast 
    have LtR_B6:"... \<subseteq> a" by (simp add: LtR_A1)
    show "a \<in> G"
      using A2 is_filter_def LtR_B4 LtR_B5 LtR_B6 is_upclosed_def by blast
  qed
qed

lemma fil_sup1:
  assumes A0:"\<forall>i \<in> I. (is_filter (EF(i)))" and A1:"EF`I \<noteq> {} \<and> EF`I \<noteq> {{}}"
  shows "IsSup2 (upclosure(pfmc (Sup (EF`(I))))) (EF`(I)) filter_set "
proof-
  let ?IM="(EF`(I))"
  let ?SUP="upclosure( pfmc (Sup (?IM)))"
  let ?IsUB="(\<lambda>G. (\<forall>i \<in> I. ((EF(i)) \<subseteq> G)))"
  have B0:"?SUP \<in> UpperBoundsIn ?IM filter_set "
  proof-
    have B00:"?SUP \<in> filter_set"  by (metis A0 A1 fil_union4 filter_set_def  filter_base_gen_filter mem_Collect_eq)
    have B01:"\<forall>Fi \<in> ?IM. Fi \<subseteq> ?SUP"  using A0 fil_union6 by blast
    with B00 B01 show ?thesis  by (simp add: upper_bounds_are_upper_bounds2)
  qed
  have B1:"\<forall>G \<in> filter_set. ?IsUB G \<longrightarrow> ?SUP \<subseteq> G" using A0 A1 fil_union7 filter_set_def by blast
  with B0 B1 show ?thesis  by (simp add: IsSup2_def)
qed
  

lemma mesh_prop1:
  assumes A0:"{a}# F" and A1:"a \<subseteq> b"
  shows "{b}#F"
proof-
  have B0:"\<forall>f \<in> F. ((a \<inter> f) \<noteq> {})" by (meson A0 insertI1 meshes_def)
  have B1:"\<forall>f \<in> F. ((a \<inter> f) \<subseteq> (b \<inter> f))" by (simp add: A1 inf.coboundedI1)
  have B2:"\<forall>f \<in> F. (b \<inter> f \<noteq> {})"  using B0 B1 by fastforce
  with B2 show ?thesis by (simp add: meshes_def)
qed

lemma mesh_prop2:
  assumes "is_upclosed F"
  shows "(a \<in> F \<longrightarrow> \<not>({(UNIV - a)}#F))"
  by (metis Diff_disjoint Int_commute meshes_def singletonI)

lemma mesh_prop3:
  assumes A0:"F \<in> proper_filterset \<and> G \<in> proper_filterset" 
  shows "F \<subseteq> G \<longrightarrow> F#G"
proof
  assume A1:"F \<subseteq> G"
  show "F#G"
  proof-
    have P0:"\<forall>f \<in>F. \<forall>g \<in> G. f \<inter> g \<noteq> {}"
    proof
      fix f assume B0:"f \<in> F"
      show "\<forall>g \<in> G. f \<inter> g \<noteq> {}"
      proof
        fix g assume B1:"g \<in> G"
        have B2:"f \<in> G" using A1 B0 by auto
        have B3:"is_properfilter G" using assms proper_filterset_def by auto 
        have B4:"is_pisystem G" using B3 is_filter_def is_properfilter_def by auto
        have B5:"f \<inter> g \<in> G" using B1 B2 B4 is_pisystem_def by auto
        have B6:"{} \<notin> G"  using B3 is_proper_def is_properfilter_def by auto       
        show "f \<inter> g \<noteq> {}"  using B5 B6 by fastforce
      qed
    qed
    show ?thesis by (simp add: P0 meshes_def)
  qed
qed

lemma mesh_prop4:
  assumes "is_upclosed A"
  shows "(x \<notin> A) \<longleftrightarrow> {(UNIV - x)}#A"
proof-
  let ?cx="UNIV-x" let ?S="{?cx}"
  let ?L="x \<notin> A" let ?R="?S#A"
  have LtR:"?L \<longrightarrow> ?R"  by (metis Diff_eq_empty_iff Int_Diff Int_commute assms inf_top.right_neutral meshes_def singletonD is_upclosed_def)
  have RtL:"?R \<longrightarrow> ?L" using assms mesh_prop2 by auto
  with LtR RtL show ?thesis by blast
qed
  
lemma mesh_prop5:
  assumes "is_upclosed A"
  shows "(x \<in> A) \<longleftrightarrow> \<not>({(UNIV - x)}#A)"
  using assms mesh_prop4 by blast

lemma mesh_prop6:
  assumes "is_upclosed A"
  shows "((UNIV-x) \<notin> A) \<longleftrightarrow> {x}#A"
  by (simp add: Diff_Diff_Int assms mesh_prop4)

lemma mesh_prop7:
  assumes "is_upclosed A"
  shows "((UNIV-x) \<in> A) \<longleftrightarrow> \<not>({x}#A)"
  using assms mesh_prop6 by auto


lemma mesh_prop8:
   "A#B \<longleftrightarrow> A \<subseteq> grill B"
proof-
  have Eq0:"A#B \<longleftrightarrow> (\<forall>a \<in> A. \<forall>b \<in> B. a \<inter> b \<noteq> {})" by (simp add: meshes_def)
  have Eq1:"... \<longleftrightarrow> (\<forall>a \<in> A. {a}#B)" by (simp add: meshes_def)
  have Eq2:"... \<longleftrightarrow> (\<forall>a \<in> A. a \<in> grill B)" by (simp add: grill_def)
  have Eq3:"... \<longleftrightarrow> A \<subseteq> grill B " by blast
  show ?thesis using Eq0 Eq1 Eq2 Eq3 by presburger
qed

lemma mesh_prop9:
  "A#B \<longleftrightarrow> B#A" by (metis Int_commute meshes_def)

lemma mesh_prop10:
   "A#B \<longleftrightarrow> B \<subseteq> grill A"
  using mesh_prop8 mesh_prop9 by blast

lemma mesh_prop11:
   "A \<subseteq> grill B \<longleftrightarrow> B \<subseteq> grill A"
  using mesh_prop10 mesh_prop8 by auto

lemma mesh_prop12:
  assumes "is_upclosed A"
  shows "x \<in> A \<longleftrightarrow> (UNIV - x) \<notin> grill A"
  by (meson assms empty_subsetI insert_subset mesh_prop4 mesh_prop8)


lemma mesh_prop13:
  assumes "is_upclosed A"
  shows "x \<notin> A \<longleftrightarrow> (UNIV - x) \<in>  grill A"
  using assms mesh_prop12 by blast

lemma mesh_prop14:
  assumes "is_upclosed A"
  shows "(UNIV - x) \<in> A \<longleftrightarrow> x \<notin> grill A"
  by (simp add: assms double_diff mesh_prop12)

lemma mesh_prop15:
  assumes "is_upclosed A"
  shows "(UNIV - x) \<notin>  A \<longleftrightarrow> x \<in> grill A"
  by (simp add: assms mesh_prop14)


lemma mesh_prop16:
  assumes A0:"\<forall>F \<in> EF. is_properfilter F" and A1:"finite EF" and A2:"is_properfilter G" and A0b:"EF \<noteq> {} \<and> EF \<noteq> {{}}"
  shows "G#(\<Inter>EF) \<longleftrightarrow> (\<exists>F \<in> EF. G#F)"
proof-
  let ?INF="\<Inter>EF" let ?L="G#?INF" let ?R=" (\<exists>F \<in> EF. G#F)"
  have A3:"is_upclosed G"  using A2 is_filter_def is_properfilter_def by blast
  have A4:"is_fcsystem G"
    using A2 filter_iff_fcsystem_with_univ is_properfilter_def by auto
  have RtL:"?R\<longrightarrow>?L"
    by (meson Inf_lower2 mesh_prop10) 
  have LtR:"\<not>?R \<longrightarrow> \<not>?L"
  proof
    assume NR:"\<not>(?R)"
    have B0:"(\<forall>F \<in> EF. \<not>(G#F))"  using NR by blast
    have B1:"(\<forall>F \<in> EF. \<exists>f \<in> F. \<not>(G#{f}))"  by (meson NR insertI1 meshes_def)
    have B2:"(\<forall>F \<in> EF. \<exists>f \<in> F. f \<notin> grill G)"
      by (simp add: B1 grill_def mesh_prop9)
    have B3:"(\<forall>F \<in> EF. \<exists>f \<in> F. (UNIV-f) \<in> G)"
      by (meson A3 B2 mesh_prop15) 
    obtain u where A5:"u=(\<lambda>F. SOME f. (f \<in> F \<and> (UNIV-f)\<in>G ) )" by simp
    have B4:" (\<forall>F \<in> EF. (UNIV-(u(F))) \<in> G)"  by (metis (no_types, lifting) A5 B3 someI)
    let ?H="u`EF"  let ?HC="{b. \<exists>h \<in>?H. b=UNIV-h}"
    have B5:"finite ?H" by (simp add: A1)
    have B6:"finite ?HC"  by (metis B5 finite_imageI image_def)
    have B7:"(\<forall>hc \<in> ?HC. hc \<in> G)" using B4 by blast
    have B8:"\<Inter>?HC \<in> G"
      by (metis (mono_tags, lifting) A2 B6 B7 Inter_empty filter_iff_fcsystem_with_univ is_fcsystem_def is_properfilter_def subsetI)
    have B9:"(UNIV - (\<Inter>?HC)) = \<Union>(?H)" by blast
    have B10:" \<Inter>?HC \<in> G  \<longrightarrow> \<Union>(?H) \<notin> grill G"
      using A3 B9 mesh_prop12 by fastforce
    have B11:"\<forall>h \<in> ?H. \<exists>F \<in> EF. h=u(F)" by blast
    have B12:"\<forall>F \<in> EF. (u(F) \<in> F)"  by (metis (mono_tags, lifting) A5 B3 someI_ex)
    have B13:"\<forall>F \<in> EF. \<exists>u \<in> ?H. u \<in> F" using B12 by blast
    have B14:"\<Union>(?H) \<in> ?INF"
      by (meson A0 B13 InterI Union_upper filter_iff_fcsystem_with_univ is_properfilter_def is_upclosed_def)
    show "\<not>(?L)"
      by (meson B10 B14 B8 in_mono mesh_prop10)
  qed
  with LtR RtL show ?thesis by blast 
qed

lemma grill_is_antitone:
  "A \<subseteq> B \<longrightarrow> grill B \<subseteq> grill A"
  by (meson equalityD1 mesh_prop11 subset_trans)

lemma grill_antitone_converse:
  assumes A0:"is_upclosed A \<and> is_upclosed B"
  shows " grill B \<subseteq> grill A \<longrightarrow> A \<subseteq> B "
  using assms mesh_prop13 by blast


lemma grill_maps_to_upclosed_sets:
  assumes "A \<noteq> {}"
  shows "is_upclosed (grill A)"
  by (simp add: grill_def mesh_prop1 is_upclosed_def)

lemma gril_is_grill_of_upclosure:
  assumes "A \<noteq> {}"
  shows "grill A = grill (upclosure A)"
proof-
  have B0:"A \<subseteq> upclosure A"
    by (simp add: upc_extensive)
  have B1:"grill (upclosure A) \<subseteq> grill A"
    by (simp add: B0 grill_is_antitone)  
  have B2:"grill A \<subseteq> grill (upclosure A)"
  proof
    fix a assume B2_A0:"a \<in> (grill A)"
    have B2_B1:"\<forall>b \<in> A. a \<inter> b \<noteq> {}"
      by (metis B2_A0 Int_commute mesh_prop10 meshes_def order_refl)
    show "a \<in> grill (upclosure A)"
    proof-
      have B2_B3:"\<forall>c \<in> upclosure A. a \<inter> c \<noteq> {}"
      proof
        fix c assume B2_A1:"c \<in> upclosure A"
        have B2_B4:"\<exists>b \<in> A. c \<supseteq> b"
          using B2_A1 upclosure_def by auto
        obtain b where B2_A2:"b \<in> A \<and> c \<supseteq> b" using B2_B4 by blast
        have B2_B5:"a \<inter> c \<supseteq> a \<inter> b" by (simp add: B2_A2 inf.coboundedI2)
        have B2_B6:"... \<noteq> {}" using B2_A2 B2_B1 by fastforce
        show "a \<inter> c \<noteq> {}" using B2_B6 by blast
      qed
      show ?thesis
        using B2_B3 mesh_prop15 upclosure_is_upclosed by auto
     qed
  qed
  with B1 B2 show ?thesis by blast
qed
     
lemma grill_of_grill_is_upclosure:
  "grill (grill A) = upclosure A"
  by (smt (verit, ccfv_SIG) emptyE empty_Collect_eq gril_is_grill_of_upclosure grill_antitone_converse mesh_prop11 order_class.order_eq_iff upc_extensive upclosure_def upclosure_is_upclosed)


lemma grill_involutory_in_upsets:
  "grill (grill A) = A \<longleftrightarrow> is_upclosed A"
  by (metis grill_antitone_converse grill_of_grill_is_upclosure subset_antisym upc_extensive upclosure_is_upclosed)

lemma degenerate_grill1:
  "grill (Pow UNIV) = {}"
  by (metis Pow_UNIV UNIV_I equals0I is_upclosed_def mesh_prop15)

lemma degenerate_grill2:
  "grill ({}) = Pow UNIV"
  by (metis degenerate_filter1 degenerate_grill1 filter_iff_fcsystem_with_univ grill_involutory_in_upsets)


lemma prime_upset_is_grill_of_filter:
  assumes A0:"A \<noteq> {} \<and> A \<noteq> {{}} \<and> (A \<noteq>  Pow UNIV)" and A1:"is_upclosed A" and A2:"is_prime A"
  shows "\<exists>F. (is_filter F) \<and> (A=grill F)" 
proof-
  have P3:"grill( grill (A) ) = A" by (simp add: A1 grill_involutory_in_upsets)
  let ?B="grill A"
  have P4:"\<forall>a \<in> ?B. (\<forall>b \<in> ?B. (a \<inter> b \<in> ?B))"
  proof
    fix a assume P4A0:"a \<in> ?B" show "\<forall>b \<in> ?B.  (a \<inter> b \<in> ?B)"
    proof
        fix b assume P4A1:"b \<in> ?B" 
        have P4B0:"(UNIV-a) \<notin> A"
          by (simp add: A1 P4A0 mesh_prop15)
        have P4B1:"(UNIV-b) \<notin> A" 
          by (simp add: P4A1 A1 mesh_prop15)
        have P4B2:"(UNIV-a) \<union> (UNIV-b) \<notin> A" 
          using A2 P4B0 P4B1 is_prime_def by blast
        have P4B3:"a \<inter> b \<in> ?B"  
          by (metis Diff_Int P4B2 A1 mesh_prop15)
        show " a \<inter> b \<in> ?B"
        by (simp add: P4B3)
      qed
  qed
  have P5:"is_pisystem ?B" by (simp add: P4 is_pisystem_def)
  have P6:"is_upclosed ?B"
    by (simp add: A0 grill_maps_to_upclosed_sets)
  have P7:"\<exists>F.  ((is_pisystem F) \<and> (is_upclosed F) \<and> (A = grill F))"
    using P3 P5 P6 by auto
  obtain F where P8:"((is_pisystem F) \<and> (is_upclosed F) \<and> (A = grill F))"
    using P7 by blast
  have P9:"is_inhabited F"
    using A0 P8 degenerate_grill2 is_inhabited_def by auto
  show ?thesis
    using is_filter_def P8 P9 by auto
qed

lemma filtergrill_then_upclosed_prime:
 assumes A0:"A \<noteq> {} \<and> A \<noteq> {{}}" and A1:"A=grill F" and A2:"is_filter F"
 shows "is_upclosed A \<and> is_prime A"
proof-
  have P0:"is_upclosed A" using A1 A2 grill_maps_to_upclosed_sets
    by (metis empty_iff filter_iff_fcsystem_with_univ)
  have P1:"\<forall>a. \<forall>b. (a\<notin>A\<and>b\<notin>A) \<longrightarrow> a\<union>b\<notin>A"
  proof-
    fix a b
    have P10:"(a \<notin> A \<and>  b \<notin>  A)\<longrightarrow>  a \<union> b \<notin> A"
    proof
      assume P1A0:" (a \<notin> A \<and>  b \<notin>  A)"
      obtain f where P1A1:"f \<in> F \<and> f \<inter> a = {}"
        by (metis A1 A2 Diff_disjoint Int_commute P1A0 filter_iff_pisystem_with_univ mesh_prop15)
      obtain g where P1A2:"g \<in> F \<and> g \<inter> b = {}"
        by (metis A1 A2 Diff_disjoint Int_commute P1A0 filter_iff_pisystem_with_univ mesh_prop15)
      have P1B1:"(f \<inter> g) \<in> F"
        using A2 is_filter_def P1A1 P1A2 is_pisystem_def by blast
      have P1B2:"(a \<union> b) \<inter> (f \<inter> g) = {}" using P1A1 P1A2 by blast
      have P1B3:"\<exists>h \<in> F. (a \<union> b) \<inter> h = {}" using P1B1 P1B2 by auto
      have P1B4:"(a\<union>b)\<notin>(grill F)"
        by (meson P1B3 dual_order.refl mesh_prop8 meshes_def) 
      show "a\<union>b\<notin>A" by (simp add: P1B4 assms)
     qed
     with P10 show ?thesis
       by (metis A1 A2 Diff_Un FiltersAgain3.is_filter_def is_pisystem_def mesh_prop14)
  qed
  have P2:"\<forall>a. \<forall>b. a\<union>b\<in>A  \<longrightarrow>  (a\<in>A\<or>b\<in>A)"  using P1 by auto
  have P3:"is_prime A" using P1 is_prime_def by blast
  show ?thesis by (simp add: P0 P3)
qed

lemma upclosed_prime_then_filtergrill:
  assumes A0:"A \<noteq> {} \<and> {} \<notin> A" and A1:"is_upclosed A" and A2:"is_prime A"
  shows "is_filtergrill A"
  by (metis A0 A1 A2 Pow_UNIV is_filtergrill_def iso_tuple_UNIV_I prime_upset_is_grill_of_filter singletonI)


lemma grill_of_proper_filter_is_filtergrill:
  assumes "is_properfilter F" shows "is_filtergrill (grill F)"
  using assms is_filtergrill_def is_properfilter_def by auto

lemma filtergrill_iff_grillage:
  assumes A0:"A \<noteq> {} \<and> {} \<notin> A"
  shows "is_filtergrill A \<longleftrightarrow> (is_grillage A)"
  by (metis assms filtergrill_then_upclosed_prime insertI1 is_filtergrill_def is_grillage_def is_inhabited_def upclosed_prime_then_filtergrill)


lemma grill_extensive:
  "\<forall>F \<in> proper_filterset. F \<subseteq> (grill F)"
  using mesh_prop10 mesh_prop3 by auto

lemma union_fchain_is_filter:
  assumes A0:"\<forall>i \<in> I. (is_filter (EF(i)))" and A1:"is_chain (EF`(I))" and A2:"EF`(I) \<noteq> {}"
  shows "is_filter (Sup (EF`(I)))"
proof-
  let ?F="Sup (EF`(I))"
  have F1:"is_upclosed ?F"
  proof-
    have F1_0:"\<And>a b. (a \<in> ?F \<and> a \<le> b) \<longrightarrow> b \<in> ?F"
    proof
      fix a b assume A3:"a \<in> ?F \<and> a \<le> b"
      obtain Fi where B0:"Fi \<in> EF`(I) \<and> a \<in> Fi"
      using A3 by auto
      have B1:"b \<in> Fi"
       by (metis A0 A3 B0 image_iff is_filter_def is_upclosed_def)
      show B4:"b \<in> ?F"
        using B0 B1 by blast
      qed
    show ?thesis
      by (meson F1_0 is_upclosed_def)
  qed
  have F2:"is_pisystem ?F"
  proof-
    have F2_0:"\<And>f1 f2. (f1 \<in> ?F \<and> f2 \<in> ?F) \<longrightarrow> ((f1 \<inter> f2) \<in> ?F)"
    proof
      fix f1 f2 assume A4:"f1 \<in> ?F \<and> f2 \<in> ?F"
      let ?f12="f1 \<inter> f2"
      obtain Fi where B0:"Fi \<in> EF`(I) \<and> f1 \<in> Fi"
        using A4 by blast
      obtain Fj where B1:"Fj\<in> EF`(I) \<and> f2 \<in> Fj"
        using A4 by blast
      have B2:"is_chain (EF`(I))"
        using A1 by auto
      from B2 have B3:"(Fi \<subseteq> Fj) \<or> (Fj \<subseteq> Fi)"
        by (meson B0 B1 is_chain_def)
      from B3 have B4:"(f1 \<in> Fi \<and> f2 \<in> Fi) \<or> (f1 \<in>Fj \<and> f2 \<in> Fj)"
        using B0 B1 by blast
      from B4 have B5:"(?f12 \<in> Fi) \<or> (?f12 \<in> Fj)"
        by (metis A0 B0 B1 image_iff is_filter_def is_pisystem_def)
      show "((f1 \<inter> f2) \<in> ?F)"
        using B0 B1 B5 by blast
    qed
    show ?thesis
      by (meson F2_0 is_pisystem_def)
  qed
  have F3:"is_inhabited ?F"
    using A0 A2 is_inhabited_def is_filter_def by fastforce
  show ?thesis
    by (simp add: F1 F2 F3 is_filter_def)
qed

lemma union_fchain_is_filter2:
  assumes A0:"\<forall>i \<in> I. (is_properfilter (EF(i)))" and A1:"is_chain (EF`(I))" and A2:"EF`(I) \<noteq> {}"
  shows "is_properfilter (Sup (EF`(I)))"
proof-
  let ?F="Sup (EF`(I))"
  have F1:"is_upclosed ?F"
  proof-
    have F1_0:"\<And>a b. (a \<in> ?F \<and> a \<le> b) \<longrightarrow> b \<in> ?F"
    proof
      fix a b assume A3:"a \<in> ?F \<and> a \<le> b"
      obtain Fi where B0:"Fi \<in> EF`(I) \<and> a \<in> Fi"
      using A3 by auto
      have B1:"b \<in> Fi"
        by (metis A0 A3 B0 filter_iff_pisystem_with_univ image_iff is_properfilter_def is_upclosed_def)
      show B4:"b \<in> ?F"
        using B0 B1 by blast
      qed
    show ?thesis
      by (meson F1_0 is_upclosed_def)
  qed
  have F2:"is_pisystem ?F"
  proof-
    have F2_0:"\<And>f1 f2. (f1 \<in> ?F \<and> f2 \<in> ?F) \<longrightarrow> ((f1 \<inter> f2) \<in> ?F)"
    proof
      fix f1 f2 assume A4:"f1 \<in> ?F \<and> f2 \<in> ?F"
      let ?f12="f1 \<inter> f2"
      obtain Fi where B0:"Fi \<in> EF`(I) \<and> f1 \<in> Fi"
        using A4 by blast
      obtain Fj where B1:"Fj\<in> EF`(I) \<and> f2 \<in> Fj"
        using A4 by blast
      have B2:"is_chain (EF`(I))"
        using A1 by auto
      from B2 have B3:"(Fi \<subseteq> Fj) \<or> (Fj \<subseteq> Fi)"
        by (meson B0 B1 is_chain_def)
      from B3 have B4:"(f1 \<in> Fi \<and> f2 \<in> Fi) \<or> (f1 \<in>Fj \<and> f2 \<in> Fj)"
        using B0 B1 by blast
      from B4 have B5:"(?f12 \<in> Fi) \<or> (?f12 \<in> Fj)"
        by (metis A0 B0 B1 filter_iff_pisystem_with_univ imageE is_pisystem_def is_properfilter_def)
      show "((f1 \<inter> f2) \<in> ?F)"
        using B0 B1 B5 by blast
    qed
    show ?thesis
      by (meson F2_0 is_pisystem_def)
  qed
  have F3:"is_inhabited ?F"
    using A0 A2 is_inhabited_def is_filter_def is_properfilter_def by fastforce
  show ?thesis
    by (metis (mono_tags, opaque_lifting) A0 F1 F2 F3 UnionE image_iff is_filter_def is_proper_def is_properfilter_def)
qed


lemma union_fchain_is_filter3:
  assumes A0: "\<forall>F \<in> EF. is_properfilter F" 
      and A1: "is_chain(EF)" 
      and A2: "EF \<noteq> {}"
  shows "is_properfilter (Sup (EF))"
proof -
  let ?F = "Sup (EF)"
  have F1: "is_upclosed ?F"
  proof -
    have F1_0: "\<And>a b. (a \<in> ?F \<and> a \<le> b) \<longrightarrow> b \<in> ?F"
    proof
      fix a b assume A3: "a \<in> ?F \<and> a \<le> b"
      then obtain F where B0: "F \<in> EF \<and> a \<in> F"
        using SUP_upper by blast
      then have "b \<in> F"
        using A0 A3 is_filter_def is_properfilter_def is_upclosed_def by blast
      thus "b \<in> ?F"
        using B0 SUP_upper by blast
    qed
    show ?thesis
      by (meson F1_0 is_upclosed_def)
  qed
  have F2: "is_pisystem ?F"
  proof -
    have F2_0: "\<And>f1 f2. (f1 \<in> ?F \<and> f2 \<in> ?F) \<longrightarrow> (f1 \<inter> f2) \<in> ?F"
    proof
      fix f1 f2 assume A4: "f1 \<in> ?F \<and> f2 \<in> ?F"
      then obtain F1 where B0: "F1 \<in> EF \<and> f1 \<in> F1"
        by blast 
      then obtain F2 where B1: "F2 \<in> EF \<and> f2 \<in> F2"
        using A4 by blast 
      from A1 have "F1 \<subseteq> F2 \<or> F2 \<subseteq> F1"
        by (simp add: B0 B1 is_chain_def)
      then have "f1 \<inter> f2 \<in> F1 \<or> f1 \<inter> f2 \<in> F2"
        using A0 B0 B1 is_filter_def is_properfilter_def is_pisystem_def by blast
      thus "(f1 \<inter> f2) \<in> ?F"
        using B0 B1 by blast
    qed
    show ?thesis
      by (meson F2_0 is_pisystem_def)
  qed
  have F3: "is_inhabited ?F"
    using A0 A2 is_inhabited_def is_filter_def is_properfilter_def by fastforce
  show ?thesis
    by (meson A0 F1 F2 F3 UnionE is_filter_def is_proper_def is_properfilter_def)
qed


lemma union_fchain_is_filter4:
  assumes A0: "\<forall>F \<in> EF. is_filter F" 
      and A1: "is_chain(EF)" 
      and A2: "EF \<noteq> {}"
  shows "is_filter (Sup (EF))"
proof -
  let ?F = "Sup (EF)"
  have F1: "is_upclosed ?F"
  proof -
    have F1_0: "\<And>a b. (a \<in> ?F \<and> a \<le> b) \<longrightarrow> b \<in> ?F"
    proof
      fix a b assume A3: "a \<in> ?F \<and> a \<le> b"
      then obtain F where B0: "F \<in> EF \<and> a \<in> F"
        using SUP_upper by blast
      then have "b \<in> F"
        using A0 A3 is_filter_def is_properfilter_def is_upclosed_def by blast
      thus "b \<in> ?F"
        using B0 SUP_upper by blast
    qed
    show ?thesis
      by (meson F1_0 is_upclosed_def)
  qed
  have F2: "is_pisystem ?F"
  proof -
    have F2_0: "\<And>f1 f2. (f1 \<in> ?F \<and> f2 \<in> ?F) \<longrightarrow> (f1 \<inter> f2) \<in> ?F"
    proof
      fix f1 f2 assume A4: "f1 \<in> ?F \<and> f2 \<in> ?F"
      then obtain F1 where B0: "F1 \<in> EF \<and> f1 \<in> F1"
        by blast 
      then obtain F2 where B1: "F2 \<in> EF \<and> f2 \<in> F2"
        using A4 by blast 
      from A1 have "F1 \<subseteq> F2 \<or> F2 \<subseteq> F1"
        by (simp add: B0 B1 is_chain_def)
      then have "f1 \<inter> f2 \<in> F1 \<or> f1 \<inter> f2 \<in> F2"
        using A0 B0 B1 is_filter_def is_properfilter_def is_pisystem_def by blast
      thus "(f1 \<inter> f2) \<in> ?F"
        using B0 B1 by blast
    qed
    show ?thesis
      by (meson F2_0 is_pisystem_def)
  qed
  have F3: "is_inhabited ?F"
    using A0 A2 is_inhabited_def is_filter_def is_properfilter_def by fastforce
  show ?thesis
    by (simp add: F1 F2 F3 is_filter_def)
qed


lemma ultrachumba0:
  assumes A0:"is_ultrafilter U"
  shows "(\<exists>F \<in> proper_filterset. U \<subset> F) \<longrightarrow> \<not>(IsMaximal2 U proper_filterset)"
  by (metis not_maximal)

lemma ultrachumba1:
  assumes A0:"is_ultrafilter U"
  shows "\<exists>a1. \<exists>a2. a1 \<union> a2 \<in> U \<and> (a1 \<notin> U \<and> a2 \<notin> U) \<longrightarrow> (\<exists>F \<in> proper_filterset. U  \<subset> F) " by blast

lemma ultrachumba1b:
  assumes A0:"is_ultrafilter U"
  shows "\<exists>a1. \<exists>a2. a1 \<union> a2 \<in> U \<and> (a1 \<notin> U \<and> a2 \<notin> U) \<longrightarrow> (\<exists>F \<in> proper_filterset. U  \<subset> F) " by blast

lemma ultrachumba4:
  fixes a1 a2
  assumes A0:"is_ultrafilter U" and A1:"\<not>(a1 \<union> a2 \<in> U \<longrightarrow> (a1 \<in> U) \<or> (a2 \<in> U))"
  shows "False"
  proof-
    have P:"(a1 \<union> a2 \<in> U) \<and> \<not>(a1 \<in> U \<or> a2 \<in> U) \<longrightarrow> False"
    proof
    assume A0b:"(a1 \<union> a2 \<in> U) \<and> \<not>(a1 \<in> U \<or> a2 \<in> U)" 
    have A1:"a1 \<union> a2 \<in> U \<and> (a1 \<notin> U \<and> a2 \<notin> U)" using A0 A0b by auto
    let ?S="{x. (a1 \<union> x) \<in> U}"
    have P2:"U \<subset> ?S"
      proof-
        have P20:"a1 \<union> a2 \<in> U" using A1 by auto
        have P21:"\<forall>u \<in> U. u \<subseteq> a1 \<union> u" by simp
        have P22:"is_upclosed U" using assms is_filter_def is_properfilter_def is_ultrafilter_def by blast
        have P23:"\<forall>u \<in> U. ((a1 \<union> u) \<in> U)" by (metis P22 Un_upper2 is_upclosed_def)
        have P24:"\<forall>u \<in> U. u \<in> ?S" by (simp add: P23)
        have P25:"U \<subseteq> ?S" using P24 by auto
        have P26:"a2 \<in> ?S \<and> \<not>(a2 \<in> U)" by (simp add: A1)
        have P27:"U \<subset> ?S" using P25 P26 by blast
        with P27 show ?thesis by simp
     qed
    have P3:"is_properfilter ?S"
      proof-
        have F1:"is_upclosed ?S"
          proof-
            have F1_0:"\<And>a b. (a \<in> ?S \<and> a \<le> b) \<longrightarrow> b \<in> ?S"
              proof
            fix a b assume A1_0:"(a \<in> ?S \<and> a \<subseteq>  b)"
            have F1_1:"a1 \<union> a \<in> U"
              using A1_0 by auto
            have F1_2:"a1 \<union> a \<subseteq> a1 \<union> b"
              by (simp add: A1_0 sup.coboundedI2)
            have F1_3:"is_upclosed U"
              using assms is_filter_def is_properfilter_def is_ultrafilter_def by blast
            have F1_4:"a1 \<union> b \<in> U"
              using F1_1 F1_2 F1_3 is_upclosed_def by blast
            show "b \<in> ?S"
              by (simp add: F1_4)
          qed
         show ?thesis using F1_0 is_upclosed_def by blast
       qed
       have F2:"is_pisystem ?S"
        proof-
          have F2_0:"\<And>f1 f2. (f1 \<in> ?S \<and> f2 \<in> ?S) \<longrightarrow> ((f1 \<inter> f2) \<in> ?S)"
            proof
              fix f1 f2 assume A4:"f1 \<in> ?S \<and> f2 \<in> ?S"
              let ?f12="f1 \<inter> f2"
              have F2_1:"a1 \<union> f1 \<in> U \<and> a1 \<union> f2 \<in> U"
                using A4 by auto
               have F2_2:"(a1 \<union> f1) \<inter> (a1 \<union> f2) \<in> U"
                 using F2_1 assms is_filter_def is_properfilter_def is_ultrafilter_def is_pisystem_def by blast
               have F2_3:"(a1 \<union> f1) \<inter> (a1 \<union> f2) = a1 \<union>(f1 \<inter> f2)"
                 by (simp add: sup_inf_distrib1)
               have F2_4:"a1 \<union>(f1 \<inter> f2) \<in> U"
                 using F2_2 F2_3 by auto
               show "?f12 \<in> ?S"
                 by (simp add: F2_4)
           qed
           show ?thesis using F2_0 is_pisystem_def by blast
         qed
      have F3:"is_inhabited ?S"
        using A1 is_inhabited_def by auto
      have F4:"is_proper ?S"
        by (simp add: A1 is_proper_def)
      show ?thesis
        by (simp add: F1 F2 F3 F4 is_filter_def is_properfilter_def)
      qed
    have P4:"\<not>(is_ultrafilter U)"
      by (metis P2 P3 is_ultrafilter_def mem_Collect_eq not_maximal proper_filterset_def)
    show "False"
      using P4 assms by blast
   qed
  show "False"
    using A1 P by auto
qed

lemma filter_is_ultra_iff_prime_alt:
  assumes A0:"is_properfilter U"
  shows "is_ultrafilter U \<longleftrightarrow> is_prime_alt U"
proof
  assume A1:"is_ultrafilter U"
  show "is_prime_alt U"
  proof-
    have B0:"\<forall>a. (a \<in> U) \<or> (UNIV-a) \<in> U"
      by (metis A1 Un_Diff_Int assms filter_iff_fcsystem_with_univ inf_top_left is_properfilter_def ultrachumba4)
    show ?thesis
      by (metis B0 Diff_disjoint assms filter_iff_pisystem_with_univ is_pisystem_def is_prime_alt_def is_proper_def is_properfilter_def)
  qed
  next
  assume A2:"is_prime_alt U"
  show "is_ultrafilter U" 
  proof-
    have B1:"IsMaximal2 U proper_filterset"
    proof (rule ccontr)
      assume A3:"\<not> (IsMaximal2 U proper_filterset)"
      obtain F where  A4:"F \<in> proper_filterset \<and> U \<subset> F "
        by (metis A3 CollectI IsMaximal2_def assms proper_filterset_def)
      obtain a where A5:"a\<in> F \<and> a \<notin> U"
        using A4 by blast
      have B2:"(UNIV-a) \<in> U"
        using A2 A5 is_prime_alt_def by blast
      show "False"
        by (meson A4 A5 B2 Diff_disjoint PowD Pow_top mesh_prop3 meshes_def psubsetD)
    qed
    show ?thesis
      by (simp add: B1 assms is_ultrafilter_def)
  qed
qed


lemma chumba_fucking_irene_wumba0:
  assumes "is_ultrafilter U"
  shows "\<forall>u.  u \<notin> (grill U) \<longrightarrow> (u \<notin> U)"
  by (metis assms filter_iff_fcsystem_with_univ is_prime_alt_def is_properfilter_def is_ultrafilter_def mesh_prop14 filter_is_ultra_iff_prime_alt)


lemma chumba_fucking_irene_wumba1:
  assumes "is_ultrafilter U"
  shows "(grill U) \<subseteq> U"
  by (meson assms filter_iff_fcsystem_with_univ is_prime_alt_def is_properfilter_def is_ultrafilter_def mesh_prop14 subsetI filter_is_ultra_iff_prime_alt)

lemma chumba_fucking_irene_wumba:
  "\<forall>U. is_ultrafilter U \<longrightarrow> (grill U) = U"
  by (simp add: IsMaximal2_def chumba_fucking_irene_wumba1 grill_extensive is_ultrafilter_def subset_antisym)

lemma filter_then_prime_imp_grillid:
  assumes A0:"is_properfilter F" and A1:"is_prime_alt F"
  shows "grill F = F"
  by (simp add: A0 A1 chumba_fucking_irene_wumba filter_is_ultra_iff_prime_alt)

lemma filter_is_ultrafilter_iff1:
  assumes  A0:"is_properfilter F"
  shows "(IsMaximal2 F proper_filterset) \<longleftrightarrow> (is_prime_alt F)"
  using assms filter_is_ultra_iff_prime_alt is_ultrafilter_def by auto 

lemma filter_is_ultrafilter_iff2:
  assumes  A0:"is_properfilter F"
  shows "(IsMaximal2 F proper_filterset) \<longleftrightarrow> (is_prime F)"
  by (smt (verit, ccfv_threshold) CollectI Diff_empty Pow_bottom UNIV_witness assms bex_empty
      chumba_fucking_irene_wumba filter_iff_pisystem_with_univ filter_is_ultrafilter_iff1
      filtergrill_then_upclosed_prime grill_extensive grill_involutory_in_upsets is_prime_alt_def 
      is_proper_def is_properfilter_def is_ultrafilter_def mesh_prop15 proper_filterset_def
      prime_upset_is_grill_of_filter singletonI subset_antisym)

lemma filter_is_ultrafilter_iff3:
  assumes  A0:"is_properfilter F"
  shows "(IsMaximal2 F proper_filterset) \<longleftrightarrow> (grill F = F)"
  by (metis Pow_UNIV assms chumba_fucking_irene_wumba degenerate_grill2 empty_not_UNIV 
      filter_is_ultrafilter_iff2 filtergrill_then_upclosed_prime is_proper_def is_properfilter_def
       is_ultrafilter_def singletonI)


(* voll vereinigungsdualer operator*)

lemma chumba_fucking_wumba_the_sqeakuel1:
  assumes A0:"I \<noteq> {}" and A1:"\<forall>i \<in> I. (is_upclosed (EF(i)))"
  shows "grill ( \<Inter>i \<in> I. EF(i) ) = (\<Union>i \<in> I. grill (EF(i)))"
proof-
  have B0:"\<forall>i \<in> I. ( \<Inter>i \<in> I. EF(i) ) \<subseteq> (EF(i))" 
     by (simp add: INT_lower)
  have B1:"\<forall>i \<in> I. grill (EF(i)) \<subseteq> grill ( \<Inter>i \<in> I. EF(i) )"
    by (simp add: INF_lower grill_is_antitone)
  have B2:"(\<Union>i \<in> I. grill (EF(i))) \<subseteq>  grill ( \<Inter>i \<in> I. EF(i))"
    using B1 by blast
  have B3:"\<forall>a. a \<notin> (\<Union>i \<in> I. grill (EF(i))) \<longrightarrow> (\<forall>i \<in> I. \<exists>fi \<in> (EF(i)). fi \<inter> a = {})"
    using A1 mesh_prop15 by fastforce
  have B12:"\<And>a. (a \<notin> (\<Union>i \<in> I. grill (EF(i)))) \<longrightarrow> (a \<notin> grill(( \<Inter>i \<in> I. EF(i))))"
  proof
  fix a assume A2:"a \<notin> (\<Union>i \<in> I. grill (EF(i)))"
  have B4:"\<forall>i \<in> I. \<exists>fi \<in> (EF(i)). fi \<inter> a = {}"
    by (meson A2 B3)
  obtain f where A3:"f=(\<lambda>i. SOME fi. fi \<in> (EF(i)) \<and>  (fi \<inter> a = {}) )"
    by simp
  have B5:"\<forall>i \<in> I. (f i) \<inter> a = {}"
    by (smt (verit, best) A3 B4 someI)
  have B6:"a \<inter> (\<Union>i \<in> I. (f i)) = {}"
    using B5 by blast
  have B7:"\<forall>i \<in> I. (f i) \<in> (EF(i))"
    by (smt (verit, del_insts) A3 B4 someI_ex)
  have B8:"\<forall>i \<in> I. (f i)\<subseteq> (\<Union>i \<in> I. (f i))" by blast
  have B9:"\<forall>i \<in> I. (\<Union>i \<in> I. (f i)) \<in> (EF(i))"
    by (meson A1 B7 B8 is_upclosed_def)
  have B10:"(\<Union>i \<in> I. (f i)) \<in>  ( \<Inter>i \<in> I. EF(i))"
    using B9 by blast
  have B11:"a \<notin> grill(( \<Inter>i \<in> I. EF(i)))"
    by (meson B10 B6 mesh_prop8 meshes_def subset_refl)
  show "a \<notin> grill(( \<Inter>i \<in> I. EF(i)))"
    using B11 by blast
  qed
  from B12 have B13:"(\<Union>i \<in> I. grill (EF(i))) \<supseteq>  grill ( \<Inter>i \<in> I. EF(i))" by blast
  with B2 B13 show ?thesis
    by blast
qed


lemma chumba_fucking_wumba_the_sqeakuel2:
  assumes A0:"I \<noteq> {}" and A1:"\<forall>i \<in> I. (is_upclosed (EF(i)))"
  shows "grill ( \<Union>i \<in> I. EF(i) ) = (\<Inter>i \<in> I. grill (EF(i)))"
proof-
  have B0:"\<forall>a. a \<in> grill ( \<Union>i \<in> I. EF(i) ) \<longleftrightarrow> (\<forall>i \<in> I. \<forall>fi \<in> (EF(i)). a \<inter> fi \<noteq> {})"
    by (simp add: grill_def meshes_def)
  have B1:"\<forall>a. (\<forall>i \<in> I. \<forall>fi \<in> (EF(i)). a \<inter> fi \<noteq> {})  \<longleftrightarrow> (\<forall>i \<in> I. a \<in> grill (EF(i)))"
    by (simp add: grill_def meshes_def)
  have B2:"\<forall>a. a \<in> grill ( \<Union>i \<in> I. EF(i) ) \<longleftrightarrow>  (\<forall>i \<in> I. a \<in> grill (EF(i)))"
    using B0 B1 by presburger
  have B3:"\<forall>a. a \<in> grill ( \<Union>i \<in> I. EF(i) ) \<longleftrightarrow>  a \<in>  (\<Inter>i \<in> I. grill (EF(i)))"
    by (simp add: B2)
  with B3 show ?thesis
    by blast
qed

lemma ultrachumba_existence0:
  "\<And>(C::('X set set set)). (C \<noteq> {} \<and> C \<subseteq> proper_filterset \<and>  is_chain C) \<longrightarrow> (\<exists>U \<in>proper_filterset. \<forall>c \<in>C. c \<subseteq> U)"
proof
  fix C::"('X set set set)" assume A00:"(C \<noteq> {} \<and> C \<subseteq> proper_filterset \<and> is_chain C)"
  have A1:"\<forall>c \<in> C. is_properfilter c"
    using A00 proper_filterset_def by blast
  have A2:"is_chain C"
    using A00 by auto
  have A3:"C \<noteq> {}"
    by (simp add: A00)
  let ?S="Sup(C)"
  have A4:"\<forall>c \<in> C. c \<subseteq> ?S"
    by (simp add: complete_lattice_class.Sup_upper)
  have A5:"is_properfilter(?S)"
    by (simp add: A00 A1 union_fchain_is_filter3)
  show "(\<exists>U \<in>proper_filterset. \<forall>c \<in>C. c \<subseteq> U)"
    using A4 A5 proper_filterset_def by auto
qed

lemma ultrachumba_existence0b:
  assumes "is_properfilter F"
  shows "\<And>(C::('X set set set)). (C \<noteq> {} \<and> C \<subseteq> (finer_filters F) \<and>  is_chain C) \<longrightarrow> (\<exists>U \<in> (finer_filters F). \<forall>c \<in>C. c \<subseteq> U)"
proof
  let ?\<F>="(finer_filters F)"
  fix C::"('X set set set)" assume A00:"(C \<noteq> {} \<and> C \<subseteq> ?\<F> \<and> is_chain C)"
  have A1:"\<forall>c \<in> C. is_properfilter c"
    using A00 finer_filters_def by blast
  have A2:"is_chain C"
    using A00 by auto
  have A3:"C \<noteq> {}"
    by (simp add: A00)
  let ?S="Sup(C)"
  have A4:"\<forall>c \<in> C. c \<subseteq> ?S"
    by (simp add: complete_lattice_class.Sup_upper)
  have A5:"is_properfilter(?S)"
    by (simp add: A00 A1 union_fchain_is_filter3)
  have A6:"\<forall>c \<in> C. F \<subseteq> c"
    by (metis A00 CollectD finer_filters_def in_mono)
  have A7:"F \<subseteq> ?S"
    by (simp add: A3 A6 less_eq_Sup)
  show "(\<exists>U \<in>?\<F>. \<forall>c \<in>C. c \<subseteq> U)"
    by (metis A4 A5 A7 CollectI finer_filters_def)
qed


lemma ultrachumba_existence0c:
  assumes "is_properfilter F"
  shows "\<And>(C::('X set set set)). (C \<noteq> {} \<and> C \<subseteq> (finer_filters F) \<and> is_chain C) \<longrightarrow> Sup(C) \<in> (finer_filters F)"
  by (smt (verit, ccfv_threshold) Ball_Collect CollectI Union_upper finer_filters_def in_mono subsetI subset_empty union_fchain_is_filter3)


lemma ultrachumba_existence2:
  "\<And>(C::('X set set set)). (C \<noteq> {} \<and> C \<subseteq> proper_filterset \<and>  is_chain C) \<longrightarrow> ( \<Union>C \<in> proper_filterset)"
  by (simp add: Ball_Collect proper_filterset_def union_fchain_is_filter3)

lemma ultrachumba_existence3:
  "\<And>(C::('X set set set)). (C \<noteq> {} \<and> C \<subseteq> filter_set \<and>  is_chain C) \<longrightarrow> ( \<Union>C \<in> filter_set)"
  by (simp add: Ball_Collect filter_set_def union_fchain_is_filter4)

lemma ultrachumba_existence3c:
  "\<And>(F::('X set set)) (C::('X set set set)). (C \<noteq> {} \<and> C \<subseteq>  (finer_filters F) \<and>  is_chain C) \<longrightarrow> ( \<Union>C \<in> (finer_filters F))"
  by (smt (verit, del_insts) CollectD CollectI Sup_upper2 ex_in_conv finer_filters_def subsetD union_fchain_is_filter3)

lemma ultrachumba_existence4:
  assumes "proper_filterset \<noteq> {}"
  shows "\<And>C. \<lbrakk>C\<noteq>{}; subset.chain proper_filterset C\<rbrakk> \<Longrightarrow> \<Union>C \<in> proper_filterset"
  by (simp add: is_chain_def subset_chain_def ultrachumba_existence2)

lemma ultrachumba_existence4c:
  assumes "is_properfilter F" and "(finer_filters F) \<noteq> {}"
  shows "\<And>C. \<lbrakk>C\<noteq>{}; subset.chain (finer_filters F) C\<rbrakk> \<Longrightarrow> \<Union>C \<in> (finer_filters F)"
  by (simp add: is_chain_def subset_chain_def ultrachumba_existence3c)


lemma ultrachumba_existence5:
  assumes "filter_set \<noteq> {}"
  shows "\<And>C. \<lbrakk>C\<noteq>{}; subset.chain filter_set C\<rbrakk> \<Longrightarrow> \<Union>C \<in> filter_set"
  by (simp add: is_chain_def subset_chain_def ultrachumba_existence3)


lemma ultra_chumba_existence6:
  assumes "filter_set \<noteq> {}" and ch: "\<And>C. \<lbrakk>C\<noteq>{}; subset.chain filter_set C\<rbrakk> \<Longrightarrow> \<Union>C \<in> filter_set"
  shows "\<exists>M\<in>filter_set. \<forall>X\<in>filter_set. M \<subseteq> X \<longrightarrow> X = M"
proof-
  have "\<And>C. subset.chain filter_set C \<Longrightarrow> \<exists>U\<in>filter_set. \<forall>X\<in>C. X \<subseteq> U"
    by (metis Union_upper empty_iff filter_intersection_is_filter filter_set_def mem_Collect_eq ultrachumba_existence5)
  then have "\<exists>M\<in>filter_set. \<forall>X\<in>filter_set. M \<subseteq> X \<longrightarrow> X = M"
    using subset_Zorn_nonempty[of filter_set] assms(1)
    by (metis empty_iff subset.chain_empty ultrachumba_existence5)
  thus ?thesis by blast
qed


lemma finer_chumba:
  assumes A0:"is_filter F" and A1:"\<forall>f \<in> F. a \<inter> f \<noteq> {}"
  shows "\<exists>G. is_filter G \<and> F \<subseteq> G \<and> a \<in> G"
proof-
  let ?G="fgenby({F}\<union>{{a}})"
  have B0:"is_filter ?G"
    by (metis (no_types, opaque_lifting) Sup_insert Un_insert_right bot_eq_sup_iff empty_not_insert empty_subsetI fcsystem_then_fcbase filter_base_gen_filter filter_generated_by_def pfmc_extensive pfmc_is_fm_closed subset_antisym)
  have B1:"F \<subseteq> ?G"
    by (metis Sup_insert filter_generated_by_def insert_is_Un order_trans pfmc_extensive sup_ge1 upc_extensive)
  have B2:"a \<in> ?G"
    by (metis Sup_insert Un_insert_right filter_generated_by_def insert_is_Un insert_subset order_trans pfmc_extensive upc_extensive)
  show ?thesis
    using B0 B1 B2 by blast
qed

lemma finer_chumba2:
  assumes A0:"is_properfilter F" and A1:"\<forall>f \<in> F. a \<inter> f \<noteq> {}"
  shows "\<exists>G. is_properfilter G \<and> F \<subseteq> G \<and> a \<in> G"
proof-
  let ?FA="{F}\<union>{{a}}"
  let ?GA="\<Union>?FA"
  let ?G="fgenby(?FA)"
  have B00:"fgenby(?FA) = upclosure(pfmc(?GA))"
    by (simp add: filter_generated_by_def)
  have B0:"is_filter ?G"
    by (metis B00 Sup_insert bot.extremum_uniqueI empty_not_insert fcsystem_then_fcbase filter_base_gen_filter insert_is_Un pfmc_extensive pfmc_is_fm_closed sup_bot_left sup_ge1)
  have B1:"F \<subseteq> ?G"
    using B00 pfmc_extensive upc_extensive by force
  have B2:"a \<in> ?G"
    using B00 pfmc_extensive upc_extensive by force
  have B3:"{} \<notin> F"
    using A0 is_proper_def is_properfilter_def by blast
  have B4:"{} \<notin> pfmc(F)"
    by (smt (verit, ccfv_threshold) A0 B3 PowD filter_iff_fcsystem_with_univ is_fcsystem_def is_properfilter_def mem_Collect_eq proper_finite_meet_closure_def)
  have B5:"{} \<notin> {a}"
    using A0 A1 filter_iff_fcsystem_with_univ is_properfilter_def by blast
  have B6:"{} \<notin> (pfmc(?GA))"
  proof (rule ccontr)
    assume B60:"\<not>({} \<notin> pfmc(?GA))"
    have B61:"{} \<in> pfmc(?GA)" using B60 by blast
    have B62:"a \<in> pfmc(?GA) \<longleftrightarrow> (\<exists>E \<in> Pow(?GA). E \<noteq> {} \<and> finite E \<and> \<Inter>E=a)"
      using proper_finite_meet_closure_def by auto
    obtain E where B62:"E \<in> Pow(?GA) \<and> E \<noteq> {} \<and> finite E \<and> \<Inter>E={}"
      by (smt (verit, best) B61 mem_Collect_eq proper_finite_meet_closure_def)
    let ?E0="E-{a}"
    have B63:"finite ?E0"
      by (simp add: B62)
    have B64:"?E0 \<subseteq> F"
      using B62 by blast
    have B63:"(\<Inter>?E0) \<in> F"
      by (metis A0 A1 B62 B63 B64 Diff_empty Diff_insert0 Int_empty_left cInf_singleton filter_iff_fcsystem_with_univ insert_Diff_single insert_absorb is_fcsystem_def is_properfilter_def)
    have B64:"(\<Inter>?E0)\<inter>a \<noteq> {}"
      by (simp add: A1 B63 Int_commute)
    have B65:"(\<Inter>?E0)\<inter>a = \<Inter>E"
      using B62 by auto
    show "False"
      using B62 B64 B65 by presburger
  qed
  have B7:"{} \<notin> upclosure(pfmc(?GA))"
    using B6 in_upclosure_imp by force
  have B8:"{}\<notin> ?G"
    using B00 B7 by blast
  have B8:"is_properfilter ?G"
    using B0 B8 is_proper_def is_properfilter_def by blast
  show ?thesis
    using B1 B2 B8 by auto
qed

lemma isultrafilter2:
  "is_ultrafilter U \<longleftrightarrow> (is_properfilter U \<and> IsMaximal1 U proper_filterset)"
  by (simp add: is_ultrafilter_def max1_equiv_max2)


lemma isultrafilter3:
  "is_ultrafilter U \<longleftrightarrow> (is_properfilter U \<and> (\<forall>F. is_properfilter F \<and> U \<subseteq> F \<longrightarrow> U=F))"
  by (metis IsMaximal2_def is_ultrafilter_def mem_Collect_eq proper_filterset_def psubsetE psubsetI)


lemma fully_eshreked0:
  assumes A0:"is_properfilter (F::('X set set))"
    shows "\<forall>C \<in> chains(finer_filters F).  C \<noteq> {} \<longrightarrow> \<Union>C \<in> (finer_filters F)"
proof
  let ?U="finer_filters F"
  fix C::"('X set set set)" assume A1:"C \<in> chains ?U"
  show "C \<noteq> {} \<longrightarrow> \<Union>C \<in> (finer_filters F)"
  proof
    assume A2:"C \<noteq> {} "
    show "\<Union>C \<in> (finer_filters F)"
      by (meson A1 A2 chainsD chainsD2 is_chain_def ultrachumba_existence3c)
  qed
qed


  


lemma fully_eshreked1:
  assumes A0:"is_properfilter (F::('X set set))"
    shows "\<exists>G . is_ultrafilter G \<and> F \<subseteq> G"
proof-
  let ?U="finer_filters F"
  have B0:"\<forall>C \<in> chains ?U .C \<noteq> {} \<longrightarrow> \<Union>C \<in> ?U"
    by (simp add: assms fully_eshreked0)
  have B1:"\<exists>S\<in>?U . \<forall>X\<in>?U . S \<subseteq> X \<longrightarrow> X = S"
    by (smt (verit, del_insts) assms empty_Collect_eq finer_filters_def order_refl subset_Zorn_nonempty ultrachumba_existence4c)
  obtain S where B2:"S \<in> ?U \<and> (\<forall>X\<in>?U . S \<subseteq> X \<longrightarrow> X = S)" using B1 by blast
  have B3:"S \<noteq> {}"
    using B2 FiltersAgain3.is_filter_def finer_filters_def is_inhabited_def is_properfilter_def by fastforce
  have B4:"\<And>G. (is_properfilter G) \<and> (S \<subseteq> G) \<Longrightarrow> F \<subseteq> G \<Longrightarrow> S = G"
    by (metis B2 CollectI finer_filters_def)
  show ?thesis
    by (metis B2 B4 CollectD finer_filters_def isultrafilter3 order_trans)
qed


end