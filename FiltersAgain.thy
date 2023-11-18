theory FiltersAgain
  imports Main "./Posets"
begin
hide_type Filter.filter

definition inhabited::"'X set  \<Rightarrow> bool" where "inhabited X \<equiv> X \<noteq> {}"

definition pisystem::"'X set set \<Rightarrow> bool" where "pisystem X \<equiv> (\<forall>a b. a \<in> X  \<longrightarrow> b \<in> X \<longrightarrow> a \<inter> b  \<in> X)"

definition pi_base::"'X set set \<Rightarrow> bool" where "pi_base X \<equiv> (\<forall>a b. a \<in> X  \<longrightarrow> b \<in> X \<longrightarrow>(\<exists>c  \<in> X. c \<subseteq> a \<inter> b ))"

definition fcsystem::"'X set set \<Rightarrow> bool" where "fcsystem X \<equiv> (\<forall>F. F \<noteq> {} \<longrightarrow> finite F \<longrightarrow> F  \<subseteq> X \<longrightarrow> \<Inter>F \<in> X)"

definition fc_base::"'X set set \<Rightarrow> bool" where "fc_base X \<equiv> (\<forall>F. finite F \<longrightarrow> F  \<subseteq> X \<longrightarrow> (\<exists>c \<in> X. c \<subseteq> \<Inter>F))"

definition upclosed::"'X::order set \<Rightarrow> bool" where "upclosed X \<equiv> (\<forall>a b. a \<le> b \<longrightarrow>  a \<in> X \<longrightarrow>  b \<in> X)"

definition isfilter::"'X set set \<Rightarrow> bool" where "isfilter F \<equiv> (pisystem F \<and> upclosed F \<and> inhabited F)"

definition cl_fmeet1::"'X set set \<Rightarrow> 'X set set" where
    "cl_fmeet1 A = {a. \<exists>f\<in>Pow(A). finite f \<and>  f \<noteq> {} \<and>  \<Inter>f=a}"

definition cl_fmeet2::"'X set set \<Rightarrow> 'X set set" where
    "cl_fmeet2 A = {a. \<exists>f\<in>Pow(A). finite f  \<and>  \<Inter>f=a}"

lemma lem_clfm1:
  "(cl_fmeet1 A) \<union> {UNIV} = cl_fmeet2 A" 
proof-
  let ?C1="(cl_fmeet1 A)" let ?C2="cl_fmeet2 A"
  have B0:"?C1 \<subseteq> ?C2"
  proof
    fix c1 assume P0:"c1 \<in> ?C1"
    obtain f where P1:"f \<in> Pow(A) \<and>  finite f \<and>  f \<noteq> {} \<and>  \<Inter>f=c1" by (smt (verit, best) P0 CollectD cl_fmeet1_def)
    show "c1 \<in> ?C2"  using P1 cl_fmeet2_def by blast
  qed
  have B1:"UNIV \<in> ?C2 "using cl_fmeet2_def by auto
  have B2:"?C1 \<union> {UNIV} \<subseteq> ?C2" by (simp add: B0 B1)
  have B3:"?C2 \<subseteq> ?C1 \<union> {UNIV}"
    by (smt (verit) Inf_empty UnCI cl_fmeet1_def cl_fmeet2_def insert_iff mem_Collect_eq subsetI)
  show ?thesis using B2 B3 by blast
qed

lemma lem_clfm2:
  "A \<subseteq> cl_fmeet2 A"
proof-
  have B0:"\<forall>a \<in> A. finite {a} \<and> {a} \<in> Pow(A) \<and> a=\<Inter>{a}" by simp
  have B1:"\<forall>a \<in> A. \<exists>f \<in> Pow(A). finite f \<and> \<Inter>f=a"using B0 by blast
  with B1 show ?thesis  by (simp add: cl_fmeet2_def subsetI)
qed

lemma lem_clfm2b:
  "A \<subseteq> cl_fmeet1 A"
proof-
  have B0:"\<forall>a \<in> A. finite {a} \<and> {a} \<noteq> {}  \<and> {a} \<in> Pow(A) \<and> a=\<Inter>{a}" by simp
  have B1:"\<forall>a \<in> A. \<exists>f \<in> Pow(A). f \<noteq> {} \<and> finite f \<and> \<Inter>f=a"using B0 by blast
  with B0 B1 show ?thesis by (smt (verit, del_insts) CollectI cl_fmeet1_def subsetI)
qed


lemma lem_clfm3:
  "A \<subseteq> B \<longrightarrow> cl_fmeet2 A \<subseteq> cl_fmeet2 B"
  by (smt (verit) Pow_iff cl_fmeet2_def mem_Collect_eq subset_eq)
  
lemma lem_clfm3b:
  "A \<subseteq> B \<longrightarrow> cl_fmeet1 A \<subseteq> cl_fmeet1 B"
  by (smt (verit) CollectD CollectI PowD PowI cl_fmeet1_def order_trans subsetI)
  

lemma lem_clfm4:
  "cl_fmeet2 A = cl_fmeet2 (cl_fmeet2 A)"
proof-
  let ?C1="cl_fmeet2 A"
  let ?C2="cl_fmeet2 ?C1"
  have B0:"A \<subseteq> ?C1" by (simp add: lem_clfm2)
  have B1:"?C1 \<subseteq> ?C2" by (simp add: lem_clfm2)
  have B2:"?C2 \<subseteq> ?C1"
  proof
    fix a assume A0:"a \<in> ?C2"
    obtain f where A1:"f= (\<lambda>a. SOME E. E \<in> Pow(A) \<and> finite E \<and> a=\<Inter>E)" by simp
    obtain B where A2:"B \<in> (Pow ?C1) \<and> finite B \<and> a=(\<Inter>B)" by (smt (verit, best) A0 cl_fmeet2_def mem_Collect_eq)
    have B20:"\<forall>b \<in> B. \<exists>E \<in> Pow (A). finite E \<and> b = \<Inter>E"
      by (smt (verit, ccfv_threshold) A2 CollectD Union_Pow_eq Union_iff cl_fmeet2_def)
    have B30:"\<forall>b \<in> B. (b=(\<Inter>(f b)))" by (metis (mono_tags, lifting) A1 B20 someI)
    have B40:"a=(\<Inter>b\<in>B. (\<Inter>(f b)))" using A2 B30 by auto
    let ?D="\<Union>b \<in> B. (f b)"
    have B50:"\<forall>b \<in> B. finite (f b)" by (metis (mono_tags, lifting) A1 B20 verit_sko_ex_indirect2)
    have B60:"\<forall>b \<in> B. (f b) \<in> Pow A"  by (metis (mono_tags, lifting) A1 B20 verit_sko_ex_indirect2)
    have B70:"?D \<in> Pow(A)" using B60 by blast
    have B80:"finite ?D" using A2 B50 by blast
    have B90:"a=\<Inter>?D" using B40 by blast
    show B110:"a \<in> ?C1" using B70 B80 B90 cl_fmeet2_def by blast
  qed
  show ?thesis using B1 B2 by auto
qed

lemma lem_clfm4b:
  assumes "A \<noteq> {}" shows "cl_fmeet1 A = cl_fmeet1 (cl_fmeet1 A)"
proof-
  let ?C1="cl_fmeet1 A"
  let ?C2="cl_fmeet1 ?C1"
  have B0:"A \<subseteq> ?C1" by (simp add: lem_clfm2b)
  have B1:"?C1 \<subseteq> ?C2" by (simp add: lem_clfm2b)
  have B2:"?C2 \<subseteq> ?C1"
  proof
    fix a assume A0:"a \<in> ?C2"
    obtain f where A1:"f= (\<lambda>a. SOME E. E \<in> Pow(A) \<and> E \<noteq> {} \<and> finite E \<and> a=\<Inter>E)" by simp
    obtain B where A2:"B \<in> (Pow ?C1) \<and> finite B \<and> B \<noteq> {} \<and> a=(\<Inter>B)" by (smt (verit, best) A0 cl_fmeet1_def mem_Collect_eq)
    have B20:"\<forall>b \<in> B. \<exists>E \<in> Pow (A). finite E \<and> E \<noteq> {}  \<and> b = \<Inter>E" by (smt (verit, ccfv_threshold) A2 CollectD Union_Pow_eq Union_iff cl_fmeet1_def)
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
    show B120:"a \<in> ?C1" using B110 B70 B80 B90 cl_fmeet1_def by blast
  qed
  show ?thesis using B1 B2 by auto
qed

lemma lem_clfm4c:
  assumes "A = {}" shows "cl_fmeet1 A = cl_fmeet1 (cl_fmeet1 A)"
  by (simp add: assms cl_fmeet1_def)

lemma lem_clfm4d:
  "cl_fmeet1 A = cl_fmeet1 (cl_fmeet1 A)"
  by (metis lem_clfm4b lem_clfm4c)
    
lemma lem_clfm5:
  "closure cl_fmeet2"
  by (metis closure_unfold extensive_def idempotent_def isotone_def lem_clfm2 lem_clfm3 lem_clfm4) 

lemma lem_clfm5b:
  "closure cl_fmeet1"
proof-
  have P0: "isotone cl_fmeet1"  by (simp add: isotone_def lem_clfm3b)
  have P1: "extensive cl_fmeet1" by (simp add: extensive_def lem_clfm2b) 
  have P2: "pseudo_closure cl_fmeet1" by (simp add: pseudo_closure_def P0 P1)
  have P3: "idempotent cl_fmeet1" using idempotent_def lem_clfm4d by auto
  with P2 P3 show ?thesis by (simp add: closure_def)
qed


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

lemma unfold_double:
  assumes "\<forall>x y. P x \<longrightarrow> Q y \<longrightarrow> R x y"
  shows "\<forall>x y. (P x \<and> Q y) \<longrightarrow>  R x y"
  by (simp add: assms)


lemma finite_intersections_in_set_app:
  assumes A0:"A \<noteq> {} \<and> A \<noteq> {{}}" shows "pisystem A \<longleftrightarrow> fcsystem A"
proof-
  let ?L="pisystem A" let ?R="fcsystem A"
  have RiL:"?R \<longrightarrow> ?L"
    by (metis (no_types, opaque_lifting) Inf_insert cInf_singleton empty_iff empty_subsetI fcsystem_def finite.emptyI finite_insert insert_subset pisystem_def)
  have LiR:"?L\<longrightarrow> ?R"
  proof
    assume P0:?L 
    have P1:"\<And>a1 a2. a1 \<in> A \<Longrightarrow> a2 \<in> A \<Longrightarrow> a1 \<inter> a2 \<in> A" using P0 pisystem_def by blast
    have P2: "\<And>F. ((F \<noteq> {}  \<and> finite F \<and> F  \<subseteq> A) \<longrightarrow>( \<Inter>F \<in> A))"
    proof
      fix F assume P3:"F \<noteq> {} \<and> finite F \<and> F \<subseteq> A"
      show "(\<Inter>F) \<in> A"
        by (simp add: P1 P3 finite_intersections_in_set)
    qed
    show ?R by (simp add: P2 fcsystem_def)
  qed
  with RiL LiR show ?thesis by blast
qed
 
lemma lem1:
  "isfilter F \<longleftrightarrow>  (pisystem F \<and> upclosed F \<and>  (UNIV \<in>  F))"
  by (metis ex_in_conv inhabited_def isfilter_def top_greatest upclosed_def)

lemma lem2:
  "isfilter F \<longleftrightarrow> (fcsystem F \<and>  upclosed F \<and>  (UNIV \<in>  F))"
  using finite_intersections_in_set_app lem1 by auto

lemma lem3:
  "isfilter F \<longleftrightarrow> (fcsystem F \<and> upclosed F \<and> inhabited F)"
proof-
  let ?lhs="isfilter F" let ?rhs="(fcsystem F \<and> upclosed F \<and> inhabited F)"
  have LtR:"?lhs \<longrightarrow> ?rhs"
  proof
    assume A0:"?lhs"
    have B0:"fcsystem F \<and> upclosed F" using A0 lem2 by auto
    have B1:"UNIV \<in> F" using A0 lem1 by auto
    have B2:"F \<noteq> {}" using B1 by auto
    show "?rhs" by (simp add: B0 B2 inhabited_def)
  qed
  have RtL:"?rhs \<longrightarrow> ?lhs"
  proof
    assume A1:"?rhs"
    have B0:"fcsystem F \<and> upclosed F \<and> F \<noteq> {}" using A1 lem2 inhabited_def by auto
    have B1:"\<exists>x. x \<in> F" using B0 by auto
    obtain x where A2:"x \<in> F" using B1 by auto
    have B2:"x \<subseteq> UNIV"  by simp
    have B3:"UNIV \<in> F" using A1 A2 B2 upclosed_def by blast
    show "?lhs" by (simp add: A1 B3 lem2)
  qed
  with LtR RtL show ?thesis by blast
qed

lemma lem4:
  assumes A0"isfilter F1 \<and> isfilter F2"
  shows "F1 \<subseteq> F2 \<longleftrightarrow> (\<forall>f1 \<in> F1. \<exists>f2 \<in> F2. f1 \<supseteq> f2)"
  by (meson assms(2) lem3 subset_eq upclosed_def)


lemma fil_inter1:
  assumes A0:"\<forall>F \<in> EF. (isfilter F)"
  shows "isfilter (\<Inter>EF)"
proof-
  let ?I="\<Inter>EF"
  have B0:"\<forall>F \<in> EF. (fcsystem F \<and> upclosed F \<and> inhabited F \<and> F \<noteq> {} \<and> pisystem F \<and> UNIV \<in> F)"
    by (metis assms inhabited_def lem1 lem3)
  have P0:"UNIV \<in> ?I" by (simp add: B0)
  have P1:"pisystem ?I" by (meson B0 Inter_iff pisystem_def)
  have P2:"upclosed ?I" by (meson B0 Inter_iff upclosed_def)
  with P0 P1 P2 show ?thesis  by (simp add: lem1)
qed


lemma fil_inter2:
  assumes A0:"\<forall>F \<in> EF. (isfilter F)" and A1:"\<forall>F \<in> EF. G \<subseteq> F"
  shows "G \<subseteq> (\<Inter>EF)" by (simp add: A1 Inter_greatest)

lemma fil_inter3:
  assumes A0:"\<forall>F \<in> EF. (isfilter F)"
  shows "Inf EF = \<Inter>EF" by simp

declare [[show_types]]

lemma fil_inter4:
  assumes A0:"\<forall>i \<in> I. (isfilter (EF(i)))" and A1:"EF`I \<noteq> {} \<and> EF`I \<noteq> {{}}"
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
    have B4:"\<forall>i \<in> I. a \<in> (EF(i))" by (meson A0 B3 lem2 upclosed_def)
    show "a \<in> ?L" using B4 by blast
  qed
  from LtR RtL have Eq:"?R = ?L" by blast
  with Eq show ?thesis by simp
qed

end