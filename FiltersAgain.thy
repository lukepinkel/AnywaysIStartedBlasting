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

definition filspace::"'X set set set" where "filspace = {F. isfilter F}"


definition cl_fmeet1::"'X set set \<Rightarrow> 'X set set" where
    "cl_fmeet1 A = {a. \<exists>f\<in>Pow(A). finite f \<and>  f \<noteq> {} \<and>  \<Inter>f=a}"

definition cl_fmeet2::"'X set set \<Rightarrow> 'X set set" where
    "cl_fmeet2 A = {a. \<exists>f\<in>Pow(A). finite f  \<and>  \<Inter>f=a}"

definition upclosure::"'X::order set \<Rightarrow> 'X::order set" where
    "upclosure A = {x. \<exists>a \<in> A. a \<le> x}"


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



lemma lem_upcl1:
  "A \<subseteq> B \<longrightarrow> upclosure A \<subseteq> upclosure B"
  by (smt (verit, best) Collect_mono subsetD upclosure_def)

lemma lem_upcl2:
  "A \<subseteq> upclosure A"
  using upclosure_def by fastforce

lemma lem_upcl3:
  "upclosure (upclosure A) = upclosure A"
proof-
  let ?A1="upclosure A" let ?A2="upclosure ?A1"
  have LtR:"?A1 \<subseteq> ?A2"  by (simp add: lem_upcl2)
  have RtL:"?A2 \<subseteq> ?A1" by (smt (verit) CollectD CollectI order_trans subsetI upclosure_def)
  with LtR RtL show ?thesis by fastforce
qed

lemma lem_upcl4:
  "closure upclosure"
  by (simp add: closure_unfold extensive_def idempotent_def isotone_def lem_upcl1 lem_upcl2 lem_upcl3)

lemma lem_upcl5:
  "upclosed (upclosure A)"
  using lem_upcl3 upclosed_def upclosure_def by fastforce

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


lemma finite_intersections_base_app:
  assumes A0:"A \<noteq> {} \<and> A \<noteq> {{}}" shows "pi_base A \<longleftrightarrow> fc_base A"
proof-
  let ?L="pi_base A" let ?R="fc_base A"
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
          obtain c where RiL_B2:"c \<in> A \<and> c \<subseteq> \<Inter>?F" by (metis RiL_B0 RiL_B1 \<open>fc_base A\<close> fc_base_def)
          have RiL_B3:"\<Inter>?F = a \<inter> b"  by simp
          show "(\<exists>c  \<in> A. c \<subseteq> a \<inter> b )" using RiL_B2 by auto
        qed
      qed
      show ?thesis  using RiL_P0 pi_base_def by blast
    qed
  qed
  have LiR:"?L\<longrightarrow> ?R"
  proof
    assume P0:?L 
    have P1:"\<And>a1 a2. a1 \<in> A \<Longrightarrow> a2 \<in> A \<Longrightarrow>(\<exists>c  \<in> A. c \<subseteq> a1 \<inter> a2 )" using P0 pi_base_def by auto
    have P2: "\<And>F. ((F \<noteq> {}  \<and> finite F \<and> F  \<subseteq> A) \<longrightarrow>(\<exists>c. c \<in> A \<and> c \<subseteq> \<Inter>F))" by (metis P1 finite_intersections_base)
    show ?R  by (metis Inter_greatest P2 assms empty_iff fc_base_def order_class.order_eq_iff subset_iff)
  qed
  with RiL LiR show ?thesis by blast
qed
 

lemma lem_clfm6:
  "fcsystem (cl_fmeet1 A)"
  by (metis (mono_tags, lifting) Pow_iff cl_fmeet1_def fcsystem_def lem_clfm4d mem_Collect_eq)


lemma lem_clfm7:
  assumes "A \<noteq> {}"
  shows "fcsystem A \<longrightarrow> fc_base A"
  by (metis Inf_empty assms dual_order.refl equals0I fc_base_def fcsystem_def top_greatest)


lemma lem_clfm7b:
  assumes "A \<noteq> {}"
  shows "pisystem A \<longrightarrow> pi_base A"
  by (metis assms empty_subsetI finite_intersections_base_app finite_intersections_in_set_app insertI1 lem_clfm7 pi_base_def)


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
  assumes A0:"isfilter F1 \<and> isfilter F2"
  shows "F1 \<subseteq> F2 \<longleftrightarrow> (\<forall>f1 \<in> F1. \<exists>f2 \<in> F2. f1 \<supseteq> f2)"
  by (meson assms in_mono lem3 subsetI upclosed_def)


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

declare [[show_types]]

lemma fil_inter5:
  assumes A0:"\<forall>i \<in> I. (isfilter (EF(i)))" and A1:"EF`I \<noteq> {} \<and> EF`I \<noteq> {{}}"
  shows "Inf1 (EF`(I)) filspace = (Inf (EF`(I))) "
proof-
  let ?INF="Inf (EF`(I))"
  have B0:"\<forall>F \<in> filspace. (\<forall>Fi \<in> EF`(I). F \<subseteq> Fi) \<longrightarrow> F \<subseteq> ?INF"
  proof
    fix F::"'b set set" assume AB00:"F \<in> filspace"
    show "(\<forall>Fi \<in> EF`(I). F \<subseteq> Fi) \<longrightarrow> F \<subseteq> ?INF"
    proof
      assume AB01:"\<forall>Fi \<in> EF`(I). F \<subseteq> Fi"
      show "F \<subseteq> ?INF" using AB01 by blast
    qed
  qed
  have B1:"\<forall>Fi \<in> EF`(I). ?INF \<subseteq> Fi " by blast
  have B2:"?INF \<in> filspace" by (simp add: A0 fil_inter1 filspace_def)
  have B3:"?INF \<in> LowerBoundsIn (EF`(I)) filspace"
    by (simp add: B1 B2 lower_bounds_are_lower_bounds2)
  have B4:"IsInf2 ?INF (EF`I) filspace"  by (simp add: B0 B3 IsInf2_def)
  with A0 A1 B4 show ?thesis by (smt (verit, ccfv_SIG) B1 B2 Inf_greatest glb_then_inf1)
qed
  
lemma filter_un1:
  assumes A0:"\<forall>F \<in> EF. (isfilter F)" and A1:"EF \<noteq> {} \<and> EF \<noteq> {{}}"
  shows "(upclosed (\<Union>EF)) \<and> (UNIV \<in> (\<Union>EF))"
proof-
  let ?S="\<Union>EF"
  have P0:"upclosed ?S" by (meson A0 Union_iff isfilter_def upclosed_def)
  have P3:"UNIV \<in> ?S"  using A0 A1 lem2 by fastforce
  with P0 P3 show ?thesis by blast
qed

lemma filter_un2:
  assumes A0:"\<forall>i \<in> I. (isfilter (EF(i)))" and A1:"EF`I \<noteq> {} \<and> EF`I \<noteq> {{}}" and A2:"I \<noteq> {}"
  shows "Sup (EF`(I)) \<subseteq>  {H. \<exists>U. (H=(\<Inter>(U`(I))) \<and> (\<forall>i \<in> I. U(i) \<in> EF(i)))}"
proof
  let ?L="Sup (EF`(I))" let ?R=" {H. \<exists>U. (H=(\<Inter>(U`(I))) \<and> (\<forall>i \<in> I. U(i) \<in> EF(i)))}"
  fix a assume A3:"a \<in> ?L"  
  obtain j where "a \<in> (EF(j)) \<and> j \<in> I" using A3 by blast
  define U where "U=(\<lambda>i. if i \<noteq> j then UNIV else a)"
  have B0:"\<forall>i \<in> I. i \<noteq> j \<longrightarrow> U(i) = UNIV" by (simp add: U_def)
  have B1:"\<forall>i \<in> I. i=j \<longrightarrow> U(i) = a" by (simp add: U_def)
  have B2:"\<forall>i \<in> I. (U(i)) \<in> {UNIV, a}" using B0 B1 by blast
  have B3:"(U`(I)) \<subseteq> {UNIV, a}" using B2 by blast
  have B4:"\<forall>i \<in> I. (i=j) \<or> (i \<noteq> j)"  by simp
  have B5:"\<forall>i \<in> I. (U(i) = UNIV) \<or> (U(i) = a)" using B0 B1 by blast
  have B6:"a = UNIV \<inter> a" by simp
  have B7:"\<exists>j \<in> I. a = (U(j))" using B1 \<open>a \<in> EF j \<and> j \<in> I\<close> by blast
  have B8:"{a} \<subseteq> U`(I)"  using B7 by blast
  have B9:"a = (\<Inter>(U`(I)))" using B5 B8 by fastforce
  have B10:"\<forall>i \<in> I. (U(i)) \<in> (EF(i))"  using A0 U_def \<open>a \<in> EF j \<and> j \<in> I\<close> lem1 by fastforce
  show "a \<in> ?R" using B10 B9 by blast
qed

lemma filter_un3:
  assumes A0:"\<forall>i \<in> I. (isfilter (EF(i)))" and A1:"EF`I \<noteq> {} \<and> EF`I \<noteq> {{}}" and A2:"I \<noteq> {}"
  shows "\<forall>a \<in>  Sup (EF`(I)). (\<exists>U. (a=(\<Inter>(U`(I))) \<and> (\<forall>i \<in> I. U(i) \<in> EF(i))))"
proof
  let ?S="Sup (EF`(I))"
  let ?P="(\<lambda>H.  (\<exists>U. (H=(\<Inter>(U`(I))) \<and> (\<forall>i \<in> I. U(i) \<in> EF(i)))))"
  fix a assume A3:"a \<in> ?S "
  have B0:"?S \<subseteq> {H. ?P H}" by (simp add: A0 A1 A2 filter_un2)
  have B1:"a \<in> {H. ?P H} " using A3 B0 by blast
  show "?P a"  using B1 by blast
qed

lemma imp_in_upclosure:
  "\<And>a. a \<in> A \<longrightarrow> a \<in> (upclosure A)"  using lem_upcl2 by blast

lemma in_upclosure_imp:
  "\<And>a. a \<in> (upclosure A) \<longrightarrow>(\<exists>b \<in> A. a \<supseteq> b )" by (simp add: upclosure_def)


lemma fc_base_lem1:
  assumes A0:"fc_base B"
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
    show "\<exists>a3 \<in> B. a3 \<subseteq> a1 \<inter> a2" by (metis B0 B1 B2 assms fc_base_def)
  qed
qed

lemma fc_base_lem2:
  "fc_base A \<longleftrightarrow> (\<forall>F. (finite F \<and>  F  \<subseteq> A) \<longrightarrow> (\<exists>c \<in> A. c \<subseteq> \<Inter>F))"
  using fc_base_def by auto

lemma fc_base_lem3:
  "fc_base A \<longleftrightarrow> (\<forall>F \<in> Pow A. finite F \<longrightarrow> (\<exists>c \<in> A. c \<subseteq> \<Inter>F))"
  using fc_base_lem2 by auto

lemma fc_base_lem4:
   "fc_base A \<longleftrightarrow>  (\<forall>F \<in> Pow A. finite F  \<longrightarrow> HasLowerBound1 F A)"
  by (simp add: HasLowerBound2_def IsLowerBound_def fc_base_lem3 le_Inf_iff lower_bounded_equiv)

lemma filter_base_gen_filter:
  assumes A0:"fc_base B" shows "isfilter (upclosure B)"
proof-
  let ?F="upclosure B"
  have P0:"pisystem ?F"
  proof-
    have P00: "\<forall>a0 \<in> ?F. \<forall>a1 \<in> ?F. a0 \<inter> a1 \<in> ?F"
    proof
      fix a0 assume P00_A0:"a0 \<in> ?F"
      obtain b0 where P00_B0:"(b0 \<in> B) \<and> (b0 \<subseteq> a0)"  using P00_A0 in_upclosure_imp by blast
      show "\<forall>a1 \<in> ?F. a0 \<inter> a1 \<in> ?F"
      proof
        fix a1 assume P00_A1:"a1 \<in> ?F"
        obtain b1 where P00_B1:"(b1 \<in> B) \<and> (b1 \<subseteq> a1)"  using P00_A1 in_upclosure_imp by blast
        let ?b01="b0 \<inter> b1"
        obtain b where P00_B2:"(b \<in> B) \<and> (b \<subseteq> ?b01)" using P00_B0 P00_B1 fc_base_lem1  using assms by blast
        have P00_B3:"b \<subseteq> a0 \<inter> a1"  using P00_B0 P00_B1 P00_B2 by blast
        show "a0 \<inter> a1 \<in> ?F" by (metis (no_types, lifting) P00_B2 P00_B3 mem_Collect_eq upclosure_def)
      qed
    qed
    with P00 show ?thesis  by (simp add: pisystem_def)
  qed
  have P1:"upclosed ?F" by (simp add: lem_upcl5)
  have P2:"inhabited ?F" by (metis assms emptyE fc_base_def finite.emptyI inhabited_def lem_upcl2 subset_empty)
  with P0 P1 P2 show ?thesis by (simp add: isfilter_def)
qed
      
lemma fil_union4:
  assumes A0:"\<forall>i \<in> I. (isfilter (EF(i)))" and A1:"EF`I \<noteq> {} \<and> EF`I \<noteq> {{}}"
  shows "fc_base (cl_fmeet1 (Sup (EF`I)))"
proof-
  let ?IM="Sup (EF`I)" let ?B="cl_fmeet1 ?IM"
  have B0:"fcsystem ?B" by (simp add: lem_clfm6)
  have B1:"fc_base ?B" by (metis A1 Pow_empty lem_clfm2b lem_clfm6 lem_clfm7 subset_Pow_Union subset_empty subset_singletonD)
  with B1 show ?thesis by simp
qed

lemma fil_union5:
  assumes A0:"\<forall>i \<in> I. (isfilter (EF(i)))" and A1:"EF`I \<noteq> {} \<and> EF`I \<noteq> {{}}"
  shows "isfilter (upclosure( cl_fmeet1 (Sup (EF`(I))) ))"
  using A0 A1 fil_union4 filter_base_gen_filter by blast

end