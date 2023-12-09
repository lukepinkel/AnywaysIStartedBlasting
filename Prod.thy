theory Prod
  imports Main
begin

declare [[show_types]]

definition CartesianProduct::"'I set \<Rightarrow> ('I \<Rightarrow> 'X set) \<Rightarrow> ('I \<Rightarrow> 'X) set" where
  "CartesianProduct I X = {f::('I \<Rightarrow> 'X). \<forall>i \<in> I. (f i) \<in> (X i)}"

abbreviation Prod::"'I set \<Rightarrow> ('I \<Rightarrow> 'X set) \<Rightarrow> ('I \<Rightarrow> 'X) set" where
  "Prod I X \<equiv> CartesianProduct I X"

lemma prod_mem:
  "f \<in> Prod I X \<longleftrightarrow> (\<forall>i \<in> I. (f i) \<in> (X i))"
  by (simp add: CartesianProduct_def)

lemma fuckthis:
  fixes I::"'I set"
  fixes J::"'I \<Rightarrow> 'J set"
  fixes X::"'I \<Rightarrow> 'J \<Rightarrow> 'X set"
  assumes A0:"I \<noteq> {}" 
  shows "(\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) = (\<Inter>f\<in>(Prod I J). (\<Union>i \<in> I. (X i (f i))))"
proof-
  let ?S="\<Union>i \<in> I. J i"
  let ?P="Prod I J"
  have B0:"\<forall>f. f \<in> ?P \<longleftrightarrow> (\<forall>i \<in> I. (f i) \<in> (J i))"
    by (simp add: prod_mem)
  have B1:"\<forall>x. x \<in> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) \<longleftrightarrow> (\<exists>i \<in>I. x \<in>  (\<Inter>j\<in>(J i). (X i j)))"
    by blast
  have B2:"\<forall>x. x \<in> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) \<longleftrightarrow> (\<exists>i \<in> I. \<forall>j \<in> (J i). x \<in> (X i j))"
    by simp
  have B3:"\<forall>x \<in> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))). (\<exists>i \<in> I. \<forall>f \<in> ?P. x \<in> (X i (f i)))"
  proof
    fix x assume B3A0:"x \<in> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j)))"
    obtain i where "i \<in>I \<and>  x \<in>  (\<Inter>j\<in>(J i). (X i j))"
      using B3A0 by blast
    have B30:"\<forall>f \<in> ?P. \<forall>i \<in> I. ((f i) \<in> (J i))"
      by (simp add: prod_mem)  
    show "(\<exists>i \<in> I. \<forall>f \<in> ?P. x \<in> (X i (f i) ))"
      using B30 B3A0 by auto
  qed
  have B4:"\<forall>x. x \<in> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) \<longrightarrow>  ( \<forall>f \<in> ?P. \<exists>i \<in> I.  x \<in> (X i (f i)))"
    using B0 by blast
  have B5:"\<forall>x. x \<in> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) \<longrightarrow> (\<forall>f \<in> ?P. x \<in> (\<Union>i \<in> I. (X i (f i))))"
    by (simp add: B4)
  have B6:" (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) \<subseteq> (\<Inter>f\<in>?P. (\<Union>i \<in> I. (X i (f i))))"
    using B5 by blast
  have B7:"\<And>x. x \<notin> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) \<longrightarrow> x \<notin> (\<Inter>f\<in>?P. (\<Union>i \<in> I. (X i (f i))))"
  proof
    fix x assume B7A0:"x \<notin> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j)))"
    have B70:"\<forall>i \<in> I. x \<notin>(\<Inter>j\<in>(J i). (X i j))"
      using B7A0 by blast
    have B71:"\<forall>i \<in> I. {j. j\<in> (J i) \<and> (x \<notin> (X i j))} \<noteq> {}"
      using B70 by fastforce
    define K where "K=(\<lambda>(i::('I)).  {j. j\<in> (J i) \<and> (x \<notin> (X i j))})"
    define f where "f=( \<lambda>(i::('I)). SOME j. j \<in> (K i))"
    have B72:"f \<in> ?P"
      by (metis (mono_tags, lifting) B0 B71 Collect_empty_eq K_def f_def mem_Collect_eq verit_sko_ex')
    have B73:"\<forall>i \<in> I. x \<notin> (X i (f i))"
      by (metis (mono_tags, lifting) B71 Collect_empty_eq K_def f_def mem_Collect_eq someI_ex)
    have B74:"x \<notin>  (\<Union>i \<in> I. (X i (f i)))"
      using B73 by blast
    show "x \<notin> (\<Inter>f\<in>?P. (\<Union>i \<in> I. (X i (f i))))"
      using B72 B74 by blast
  qed
  have B8:"\<forall>x. x \<notin> (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j))) \<longrightarrow> x \<notin> (\<Inter>f\<in>?P. (\<Union>i \<in> I. (X i (f i))))"
    using B7 by blast
  have B9:"(\<Inter>f\<in>?P. (\<Union>i \<in> I. (X i (f i)))) \<subseteq>  (\<Union>i\<in>I. (\<Inter>j\<in>(J i). (X i j)))"
    using B8 by blast
  with B6 B9 show ?thesis
    by blast
qed
  
    

end
