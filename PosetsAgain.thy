theory PosetsAgain
  imports Main
begin


definition IsBoundedAbove::"'X::order set \<Rightarrow> bool" where
  "IsBoundedAbove A \<equiv> (A={} \<or> (\<exists>u. \<forall>a \<in> A. a \<le> u))"

definition IsBoundedBelow::"'X::order set \<Rightarrow> bool" where
  "IsBoundedBelow A \<equiv> (A={} \<or> (\<exists>l. \<forall>a \<in> A. l \<le> a))"

definition HasMaximum::"'X::order set \<Rightarrow> bool " where
  "HasMaximum A \<equiv> (\<exists>m \<in> A. \<forall>a \<in> A. a \<le> m)"

definition HasMinimum::"'X::order set \<Rightarrow> bool " where
  "HasMinimum A \<equiv> (\<exists>m \<in> A. \<forall>a \<in> A. m \<le> a)"

definition Maximum::"'X::order set \<Rightarrow> 'X::order" where
  "Maximum A = (THE m.( m \<in> A \<and> (\<forall>a \<in> A. a \<le> m)))"

definition Minimum::"'X::order set \<Rightarrow> 'X::order" where
  "Minimum A = (THE m.( m \<in> A \<and> (\<forall>a \<in> A. m \<le> a)))"

definition UpperBounds::"'X::order set \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set" where
  "UpperBounds A X = {x \<in> X. \<forall>a \<in> A. a\<le> x}"

definition LowerBounds::"'X::order set \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set" where
  "LowerBounds A X = {x \<in> X. \<forall>a \<in> A. x \<le> a}"

definition Supremum::"'X::order set \<Rightarrow>'X::order set \<Rightarrow>'X::order " where
  "Supremum A X = Minimum(UpperBounds A X)"

definition Infimum::"'X::order set \<Rightarrow>'X::order set \<Rightarrow>'X::order " where
  "Infimum A X = Maximum(LowerBounds A X)"

definition HasSup::"'X::order set \<Rightarrow> 'X::order set \<Rightarrow> bool" where
  "HasSup A X \<equiv> HasMinimum (UpperBounds A X)"

definition HasInf::"'X::order set \<Rightarrow> 'X::order set \<Rightarrow> bool" where
  "HasInf A X \<equiv> HasMaximum (LowerBounds A X)"

lemma max_lemma1:
  assumes "HasMaximum A"
  shows "(\<exists>!m. (m \<in> A \<and> (\<forall>a \<in> A. a \<le> m)))"
  by (meson HasMaximum_def assms order_antisym)

lemma max_lemma2:
  assumes "HasMaximum A"
  shows "((Maximum A) \<in> A) \<and> (\<forall>a \<in> A. a \<le> (Maximum A)) "
proof-
  let ?M="THE m.( m \<in> A \<and> (\<forall>a \<in> A. a \<le> m))"
  have B0:"\<exists>!M. (M \<in> A \<and> (\<forall>a \<in> A. a \<le> M))" by (simp add: assms max_lemma1)
  have B1:"(?M \<in> A) \<and>  (\<forall>a \<in> A. a \<le> ?M)" by (smt (verit, ccfv_threshold) B0 the_equality)
  have B2:"?M=Maximum A"  by (simp add: Maximum_def)
  have B3:"(Maximum A) \<in> A \<and>  (\<forall>a \<in> A. a \<le> (Maximum A))" using B1 B2 by auto
  with B3 show ?thesis by simp
qed

lemma min_lemma1:
  assumes "HasMinimum A"
  shows "(\<exists>!m. (m \<in> A \<and> (\<forall>a \<in> A. m\<le> a)))"
  by (meson HasMinimum_def assms order_antisym)

lemma min_lemma2:
  assumes "HasMinimum A"
  shows "((Minimum A) \<in> A) \<and> (\<forall>a \<in> A. (Minimum A) \<le> a) "
proof-
  let ?m="THE m.( m \<in> A \<and> (\<forall>a \<in> A. m\<le> a))"
  have B0:"\<exists>!m. (m \<in> A \<and> (\<forall>a \<in> A. m \<le> a))" by (simp add: assms min_lemma1)
  have B1:"(?m \<in> A) \<and>  (\<forall>a \<in> A. ?m \<le> a)" by (smt (verit, ccfv_threshold) B0 the_equality)
  have B2:"?m=Minimum A"  by (simp add: Minimum_def)
  have B3:"(Minimum A) \<in> A \<and>  (\<forall>a \<in> A. (Minimum A) \<le> a)" using B1 B2 by auto
  with B3 show ?thesis by simp
qed

lemma max_nonnull: "HasMaximum A \<longrightarrow> A \<noteq> {}" using max_lemma1 by auto
lemma min_nonnull: "HasMinimum A \<longrightarrow> A \<noteq> {}" using min_lemma1 by auto


lemma sup_ltub:
  assumes "HasSup A X \<and> A \<noteq> {} \<and> A \<subseteq> X"
  shows "\<forall>u \<in> X. (\<forall>a \<in> A. a \<le> u) \<longrightarrow> Supremum A X \<le> u"
  by (smt (verit) HasSup_def Supremum_def UpperBounds_def assms mem_Collect_eq min_lemma2)

lemma inf_gtlb:
  assumes "HasInf A X \<and> A \<noteq> {} \<and> A \<subseteq> X"
  shows "\<forall>l \<in> X. (\<forall>a \<in> A. l \<le> a) \<longrightarrow> l \<le>  Infimum A X"
  by (smt (verit) HasInf_def Infimum_def LowerBounds_def assms max_lemma2 mem_Collect_eq)

end