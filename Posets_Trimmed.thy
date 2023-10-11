theory Posets_Trimmed
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


lemma sup_lt_ub:
  assumes "HasSup A X \<and> A \<noteq> {} \<and> A \<subseteq> X"
  shows "\<forall>u \<in> X. (\<forall>a \<in> A. a \<le> u) \<longrightarrow> Supremum A X \<le> u"
  by (smt (verit) HasSup_def Supremum_def UpperBounds_def assms mem_Collect_eq min_lemma2)

lemma inf_gt_lb:
  assumes "HasInf A X \<and> A \<noteq> {} \<and> A \<subseteq> X"
  shows "\<forall>l \<in> X. (\<forall>a \<in> A. l \<le> a) \<longrightarrow> l \<le>  Infimum A X"
  by (smt (verit) HasInf_def Infimum_def LowerBounds_def assms max_lemma2 mem_Collect_eq)

lemma sup_is_unique:
  assumes "HasSup A X"
  shows "\<exists>!s. (s \<in> UpperBounds A X \<and> (\<forall>u \<in> UpperBounds A X. s \<le> u))"
  using HasSup_def assms min_lemma1 by blast

lemma inf_is_unique:
  assumes "HasInf A X"
  shows "\<exists>!i. (i \<in> LowerBounds A X \<and> (\<forall>l \<in> LowerBounds A X. l \<le> i))"
  using HasInf_def assms max_lemma1 by blast

lemma test1:
  assumes "HasSup A X"
  shows "(\<forall>a \<in> A. a \<le> (Supremum A X))"
  by (metis (no_types, lifting) HasSup_def Supremum_def UpperBounds_def assms mem_Collect_eq min_lemma2)

lemma posets_lemma_0:
  assumes "HasSup A X" 
  shows "\<forall>x \<in> X. ((x \<ge> Supremum A X) \<longleftrightarrow> (\<forall>a \<in> A. x \<ge> a))"
  by (smt (verit, ccfv_threshold) HasSup_def Supremum_def UpperBounds_def assms dual_order.trans mem_Collect_eq min_lemma2)

lemma posets_lemma_1:
  assumes "HasSup A X \<and> HasInf B X \<and> A \<subseteq> X \<and> B \<subseteq> X" 
  shows "(Supremum A X \<le> Infimum B X) \<longleftrightarrow>  (\<forall>a \<in> A. \<forall>b \<in> B. a \<le> b)"
proof-
  have LR:"(Supremum A X \<le> Infimum B X) \<longrightarrow> (\<forall>a \<in> A. \<forall>b \<in> B. a \<le> b)" 
    by (metis (no_types, lifting) HasInf_def Infimum_def LowerBounds_def assms dual_order.trans max_lemma2 mem_Collect_eq test1)
  have RL:"(\<forall>a \<in> A. \<forall>b \<in> B. a \<le> b)\<longrightarrow>(Supremum A X \<le> Infimum B X)"
    by (smt (verit) HasInf_def Infimum_def LowerBounds_def assms max_lemma2 mem_Collect_eq posets_lemma_0 subset_eq)
  with LR RL show ?thesis by meson
qed

lemma sup_isinf_ub:
  assumes A0:"(A \<subseteq> X)" and
          A1:"(A \<noteq> {})" and
          A2:"HasInf(UpperBounds A X) X"
  shows "Supremum A X = Infimum (UpperBounds A X) X"
proof-
  let ?i="Infimum (UpperBounds A X) X"
  have B0:"?i \<in> UpperBounds A X"
    by (smt (verit) A0 A2 HasInf_def Infimum_def LowerBounds_def UpperBounds_def max_lemma2 mem_Collect_eq subset_eq)
  have B1:"\<forall>u \<in> UpperBounds A X. ?i \<le> u"
    by (metis (no_types, lifting) A2 HasInf_def Infimum_def LowerBounds_def max_lemma2 mem_Collect_eq)
  have B2:"?i=Minimum (UpperBounds A X)"
    by (meson B0 B1 HasMinimum_def min_lemma2 order_antisym)
  have B3:"?i=Supremum A X"
    by (simp add: B2 Supremum_def)
  with B3 show ?thesis by simp
qed

lemma has_min_sup_null:
  assumes P1:"HasMinimum X"
  shows "Supremum {} X = Minimum X"
proof-
  have B1: "\<forall>x \<in> X. (x \<in> {y \<in> X. \<forall>a \<in> {}. y \<le> a})" by simp
  from B1 have  B2: "\<forall>x \<in> X. (x \<in> UpperBounds {} X)" by (simp add: UpperBounds_def)
  have B3:"X = (UpperBounds {} X)" by (simp add: UpperBounds_def)
  have B4:"Minimum X=Minimum(UpperBounds {} X)" using B3 by auto
  have B5:"Minimum X=(Supremum {} X)" by (simp add: B4 Supremum_def)
  with B5 show ?thesis by simp
qed

lemma has_max_inf_null:
  assumes P1:"HasMaximum X"
  shows "Infimum {} X = Maximum X"
proof-
  have B1: "\<forall>x \<in> X. (x \<in> {y \<in> X. \<forall>a \<in> {}. y \<ge> a})" by simp
  from B1 have  B2: "\<forall>x \<in> X. (x \<in> LowerBounds {} X)" by (simp add: LowerBounds_def)
  have B3:"X=(LowerBounds {} X)" by (simp add: LowerBounds_def)
  have B4:"Maximum X=Maximum (LowerBounds {} X)" using B3 by auto
  have B5:"Maximum X=(Infimum {} X)" by (simp add: B4 Infimum_def)
  with B5 show ?thesis by simp
qed



end