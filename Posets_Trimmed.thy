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
  have B1:"X = (UpperBounds {} X)" by (simp add: UpperBounds_def)
  have B2:"Minimum X=Minimum(UpperBounds {} X)" using B1 by auto
  have B3:"Minimum X=(Supremum {} X)" by (simp add: B2 Supremum_def)
  with B3 show ?thesis by simp
qed

lemma has_max_inf_null:
  assumes P1:"HasMaximum X"
  shows "Infimum {} X = Maximum X"
proof-
  have B1:"X=(LowerBounds {} X)" by (simp add: LowerBounds_def)
  have B2:"Maximum X=Maximum (LowerBounds {} X)" using B1 by auto
  have B3:"Maximum X=(Infimum {} X)" by (simp add: B2 Infimum_def)
  with B3 show ?thesis by simp
qed

definition is_ftriple::"('X \<Rightarrow> 'Y) \<Rightarrow> 'X set \<Rightarrow> 'Y set \<Rightarrow> bool " where "is_ftriple f X Y \<equiv> (\<forall>x \<in>X. f x \<in> Y)"

definition is_antitone::"('X::order \<Rightarrow> 'Y::order) \<Rightarrow> 'X::order set \<Rightarrow> 'Y::order set \<Rightarrow> bool " 
  where "is_antitone f X Y \<equiv> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. (f x2 \<le> f x1))"

definition is_isotone::"('X::order \<Rightarrow> 'Y::order) \<Rightarrow> 'X::order set \<Rightarrow> 'Y::order set \<Rightarrow> bool " 
  where "is_isotone f X Y \<equiv> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. (f x1 \<le> f x2))"

definition is_extensive::"('X::order \<Rightarrow> 'X::order) \<Rightarrow>  'X::order set  \<Rightarrow> bool"
  where "is_extensive f X \<equiv> (\<forall>x \<in> X. x \<le> (f x) )"

definition is_idempotent::"('X::order \<Rightarrow> 'X::order) \<Rightarrow> 'X::order set \<Rightarrow> bool" 
  where "is_idempotent f X \<equiv> (\<forall>x \<in> X. f x = f (f x))"

definition is_a_closure::"('X::order \<Rightarrow> 'X::order) \<Rightarrow> 'X::order set \<Rightarrow> bool"
  where "is_a_closure f X \<equiv> ((is_extensive f X) \<and> (is_isotone f X X) \<and> (is_idempotent f X) \<and> (is_ftriple f X X)) "

lemma lemf1: "is_ftriple f X Y \<longrightarrow> (\<forall>A \<in> Pow X. f`A \<in> Pow Y)" by (metis PowI UnionI Union_Pow_eq is_ftriple_def image_subsetI)

lemma lemf2: "is_ftriple f X Y \<longrightarrow> (\<forall>A. A \<subseteq>X \<longrightarrow>  f`A \<subseteq> Y)" by (meson PowD PowI lemf1)

lemma lemf3: "(\<forall>A. A \<subseteq>X \<longrightarrow>  f`A \<subseteq> Y) \<longrightarrow> is_ftriple f X Y " by (meson is_ftriple_def image_subset_iff order_refl)

lemma lemf4: " (\<forall>A \<in> Pow X. f`A \<in> Pow Y) \<longrightarrow>  is_ftriple f X Y" by (meson PowD PowI lemf3)

lemma smallest_largedst_closed:
  assumes P:"is_a_closure f X"
  shows "(\<forall>a \<in> X. (f a = Minimum ({y \<in> f`X. a \<le>y })))"
proof
  fix a assume A0:"a \<in> X"
  let ?C="f`X" and ?aUp="{x \<in> X. a \<le> x}" and ?b="f a" and ?Ca="{y \<in> f`X. a \<le>y }"
  have B0:"?b \<in> ?C" by (simp add: A0)
  have B1:"?b \<in> X" by (meson A0 assms is_a_closure_def is_ftriple_def)
  have B2:"?b \<in> ?aUp" using A0 B1 assms is_a_closure_def is_extensive_def by blast
  have B3:"?Ca= (?C \<inter> ?aUp)" by (smt (verit, ccfv_SIG) Collect_cong Int_def assms image_iff is_a_closure_def is_ftriple_def mem_Collect_eq)
  have B4:"?b \<in> ?Ca" using B0 B2 by blast
  have B5:"\<forall>y \<in> ?Ca. (\<exists>x\<in>X. (y=(f x)) \<and> (a \<le> (f x))) \<longrightarrow> (\<exists>x\<in>X. (y=(f x)) \<and> (f a \<le>  f x))"
    using A0 assms is_a_closure_def is_isotone_def by blast
  have B6:"\<forall>y \<in> ?Ca. (f a \<le> y)" 
    using B5 by auto
  have B7:"f a = Minimum {y \<in> f`X. a \<le>y }"
    by (metis (no_types, lifting) B4 B6 HasMinimum_def min_lemma2 order_antisym)
  show "(f a = Minimum ({y \<in> f`X. a \<le>y }))"
    using B7 by blast
qed
  

end