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




definition is_ftriple::"('X \<Rightarrow> 'Y) \<Rightarrow> 'X set \<Rightarrow> 'Y set \<Rightarrow> bool " 
  where "is_ftriple f X Y \<equiv> (\<forall>x \<in>X. f x \<in> Y)"

definition is_antitone::"('X::order \<Rightarrow> 'Y::order) \<Rightarrow> 'X::order set \<Rightarrow> bool " 
  where "is_antitone f X \<equiv> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. (f x2 \<le> f x1))"

definition is_isotone::"('X::order \<Rightarrow> 'Y::order) \<Rightarrow> 'X::order set \<Rightarrow> bool " 
  where "is_isotone f X \<equiv> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. (x1 \<le> x2)\<longrightarrow>(f x1 \<le> f x2))"

definition is_extensive::"('X::order \<Rightarrow> 'X::order) \<Rightarrow>  'X::order set  \<Rightarrow> bool"
  where "is_extensive f X \<equiv> (\<forall>x \<in> X. x \<le> (f x) )"

definition is_idempotent::"('X::order \<Rightarrow> 'X::order) \<Rightarrow> 'X::order set \<Rightarrow> bool" 
  where "is_idempotent f X \<equiv> (\<forall>x \<in> X. f x = f (f x))"

definition is_a_closure::"('X::order \<Rightarrow> 'X::order) \<Rightarrow> 'X::order set \<Rightarrow> bool"
  where "is_a_closure f X \<equiv> ((is_extensive f X) \<and> (is_isotone f X) \<and> (is_idempotent f X) \<and> (is_ftriple f X X)) "

definition IsUpClosed::"'X::order set \<Rightarrow>'X::order set \<Rightarrow>bool"
  where "IsUpClosed A X \<equiv> (\<forall>x \<in> X. \<forall>a \<in> A. a \<le> x \<longrightarrow> x \<in> A)"

definition IsDownClosed::"'X::order set \<Rightarrow>'X::order set \<Rightarrow>bool"
  where "IsDownClosed A X \<equiv> (\<forall>x \<in> X. \<forall>a \<in> A. a \<ge> x \<longrightarrow> x \<in> A)"

definition UpClosure::"'X::order set \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set"
  where "UpClosure A X = {x \<in> X. \<exists>a \<in> A. x \<le> a}"

definition DownClosure::"'X::order set \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set"
  where "DownClosure A X = {x \<in> X. \<exists>a \<in> A. x \<ge>  a}"

definition UpSetsIn::"'X::order set \<Rightarrow> 'X::order set set" 
  where "UpSetsIn X = {U \<in> Pow X. IsUpClosed U X}"

definition DownSetsIn::"'X::order set \<Rightarrow> 'X::order set set" 
  where "DownSetsIn X = {D \<in> Pow X. IsDownClosed D X}"

definition PrincipalIdeal::"'X::order \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set" where
  "PrincipalIdeal a X = {x \<in> X. x \<le> a}"

definition PrincipalFilter::"'X::order \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set" where
  "PrincipalFilter a X = {x \<in> X. x \<ge> a}"


lemma upper_bounds_is_up_closed:
  "IsUpClosed (UpperBounds A X) X"
  by (simp add: IsUpClosed_def UpperBounds_def dual_order.trans)

lemma lower_bounds_is_down_closed:
  "IsDownClosed (LowerBounds A X) X"
  by (smt (verit) IsDownClosed_def LowerBounds_def dual_order.trans mem_Collect_eq)

lemma downset_transitivity:
  assumes P0:"D \<in> DownSetsIn E" and
          P1:"E \<in> DownSetsIn X"
  shows " D \<in> DownSetsIn X"
proof-
  have B0:"D \<in> Pow E \<and> E \<in> Pow X" using DownSetsIn_def P0 P1 by blast  
  have B1:"D \<in> Pow X" using B0 P0 P1 by blast
  have B2:"IsDownClosed D X" by (smt (verit) DownSetsIn_def IsDownClosed_def P0 P1 PowD mem_Collect_eq subset_eq)
  with B1 B2 show ?thesis by (simp add: DownSetsIn_def)
qed


lemma upset_transitivity:
  assumes P0:"U \<in> UpSetsIn E" and
          P1:"E \<in> UpSetsIn X"
  shows "U \<in> UpSetsIn X"
proof-
  have B0:"U \<in> Pow E \<and> E \<in> Pow X" using UpSetsIn_def P0 P1 by blast  
  have B1:"U \<in> Pow X" using B0 P0 P1 by blast
  have B2:"IsUpClosed U X" by (smt (verit) UpSetsIn_def IsUpClosed_def P0 P1 PowD mem_Collect_eq subset_eq)
  with B1 B2 show ?thesis by (simp add: UpSetsIn_def)
qed

lemma downset_iff_comp_upset:
  assumes P0:"X \<noteq> {}" and P1:"D \<in> Pow X" shows
  "D \<in> DownSetsIn X \<longleftrightarrow> (X-D) \<in> UpSetsIn X"
  by (smt (z3) DiffD2 DiffI Diff_subset DownSetsIn_def IsDownClosed_def IsUpClosed_def P1 PowD PowI UpSetsIn_def mem_Collect_eq subset_eq)

lemma principal_order_iso1:
  assumes P0:"a \<in> X \<and> b \<in> X" shows
  "PrincipalIdeal a X \<subseteq> PrincipalIdeal b X \<longleftrightarrow> a \<le> b"
  by (smt (verit) PrincipalIdeal_def assms dual_order.trans in_mono mem_Collect_eq order_refl subsetI)

lemma principal_order_iso2:
  assumes P0:"a \<in> X \<and> b \<in> X" shows
  "PrincipalFilter a X \<subseteq> PrincipalFilter b X \<longleftrightarrow> a \<ge> b"
  by (smt (verit) Collect_mono_iff PrincipalFilter_def assms dual_order.trans order_refl)

lemma downsets_unionclosed:
  assumes P0: "\<E> \<in> Pow (DownSetsIn X)"
  shows "(\<Union>\<E>) \<in> (DownSetsIn X)"
  by (smt (verit, ccfv_threshold) DownSetsIn_def IsDownClosed_def Pow_iff Union_iff assms mem_Collect_eq subset_eq)

lemma upsets_unionclosed:
  assumes P0: "\<E> \<in> Pow (UpSetsIn X)" and P1:"\<E> \<noteq> {}"
  shows "(\<Inter>\<E>) \<in> (UpSetsIn X)"
proof-
  let ?I="(\<Inter>\<E>)" and ?U="UpSetsIn X"
  have B0:"?I \<in> Pow X" by (metis (no_types, lifting) CollectD Inf_less_eq P0 P1 PowD PowI UpSetsIn_def subset_eq)
  have B1:"IsUpClosed ?I X" by (smt (verit, best) Inter_iff IsUpClosed_def P0 PowD UpSetsIn_def mem_Collect_eq subset_eq)
  with B0 B1 show ?thesis by (simp add: UpSetsIn_def)
qed


lemma lemf1: "is_ftriple f X Y \<longrightarrow> (\<forall>A \<in> Pow X. f`A \<in> Pow Y)" by (metis PowI UnionI Union_Pow_eq is_ftriple_def image_subsetI)

lemma lemf2: "is_ftriple f X Y \<longrightarrow> (\<forall>A. A \<subseteq>X \<longrightarrow>  f`A \<subseteq> Y)" by (meson PowD PowI lemf1)

lemma lemf3: "(\<forall>A. A \<subseteq>X \<longrightarrow>  f`A \<subseteq> Y) \<longrightarrow> is_ftriple f X Y " by (meson is_ftriple_def image_subset_iff order_refl)

lemma lemf4: " (\<forall>A \<in> Pow X. f`A \<in> Pow Y) \<longrightarrow>  is_ftriple f X Y" by (meson PowD PowI lemf3)



lemma smallest_larger_closed_element:
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
    by (smt (verit, best) A0 assms is_a_closure_def is_ftriple_def is_idempotent_def is_isotone_def)
  have B6:"\<forall>y \<in> ?Ca. (f a \<le> y)" 
    using B5 by auto
  have B7:"f a = Minimum {y \<in> f`X. a \<le>y }"
    by (metis (no_types, lifting) B4 B6 HasMinimum_def min_lemma2 order_antisym)
  show "(f a = Minimum ({y \<in> f`X. a \<le>y }))"
    using B7 by blast
qed

lemma maximum_then_closed:
  assumes P1:"HasMaximum X" and P2:"is_a_closure f X"
  shows "f (Maximum X) = Maximum X"
  by (meson P1 P2 antisym is_a_closure_def is_extensive_def is_ftriple_def max_lemma2)


definition hull_equivalence::"('X::order \<Rightarrow> 'X::order) \<Rightarrow> 'X::order set \<Rightarrow> bool"
  where "hull_equivalence f X \<equiv> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. ((x1 \<le> f x2) \<longleftrightarrow>(f x1 \<le> f x2)))"

definition is_closure_range::"'X::order set \<Rightarrow> 'X::order set \<Rightarrow> bool"
  where "is_closure_range C X \<equiv> (C \<in> Pow X) \<and> (\<forall>x \<in> X. HasMinimum (PrincipalFilter x C))"

definition closure_from_closure_range::"'X::order set \<Rightarrow> 'X::order set \<Rightarrow> ('X::order \<Rightarrow> 'X::order)"
  where "closure_from_closure_range C X = (\<lambda>x. Minimum (PrincipalFilter x C))"

definition fixed_point_set::"('X::order \<Rightarrow> 'X::order) \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set" 
  where "fixed_point_set f X = {x \<in> X. f x = x}"

lemma closure_equiv:
  "is_a_closure f X \<longleftrightarrow> (hull_equivalence f X) \<and> (is_ftriple f X X)"
proof-
  let ?L="is_a_closure f X" and ?R="(hull_equivalence f X) \<and> (is_ftriple f X X)"
  have C1:"?R \<longrightarrow> is_extensive f X" by (simp add: hull_equivalence_def is_extensive_def)
  have C2:"?R \<longrightarrow> is_isotone f X"
  proof-
    have C20:"?R \<longrightarrow> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. (x1 \<le>x2 \<longrightarrow> f x1 \<le> f x2))"
      by (metis C1 dual_order.trans hull_equivalence_def is_extensive_def)
    with C20 show ?thesis by (simp add: is_isotone_def)
  qed  
  have C3:"?R\<longrightarrow>is_idempotent f X"
    by (simp add: hull_equivalence_def is_ftriple_def is_idempotent_def order_class.order_eq_iff)
  have RtL:"?R \<longrightarrow> ?L" by (simp add: C1 C2 C3 is_a_closure_def)  
  have LtR:"?L \<longrightarrow> ?R"
    by (smt (verit, ccfv_threshold) dual_order.trans hull_equivalence_def is_a_closure_def is_extensive_def is_ftriple_def is_idempotent_def is_isotone_def)
  with RtL LtR show ?thesis by fastforce
qed

lemma cr_cl_is_closure:
  assumes P0:"is_closure_range C X"
  shows "is_a_closure (closure_from_closure_range C X) X"
proof-
  let ?f="closure_from_closure_range C X" and ?pf="\<lambda>x. PrincipalFilter x C" 
  let ?P0="is_closure_range C X"
  have C0:"is_extensive ?f X"
  proof-
    have C00:"\<forall>x \<in> X. (?f x) = Minimum (?pf x)" by (simp add: closure_from_closure_range_def)
    have C01:"is_closure_range C X \<longrightarrow> (\<forall>x \<in> X. HasMinimum (?pf x))"
      by (simp add: is_closure_range_def)
    have C02:"is_closure_range C X \<longrightarrow> (\<forall>x \<in> X. (?f x) \<in> (?pf x))"
      by (simp add: C01 closure_from_closure_range_def min_lemma2)
    have C03:"is_closure_range C X \<longrightarrow> (\<forall>x \<in> X. x \<le> (?f x))"
      using C02 PrincipalFilter_def by fastforce
    with C03 P0  show ?thesis using is_extensive_def by blast
  qed
  have C1:"is_closure_range C X \<longrightarrow> is_isotone ?f X"
  proof-
    have C10:"?P0\<longrightarrow> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. (x1 \<le> x2) \<longrightarrow> (?pf x2 \<subseteq> ?pf x1))"
      by (smt (verit, best) PrincipalFilter_def dual_order.trans mem_Collect_eq subsetI)
    have C11:"?P0 \<longrightarrow> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. (x1 \<le> x2) \<longrightarrow> (?f x1 \<le> ?f x2))"
      by (metis C10 closure_from_closure_range_def in_mono is_closure_range_def min_lemma2)
    with C11 show ?thesis by (simp add: is_isotone_def)
  qed
  have C2:"?P0 \<longrightarrow> is_idempotent ?f X"
  proof-
    have C20:"?P0 \<longrightarrow> (\<forall>c \<in> C. ?f c = c)"
      by (smt (verit, ccfv_threshold) PowD PrincipalFilter_def closure_from_closure_range_def dual_order.refl in_mono is_closure_range_def mem_Collect_eq min_lemma2 order_antisym)
    have C21:"?P0 \<longrightarrow> is_idempotent ?f X "
      by (metis (no_types, lifting) C20 PrincipalFilter_def closure_from_closure_range_def is_closure_range_def is_idempotent_def mem_Collect_eq min_lemma2)
    with C21 show ?thesis by simp
  qed
  with C0 C1 C2 show ?thesis
    by (smt (verit, ccfv_threshold) CollectD PowD PrincipalFilter_def assms closure_from_closure_range_def in_mono is_a_closure_def is_closure_range_def is_ftriple_def min_lemma2)
qed


definition pointwise_lt:: "('X::order \<Rightarrow> 'Y::order) \<Rightarrow> 
                           ('X::order \<Rightarrow> 'Y::order) \<Rightarrow>
                           bool"
                           (infix "\<preceq>" 50) where
   "f \<preceq> g  \<longleftrightarrow> (\<forall>x. (f x \<le> g x ))"

definition precedes_on_dom:: "('X::order  \<Rightarrow> 'Y::order ) \<Rightarrow> 
                              ('X::order  \<Rightarrow> 'Y::order ) \<Rightarrow>
                               'X::order set  \<Rightarrow>  bool"
where "precedes_on_dom f g X \<equiv> (\<forall>x \<in> X. (f x \<le> g x))"


lemma cliso_lemma1:
  assumes P0:"is_a_closure f X" and
          P1:"is_a_closure g X" and
          P2:"f \<preceq> g"
  shows "{x \<in> X. g x \<le> x} \<subseteq> {x \<in> X. f x \<le> x}"
proof-
  let ?Eg="{x \<in> X. g x \<le> x}" and ?Ef="{x \<in> X. f x \<le> x}"
  have B0:"f \<preceq> g \<longrightarrow> (\<forall>x \<in> X. g x \<le> x \<longrightarrow> f x \<le> x)" by (meson dual_order.trans pointwise_lt_def) 
  have B1:"f \<preceq> g \<longrightarrow> (\<forall>x \<in> X. x \<in>?Eg \<longrightarrow> x \<in> ?Ef) " using B0 by blast
  have B2:"f \<preceq> g \<longrightarrow> ?Eg \<subseteq> ?Ef"  using B1 by blast
  with B2 show ?thesis using P2 by fastforce 
qed

lemma lem0:
  assumes P0:"A \<subseteq> fixed_point_set f X" and
          P1:"is_a_closure f X" and
          P2:"HasInf A X" 
  shows "f (Infimum A X) = Infimum A X"
proof-
  let ?i="Infimum A X"
  have A0:"?i \<le> f ?i"
    by (metis (mono_tags, lifting) HasInf_def Infimum_def LowerBounds_def P1 P2 is_a_closure_def is_extensive_def max_lemma2 mem_Collect_eq)
  have A1:"(\<forall>a \<in> A.  ?i \<le> a) \<longrightarrow> (\<forall>a \<in> A. f ?i \<le> f a)\<longrightarrow> (\<forall>a \<in> A. f ?i \<le> a) "
    by (metis (mono_tags, lifting) CollectD P0 fixed_point_set_def in_mono)
  have A2:"f ?i \<le> ?i"
    by (smt (verit, del_insts) HasInf_def Infimum_def LowerBounds_def P0 P1 P2 fixed_point_set_def is_a_closure_def is_ftriple_def is_isotone_def max_lemma2 mem_Collect_eq subset_eq)
  from A0 A2 have A3:"f ?i = ?i"
    using order_antisym by blast
  with A3 show ?thesis by simp
qed

lemma lem1:
  assumes P0: "is_a_closure f X"
  shows "is_closure_range (f`X) X"
proof-
  let ?C="f`X"
  have A0: "\<forall>x \<in> X. (x \<le> f x)"  using assms is_a_closure_def is_extensive_def by blast
  have A1:"\<forall>x \<in> X. (\<exists>c \<in> ?C . (x \<le> c))" using A0 by blast
  have A2:"\<forall>x \<in> X. (PrincipalFilter x ?C \<noteq> {}) " using A0 A1 PrincipalFilter_def by blast
  have A3:"\<forall>x \<in> X. (\<forall>y \<in> (PrincipalFilter x ?C). (x\<le> y))" by (simp add: PrincipalFilter_def)
  have A4:"\<forall>x \<in> X. (\<forall>y \<in> (PrincipalFilter x ?C). (f x \<le> f y))"
    by (metis (mono_tags, lifting) CollectD PrincipalFilter_def assms imageE is_a_closure_def is_ftriple_def is_isotone_def) 
  have A5:"\<forall>x \<in> X. (\<forall>y \<in> (PrincipalFilter x ?C). (f x \<le> y))"
    by (metis (no_types, lifting) A4 CollectD PrincipalFilter_def assms image_iff is_a_closure_def is_idempotent_def)
  have A6:"\<forall>x \<in> X. (HasMinimum (PrincipalFilter x ?C))"
    using A0 A5 HasMinimum_def PrincipalFilter_def by fastforce
  have A7:"?C \<in> Pow X"
    by (meson Pow_top assms is_a_closure_def lemf1)
  have A8:"is_closure_range ?C  X"
    by (meson A6 A7 is_closure_range_def)
  with A8 show ?thesis by simp
qed

lemma lem2:
  assumes P0:"is_a_closure f X"
  shows "\<forall>x \<in> X. (f x = (closure_from_closure_range (f`X) X) x)"  
proof-
  let ?C="f`X"  
  let ?G="\<lambda>x. (closure_from_closure_range ?C X)(x)"
  have A0:"\<forall>x \<in> X. (f x =?G x )"
    by (simp add: PrincipalFilter_def assms closure_from_closure_range_def smallest_larger_closed_element)
  with A0 show ?thesis by simp
qed


lemma lem3:
  assumes P0:"is_closure_range C X"
  shows "(closure_from_closure_range C X)`(X) = C"  
proof-
  let ?f="closure_from_closure_range C X"  
  have A0:"?f`(X) = {y \<in> X. \<exists>x \<in> X. ?f x = y}"
    using assms closure_equiv cr_cl_is_closure is_ftriple_def by fastforce
  have A1:"?f`(X) = {y \<in> X. \<exists>x \<in> X. y= Minimum(PrincipalFilter x C)}"
    by (smt (verit, best) A0 Collect_cong closure_from_closure_range_def)
  have A2:"?f`(X) \<subseteq> C"
    by (metis (no_types, lifting) PrincipalFilter_def assms closure_from_closure_range_def image_subsetI is_closure_range_def mem_Collect_eq min_lemma2)
  have A3:"\<forall>c \<in> C. (c = Minimum(PrincipalFilter c C))"
    by (smt (verit, ccfv_threshold) Pow_def PrincipalFilter_def assms insert_subset is_closure_range_def mem_Collect_eq min_lemma2 order_antisym order_refl)
  have A4:"C \<subseteq> ?f`(X)"
    by (smt (verit) A3 PowD assms closure_from_closure_range_def image_iff is_closure_range_def subsetD subsetI)
  have A5:"C= ?f`(X)"
    by (simp add: A2 A4 subset_antisym)
  with A5 show ?thesis by simp
qed

lemma lem4:
  assumes P0:"is_a_closure f1 X" and
          P1:"is_a_closure f2 X"
  shows "(precedes_on_dom f1 f2  X) \<longleftrightarrow> ((f2`X) \<subseteq> (f1`X))"
proof-
  let ?C1="f1`X" and ?C2="f2`X"
  let ?L="(precedes_on_dom f1 f2 X)"
  let ?R="(?C2 \<subseteq> ?C1 )"
  have LtR:"?L \<longrightarrow>?R"
  proof-
    have A0:"?L \<longrightarrow> (\<forall>x \<in> X. ((PrincipalFilter x ?C2) \<subseteq> (PrincipalFilter x ?C1)))"
      by (smt (verit) P0 P1 PrincipalFilter_def image_iff is_a_closure_def is_extensive_def is_ftriple_def is_idempotent_def mem_Collect_eq order_antisym_conv precedes_on_dom_def subsetI)
    have A1:"?L \<longrightarrow> (\<forall>x \<in> X. (Minimum(PrincipalFilter x ?C1) \<le>  Minimum(PrincipalFilter x ?C2) ))"
      by (meson A0 P0 P1 in_mono is_closure_range_def lem1 min_lemma2)
    have A2:"?L \<longrightarrow> (?C2 \<subseteq> ?C1)"
      by (smt (verit, ccfv_threshold) P0 P1 dual_order.antisym image_iff image_subset_iff is_a_closure_def is_extensive_def is_ftriple_def is_idempotent_def precedes_on_dom_def) 
    with A2 show ?thesis by simp
  qed
  have RtL:"?R \<longrightarrow> ?L"
  proof-
    let ?u="\<lambda>x. \<lambda>C. (PrincipalFilter x C) "
    have B0:"\<forall>x \<in> X. (?R \<longrightarrow> (?u x ?C2 \<subseteq> (?u x ?C1)))"
      by (simp add: Collect_mono_iff PrincipalFilter_def in_mono)
    have B1:"\<forall>x \<in> X.  ?R \<longrightarrow> (Minimum(?u x ?C1) \<le>  Minimum(?u x ?C2))"
      by (meson B0 P0 P1 in_mono is_closure_range_def lem1 min_lemma2)
    have B2:"\<forall>x \<in> X. (f1 x  = Minimum(?u x ?C1))"
      by (simp add: P0 PrincipalFilter_def smallest_larger_closed_element)
    have B3:"\<forall>x \<in> X. (f2 x  = Minimum(?u x ?C2))"
      by (simp add: P1 PrincipalFilter_def smallest_larger_closed_element)
    have B4: "?R\<longrightarrow>(\<forall>x \<in> X. f1 x  \<le>  f2 x)"
      using B1 B2 B3 by fastforce
    have B5: "?R\<longrightarrow>?L"  by (simp add: B4 precedes_on_dom_def)
    with B5 show ?thesis by simp
  qed
  from LtR RtL have LtRtL:"?L \<longleftrightarrow> ?R" by blast
  with LtRtL show ?thesis by simp
qed



end