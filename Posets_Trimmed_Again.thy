theory Posets_Trimmed_Again
  imports Main
begin

definition HasMinimum::"'X::order set \<Rightarrow> bool " where
  "HasMinimum A \<equiv> (\<exists>m \<in> A. \<forall>a \<in> A. m \<le> a)"

definition Minimum::"'X::order set \<Rightarrow> 'X::order" where
  "Minimum A = (THE m.( m \<in> A \<and> (\<forall>a \<in> A. m \<le> a)))"


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

definition PrincipalIdeal::"'X::order \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set" where
  "PrincipalIdeal a X = {x \<in> X. x \<le> a}"

definition PrincipalFilter::"'X::order \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set" where
  "PrincipalFilter a X = {x \<in> X. x \<ge> a}"

definition hull_equivalence::"('X::order \<Rightarrow> 'X::order) \<Rightarrow> 'X::order set \<Rightarrow> bool"
  where "hull_equivalence f X \<equiv> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. ((x1 \<le> f x2) \<longleftrightarrow>(f x1 \<le> f x2)))"

definition is_closure_range::"'X::order set \<Rightarrow> 'X::order set \<Rightarrow> bool"
  where "is_closure_range C X \<equiv> (C \<in> Pow X) \<and> (\<forall>x \<in> X. HasMinimum (PrincipalFilter x C))"

definition closure_from_closure_range::"'X::order set \<Rightarrow> 'X::order set \<Rightarrow> ('X::order \<Rightarrow> 'X::order)"
  where "closure_from_closure_range C X = (\<lambda>x. Minimum (PrincipalFilter x C))"

definition fixed_point_set::"('X::order \<Rightarrow> 'X::order) \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set" 
  where "fixed_point_set f X = {x \<in> X. f x = x}"


definition pointwise_lt:: "('X::order \<Rightarrow> 'Y::order) \<Rightarrow> 
                           ('X::order \<Rightarrow> 'Y::order) \<Rightarrow>
                           bool"
                           (infix "\<preceq>" 50) where
   "f \<preceq> g  \<longleftrightarrow> (\<forall>x. (f x \<le> g x ))"

definition precedes_on_dom:: "('X::order  \<Rightarrow> 'Y::order ) \<Rightarrow> 
                              ('X::order  \<Rightarrow> 'Y::order ) \<Rightarrow>
                               'X::order set  \<Rightarrow>  bool"
where "precedes_on_dom f g X \<equiv> (\<forall>x \<in> X. (f x \<le> g x))"


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



lemma lemf1: "is_ftriple f X Y \<longrightarrow> (\<forall>A \<in> Pow X. f`A \<in> Pow Y)" by (metis PowI UnionI Union_Pow_eq is_ftriple_def image_subsetI)

lemma closure_implies_closure_range:
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
lemma precedence_equiv_range_subset_for_closures:
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
      by (meson A0 P0 P1 in_mono is_closure_range_def closure_implies_closure_range min_lemma2)
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
      by (meson B0 P0 P1 in_mono is_closure_range_def closure_implies_closure_range min_lemma2)
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