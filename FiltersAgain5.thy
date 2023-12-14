theory FiltersAgain5
  imports Main 
begin
hide_type Filter.filter
hide_const(open) List.list.Nil
no_notation List.list.Nil ("[]")  
no_notation Cons (infixr "#" 65)

declare [[show_types]]

definition is_inhabited::"'X set  \<Rightarrow> bool" where
   "is_inhabited X \<equiv> (X \<noteq> {})"

definition is_downdir::"'X::ord set \<Rightarrow> bool" where
   "is_downdir X \<equiv> (\<forall>a b. a \<in> X  \<longrightarrow> b \<in> X \<longrightarrow> (\<exists>c  \<in> X. (c \<le> a) \<and>  (c \<le> b)))"

definition is_upclosed::"'X::ord set \<Rightarrow> bool" where
   "is_upclosed X \<equiv> (\<forall>a b. a \<le> b \<longrightarrow>  a \<in> X \<longrightarrow>  b \<in> X)"

definition is_pisystem::"'X::{ord,inf} set \<Rightarrow> bool" where
   "is_pisystem X \<equiv> (\<forall>a b. a \<in> X  \<longrightarrow> b \<in> X \<longrightarrow> (inf a b)  \<in> X)"

definition filter_generated_by::"'X::{semilattice_inf,Inf} set \<Rightarrow> 'X::{semilattice_inf,Inf} set" where
  "filter_generated_by A \<equiv> {a. \<exists>S\<in>Pow(A). finite S \<and>  S \<noteq> {} \<and>  (Inf S) \<le> a}"

definition filter_generated_by_family::"'X::{semilattice_inf,Inf} set set\<Rightarrow> 'X::{semilattice_inf,Inf} set" where
  "filter_generated_by_family A \<equiv> {a. \<exists>S\<in>Pow(\<Union>A). finite S \<and>  S \<noteq> {} \<and>  (Inf S) \<le> a}"

definition filter_closure::"'X::{semilattice_inf,Inf,order_top} set set\<Rightarrow> 'X::{semilattice_inf,Inf,order_top} set" where
  "filter_closure EF = (if EF={} then {top} else filter_generated_by_family EF)"

locale is_filter = fixes F::"'X set set"
  assumes F0:"is_inhabited F" 
  assumes F1:"is_pisystem F"
  assumes F2:"is_upclosed F"

lemma filter_meet:
  assumes A0:"is_filter F1 \<and> is_filter F2"
  shows "\<And>x. x \<in> (F1 \<inter> F2) \<longleftrightarrow> (\<exists>x1 \<in> F1. \<exists>x2 \<in> F2. x=x1 \<union> x2)"
proof
  fix x assume "x \<in> (F1 \<inter> F2)"
  show "(\<exists>x1 \<in> F1. \<exists>x2 \<in> F2. x=x1 \<union> x2)"
    using \<open>(x::'a set) \<in> (F1::'a set set) \<inter> (F2::'a set set)\<close> by blast
  next
  fix x  assume "(\<exists>x1 \<in> F1. \<exists>x2 \<in> F2. x=x1 \<union> x2)"
  show "x \<in> F1 \<inter> F2"
    by (metis Int_iff \<open>\<exists>x1::'a set\<in>F1::'a set set. \<exists>x2::'a set\<in>F2::'a set set. (x::'a set) = x1 \<union> x2\<close> assms inf_sup_ord(4) is_filter.F2 is_upclosed_def sup_ge1)
qed

lemma filter_topped:
  assumes A0:"is_filter F" shows "UNIV \<in> F"
proof-
  have B0:"is_inhabited F"
    using A0 is_filter_def by auto
  have B1:"is_upclosed F"
    by (simp add: A0 is_filter.F2)
  obtain x where B2:"x \<in> F"
    using B0 is_inhabited_def by fastforce
  have B3:"x \<subseteq> UNIV" by simp
  show ?thesis
    using B1 B2 B3 is_upclosed_def by blast
qed


  

lemma filter_meet_set:
  assumes A0:"is_filter F1 \<and> is_filter F2"
  shows "\<And>x. x \<in> (F1 \<inter> F2) \<longleftrightarrow> x \<in>{x. \<exists>x1 \<in> F1. \<exists>x2 \<in> F2. x=x1 \<union> x2}"
  using assms filter_meet by blast
  

typedef 'a filter = "{F::('a set set). is_filter F}"
proof -
  have "\<And>b. is_pisystem ({A. b}::'a set set)"
    using is_pisystem_def by blast
  then have "\<exists>A. FiltersAgain5.is_filter (A::'a set set)"
    by (metis (no_types) FiltersAgain5.is_filter_def is_inhabited_def is_upclosed_def mem_Collect_eq)
  then show ?thesis
    by blast
qed

lemma Rep_is_filter:
  "is_filter (Rep_filter F)"
  using FiltersAgain5.filter.Rep_filter by blast

lemma Repfilter_Absfilter_inv:
  "\<And>F. is_filter F \<Longrightarrow> Rep_filter (Abs_filter F) = F"
  by (simp add: FiltersAgain5.filter.Abs_filter_inverse)

lemma filter_eq:
  "(F1 = F2) \<longleftrightarrow> (\<forall>x. x \<in> (Rep_filter F1) \<longleftrightarrow> x \<in> (Rep_filter F2))"
  by (metis filter.Rep_filter_inverse subsetI subset_antisym)

instantiation filter::(type) complete_lattice
begin

definition le_filter_def:
  "F1 \<le> F2 \<longleftrightarrow> (filter.Rep_filter F1) \<subseteq> (filter.Rep_filter F2)"

definition less_filter_def:
  "F1 <  F2 \<longleftrightarrow> (filter.Rep_filter F1) \<subset> (filter.Rep_filter F2)"

definition top_filter:
  "top = filter.Abs_filter (Pow (UNIV))"

definition bot_filter:
  "bot = filter.Abs_filter({UNIV})"

definition sup_filter:
  "sup F1 F2 = Abs_filter {x. \<exists>x1 \<in> (Rep_filter F1). \<exists>x2 \<in> (Rep_filter F2). x1 \<inter> x2 \<le> x}"

definition inf_filter:
  "inf F1 F2 = Abs_filter {x. \<exists>x1 \<in> (Rep_filter F1). \<exists>x2 \<in> (Rep_filter F2). x=x1 \<union> x2}"

definition filter_sup:
  "Sup EF = Abs_filter(filter_closure (Rep_filter`EF))"

definition filter_inf:
  "Inf EF = Abs_filter(\<Inter> (Rep_filter`EF))"

lemma filter_sup_is_filter:
  "is_filter {x. \<exists>x1 \<in> (Rep_filter F1). \<exists>x2 \<in> (Rep_filter F2). x1 \<inter> x2 \<le> x}"
proof-
  let ?S="{x. \<exists>x1 \<in> (Rep_filter F1). \<exists>x2 \<in> (Rep_filter F2). x1 \<inter> x2 \<le> x}"
  let ?G1="Rep_filter F1"
  let ?G2="Rep_filter F2"
  have "is_filter ?G1 \<and> is_filter ?G2"
    by (simp add: Rep_is_filter)
  have "is_inhabited ?S"
    by (metis (mono_tags, lifting) \<open>FiltersAgain5.is_filter (FiltersAgain5.filter.Rep_filter (F1::'b filter)) \<and> FiltersAgain5.is_filter (FiltersAgain5.filter.Rep_filter (F2::'b filter))\<close> ex_in_conv inf_le1 is_filter.F0 is_inhabited_def mem_Collect_eq)
  have "is_pisystem ?S"
  proof-
    have "\<And>a b. (a \<in> ?S \<and> b \<in> ?S) \<longrightarrow> (a \<inter> b) \<in> ?S"
    proof
      fix a b assume "(a \<in> ?S \<and> b \<in> ?S)"
      obtain a1 a2 where"a1 \<in> ?G1 \<and> a2 \<in> ?G2 \<and> a1 \<inter> a2 \<subseteq> a"
        using \<open>(a::'b set) \<in> {x::'b set. \<exists>x1::'b set \<in>FiltersAgain5.filter.Rep_filter (F1::'b filter). \<exists>x2::'b set \<in>FiltersAgain5.filter.Rep_filter (F2::'b filter). x1 \<inter> x2 \<subseteq> x} \<and> (b::'b set) \<in> {x::'b set. \<exists>x1::'b set\<in>FiltersAgain5.filter.Rep_filter F1. \<exists>x2::'b set\<in>FiltersAgain5.filter.Rep_filter F2. x1 \<inter> x2 \<subseteq> x}\<close> by blast
      obtain b1 b2 where"b1 \<in> ?G1 \<and> b2 \<in> ?G2 \<and> b1 \<inter> b2 \<subseteq> b"
        using \<open>(a::'b set) \<in> {x::'b set. \<exists>x1::'b set \<in>FiltersAgain5.filter.Rep_filter (F1::'b filter). \<exists>x2::'b set \<in>FiltersAgain5.filter.Rep_filter (F2::'b filter). x1 \<inter> x2 \<subseteq> x} \<and> (b::'b set) \<in> {x::'b set. \<exists>x1::'b set\<in>FiltersAgain5.filter.Rep_filter F1. \<exists>x2::'b set\<in>FiltersAgain5.filter.Rep_filter F2. x1 \<inter> x2 \<subseteq> x}\<close> by blast
      have "a1 \<inter> b1 \<in> ?G1 \<and> a2 \<inter> b2 \<in> ?G2"
        by (meson Rep_is_filter \<open>(a1::'b set) \<in> FiltersAgain5.filter.Rep_filter (F1::'b filter) \<and> (a2::'b set) \<in> FiltersAgain5.filter.Rep_filter (F2::'b filter) \<and> a1 \<inter> a2 \<subseteq> (a::'b set)\<close> \<open>(b1::'b set) \<in> FiltersAgain5.filter.Rep_filter (F1::'b filter) \<and> (b2::'b set) \<in> FiltersAgain5.filter.Rep_filter (F2::'b filter) \<and> b1 \<inter> b2 \<subseteq> (b::'b set)\<close> is_filter.F1 is_pisystem_def)
      have "(a \<inter> b) \<supseteq> (a1 \<inter> a2) \<inter> (b1 \<inter> b2)"
        using \<open>(a1::'b set) \<in> FiltersAgain5.filter.Rep_filter (F1::'b filter) \<and> (a2::'b set) \<in> FiltersAgain5.filter.Rep_filter (F2::'b filter) \<and> a1 \<inter> a2 \<subseteq> (a::'b set)\<close> \<open>(b1::'b set) \<in> FiltersAgain5.filter.Rep_filter (F1::'b filter) \<and> (b2::'b set) \<in> FiltersAgain5.filter.Rep_filter (F2::'b filter) \<and> b1 \<inter> b2 \<subseteq> (b::'b set)\<close> by auto
      have "(a1 \<inter> a2) \<inter> (b1 \<inter> b2) = (a1 \<inter> b1) \<inter> (a2 \<inter> b2)"
        by (simp add: inf_assoc inf_left_commute)
      show "(a \<inter> b) \<in> ?S"
        using \<open>(a1::'b set) \<inter> (a2::'b set) \<inter> ((b1::'b set) \<inter> (b2::'b set)) = a1 \<inter> b1 \<inter> (a2 \<inter> b2)\<close> \<open>(a1::'b set) \<inter> (a2::'b set) \<inter> ((b1::'b set) \<inter> (b2::'b set)) \<subseteq> (a::'b set) \<inter> (b::'b set)\<close> \<open>(a1::'b set) \<inter> (b1::'b set) \<in> FiltersAgain5.filter.Rep_filter (F1::'b filter) \<and> (a2::'b set) \<inter> (b2::'b set) \<in> FiltersAgain5.filter.Rep_filter (F2::'b filter)\<close> by auto
    qed
    show ?thesis
      by (metis (mono_tags, lifting) \<open>\<And>(b::'b set) a::'b set. a \<in> {x::'b set. \<exists>x1::'b set \<in>FiltersAgain5.filter.Rep_filter (F1::'b filter). \<exists>x2::'b set \<in>FiltersAgain5.filter.Rep_filter (F2::'b filter). x1 \<inter> x2 \<subseteq> x} \<and> b \<in> {x::'b set. \<exists>x1::'b set\<in>FiltersAgain5.filter.Rep_filter F1. \<exists>x2::'b set\<in>FiltersAgain5.filter.Rep_filter F2. x1 \<inter> x2 \<subseteq> x} \<longrightarrow> a \<inter> b \<in> {x::'b set. \<exists>x1::'b set\<in>FiltersAgain5.filter.Rep_filter F1. \<exists>x2::'b set\<in>FiltersAgain5.filter.Rep_filter F2. x1 \<inter> x2 \<subseteq> x}\<close> is_pisystem_def)
  qed
  have "is_upclosed ?S"
    using inf.absorb_iff2 is_upclosed_def by fastforce
  show ?thesis
    by (simp add: FiltersAgain5.is_filter_def \<open>is_inhabited {x::'b set. \<exists>x1::'b set\<in>FiltersAgain5.filter.Rep_filter (F1::'b filter). \<exists>x2::'b set \<in>FiltersAgain5.filter.Rep_filter (F2::'b filter). x1 \<inter> x2 \<subseteq> x}\<close> \<open>is_pisystem {x::'b set. \<exists>x1::'b set\<in>FiltersAgain5.filter.Rep_filter (F1::'b filter). \<exists>x2::'b set \<in>FiltersAgain5.filter.Rep_filter (F2::'b filter). x1 \<inter> x2 \<subseteq> x}\<close> \<open>is_upclosed {x::'b set. \<exists>x1::'b set\<in>FiltersAgain5.filter.Rep_filter (F1::'b filter). \<exists>x2::'b set \<in>FiltersAgain5.filter.Rep_filter (F2::'b filter). x1 \<inter> x2 \<subseteq> x}\<close>)
qed

lemma filter_join_is_filter:
  "is_filter  (filter_closure(Rep_filter`EF))"
proof(cases "(Rep_filter`EF) = {}")
  case True
  have "filter_closure(Rep_filter`EF) = {UNIV}"
    by (simp add: True filter_closure_def)
  then show ?thesis
    by (simp add: FiltersAgain5.is_filter_def is_inhabited_def is_pisystem_def is_upclosed_def top.extremum_unique) 
next
  case False
  let ?R="Rep_filter`EF"
  let ?S="filter_generated_by_family ?R"
  have B0:"\<forall>F \<in> ?R. is_filter F"
    using Rep_is_filter by blast
  have B1:"\<forall>F \<in> ?R. is_inhabited F"
    using B0 is_filter.F0 by blast
  have B2:"\<forall>F \<in> ?R. is_upclosed F"
    using B0 is_filter.F2 by blast
  have B3:"\<forall>F \<in> ?R. UNIV \<in> F"
    by (simp add: B0 filter_topped)
  have B4:"\<forall>F \<in> ?R. F \<subseteq> ?S"
  proof
    fix F assume A0:"F \<in> ?R"
     show B40:"F \<subseteq> ?S"
    proof
      fix x assume A1:"x \<in> F" 
      have B41:"{x} \<in> Pow(\<Union>?R)"
        using A0 A1 by blast
      have B42: "finite {x} \<and>  {x} \<noteq> {} \<and>  (Inf {x}) \<le> x"
        by simp
      show "x \<in> ?S"
        by (metis (mono_tags, lifting) B41 B42 filter_generated_by_family_def mem_Collect_eq)
      qed
  qed
  have B5:"is_inhabited ?S"
    by (metis B0 B4 False FiltersAgain5.is_filter_def empty_subsetI ex_in_conv is_inhabited_def subset_antisym)
  have B6:"is_pisystem ?S"
  proof-
    have "\<And>x y. (x \<in> ?S \<and> y \<in> ?S) \<longrightarrow> x \<inter> y \<in> ?S"
    proof
    fix x y assume "x \<in> ?S \<and> y \<in> ?S"
    obtain Ex where "Ex \<in> Pow(\<Union>?R) \<and> finite Ex \<and> Ex \<noteq> {} \<and> Inf Ex \<subseteq> x"
      by (smt (verit, best) \<open>(x::'b set) \<in> filter_generated_by_family (FiltersAgain5.filter.Rep_filter ` (EF::'b filter set)) \<and> (y::'b set) \<in> filter_generated_by_family (FiltersAgain5.filter.Rep_filter ` EF)\<close> filter_generated_by_family_def mem_Collect_eq)
    obtain Ey where "Ey \<in> Pow(\<Union>?R) \<and> finite Ey \<and> Ey \<noteq> {} \<and> Inf Ey \<subseteq> y"
      by (smt (verit, del_insts) \<open>(x::'b set) \<in> filter_generated_by_family (FiltersAgain5.filter.Rep_filter ` (EF::'b filter set)) \<and> (y::'b set) \<in> filter_generated_by_family (FiltersAgain5.filter.Rep_filter ` EF)\<close> filter_generated_by_family_def mem_Collect_eq)
    define Exy where "Exy = Ex \<union> Ey"
    have "Exy \<in> Pow(\<Union>?R)  \<and> finite Exy \<and> Exy \<noteq> {}"
      using Exy_def \<open>(Ex::'b set set) \<in> Pow (\<Union> (FiltersAgain5.filter.Rep_filter ` (EF::'b filter set))) \<and> finite Ex \<and> Ex \<noteq> {} \<and> \<Inter> Ex \<subseteq> (x::'b set)\<close> \<open>(Ey::'b set set) \<in> Pow (\<Union> (FiltersAgain5.filter.Rep_filter ` (EF::'b filter set))) \<and> finite Ey \<and> Ey \<noteq> {} \<and> \<Inter> Ey \<subseteq> (y::'b set)\<close> by auto
    have " Inf Exy \<le> x \<inter> y"
      using Exy_def \<open>(Ex::'b set set) \<in> Pow (\<Union> (FiltersAgain5.filter.Rep_filter ` (EF::'b filter set))) \<and> finite Ex \<and> Ex \<noteq> {} \<and> \<Inter> Ex \<subseteq> (x::'b set)\<close> \<open>(Ey::'b set set) \<in> Pow (\<Union> (FiltersAgain5.filter.Rep_filter ` (EF::'b filter set))) \<and> finite Ey \<and> Ey \<noteq> {} \<and> \<Inter> Ey \<subseteq> (y::'b set)\<close> by blast
    show "x \<inter> y \<in> ?S"
      using \<open>(Exy::'b set set) \<in> Pow (\<Union> (FiltersAgain5.filter.Rep_filter ` (EF::'b filter set))) \<and> finite Exy \<and> Exy \<noteq> {}\<close> \<open>\<Inter> (Exy::'b set set) \<subseteq> (x::'b set) \<inter> (y::'b set)\<close> filter_generated_by_family_def by blast
  qed
    show ?thesis
      by (simp add: \<open>\<And>(y::'b set) x::'b set. x \<in> filter_generated_by_family (FiltersAgain5.filter.Rep_filter ` (EF::'b filter set)) \<and> y \<in> filter_generated_by_family (FiltersAgain5.filter.Rep_filter ` EF) \<longrightarrow> x \<inter> y \<in> filter_generated_by_family (FiltersAgain5.filter.Rep_filter ` EF)\<close> is_pisystem_def)
  qed
  have B7:"is_upclosed ?S"
    by (smt (verit) B6 CollectD CollectI False Int_subset_iff all_not_in_conv bexE filter_generated_by_family_def inf.absorb_iff2 inf.order_iff inf_le1 is_pisystem_def is_upclosed_def subset_iff top_greatest)
  show ?thesis
    by (metis B5 B6 B7 False FiltersAgain5.is_filter.intro filter_closure_def)
qed


lemma finite_meet_in_set:
  fixes C::"'X::{semilattice_inf,Inf} set"
  assumes Inf_lower:"\<And>(x::'X::{semilattice_inf,Inf}) A. x \<in> A \<Longrightarrow> Inf A \<le> x" and
          Inf_grlow:"\<And>z A. (\<And>(x::'X::{semilattice_inf,Inf}). x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A" and
          A2: "\<And>a1 a2. a1 \<in> C \<Longrightarrow> a2 \<in> C \<Longrightarrow> (inf a1 a2) \<in> C"and 
          A3:"finite E" and A4:"E \<noteq> {}" and A5:"E \<subseteq> C"
  shows "(Inf E) \<in> C"
proof -
  from A3 A4 A5 show ?thesis
  proof (induct E rule: finite_ne_induct)
    case (singleton x) with assms show ?case
      by (metis Inf_fin.coboundedI Inf_fin.singleton dual_order.eq_iff finite.emptyI finite_insert insert_subset)
    next case (insert x F)
    then have "(Inf (insert x F)) \<in> C" using assms
    proof-
      have P0:"x \<in> C" using insert.prems by auto
      have P1: "F \<subseteq> C" using insert.prems by auto
      with A2 have P2:"inf x (Inf F) \<in> C" by (simp add: P0 insert.hyps(4))
      from insert.hyps have P3:"(Inf F) \<in> C" using P1 by blast
      have P4:"Inf (insert x F) = inf x (Inf F)"
      proof-
        have B0:"Inf (insert x F) \<le>  (Inf F)"
          by (simp add: Inf_grlow local.Inf_lower)
        have B1:"inf x (Inf F) = Inf {x, Inf F}"
        proof-
          have "Inf {x, Inf F} \<le> x"
            by (simp add: local.Inf_lower)
          have "Inf {x, Inf F} \<le> Inf F"
            by (simp add: local.Inf_lower)
          have "inf x (Inf F) \<le> x"
            by simp
          have "inf x (Inf F) \<le> Inf F"
            by simp
          have "Inf {x, Inf F} \<le> inf x (Inf F)"
            by (simp add: \<open>Inf {x::'X, Inf (F::'X set)} \<le> Inf F\<close> \<open>Inf {x::'X, Inf (F::'X set)} \<le> x\<close>)
          have "Inf {x, Inf F} \<ge> inf x (Inf F)"
            using Inf_grlow by fastforce
          show ?thesis
            using \<open>Inf {x::'X, Inf (F::'X set)} \<le> inf x (Inf F)\<close> \<open>inf (x::'X) (Inf (F::'X set)) \<le> Inf {x, Inf F}\<close> order_antisym_conv by blast
        qed
        have "Inf {x, Inf F} = Inf (insert x F)"
        proof-
          have "\<forall>y \<in> (insert x F). Inf {x, Inf F} \<le> y"
            by (metis B1 inf.coboundedI2 insert_iff local.Inf_lower)
          have "\<forall>y \<in>  (insert x F).  Inf (insert x F) \<le> y"
            by (simp add: local.Inf_lower)
          show ?thesis
            by (metis B0 B1 Inf_grlow \<open>\<forall>y::'X\<in>insert (x::'X) (F::'X set). Inf {x, Inf F} \<le> y\<close> antisym_conv insertI1 le_inf_iff local.Inf_lower)
        qed
        show ?thesis
          by (simp add: B1 \<open>Inf {x::'X, Inf (F::'X set)} = Inf (insert x F)\<close>)
      qed
      then show "(Inf (insert x F)) \<in> C"  by (simp add: P2)
    qed
    show ?case
      using \<open>Inf (insert x F) \<in> C\<close> by auto
  qed
qed



lemma filter_join_is_ub:
  "\<forall>F \<in>(Rep_filter`EF). F \<subseteq>  (filter_closure(Rep_filter`EF))"
proof(cases "(Rep_filter`EF) = {}")
  case True
  then show ?thesis  by simp
next
  case False
  then show ?thesis
  proof-
    let ?R="Rep_filter`EF"
    let ?S="filter_generated_by_family ?R"
    have "\<forall>F \<in> ?R. F \<subseteq> ?S"
    proof
     fix F assume A0:"F \<in>?R"
     show "F \<subseteq> ?S"
     proof
      fix x assume A1:"x \<in> F" 
      have B41:"{x} \<in> Pow(\<Union>?R)"
        using A0 A1 by blast
      have B42: "finite {x} \<and>  {x} \<noteq> {} \<and>  (Inf {x}) \<le> x"
        by simp
      show "x \<in> ?S"
        by (metis (mono_tags, lifting) B41 B42 filter_generated_by_family_def mem_Collect_eq)
      qed
  qed
  show ?thesis
    by (simp add: \<open>\<forall>F::'b set set \<in>FiltersAgain5.filter.Rep_filter ` (EF::'b filter set). F \<subseteq> filter_generated_by_family (FiltersAgain5.filter.Rep_filter ` EF)\<close> filter_closure_def)
  qed
qed


lemma filter_join_is_lub:
  assumes A0:"\<forall>F \<in> (Rep_filter`EF). F \<subseteq> (Rep_filter H)"
  shows "(filter_closure(Rep_filter`EF)) \<subseteq> (Rep_filter H)"
proof(cases "(Rep_filter`EF) = {}")
  case True
  then show ?thesis
    by (simp add: Rep_is_filter filter_closure_def filter_topped)
next
  case False
  then show ?thesis
  proof-
    let ?R="Rep_filter`EF"
    let ?S="filter_generated_by_family ?R"
    have "\<forall>x \<in>  (filter_closure(Rep_filter`EF)). x \<in> (Rep_filter H)"
    proof
      fix x assume "x \<in> (filter_closure(Rep_filter`EF))"
      obtain Ex where "Ex \<in> Pow(\<Union>?R) \<and> finite Ex \<and> Ex \<noteq> {} \<and> Inf Ex \<subseteq> x"
        by (smt (verit, ccfv_SIG) False \<open>(x::'b set) \<in> filter_closure (FiltersAgain5.filter.Rep_filter ` (EF::'b filter set))\<close> filter_closure_def filter_generated_by_family_def mem_Collect_eq)
      have "Ex \<subseteq> (Rep_filter H)" 
        using \<open>(Ex::'b set set) \<in> Pow (\<Union> (FiltersAgain5.filter.Rep_filter ` (EF::'b filter set))) \<and> finite Ex \<and> Ex \<noteq> {} \<and> \<Inter> Ex \<subseteq> (x::'b set)\<close> assms by fastforce
      have "is_filter (Rep_filter H)"
        by (simp add: Rep_is_filter)
      have "(Inf Ex) \<in> (Rep_filter H)"
        by (metis Inf_greatest Inter_lower \<open>(Ex::'b set set) \<in> Pow (\<Union> (FiltersAgain5.filter.Rep_filter ` (EF::'b filter set))) \<and> finite Ex \<and> Ex \<noteq> {} \<and> \<Inter> Ex \<subseteq> (x::'b set)\<close> \<open>(Ex::'b set set) \<subseteq> FiltersAgain5.filter.Rep_filter (H::'b filter)\<close> \<open>FiltersAgain5.is_filter (FiltersAgain5.filter.Rep_filter (H::'b filter))\<close> finite_meet_in_set is_filter.F1 is_pisystem_def)
      show "x \<in> (Rep_filter H)"
        using \<open>(Ex::'b set set) \<in> Pow (\<Union> (FiltersAgain5.filter.Rep_filter ` (EF::'b filter set))) \<and> finite Ex \<and> Ex \<noteq> {} \<and> \<Inter> Ex \<subseteq> (x::'b set)\<close> \<open>FiltersAgain5.is_filter (FiltersAgain5.filter.Rep_filter (H::'b filter))\<close> \<open>\<Inter> (Ex::'b set set) \<in> FiltersAgain5.filter.Rep_filter (H::'b filter)\<close> is_filter.F2 is_upclosed_def by blast
    qed
    show ?thesis
      by (simp add: \<open>\<forall>x::'b set \<in>filter_closure (FiltersAgain5.filter.Rep_filter ` (EF::'b filter set)). x \<in> FiltersAgain5.filter.Rep_filter (H::'b filter)\<close> subsetI)
  qed
qed

lemma filter_sup_lub2:
  fixes z::"'a filter" and A::"'a filter set"
  assumes "\<forall>x \<in> (Rep_filter`A). x \<le> (Rep_filter z)"
  shows "(Rep_filter (Sup A)) \<le>  (Rep_filter z)"
proof-
  have "\<forall>x \<in> (Rep_filter`A). is_filter x"
    using Rep_is_filter by blast
  have "(Rep_filter (Sup A)) \<le>  (Rep_filter z)"
    by (simp add: FiltersAgain5.filter_sup Repfilter_Absfilter_inv \<open>\<forall>x::'a set set \<in>FiltersAgain5.filter.Rep_filter ` (A::'a filter set). x \<subseteq> FiltersAgain5.filter.Rep_filter (z::'a filter)\<close> filter_join_is_filter filter_join_is_lub)
  show ?thesis
    by (simp add: \<open>FiltersAgain5.filter.Rep_filter (Sup (A::'a filter set)) \<subseteq> FiltersAgain5.filter.Rep_filter (z::'a filter)\<close>)
qed


lemma filter_meet_is_filter:
  "is_filter  (\<Inter>(Rep_filter`EF))"
proof-
  let ?R="Rep_filter`EF"
  let ?I="\<Inter>?R"
  have B0:"\<forall>F \<in> ?R. is_filter F"
    using Rep_is_filter by blast
  have B1:"\<forall>F \<in> ?R. is_inhabited F"
    using B0 is_filter.F0 by blast
  have B2:"\<forall>F \<in> ?R. is_upclosed F"
    using B0 is_filter.F2 by blast
  have B3:"\<forall>F \<in> ?R. UNIV \<in> F"
    by (metis B1 B2 ex_in_conv is_inhabited_def is_upclosed_def top_greatest)
  have B4:"\<forall>F \<in> ?R. is_pisystem F"
    using B0 is_filter.F1 by blast
  have B5:"is_inhabited ?I"
    using B3 is_inhabited_def by fastforce
  have B6:"is_pisystem ?I"
    by (meson B4 Inter_iff is_pisystem_def)
  have B7:"is_upclosed ?I"
    by (meson B2 Inter_iff is_upclosed_def)
  show ?thesis
    by (simp add: B5 B6 B7 FiltersAgain5.is_filter_def)
qed

lemma filter_meet_is_filter2:
  "is_filter ((Rep_filter F1) \<inter> (Rep_filter F2))"
proof-
  have "(Rep_filter F1) \<inter> (Rep_filter F2) = (\<Inter>(Rep_filter`{F1, F2}))"
    by blast
  show ?thesis
    by (metis \<open>FiltersAgain5.filter.Rep_filter (F1::'b filter) \<inter> FiltersAgain5.filter.Rep_filter (F2::'b filter) = \<Inter> (FiltersAgain5.filter.Rep_filter ` {F1, F2})\<close> filter_meet_is_filter)
qed


lemma filter_meet_is_lb:
  "\<forall>F \<in> (Rep_filter`EF).  (\<Inter>(Rep_filter`EF)) \<subseteq> F"
  by blast



lemma filter_meet_is_glb:
  assumes "\<forall>F \<in> (Rep_filter`EF).  (Rep_filter H) \<subseteq> F"
  shows "  (Rep_filter H) \<subseteq> (\<Inter>(Rep_filter`EF))"
  using assms by fastforce

  


lemma rep_filter_meet_set:
  "((Rep_filter F1) \<inter> (Rep_filter F2))={x. \<exists>x1 \<in> (Rep_filter F1). \<exists>x2 \<in> (Rep_filter F2). x=x1 \<union> x2}"
proof-
  have "\<forall>A Aa Ab. FiltersAgain5.is_filter A \<and> FiltersAgain5.is_filter Aa \<longrightarrow> ((Ab::'a set) \<in> A \<inter> Aa) = (\<exists>Ac. Ac \<in> A \<and> (\<exists>A. A \<in> Aa \<and> Ab = Ac \<union> A))"
    by (smt (z3) filter_meet)
  then have "{A. \<exists>Aa. Aa \<in> FiltersAgain5.filter.Rep_filter F1 \<and> (\<exists>Ab. Ab \<in> FiltersAgain5.filter.Rep_filter F2 \<and> A = Aa \<union> Ab)} = {A. A \<in> FiltersAgain5.filter.Rep_filter F1 \<inter> FiltersAgain5.filter.Rep_filter F2}"
    by (metis (no_types, opaque_lifting) Rep_is_filter filter_meet)  
  then show ?thesis
    by blast
qed
  
lemma sup_filter_rep:
  "\<And>x. x \<in> Rep_filter(inf F1 F2) \<longleftrightarrow> (x \<in> ((Rep_filter F1) \<inter> (Rep_filter F2)))"
proof
  fix x assume "x \<in> Rep_filter (inf F1 F2)"
  show "x \<in> ((Rep_filter F1) \<inter> (Rep_filter F2))"
    by (metis Repfilter_Absfilter_inv \<open>(x::'a set) \<in> FiltersAgain5.filter.Rep_filter (inf (F1::'a filter) (F2::'a filter))\<close> filter_meet_is_filter2 inf_filter rep_filter_meet_set)
  next
    fix x assume "x \<in> ((Rep_filter F1) \<inter> (Rep_filter F2))"
    show "x \<in>  Rep_filter(inf F1 F2)"
      by (metis FiltersAgain5.inf_filter Repfilter_Absfilter_inv \<open>(x::'a set) \<in> FiltersAgain5.filter.Rep_filter (F1::'a filter) \<inter> FiltersAgain5.filter.Rep_filter (F2::'a filter)\<close> filter_meet_is_filter2 rep_filter_meet_set)
qed

lemma sup_filter_rep2:
  "\<And>x. x \<in> Rep_filter(sup F1 F2) \<longleftrightarrow> (\<exists>x1 \<in> (Rep_filter F1). \<exists>x2 \<in> (Rep_filter F2). x1 \<inter> x2 \<le> x)"
proof
  fix x assume "x \<in> Rep_filter (sup F1 F2)"
  show "(\<exists>x1 \<in> (Rep_filter F1). \<exists>x2 \<in> (Rep_filter F2). x1 \<inter> x2 \<le> x)"
    by (smt (verit) CollectD Repfilter_Absfilter_inv \<open>(x::'a set) \<in> FiltersAgain5.filter.Rep_filter (sup (F1::'a filter) (F2::'a filter))\<close> filter_sup_is_filter sup_filter)
   next 
  fix x assume "(\<exists>x1 \<in> (Rep_filter F1). \<exists>x2 \<in> (Rep_filter F2). x1 \<inter> x2 \<le> x)"
  show "x \<in> Rep_filter (sup F1 F2)"
    by (simp add: Repfilter_Absfilter_inv \<open>\<exists>x1::'a set\<in>FiltersAgain5.filter.Rep_filter (F1::'a filter). \<exists>x2::'a set\<in>FiltersAgain5.filter.Rep_filter (F2::'a filter). x1 \<inter> x2 \<subseteq> (x::'a set)\<close> filter_sup_is_filter sup_filter)
qed

lemma fsup_is_ub:
  "(Rep_filter F1) \<subseteq> Rep_filter(sup F1 F2)"
  using Rep_is_filter filter_topped sup_filter_rep2 by fastforce

lemma fsup_as:
  "Rep_filter(sup F1 F2) =  Rep_filter(sup F2 F1)"
  by (smt (verit, best) Collect_cong inf.commute sup_filter)

lemma fsup_is_ub2:
  "(Rep_filter F2) \<subseteq> Rep_filter(sup F1 F2)"
  using Rep_is_filter filter_topped sup_filter_rep2 by fastforce

lemma fsup_is_lub:
  assumes "((Rep_filter F2) \<subseteq> (Rep_filter H)) \<and> ((Rep_filter F1) \<subseteq> (Rep_filter H))"
  shows "(Rep_filter(sup F1 F2)) \<subseteq> (Rep_filter H)"
  by (smt (verit) FiltersAgain5.is_filter_def Rep_is_filter assms is_pisystem_def is_upclosed_def subset_iff sup_filter_rep2)

lemma fsup_eq_sup:
  "Rep_filter(Sup{F1, F2}) = Rep_filter(sup F1 F2)"
proof-
  have "Rep_filter(Sup{F1, F2}) \<subseteq> Rep_filter(sup F1 F2)"
  proof
    fix x assume "x \<in> Rep_filter(Sup{F1, F2}) "
    have "x \<in> filter_closure(Rep_filter`{F1, F2})"
      by (metis FiltersAgain5.filter_sup Repfilter_Absfilter_inv \<open>(x::'a set) \<in> FiltersAgain5.filter.Rep_filter (Sup {F1::'a filter, F2::'a filter})\<close> filter_join_is_filter)
    obtain Ex where "Ex \<in> Pow(\<Union>(Rep_filter`{F1, F2})) \<and> finite Ex \<and> Ex \<noteq> {} \<and> Inf Ex \<subseteq> x"
      by (smt (z3) \<open>(x::'a set) \<in> filter_closure (FiltersAgain5.filter.Rep_filter ` {F1::'a filter, F2::'a filter})\<close> empty_iff filter_closure_def filter_generated_by_family_def image_is_empty insertCI mem_Collect_eq)
    define Ex1 where "Ex1=Ex \<inter> Rep_filter(F1)"
    have "finite Ex1 \<and> Ex1 \<subseteq> Rep_filter(F1)"
      by (simp add: \<open>(Ex::'a set set) \<in> Pow (\<Union> (FiltersAgain5.filter.Rep_filter ` {F1::'a filter, F2::'a filter})) \<and> finite Ex \<and> Ex \<noteq> {} \<and> \<Inter> Ex \<subseteq> (x::'a set)\<close> local.Ex1_def)
    have "is_filter (Rep_filter(F1))"
      by (simp add: Rep_is_filter)
    have "(Inf Ex1) \<in> (Rep_filter(F1))"
      by (metis Inf_empty Inf_greatest Inter_lower \<open>FiltersAgain5.is_filter (FiltersAgain5.filter.Rep_filter (F1::'a filter))\<close> \<open>finite (Ex1::'a set set) \<and> Ex1 \<subseteq> FiltersAgain5.filter.Rep_filter (F1::'a filter)\<close> filter_topped finite_meet_in_set is_filter.F1 is_pisystem_def)
    define Ex2 where "Ex2=Ex \<inter> Rep_filter(F2)"
    have "finite Ex2 \<and> Ex2 \<subseteq> Rep_filter(F2)"
      by (simp add: Ex2_def \<open>(Ex::'a set set) \<in> Pow (\<Union> (FiltersAgain5.filter.Rep_filter ` {F1::'a filter, F2::'a filter})) \<and> finite Ex \<and> Ex \<noteq> {} \<and> \<Inter> Ex \<subseteq> (x::'a set)\<close>)
    have "is_filter (Rep_filter(F2))"
      by (simp add: Rep_is_filter)
    have "(Inf Ex2) \<in> (Rep_filter(F2))"
      by (metis (no_types, lifting) Inf_empty Inf_greatest Inter_lower \<open>FiltersAgain5.is_filter (FiltersAgain5.filter.Rep_filter (F2::'a filter))\<close> \<open>finite (Ex2::'a set set) \<and> Ex2 \<subseteq> FiltersAgain5.filter.Rep_filter (F2::'a filter)\<close> filter_topped finite_meet_in_set is_filter.F1 is_pisystem_def)
    define x1 where "x1=(Inf Ex1)" define x2 where "x2=(Inf Ex2)"
    have "x1 \<in> (Rep_filter F1) \<and> x2 \<in> (Rep_filter F2)"
      using \<open>\<Inter> (Ex1::'a set set) \<in> FiltersAgain5.filter.Rep_filter (F1::'a filter)\<close> \<open>\<Inter> (Ex2::'a set set) \<in> FiltersAgain5.filter.Rep_filter (F2::'a filter)\<close> x1_def x2_def by auto
    have "Ex \<subseteq> (\<Union>(Rep_filter`{F1, F2}))"
      using \<open>(Ex::'a set set) \<in> Pow (\<Union> (FiltersAgain5.filter.Rep_filter ` {F1::'a filter, F2::'a filter})) \<and> finite Ex \<and> Ex \<noteq> {} \<and> \<Inter> Ex \<subseteq> (x::'a set)\<close> by blast
    have "(\<Union>(Rep_filter`{F1, F2})) = (Rep_filter F1) \<union> (Rep_filter F2)"
      by blast
    have "Ex \<subseteq> (Rep_filter F1) \<union> (Rep_filter F2)"
      using \<open>(Ex::'a set set) \<subseteq> \<Union> (FiltersAgain5.filter.Rep_filter ` {F1::'a filter, F2::'a filter})\<close> by blast
    have "Ex = Ex1 \<union> Ex2 "
      using Ex2_def \<open>(Ex::'a set set) \<subseteq> \<Union> (FiltersAgain5.filter.Rep_filter ` {F1::'a filter, F2::'a filter})\<close> local.Ex1_def by auto
    have "(Inf Ex) = (Inf Ex1) \<inter> (Inf Ex2)"
      by (simp add: Inf_union_distrib \<open>(Ex::'a set set) = (Ex1::'a set set) \<union> (Ex2::'a set set)\<close>)
    have "... = x1 \<inter> x2"
      by (simp add: x1_def x2_def)
    have "\<exists>x1 \<in> (Rep_filter F1). \<exists>x2 \<in> (Rep_filter F2). x1 \<inter> x2 \<le> x"
      using \<open>(Ex::'a set set) \<in> Pow (\<Union> (FiltersAgain5.filter.Rep_filter ` {F1::'a filter, F2::'a filter})) \<and> finite Ex \<and> Ex \<noteq> {} \<and> \<Inter> Ex \<subseteq> (x::'a set)\<close> \<open>(x1::'a set) \<in> FiltersAgain5.filter.Rep_filter (F1::'a filter) \<and> (x2::'a set) \<in> FiltersAgain5.filter.Rep_filter (F2::'a filter)\<close> \<open>\<Inter> (Ex::'a set set) = \<Inter> (Ex1::'a set set) \<inter> \<Inter> (Ex2::'a set set)\<close> x1_def x2_def by fastforce
    have "\<forall>y. y \<in> (Rep_filter (sup F1 F2)) \<longleftrightarrow> (\<exists>x1 \<in> (Rep_filter F1). \<exists>x2 \<in> (Rep_filter F2). x1 \<inter> x2 \<le> y) "
      using sup_filter_rep2 by auto
    show "x \<in>  Rep_filter(sup F1 F2)"
      by (simp add: \<open>\<exists>x1::'a set\<in>FiltersAgain5.filter.Rep_filter (F1::'a filter). \<exists>x2::'a set\<in>FiltersAgain5.filter.Rep_filter (F2::'a filter). x1 \<inter> x2 \<subseteq> (x::'a set)\<close> \<open>\<forall>y::'a set. (y \<in> FiltersAgain5.filter.Rep_filter (sup (F1::'a filter) (F2::'a filter))) = (\<exists>x1::'a set\<in>FiltersAgain5.filter.Rep_filter F1. \<exists>x2::'a set\<in>FiltersAgain5.filter.Rep_filter F2. x1 \<inter> x2 \<subseteq> y)\<close>)
  qed
  have "Rep_filter(sup F1 F2) \<subseteq> Rep_filter(Sup{F1, F2})"
  proof-
   have "(Rep_filter F1)\<subseteq>  Rep_filter(Sup{F1, F2})"
      by (metis Repfilter_Absfilter_inv filter_join_is_filter filter_join_is_ub filter_sup image_eqI insertI1)
   have "(Rep_filter F2) \<subseteq>  Rep_filter(Sup{F1, F2})"
     by (metis Repfilter_Absfilter_inv filter_join_is_filter filter_join_is_ub filter_sup image_eqI insertCI)
   have "Rep_filter(Sup{F1, F2}) \<supseteq>  Rep_filter(sup F1 F2)"
     by (simp add: \<open>FiltersAgain5.filter.Rep_filter (F1::'a filter) \<subseteq> FiltersAgain5.filter.Rep_filter (Sup {F1, F2::'a filter})\<close> \<open>FiltersAgain5.filter.Rep_filter (F2::'a filter) \<subseteq> FiltersAgain5.filter.Rep_filter (Sup {F1::'a filter, F2})\<close> fsup_is_lub)
   show ?thesis
     by (simp add: \<open>FiltersAgain5.filter.Rep_filter (sup (F1::'a filter) (F2::'a filter)) \<subseteq> FiltersAgain5.filter.Rep_filter (Sup {F1, F2})\<close>)
  qed
  show ?thesis
    by (simp add: \<open>FiltersAgain5.filter.Rep_filter (Sup {F1::'a filter, F2::'a filter}) \<subseteq> FiltersAgain5.filter.Rep_filter (sup F1 F2)\<close> \<open>FiltersAgain5.filter.Rep_filter (sup (F1::'a filter) (F2::'a filter)) \<subseteq> FiltersAgain5.filter.Rep_filter (Sup {F1, F2})\<close> subset_antisym)
qed

instance proof
fix x::"'a filter" and  y::"'a filter" and  z::"'a filter" and A::"'a filter set"
show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
  by (simp add: dual_order.strict_iff_not local.le_filter_def local.less_filter_def)
show "x \<le> x"
  by (simp add: local.le_filter_def)
show " x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  using local.le_filter_def by force
show " x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  by (simp add: FiltersAgain5.filter.Rep_filter_inject local.le_filter_def)
show "inf x y \<le> x"
  by (simp add: FiltersAgain5.le_filter_def FiltersAgain5.sup_filter_rep subset_eq)
show "inf x y \<le> y"
  by (simp add: FiltersAgain5.sup_filter_rep local.le_filter_def subset_iff)
show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> inf y z"
  by (metis (mono_tags, lifting) FiltersAgain5.inf_filter Repfilter_Absfilter_inv filter_meet_is_filter2 le_inf_iff local.le_filter_def rep_filter_meet_set)
show "x \<le> sup x y"
  by (simp add: fsup_is_ub local.le_filter_def)
show "y \<le> sup x y"
  by (simp add: fsup_is_ub2 local.le_filter_def)
show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> sup y z \<le> x"
  by (simp add: fsup_is_lub local.le_filter_def)
show "x \<in> A \<Longrightarrow> Inf A \<le> x"
  by (simp add: Inf_lower Repfilter_Absfilter_inv filter_inf filter_meet_is_filter local.le_filter_def)
show "(\<And>x::'a filter. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A"
  by (simp add: FiltersAgain5.le_filter_def Repfilter_Absfilter_inv filter_inf filter_meet_is_filter filter_meet_is_glb)
show "x \<in> A \<Longrightarrow> x \<le> Sup A"
  by (simp add: FiltersAgain5.filter_sup FiltersAgain5.le_filter_def Repfilter_Absfilter_inv filter_join_is_filter filter_join_is_ub)
show "(\<And>x::'a filter. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup A \<le> z"
  by (simp add: FiltersAgain5.le_filter_def filter_sup_lub2)
show "Inf {} = (top::'a filter)"
  by (simp add: FiltersAgain5.filter_inf top_filter)
show "Sup {} = (bot::'a filter)"
  by (simp add: FiltersAgain5.filter_sup bot_filter filter_closure_def)
qed


end  


end