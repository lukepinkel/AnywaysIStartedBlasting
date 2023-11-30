theory FiltersAgain2
  imports Main "./Posets" 
begin
hide_type Filter.filter

declare [[show_types]]




definition is_upset::"'X::ord set \<Rightarrow> bool" where
  "is_upset A \<equiv> \<forall>x. (\<exists>a \<in> A. x \<ge> a) \<longrightarrow> x \<in> A"

definition is_upset_in::"'X::ord set \<Rightarrow> 'X::ord set \<Rightarrow> bool" where
  "is_upset_in A X \<equiv> \<forall>x \<in> X. (\<exists>a \<in> A. x \<ge> a) \<longrightarrow> x \<in> A"

definition principal_filter::"'X::ord \<Rightarrow> 'X::ord set" where
  "principal_filter a \<equiv> {x. x \<ge> a }"

definition principal_filter_in::"'X::ord \<Rightarrow> 'X::ord set  \<Rightarrow> 'X::ord set" where
  "principal_filter_in a X \<equiv> {x \<in> X. x \<ge> a }"

definition is_finf_closed::"'X::semilattice_inf set \<Rightarrow> bool" where
  "is_finf_closed A \<equiv> (\<forall>x. \<forall>y. (inf x y)\<in>A)"

definition is_finf_closed_in::"'X::semilattice_inf set \<Rightarrow> 'X::semilattice_inf set \<Rightarrow> bool" where
  "is_finf_closed_in A X \<equiv> (\<forall>x \<in> X. \<forall>y \<in> X. (inf x y)\<in>A)"

definition is_inhabited::"'X set \<Rightarrow> bool" where
  "is_inhabited A \<equiv> (A \<noteq> {})"

definition is_inhabited_in::"'X set\<Rightarrow> 'X set \<Rightarrow> bool" where
  "is_inhabited_in A X \<equiv> (is_inhabited A) \<and> (A \<in> Pow X)"

definition is_proper::"'X set \<Rightarrow> bool" where
  "is_proper A \<equiv> (A \<noteq> UNIV)"

definition is_proper_in::"'X set \<Rightarrow> 'X set  \<Rightarrow> bool" where
  "is_proper_in A X \<equiv> (A \<noteq> X)"

definition is_filter::"'X::semilattice_inf set \<Rightarrow> bool" where
  "is_filter A \<equiv> (is_upset A) \<and> (is_finf_closed A) \<and> (is_inhabited A) "

definition is_filter_in::"'X::semilattice_inf set \<Rightarrow> 'X::semilattice_inf set \<Rightarrow> bool" where
  "is_filter_in A X  \<equiv> (is_upset_in A X) \<and> (is_finf_closed_in A X) \<and> (is_inhabited_in A X) "

definition is_pfilter::"'X::semilattice_inf set \<Rightarrow> bool" where
  "is_pfilter A \<equiv> (is_filter A) \<and> (is_proper A)"

definition is_pfilter_in::"'X::semilattice_inf set \<Rightarrow>'X::semilattice_inf set \<Rightarrow> bool" where
  "is_pfilter_in A X \<equiv> (is_filter_in A X) \<and> (is_proper_in A X)"

definition is_set_filter::"'X set set \<Rightarrow> bool" where
  "is_set_filter A \<equiv> is_filter A"

definition is_set_filter_in::"'X set set \<Rightarrow> 'X set set \<Rightarrow> bool" where
  "is_set_filter_in A X \<equiv> (is_upset_in A X) \<and>  (is_finf_closed_in A X) \<and> (is_inhabited_in A X)"

definition is_pset_filter_in::"'X set set \<Rightarrow> 'X set set \<Rightarrow> bool" where
  "is_pset_filter_in A X \<equiv> (is_set_filter_in A X) \<and> (is_proper_in A X)"



lemma chumba1a:
  assumes A0:"is_upset A"
  shows "is_upset_in A X"
  by (meson assms is_upset_def is_upset_in_def)

lemma chumba1b:
  assumes A0:"is_upset_in A UNIV" 
  shows "is_upset A"
  by (meson UNIV_I assms is_upset_def is_upset_in_def)

lemma chumba2a:
  assumes A0:"is_finf_closed A"
  shows "is_finf_closed_in A X"
  by (meson assms is_finf_closed_def is_finf_closed_in_def)

lemma chumba2b:
  assumes A0: "is_finf_closed_in A UNIV"
  shows "is_finf_closed A"
  by (meson UNIV_I assms is_finf_closed_def is_finf_closed_in_def)

lemma chumba3a:
  assumes A0:"is_inhabited A" and A1:"A \<in> Pow X"
  shows "is_inhabited_in A X"
  by (meson assms is_inhabited_def is_inhabited_in_def)

lemma chumba3b:
  assumes A0: "is_inhabited_in A UNIV"
  shows "is_inhabited A"
  by (meson UNIV_I assms is_inhabited_def is_inhabited_in_def)

lemma chumba4a:
  "principal_filter_in a X = (principal_filter a) \<inter> X"
  by (simp add: principal_filter_def principal_filter_in_def subset_antisym subset_eq)

lemma chumba4b:
  "(principal_filter a) \<inter> UNIV = (principal_filter_in a UNIV)"
  by (simp add: chumba4a)

lemma chumbawumba1a:
  assumes A0:"is_upset (A::'X set set)"
  shows "\<forall>x::('X set). (\<exists>a::('X set) \<in> A. x \<supseteq> a) \<longrightarrow> x \<in> A"
  using assms is_upset_def by (simp add: A0 is_upset_def)
 
lemma chumbawumba1b:
  assumes A0:"A \<in> Pow X" and A1:"is_upset_in A X"
  shows "\<forall>x::('X set) \<in> X. (\<exists>a::('X set) \<in> A. x \<supseteq> a) \<longrightarrow> x \<in> A"
  by (meson A1 is_upset_in_def)

lemma chumbawumba2a:
  assumes A0:"is_finf_closed (A::'X set set)"
  shows "(\<forall>x. \<forall>y. (inf x y)\<in>A)"
  using assms is_finf_closed_def by (simp add: A0 is_finf_closed_def)
 
lemma chumbawumba2b:
  assumes A0:"is_finf_closed_in (A::'X set set) X"
  shows "(\<forall>x \<in> X. \<forall>y \<in> X. (inf x y)\<in>A)"
  by (meson assms is_finf_closed_in_def)
 
lemma chumbawumba3a:
  assumes A0:"is_inhabited A" and A1:"is_finf_closed A" and A2:"is_upset A"
  shows "(inf x y) \<in> A \<longleftrightarrow> (x \<in> A \<and> y \<in> A)"
  by (metis A1 is_finf_closed_def inf.idem)

lemma chumbawumba3b:
  assumes A0:"is_inhabited_in A X" and A1:"is_finf_closed_in A X" and A2:"is_upset_in A X"
  shows "\<forall>x \<in> X. \<forall>y \<in> X. (inf x y) \<in> A \<longleftrightarrow> (x \<in> A \<and> y \<in> A)"
  by (metis A1 is_finf_closed_in_def inf.idem)

lemma chubmawumba4a:
  "x \<in> (principal_filter a) \<longleftrightarrow> (x \<ge> a)"
  by (simp add: principal_filter_def)

lemma chubmawumba4b:
  "(a::('X::preorder)) \<in> (principal_filter a)"
  by (simp add: chubmawumba4a)

lemma chumbawumba5a1:
  assumes A0:"is_upset F"
  shows "(a \<in> F \<longrightarrow>  principal_filter a \<subseteq> F)"
  using principal_filter_def assms is_upset_def by fastforce

lemma chumbawumba5a2:
  fixes a::"('X::preorder)"
  assumes A0:"is_upset F"
  shows "(principal_filter a \<subseteq> F \<longrightarrow> a \<in> F )"
  by (simp add: chubmawumba4b in_mono)

lemma chumbawumba5a:
  assumes A0:"is_upset (F::('X::preorder set))"
  shows "((a::('X::preorder)) \<in> F) \<longleftrightarrow> (principal_filter a \<subseteq> F )"
  using assms chumbawumba5a1 chumbawumba5a2 by blast
  

lemma chumbawumba5b1:
  assumes A0:"is_upset_in F X"
  shows "\<forall>a \<in> X. a \<in> F \<longrightarrow>  principal_filter_in a X \<subseteq> F"
  by (metis IntD1 IntD2 assms chubmawumba4a chumba4a is_upset_in_def subsetI)

lemma chumbawumba5b2:
  assumes A0:"is_upset_in (F::('X::preorder set)) (X::('X::preorder set))"
  shows "\<forall>a \<in> X. principal_filter_in a X \<subseteq> F \<longrightarrow> a \<in> F"
  by (simp add: chubmawumba4b chumba4a subsetD)

lemma chumbawumba5b:
  assumes A0: "is_upset_in (F::('X::preorder set)) (X::('X::preorder set))"
  shows "\<forall>a \<in> X. (a \<in> F) \<longleftrightarrow> (principal_filter_in a X \<subseteq> F)"
  using assms chumbawumba5b1 chumbawumba5b2 by blast

lemma chumbawumba6a:
  "is_inhabited A \<longrightarrow> is_upset A \<longrightarrow> UNIV \<in> A"
  by (simp add: chumbawumba1a ex_in_conv is_inhabited_def)

lemma chumbawumba6b:
  "is_inhabited_in A (Pow(X)) \<longrightarrow> is_upset_in A (Pow(X)) \<longrightarrow> X \<in> A"
  by (metis PowD Pow_top UnionI Union_Pow_eq chumba1b chumbawumba6a is_inhabited_in_def is_upset_in_def)

lemma chumbawumba7a:
  assumes A0:"is_upset A"
  shows "is_proper A \<longleftrightarrow> {} \<notin> A"
  by (metis principal_filter_def UNIV_eq_I assms bot.extremum chumbawumba5a1 mem_Collect_eq is_proper_def top.extremum_uniqueI)

lemma chumbawumba7b1:
  assumes A0:"is_upset_in A X" and A1:"X \<noteq> {}" and A2:"A \<in> Pow X"
  shows "is_proper_in A X \<longrightarrow> {} \<notin> A"
  by (metis A0 A2 Pow_iff bot.extremum is_upset_in_def is_proper_in_def subsetI subset_antisym)


lemma chumbawumba8a:
  "is_filter (A::('X::bounded_lattice set)) \<longrightarrow> top \<in> A"

proof-
  have P0:"is_filter A \<longrightarrow> inf top top \<in> A"
    using FiltersAgain2.is_filter_def is_finf_closed_def by blast
   with P0 show ?thesis  by (simp add: is_filter_def)
qed
(* by (meson is_filter_def chumbawumba3a is_finf_closed_def)*)

lemma chumbawumba8b:
  assumes A0:"top \<in> (X::('X::bounded_lattice set))"
  shows "is_filter_in (A::('X::bounded_lattice set)) X  \<longrightarrow> top \<in> A"
proof-
  from A0 have P0:"is_filter_in A X \<longrightarrow> inf top top \<in> A"
    using is_filter_in_def is_finf_closed_in_def by blast
   with P0 show ?thesis  by (simp add: is_filter_in_def)
qed






end