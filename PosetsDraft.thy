theory PosetsDraft
  imports Main
begin

section MaximalAndMinimal
subsection Predicates
subsubsection DefinitionalPredicates
definition IsMaximal:: "'X::order  \<Rightarrow> 'X::order set  \<Rightarrow> bool" where "IsMaximal m X \<equiv> (m \<in> X) \<and> (\<forall>x \<in> X. m\<le> x \<longrightarrow> m=x)"

definition IsMinimal:: "'X::order  \<Rightarrow> 'X::order set  \<Rightarrow> bool" where"IsMinimal m X \<equiv> (m \<in> X) \<and> (\<forall>x \<in> X. m\<le> x \<longrightarrow> m=x)"

subsubsection ExistentialPredicates
definition HasMaximal::" 'X::order set  \<Rightarrow>  bool" where "HasMaximal A \<equiv> \<exists>m. IsMaximal m A"

definition HasMinimal::" 'X::order set  \<Rightarrow>  bool" where "HasMinimal A \<equiv> \<exists>m. IsMinimal m A"


section Bounds
subsection Predicates
subsubsection DefinitionalPredicates
definition IsUpperBound::"'X::order  \<Rightarrow> 'X::order set  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where "IsUpperBound m A X \<equiv> (m \<in> X) \<and> (\<forall>a \<in> A.  a\<le>m)"

definition IsLowerBound::"'X::order  \<Rightarrow> 'X::order set  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where "IsLowerBound m A X \<equiv> (m \<in> X) \<and> (\<forall>a \<in> A.  m\<le>a)"

subsubsection ExistentialPredicates

definition HasUpperBound::" 'X::order set  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where "HasUpperBound A X \<equiv> \<exists>u. IsUpperBound u A X"

definition HasLowerBound::" 'X::order set  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where "HasLowerBound A X \<equiv> \<exists>l. IsLowerBound l A X"

subsection Operators

definition UpperBounds::"'X::order set \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set" where "UpperBounds A X = {u \<in> X. IsUpperBound u A X }"

definition LowerBounds::"'X::order set \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set" where "LowerBounds A X = {l \<in> X. IsLowerBound l A X }"

definition IsDownset::"'X::order set\<Rightarrow>'X::order set \<Rightarrow> bool" where  "IsDownset D X \<equiv> (D \<in> Pow X) \<and> (\<forall>x \<in> X. \<forall>d \<in> D. x\<le>d \<longrightarrow> x \<in> D)"

definition IsUpset::"'X::order set\<Rightarrow>'X::order set \<Rightarrow> bool" where "IsUpset U X \<equiv> (U \<in> Pow X) \<and> (\<forall>x \<in> X. \<forall>u \<in> U. u\<le>x \<longrightarrow> x \<in> U)"

definition DownSets::"'X::order set \<Rightarrow>  'X::order set set" where "DownSets X = {D\<in>(Pow X). IsDownset D X }"

definition UpSets::"'X::order set \<Rightarrow>  'X::order set set" where "UpSets X = {U\<in>(Pow X). IsUpset U X }"
 
definition DownClosure::"'X::order set \<Rightarrow>  'X::order set\<Rightarrow>'X::order set" where "DownClosure A X = {x \<in> X. \<exists>a \<in> A. x \<le> a }"

definition UpClosure::"'X::order set \<Rightarrow>  'X::order set\<Rightarrow>'X::order set" where "UpClosure A X = {x \<in> X. \<exists>a \<in> A. a \<le> x }"
 
definition PrincipalDownClosure::"'X::order \<Rightarrow>'X::order set \<Rightarrow> 'X::order set" where "PrincipalDownClosure x X = (DownClosure {x} X)"

definition PrincipalUpClosure::"'X::order \<Rightarrow>'X::order set \<Rightarrow> 'X::order set" where "PrincipalUpClosure x X = (UpClosure {x} X)"


subsection BasicLemmas

lemma upper_bounds_well_defined: 
  "(UpperBounds A X \<subseteq> X) \<and> (UpperBounds A X \<in> Pow X)"
  by (simp add: UpperBounds_def)

lemma upper_bound_is_upper_bound1:
  "\<forall>x \<in>X. (x \<in> UpperBounds A X \<longleftrightarrow> IsUpperBound x A X)" 
  by (simp add: UpperBounds_def)

lemma upper_bound_is_upper_bound2:
  "\<forall>x \<in>UpperBounds A X. \<forall>a \<in>A. a\<le>x"
  by (metis IsUpperBound_def subset_iff upper_bounds_well_defined upper_bound_is_upper_bound1) 

lemma upper_bound_then_in_upperbounds:
  "\<forall>x \<in> X. (\<forall>a \<in>A. a \<le> x) \<longrightarrow> x \<in> UpperBounds A X" 
  by (simp add: IsUpperBound_def upper_bound_is_upper_bound1)

lemma upper_bounds_lem5:"IsUpset (UpperBounds A X) X"
proof-
  have B0:"\<forall>u \<in> UpperBounds A X. \<forall>a \<in> A. a\<le>u" by (simp add: upper_bound_is_upper_bound2)
  have B1:"\<forall>x \<in> X. ((\<exists>u \<in> UpperBounds A X. x \<ge> u) \<longrightarrow>(\<forall>a \<in> A. a \<le> x)) " by (meson B0 dual_order.trans)
  have B2:"\<forall>x \<in> X. ((\<exists>u \<in> UpperBounds A X. x \<ge> u) \<longrightarrow>(x \<in> UpperBounds A X))" by (meson B1 IsUpperBound_def upper_bound_is_upper_bound1)
  have B3:"IsUpset (UpperBounds A X) X" by (meson B2 IsUpset_def upper_bounds_well_defined)
  with B3 show ?thesis by auto
qed

lemma lower_bounds_well_defined: 
  "(LowerBounds A X \<subseteq> X) \<and> (LowerBounds A X \<in> Pow X)"
  by (simp add: LowerBounds_def)

lemma lower_bound_is_lower_bound1:
  "\<forall>x \<in> X. (x \<in> LowerBounds A X \<longleftrightarrow> IsLowerBound x A X)"
  by (simp add: LowerBounds_def)

lemma lower_bound_is_lower_bound2:
  "\<forall>x \<in> LowerBounds A X. \<forall>a \<in> A. x \<le> a"
  by (metis IsLowerBound_def subset_iff lower_bounds_well_defined lower_bound_is_lower_bound1)

lemma lower_bound_then_in_lowerbounds:
  "\<forall>x \<in> X. (\<forall>a \<in> A. x \<le> a) \<longrightarrow> x \<in> LowerBounds A X"
  by (simp add: IsLowerBound_def lower_bound_is_lower_bound1)

lemma lower_bounds_lem5:"IsDownset (LowerBounds A X) X"
(* by (smt (verit) IsDownset_def dual_order.trans lower_bound_is_lower_bound2 lower_bound_then_in_lowerbounds lower_bounds_well_defined)*)
proof-
  have B0:"\<forall>l \<in> LowerBounds A X. \<forall>a \<in> A. l \<le> a" by (simp add: lower_bound_is_lower_bound2)
  have B1:"\<forall>x \<in> X. ((\<exists>l \<in> LowerBounds A X. x \<le> l) \<longrightarrow> (\<forall>a \<in> A. x \<le> a))" by (meson B0 order_trans)
  have B2:"\<forall>x \<in> X. ((\<exists>l \<in> LowerBounds A X. x \<le> l) \<longrightarrow> (x \<in> LowerBounds A X))" by (meson B1 IsLowerBound_def lower_bound_is_lower_bound1)
  have B3:"IsDownset (LowerBounds A X) X" by (meson B2 IsDownset_def lower_bounds_well_defined)
  with B3 show ?thesis by auto
qed


section MaximumMinimum
subsection Predicates
subsubsection DefinitionalPredicates
definition IsMaximum::"'X::order  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where "IsMaximum m X \<equiv> IsUpperBound m X X"

definition IsMinimum::"'X::order  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where "IsMinimum m X \<equiv> IsLowerBound m X X"



subsubsection ExistentialPredicates
definition HasMaximum::"'X::order set  \<Rightarrow>  bool" where  "HasMaximum A \<equiv> \<exists>m \<in> A. \<forall>a \<in> A. a\<le>m"

definition HasMinimum::" 'X::order set  \<Rightarrow>  bool" where "HasMinimum A \<equiv> \<exists>m \<in> A. \<forall>a \<in> A. m\<le>a"

subsection Operators
definition Max::"'X::order set\<Rightarrow> 'X::order" where "Max A = (THE m. IsMaximum m A)"

definition Min::"'X::order set\<Rightarrow> 'X::order" where "Min A = (THE m. IsMinimum m A)"


definition IsBoundedPoset::"'X::order set \<Rightarrow> bool" where "IsBoundedPoset X \<equiv> (X \<noteq> {}) \<and> (HasMaximum X) \<and> (HasMinimum X)"

subsection BasicLemmas

lemma max_unique:
  "HasMaximum A \<longrightarrow> (\<exists>!m. IsMaximum m A)"
  by (meson HasMaximum_def IsMaximum_def IsUpperBound_def order_class.order_eq_iff)

lemma min_unique:
  "HasMinimum A \<longrightarrow> (\<exists>!m. IsMinimum m A)"
  by (meson HasMinimum_def IsLowerBound_def IsMinimum_def order_antisym_conv)


section SupremaInfima
subsection Predicates
subsubsection DefinitionalPredicates
definition IsSup::"'X::order \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set \<Rightarrow> bool" where "IsSup s A X \<equiv> (s \<in> UpperBounds A X) \<and> (IsMinimum s ( UpperBounds A X))"

definition IsInf::"'X::order \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set \<Rightarrow> bool" where "IsInf i A X \<equiv> (i \<in> LowerBounds A X) \<and> (IsMaximum i ( LowerBounds A X))"


subsubsection ExistentialPredicates

definition HasSup::" 'X::order set  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where "HasSup A X \<equiv> \<exists>s. IsSup s A X"

definition HasInf::" 'X::order set  \<Rightarrow> 'X::order set  \<Rightarrow>  bool" where "HasInf A X \<equiv> \<exists>i. IsInf i A X"


subsection Operators
definition Sup1::"'X::order set\<Rightarrow> 'X::order set \<Rightarrow> 'X::order" where "Sup1 A X = (THE s. IsSup s A X)"

definition Inf1::"'X::order set\<Rightarrow> 'X::order set \<Rightarrow> 'X::order" where "Inf1 A X = (THE i. IsInf i A X)"

subsection BasicLemmas

lemma issup_then_lub:
  "(IsSup s A X) \<longrightarrow> ((s \<in> UpperBounds A X) \<and> (IsMinimum s( UpperBounds A X)))"
  by (simp add: IsSup_def)

lemma issup_well_defined:
  "IsSup s A X \<longrightarrow> s \<in> X" using issup_then_lub upper_bounds_well_defined by fastforce

lemma issup_then_lbub:
  "IsSup s A X \<longrightarrow> (\<forall>u \<in> UpperBounds A X. s \<le> u) \<and> (s \<in> LowerBounds (UpperBounds A X) X) "
  by (meson IsLowerBound_def IsMinimum_def in_mono issup_then_lub lower_bound_then_in_lowerbounds upper_bounds_well_defined)

lemma issup_lt_then_ub:
  "IsSup s A X \<longrightarrow> (\<forall>x \<in> X. (s \<le> x) \<longrightarrow> (x \<in> UpperBounds A X))" 
  by (meson IsUpset_def issup_then_lub upper_bounds_lem5)

lemma issup_sup1:
  assumes "HasSup A X"
  shows "IsSup (Sup1 A X) A X"
proof-
  let ?s="Sup1 A X"
  have B0:"?s=(THE s. IsSup s A X)" using Sup1_def by auto
  have B2:"IsSup ?s A X"

lemma sup_lem6:
  assumes A0:"A \<in> Pow X \<and> A \<noteq> {} \<and> HasSup A X"
  shows "Sup1 A X \<in> UpperBounds A X"
proof-
  have B0:"IsSup (Sup1 A X) A X"
    by (metis HasSup_def Sup1_def assms order_class.order_eq_iff issup_then_lub issup_then_lbub the_equality)
  have B1:"Sup1 A X \<in> UpperBounds A X" by (simp add: B0 issup_then_lub)
  with B1 show ?thesis by simp
qed
lemma sup_lem7:"IsMinimum s (UpperBounds A X) \<longrightarrow>  IsSup s A X" by (simp add: IsLowerBound_def IsMinimum_def IsSup_def)
lemma sup_lem8:"IsMinimum s (UpperBounds A X) \<longleftrightarrow>  IsSup s A X" using issup_then_lub sup_lem7 by blast 
lemma sup_unique:  "HasSup A X \<longrightarrow> (\<exists>!s. IsSup s A X)" by (meson HasSup_def IsLowerBound_def IsMinimum_def order_antisym_conv issup_then_lub)
lemma sup_lem9:"HasSup A X \<longrightarrow> (IsSup (Sup1 A X) A X)" by (metis PosetsDraft.sup_unique Sup1_def the_equality)
lemma issup_then_lub1:assumes A0: "HasSup A X" shows "(Sup1 A X) \<in> (UpperBounds A X)"
proof-
  let ?s="Sup1 A X"
  have B0:"IsSup ?s A X" by (simp add: assms sup_lem9)
  have B1:"?s \<in> UpperBounds A X" by (simp add: B0 issup_then_lub)
  with B1 show ?thesis by auto
qed



lemma lem_lub1:
  assumes A0:"HasSup A X" and
          A1: "A \<noteq> {}" and
          A2: "A \<in> Pow X" and
          A3: "s \<in> X"
  shows "IsSup s A X \<longleftrightarrow> (\<forall>x \<in> X. (\<forall>a \<in>A. a \<le> x) \<longleftrightarrow> (s \<le> x))"
proof-
  let ?L="IsSup s A X"
  let ?U="UpperBounds A X"
  let ?R="\<forall>x \<in> X. (\<forall>a \<in>A. a \<le> x) \<longleftrightarrow> (s \<le> x)"
  let ?RL="\<forall>x \<in> X. (\<forall>a \<in>A. a \<le> x) \<longrightarrow> (s \<le> x)"
  let ?RR="\<forall>x \<in> X. (s \<le> x) \<longrightarrow> (\<forall>a \<in>A. a \<le> x)"
  have B0:"?L \<longrightarrow> (s \<in> ?U)" by (simp add: IsSup_def)
  have B1:"?L \<longrightarrow> (IsMinimum s ?U)" by (simp add: IsSup_def)
  have B2:"?R \<longleftrightarrow> (?RL \<and> ?RR)" by auto
  have LtR:"?L \<longrightarrow> ?R"
  proof-
    have B0:"?L \<longrightarrow> (\<forall>u \<in> ?U. s \<le> u)" by (simp add: issup_then_lbub)
    have B1:"?L \<longrightarrow> (\<forall>x \<in> X. (\<forall>a \<in>A. a \<le> x) \<longrightarrow> x \<in> ?U)"  by (simp add: upper_bound_then_in_upperbounds)
    have B2:"?L \<longrightarrow> ?RL"  by (simp add: B0 B1) 
    have B3:"?L \<longrightarrow> (\<forall>x \<in> X. (s \<le> x) \<longrightarrow> x \<in> ?U)" by (simp add: issup_lt_then_ub)
    have B4:"?L \<longrightarrow> ?RR" using B3 upper_bound_is_upper_bound2 by blast
    show "?L \<longrightarrow> ?R" using B2 B4 by blast
  qed
  have RtL:"?R \<longrightarrow> ?L"
  proof-
    have C0:"\<forall>x \<in> X. (\<forall>a \<in>A. a \<le> x) \<longrightarrow> x \<in> ?U" by (simp add: upper_bound_then_in_upperbounds)
    have C1:"?RL \<longrightarrow> (\<forall>x \<in>X. x \<in> ?U \<longrightarrow> s\<le> x)" by (simp add: upper_bound_is_upper_bound2)
    have C2:"?RR \<longrightarrow> s \<in> ?U" by (simp add: A3 C0)
    have C3:"?R \<longrightarrow> IsLowerBound s ?U ?U" by (smt (verit) C1 C2 IsLowerBound_def subset_eq upper_bounds_well_defined)
    have C4:"?R \<longrightarrow> IsMinimum s ?U" by (simp add: C3 IsMinimum_def)
    show "?R \<longrightarrow> ?L" by (simp add: C2 C4 IsSup_def)
  qed
  show "?L \<longleftrightarrow> ?R" using RtL LtR by auto
qed

lemma inf_lem0:"IsInf i A X \<longrightarrow> (i \<in> LowerBounds A X)" by (simp add: IsInf_def)
lemma inf_lem1:"IsInf i A X \<longrightarrow> (IsMaximum i (LowerBounds A X))" by (simp add: IsInf_def)
lemma inf_lem2:"IsInf i A X \<longrightarrow> (\<forall>l \<in> LowerBounds A X. i \<ge> l)" by (meson IsUpperBound_def IsMaximum_def inf_lem1)
lemma inf_lem3:"IsInf i A X \<longrightarrow> (\<forall>x \<in> X. (i \<ge> x) \<longrightarrow> (x \<in> LowerBounds A X))" by (meson IsDownset_def inf_lem0 lower_bounds_lem5)
lemma inf_lem4:"IsInf i A X \<longrightarrow> i \<in> X" using inf_lem0 lower_bounds_well_defined by fastforce
lemma inf_lem5:"(i=Inf1 A X) \<longrightarrow> (i=(THE i. IsInf i A X))" by (simp add: Inf1_def)
lemma inf_lem6:  assumes A0:"A \<in> Pow X \<and> A \<noteq> {} \<and> HasInf A X" shows "Inf1 A X \<in> LowerBounds A X"
proof-
  have B0:"IsInf (Inf1 A X) A X"
    by (metis HasInf_def Inf1_def assms order_class.order_eq_iff inf_lem0 inf_lem2 the_equality)
  have B1:"Inf1 A X \<in> LowerBounds A X" by (simp add: B0 inf_lem0)
  with B1 show ?thesis by simp
qed
lemma inf_lem7:"IsMaximum i (LowerBounds A X) \<longrightarrow>  IsInf i A X" by (simp add: IsInf_def IsMaximum_def IsUpperBound_def)
lemma inf_lem8:"IsMaximum i (LowerBounds A X) \<longleftrightarrow>  IsInf i A X" using inf_lem1 inf_lem7 by blast 
lemma inf_unique: "HasInf A X \<longrightarrow> (\<exists>!i. IsInf i A X)"  by (meson HasInf_def IsUpperBound_def IsMaximum_def order_antisym_conv inf_lem1)
lemma inf_lem9:"HasInf A X \<longrightarrow> (IsInf (Inf1 A X) A X)" by (metis PosetsDraft.inf_unique Inf1_def the_equality)
lemma inf_lem01:assumes A0: "HasInf A X" shows "(Inf1 A X) \<in> (LowerBounds A X)"
proof-
  let ?i="Inf1 A X"
  have B0:"IsInf ?i A X" by (simp add: assms inf_lem9)
  have B1:"?i \<in> LowerBounds A X" by (simp add: B0 inf_lem0)
  with B1 show ?thesis by auto
qed



lemma lem_glb1:
  assumes A0:"HasInf A X" and
          A1: "A \<noteq> {}" and
          A2: "A \<in> Pow X" and
          A3: "i \<in> X"
  shows "IsInf i A X \<longleftrightarrow> (\<forall>x \<in> X. (\<forall>a \<in>A. a \<ge> x) \<longleftrightarrow> (i \<ge> x))"
proof-
  let ?L="IsInf i A X"
  let ?Lw="LowerBounds A X"
  let ?R="\<forall>x \<in> X. (\<forall>a \<in>A. a \<ge> x) \<longleftrightarrow> (i \<ge> x)"
  let ?RL="\<forall>x \<in> X. (\<forall>a \<in>A. a \<ge> x) \<longrightarrow> (i \<ge> x)"
  let ?RR="\<forall>x \<in> X. (i \<ge> x) \<longrightarrow> (\<forall>a \<in>A. a \<ge> x)"
  
  have B0:"?L \<longrightarrow> (i \<in> ?Lw)" by (simp add: IsInf_def)
  have B1:"?L \<longrightarrow> (IsMaximum i ?Lw)" by (simp add: IsInf_def)
  have B2:"?R \<longleftrightarrow> (?RL \<and> ?RR)" by auto
  
  have LtR:"?L \<longrightarrow> ?R"
  proof-
    have B0:"?L \<longrightarrow> (\<forall>l \<in> ?Lw. i \<ge> l)" by (simp add: inf_lem2)
    have B1:"?L \<longrightarrow> (\<forall>x \<in> X. (\<forall>a \<in>A. a \<ge> x) \<longrightarrow> x \<in> ?Lw)" by (simp add: lower_bound_then_in_lowerbounds)
    have B2:"?L \<longrightarrow> ?RL" by (simp add: B0 B1) 
    have B3:"?L \<longrightarrow> (\<forall>x \<in> X. (i \<ge> x) \<longrightarrow> x \<in> ?Lw)" by (simp add: inf_lem3)
    have B4:"?L \<longrightarrow> ?RR" using B3 lower_bound_is_lower_bound2 by blast
    show "?L \<longrightarrow> ?R" using B2 B4 by blast
  qed
  
  have RtL:"?R \<longrightarrow> ?L"
  proof-
    have C0:"\<forall>x \<in> X. (\<forall>a \<in>A. a \<ge> x) \<longrightarrow> x \<in> ?Lw" by (simp add: lower_bound_then_in_lowerbounds)
    have C1:"?RL \<longrightarrow> (\<forall>x \<in>X. x \<in> ?Lw \<longrightarrow> i \<ge> x)" by (simp add: lower_bound_is_lower_bound2)
    have C2:"?RR \<longrightarrow> i \<in> ?Lw" by (simp add: A3 C0)
    have C3:"?R \<longrightarrow> IsUpperBound i ?Lw ?Lw" by (smt (verit) C1 C2 IsUpperBound_def subset_eq lower_bounds_well_defined)
    have C4:"?R \<longrightarrow> IsMaximum i ?Lw" by (simp add: C3 IsMaximum_def)
    show "?R \<longrightarrow> ?L" by (simp add: C2 C4 IsInf_def)
  qed
  
  show "?L \<longleftrightarrow> ?R" using RtL LtR by auto
qed



lemma inf_to_sup0:
  assumes A0: "X \<noteq> {}" and A1:"A \<in> Pow X" and A2:"A \<noteq> {}" and A3:"HasInf (UpperBounds A X) X"
  shows "HasSup A X \<and> Sup1 A X = Inf1 (UpperBounds A X) X "
proof-
  let ?U="UpperBounds A X"
  let ?i="Inf1 ?U X"
  have C0:"?i=(THE i. IsInf i ?U X)" by (simp add: Inf1_def)
  have B0:"IsMaximum ?i (LowerBounds ?U X)" by (metis A3 C0 IsInf_def PosetsDraft.inf_unique theI)
  have B1:"\<forall>a \<in> A. (\<forall>u \<in> ?U. a\<le> u)" by (simp add: upper_bound_is_upper_bound2)
  have B2:"\<forall>a \<in> A. (a \<in> LowerBounds ?U X)" by (meson A1 B1 PowD in_mono lower_bound_then_in_lowerbounds)
  have B3:"\<forall>a \<in> A. (a\<le>?i)" by (metis B0 B2 IsMaximum_def IsUpperBound_def)
  have B4:"\<forall>z \<in> X. (\<forall>a \<in> A. a\<le> z)\<longrightarrow> (?i\<le>z)" by (meson A3 inf_lem01 lower_bound_is_lower_bound2 upper_bound_then_in_upperbounds)
  have B5:"?i \<in> UpperBounds A X" by (smt (verit) B0 B3 IsMaximum_def IsUpperBound_def insert_absorb insert_subset lower_bounds_well_defined upper_bound_then_in_upperbounds)
  have B6:"\<forall>u \<in> ?U. ?i\<le> u" by (metis B1 B4 in_mono upper_bounds_well_defined)
  have B8:"IsMinimum ?i ?U" by (simp add: B5 B6 IsLowerBound_def IsMinimum_def)
  have B9:"IsSup ?i A X" by (simp add: B5 B8 IsSup_def)
  have B10:"HasSup A X"  using B9 HasSup_def by auto
  have B11:"Sup1 A X = Inf1 ?U X"  by (metis B9 HasSup_def PosetsDraft.sup_unique Sup1_def the_equality)
  with B10 B11 show ?thesis  by simp
qed

lemma sup_to_inf0:
  assumes A0: "X \<noteq> {}" and A1: "A \<in> Pow X" and A2: "A \<noteq> {}" and A3: "HasSup (LowerBounds A X) X"
  shows "HasInf A X \<and> Inf1 A X = Sup1 (LowerBounds A X) X "
proof-
  let ?L = "LowerBounds A X"
  let ?s="Sup1 ?L X"
  have C0:"?s=(THE s. IsSup s ?L X)" by (simp add: Sup1_def)
  have B0: "IsMinimum ?s (UpperBounds ?L X)" by (metis A3 C0 IsSup_def PosetsDraft.sup_unique theI)
  have B1: "\<forall>a \<in> A. (\<forall>l \<in> ?L. l \<le> a)" by (simp add: lower_bound_is_lower_bound2)
  have B2: "\<forall>a \<in> A. (a \<in> UpperBounds ?L X)" by (meson A1 B1 PowD in_mono upper_bound_then_in_upperbounds)
  have B3: "\<forall>a \<in> A. (?s \<le> a)" by (metis B0 B2 IsMinimum_def IsLowerBound_def)
  have B4: "\<forall>z \<in> X. (\<forall>a \<in> A. z \<le> a) \<longrightarrow> (z \<le> ?s)" by (metis B0 IsMinimum_def IsLowerBound_def upper_bound_is_upper_bound2 lower_bound_then_in_lowerbounds)
  have B5: "?s \<in> LowerBounds A X" by (smt (verit) B0 B3 IsMinimum_def IsLowerBound_def insert_absorb insert_subset upper_bounds_well_defined lower_bound_then_in_lowerbounds)
  have B6: "\<forall>l \<in> ?L. l \<le> ?s" by (metis B1 B4 in_mono lower_bounds_well_defined)
  have B8: "IsMaximum ?s ?L" by (simp add: B5 B6 IsUpperBound_def IsMaximum_def)
  have B9: "IsInf ?s A X" by (simp add: B5 B8 IsInf_def)
  have B10: "HasInf A X" using B9 HasInf_def by auto
  have B11: "Inf1 A X = Sup1 ?L X" by (metis B9 HasInf_def PosetsDraft.inf_unique Inf1_def the_equality)
  with B10 B11 show ?thesis by simp
qed



lemma sup_leq_inf_iff:
  assumes A0:"(A \<in> Pow X) \<and> (B \<in> Pow X) \<and> (A \<noteq>{}) \<and>( B \<noteq> {})" and 
          A1: "HasSup A X \<and> HasInf B X"
  shows "(Sup1 A X \<le> Inf1 B X) \<longleftrightarrow> (\<forall>a \<in> A. \<forall> b \<in> B. a\<le> b)" 
proof-
  let ?s="Sup1 A X" and ?i="Inf1 B X"
  let ?L="?s \<le> ?i" and ?R="(\<forall>a \<in> A. \<forall> b \<in> B. a\<le> b)"
  have LtR:"?L\<longrightarrow> ?R"
  proof-
    have B0:"(\<forall>a \<in> A. ( a \<le>?s))"
      by (meson A0 A1 sup_lem6 upper_bound_is_upper_bound2)
    have B1:"\<forall>b \<in>B. (b\<ge> ?i)" using A1 inf_lem01 lower_bound_is_lower_bound2 by blast
    have B3:"?L\<longrightarrow> (\<forall>a \<in> A. \<forall> b \<in> B. a \<le> b)" by (meson B0 B1 dual_order.trans)
    with B3 show ?thesis by auto
  qed
  have RtL:"?R \<longrightarrow> ?L"
  proof-
    have C0:"?R \<longrightarrow> (\<forall>a \<in>A. a \<in> LowerBounds B X)" by (metis A0 PowD in_mono lower_bound_then_in_lowerbounds)
    have C1:"(\<forall>a \<in>A. a \<in> LowerBounds B X) \<longrightarrow> (\<forall>a \<in> A. a \<le> ?i)"  using A1 inf_lem2 inf_lem9 by blast
    have C2:"(\<forall>a \<in> A. a \<le> ?i)\<longrightarrow> (?i \<in> UpperBounds A X)" using A1 inf_lem4 inf_lem9 upper_bound_then_in_upperbounds by blast
    have C3:"(?i \<in> UpperBounds A X) \<longrightarrow> (?s \<le> ?i)" using A1 issup_then_lbub sup_lem9 by blast
    have C4:"?R\<longrightarrow>?L" by (simp add: C0 C1 C2 C3) 
    with C4 show ?thesis by simp
  qed
  from LtR RtL have RtLtR:"?L \<longleftrightarrow> ?R" by blast
  with RtLtR show ?thesis by simp
qed


lemma isotone_lem1:"A \<subseteq> B \<longrightarrow> UpperBounds A X \<supseteq> UpperBounds B X" by (meson subsetD subsetI upper_bounds_well_defined upper_bound_is_upper_bound2 upper_bound_then_in_upperbounds)
lemma isotone_lem2:"A \<subseteq> B \<longrightarrow> LowerBounds A X \<supseteq> LowerBounds B X" by (meson subsetD subsetI lower_bounds_well_defined lower_bound_is_lower_bound2 lower_bound_then_in_lowerbounds)
lemma isotone_lem3:"A \<subseteq> B \<longrightarrow> HasInf A X \<longrightarrow> HasInf B X \<longrightarrow> (Inf1 B X \<le> Inf1 A X)" by (meson in_mono inf_lem01 inf_lem2 inf_lem9 isotone_lem2) 
lemma isotone_lem4:"A \<subseteq> B \<longrightarrow> HasSup A X \<longrightarrow> HasSup B X \<longrightarrow> (Sup1 A X \<le> Sup1  B X)" by (meson in_mono isotone_lem1 issup_then_lub1 issup_then_lbub sup_lem9)



section Functions

definition ftriple::"('X \<Rightarrow> 'Y) \<Rightarrow> 'X set \<Rightarrow> 'Y set \<Rightarrow> bool " where "ftriple f X Y \<equiv> (\<forall>x \<in>X. f x \<in> Y)"

definition antitone::"('X::order \<Rightarrow> 'Y::order) \<Rightarrow> 'X::order set \<Rightarrow> 'Y::order set \<Rightarrow> bool " where "antitone f X Y \<equiv> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. (f x2 \<le> f x1))"

definition isotone::"('X::order \<Rightarrow> 'Y::order) \<Rightarrow> 'X::order set \<Rightarrow> 'Y::order set \<Rightarrow> bool " where "isotone f X Y \<equiv> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. (f x1 \<le> f x2))"


lemma lemf1: "ftriple f X Y \<longrightarrow> (\<forall>A \<in> Pow X. f`A \<in> Pow Y)" by (metis PowI UnionI Union_Pow_eq ftriple_def image_subsetI)

lemma lemf2: "ftriple f X Y \<longrightarrow> (\<forall>A. A \<subseteq>X \<longrightarrow>  f`A \<subseteq> Y)" by (meson PowD PowI lemf1)

lemma lemf3: "(\<forall>A. A \<subseteq>X \<longrightarrow>  f`A \<subseteq> Y) \<longrightarrow> ftriple f X Y " by (meson ftriple_def image_subset_iff order_refl)

lemma lemf4: " (\<forall>A \<in> Pow X. f`A \<in> Pow Y) \<longrightarrow>  ftriple f X Y" by (meson PowD PowI lemf3)


section Lemmas


lemma lem0:"IsMaximum X (Pow X)"  by (metis IsMaximum_def IsUpperBound_def Pow_iff Pow_top)

lemma lem01:"IsDownset D X \<longrightarrow> (\<forall>x \<in> X. \<forall>d \<in>D. x\<le> d\<longrightarrow> x \<in> D)" by (simp add: IsDownset_def)

lemma lem01_dual: "IsUpset U X \<longrightarrow> (\<forall>x \<in> X. \<forall>d \<in> U. d \<le> x\<longrightarrow> x \<in>U)" by (simp add: IsUpset_def)

lemma lem02:"(DownClosure A X) \<subseteq> X"
proof-
  have B0:"DownClosure A X = {x \<in> X. \<exists>a \<in> A. x \<le> a}" using DownClosure_def by auto
  have B1:"\<forall>x \<in> DownClosure A X.  x \<in> X" by (simp add: B0)
  have B2:"(DownClosure A X) \<subseteq> X" by (simp add: B1 subsetI)
  with B2 show ?thesis by simp
qed

lemma lem02_dual:"(UpClosure A X) \<subseteq> X"
proof-
  have B0:"UpClosure A X = {x \<in> X. \<exists>a \<in> A. x \<ge>  a}" using UpClosure_def  by auto
  have B1:"\<forall>x \<in> UpClosure A X.  x \<in> X" by (simp add: B0)
  have B2:"(UpClosure A X) \<subseteq> X" by (simp add: B1 subsetI)
  with B2 show ?thesis by simp
qed

lemma lem1:
  assumes A0: "X \<noteq> {}" and
          A1: "E \<in> DownSets X" and
          A2: "D \<in> DownSets E" 
        shows "D \<in> DownSets X"
proof-
  have B0:"IsDownset D E" using A2 DownSets_def by auto
  have B1:"IsDownset E X" using A1 DownSets_def by auto
  have B21: "(D \<in> Pow E)" using B0 IsDownset_def by auto 
  have B22:"(\<forall>y \<in> E. \<forall>d \<in> D. y\<le>d \<longrightarrow> y \<in> D)" by (meson B0 IsDownset_def)
  have B31:"(E \<in> Pow X)" using B1 IsDownset_def by auto 
  have B32:"(\<forall>x \<in> X. \<forall>y \<in> E. x\<le>y \<longrightarrow> x \<in> E)" by (meson B1 IsDownset_def)
  have B4:"D \<in> Pow X" using B21 B31 by blast
  have B5:"\<forall>x \<in> X. \<forall>d \<in> D. x \<le>d \<longrightarrow> x \<in> D" using B21 B22 B32 by blast
  have B6:"IsDownset D X" by (meson B4 B5 IsDownset_def)
  from B4 B6 have B7:"D \<in> DownSets X" by (simp add: DownSets_def)
  with B7 show ?thesis by simp
qed


lemma lem1_dual:
  assumes A0: "X \<noteq> {}" and
          A1: "E \<in> UpSets X" and
          A2: "U \<in> UpSets E" 
        shows "U \<in> UpSets X"
proof-
  have B0:"IsUpset U E" using A2 UpSets_def by auto
  have B1:"IsUpset E X" using A1 UpSets_def by auto
  have B21: "(U \<in> Pow E)" using B0 IsUpset_def by auto 
  have B22:"(\<forall>y \<in> E. \<forall>u \<in> U. y \<ge> u \<longrightarrow> y \<in> U)" by (meson B0 IsUpset_def)
  have B31:"(E \<in> Pow X)" using B1 IsUpset_def by auto 
  have B32:"(\<forall>x \<in> X. \<forall>y \<in> E. x \<ge> y \<longrightarrow> x \<in> E)" by (meson B1 IsUpset_def)
  have B4:"U \<in> Pow X" using B21 B31 by blast
  have B5:"\<forall>x \<in> X. \<forall>u \<in> U. x \<ge> u \<longrightarrow> x \<in> U" using B21 B22 B32 by blast
  have B6:"IsUpset U X" by (meson B4 B5 IsUpset_def)
  from B4 B6 have B7:"U \<in> UpSets X" by (simp add: UpSets_def)
  with B7 show ?thesis by simp
qed


lemma lem2:
  assumes A0: "X \<noteq> {}" and
          A1: "D \<in> Pow X"
  shows "IsDownset D X \<longleftrightarrow> IsUpset (X-D) X"
proof-
  have B0:"IsDownset D X \<longrightarrow> IsUpset (X-D) X"
  proof-
    have C0: "IsDownset D X \<longrightarrow> (\<forall>x \<in> X. \<forall>d \<in>D. x\<le> d\<longrightarrow> x \<in> D)" by (simp add: IsDownset_def) 
    have C1: " (\<forall>x \<in> X. \<forall>d \<in>D. x\<le> d\<longrightarrow> x \<in> D) \<longrightarrow>  (\<forall>x \<in> X. \<forall>d \<in>(X-D). d\<le> x \<longrightarrow> x \<notin> D)" by auto
    have C2: "(\<forall>x \<in> X. \<forall>d \<in>(X-D). d\<le> x \<longrightarrow> x \<notin> D) \<longrightarrow>  (\<forall>x \<in> X. \<forall>d \<in>(X-D). d\<le> x \<longrightarrow> x \<in>(X-D))" by blast
    have C3:" (\<forall>x \<in> X. \<forall>d \<in>(X-D). d\<le> x \<longrightarrow> x \<in>(X-D)) \<longrightarrow> IsUpset (X-D) X" by (simp add: IsUpset_def)
    have C4:"IsDownset D X \<longrightarrow> IsUpset (X-D) X" using C0 C3 by blast
    with C4 show ?thesis by simp
  qed
  have B1:"IsUpset (X-D) X \<longrightarrow> IsDownset D X"
  proof-
    have D0: "IsUpset (X-D) X \<longrightarrow> (\<forall>x \<in> X. \<forall>d \<in> (X-D). d \<le> x\<longrightarrow> x \<in>(X-D))" by (simp add: IsUpset_def) 
    have D1: "(\<forall>x \<in> X. \<forall>d \<in> (X-D). d \<le> x\<longrightarrow> x \<in>(X-D)) \<longrightarrow> (\<forall>x \<in> X. \<forall>d \<in> D. x \<le> d \<longrightarrow> x \<in> D) "  using A1 by blast
    have D2: " (\<forall>x \<in> X. \<forall>d \<in> D. x \<le> d \<longrightarrow> x \<in> D)  \<longrightarrow> IsDownset D X" using A1 IsDownset_def by auto
    have D3:"IsUpset (X-D) X \<longrightarrow> IsDownset D X" using D0 D1 D2 by blast
    with D3 show ?thesis by simp
  qed
  from B0 B1 have B2:"IsDownset D X \<longleftrightarrow> IsUpset (X-D) X" by blast
  with B2 show ?thesis by simp
qed



lemma lem3:
  "PrincipalDownClosure a X = {x \<in> X. x\<le> a }"
proof-
  have B0:"PrincipalDownClosure a X = {x \<in> X. \<exists>b \<in> {a}. x \<le> b }"
    by (simp add: DownClosure_def PrincipalDownClosure_def)
  have B1:"PrincipalDownClosure a X = {x \<in> X.  x \<le> a }" using B0 by auto
  with B1 show ?thesis by simp
qed

lemma lem3_dual:
  "PrincipalUpClosure a X = {x \<in> X. x\<ge> a }"
proof-
  have B0:"PrincipalUpClosure a X = {x \<in> X. \<exists>b \<in> {a}. x \<ge> b }"
    by (simp add: UpClosure_def PrincipalUpClosure_def)
  have B1:"PrincipalUpClosure a X = {x \<in> X. x \<ge> a }" using B0 by auto
  with B1 show ?thesis by simp
qed

lemma lem4:
  "PrincipalUpClosure a X \<subseteq> X"
proof-
  let ?U="PrincipalUpClosure a X"
  have B0:"?U = {x \<in> X. \<exists>b \<in> {a}. x \<ge> b }"
    by (simp add: UpClosure_def PrincipalUpClosure_def)
  have B1:"\<forall>x \<in>?U. x \<in> X"  by (simp add: B0)
  with B1 show ?thesis by auto
qed

lemma lem4_dual:"PrincipalDownClosure a X \<subseteq> X"
proof-
  let ?D="PrincipalDownClosure a X"
  have B0:"?D = {x \<in> X. \<exists>b \<in> {a}. x \<le>  b }"
    by (simp add: DownClosure_def PrincipalDownClosure_def)
  have B1:"\<forall>x \<in>?D. x \<in> X"  by (simp add: B0)
  with B1 show ?thesis by auto
qed

lemma lem5:
  assumes A0:"X \<noteq> {}" and A1: "x1 \<in> X" and A2:"x2 \<in> X"
  shows "PrincipalDownClosure x1 X \<subseteq> PrincipalDownClosure x2 X \<longleftrightarrow> x1 \<le> x2"
proof-
  let ?D1="PrincipalDownClosure x1 X"
  let ?D2="PrincipalDownClosure x2 X"
  have B01:"\<forall>x \<in> X. (x \<in> ?D1  \<longleftrightarrow> x \<le> x1)" using lem3 A0 A1 by auto
  have B02:"\<forall>x \<in> X. (x \<in> ?D2  \<longleftrightarrow> x \<le> x2)" using lem3 A0 A2 by auto
  have B03:"?D1 \<in> Pow X" by (simp add: lem4_dual)
  have B04:"?D2 \<in> Pow X" by (simp add: lem4_dual)
  have B1: "?D1 \<subseteq> ?D2  \<longrightarrow>  x1 \<le> x2"
  proof-
    have B11:"?D1 \<subseteq> ?D2 \<longrightarrow> (\<forall>x \<in> ?D1. x \<in> ?D2) " by (simp add: in_mono)
    have B12:"x1 \<in> ?D1"  by (simp add: A1 B01)
    have B13:"?D1 \<subseteq> ?D2 \<longrightarrow> x1 \<in> ?D2" by (simp add: B11 B12)
    have B14:"?D1 \<subseteq> ?D2 \<longrightarrow> x1 \<le> x2" using A1 B02 B13 by auto
    with B14 show ?thesis by simp
  qed
  have B2: "x1 \<le> x2  \<longrightarrow> ?D1 \<subseteq> ?D2 "
  proof-
    have B21:"x1\<le>x2 \<longrightarrow> (\<forall>x \<in> X. x\<le>x1 \<longrightarrow> x \<le> x2)"
      by auto
    have B22:"(\<forall>x \<in> X. x\<le>x1 \<longrightarrow> x \<le> x2) \<longrightarrow>(\<forall>x \<in> X. (x \<in> ?D1  \<longrightarrow>  x \<in> ?D2)) "
      by (simp add: B01 B02)
    have B23:"x1\<le>x2 \<longrightarrow>  ?D1 \<subseteq> ?D2" using B03 B21 B22 by blast 
    with B23 show ?thesis by simp
  qed
  have B3: "?D1 \<subseteq> ?D2 \<longleftrightarrow> x1 \<le> x2" using B1 B2 by blast
  with B3 show ?thesis by auto
qed





lemma lem6:
  assumes A0:"X \<noteq> {}"  and
          A1:"\<D> \<in> Pow (DownSets X)"
  shows "\<Union>\<D> \<in> DownSets X"
proof-
  let ?D="\<Union>\<D>"
  have B0:"\<forall>d \<in> X. (d \<in> ?D \<longleftrightarrow> (\<exists>D \<in>\<D>. d \<in> D))" by simp
  have B1:"\<forall>x \<in> X. (\<forall>d \<in>?D. (x\<le> d) \<longrightarrow> (\<exists>D \<in>\<D>. x \<in> D))"
    by (smt (verit, best) A1 DownSets_def IsDownset_def Pow_iff UnionE in_mono mem_Collect_eq)
  have B2:"\<forall>x \<in> X. (\<forall>d \<in>?D. (x\<le> d) \<longrightarrow> x \<in> ?D)" using B1 by blast
  have B3:"\<forall>d \<in> ?D. d \<in> X"  using A1 DownSets_def by blast
  have B4:"?D \<in> Pow X"  using B3 by blast
  from B2 IsDownset_def B3 B4 have B5:"IsDownset ?D X" by metis
  have B6:"?D \<in> DownSets X"
    using B4 B5 DownSets_def by auto
  with B6 show ?thesis by simp
qed

lemma lem6_dual:
  assumes A0:"X \<noteq> {}"  and
          A1:"\<U> \<in> Pow (UpSets X)" and
          A2:"\<Inter>\<U> \<in> Pow X"
  shows "\<Inter>\<U> \<in> UpSets X"
proof-
  let ?U="\<Inter>\<U>"
  have B0:"\<forall>u \<in> X. (u \<in> ?U \<longleftrightarrow> (\<forall>U \<in>\<U>. u \<in> U))" by simp
  have B1:"\<forall>x \<in> X. (\<forall>u \<in>?U. (u \<le> x) \<longrightarrow> (\<forall>U \<in>\<U>. x \<in> U))"
    by (smt (verit, best) A1 UpSets_def IsUpset_def Pow_iff InterE in_mono mem_Collect_eq)
  have B2:"\<forall>x \<in> X. (\<forall>u \<in>?U. (u \<le> x) \<longrightarrow> x \<in> ?U)" using B1 by blast
  have B3:"\<forall>u \<in> ?U. u \<in> X"  using A1 A2 UpSets_def by blast
  have B4:"\<Inter>\<U> \<in> Pow X"  using B3 by blast
  from B2 IsUpset_def B3 B4 have B5:"IsUpset ?U X" by metis
  have B6:"?U \<in> UpSets X"
    using B4 B5 UpSets_def by auto
  with B6 show ?thesis by simp
qed



end