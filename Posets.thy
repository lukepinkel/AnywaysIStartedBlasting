theory Posets
  imports Main
begin

section Definitions
subsection Bounds
subsubsection UpperBounds

definition IsUpperBound :: "'X::order  \<Rightarrow> 'X::order set  \<Rightarrow> bool" where
  "(IsUpperBound m A) \<equiv> (\<forall>a \<in> A. a \<le> m)"

definition UpperBoundsIn :: " 'X::order set \<Rightarrow> 'X::order set  \<Rightarrow> 'X::order set" where
  "(UpperBoundsIn A X) =  {x\<in>X. \<forall>a \<in> A. x\<ge>a}"

definition HasUpperBound1 ::" 'X::order set \<Rightarrow> 'X::order set  \<Rightarrow> bool" where
  "HasUpperBound1 A X \<equiv>  (UpperBoundsIn A X \<noteq> {})"

definition HasUpperBound2 ::" 'X::order set \<Rightarrow> 'X::order set  \<Rightarrow> bool" where
  "HasUpperBound2 A X \<equiv>  \<exists>m \<in> X. IsUpperBound m A"


subsubsection LowerBounds
definition IsLowerBound :: "'X::order  \<Rightarrow> 'X::order set  \<Rightarrow> bool" where
  "(IsLowerBound m A) \<equiv> (\<forall>x \<in> A. x \<ge>  m)"

definition LowerBoundsIn :: " 'X::order set \<Rightarrow> 'X::order set  \<Rightarrow> 'X::order set" where
  "(LowerBoundsIn A X) =  {x\<in>X. \<forall>a \<in> A. x \<le> a}"

definition HasLowerBound1 :: " 'X::order set \<Rightarrow> 'X::order set  \<Rightarrow> bool" where
  "HasLowerBound1 A X \<equiv>  (LowerBoundsIn A X \<noteq> {})"

definition HasLowerBound2 :: " 'X::order set \<Rightarrow> 'X::order set  \<Rightarrow> bool" where
  "HasLowerBound2 A X \<equiv>  \<exists>m \<in> X. IsLowerBound m A"


subsection GreatestAndLeast

subsubsection Greatest
definition IsGreatest :: "'X::order \<Rightarrow> 'X::order set \<Rightarrow> bool" where
  "IsGreatest m A \<equiv> ((m \<in> A) \<and> (IsUpperBound m A))"

definition HasGreatest :: "'X::order set \<Rightarrow> bool" where
  "HasGreatest A  \<equiv> \<exists>m. IsGreatest m A"

definition Greatest :: "('X::order set) \<Rightarrow> 'X::order" where
  "Greatest A = (THE m. (IsGreatest m A))"


subsubsection Least
definition IsLeast :: "'X::order \<Rightarrow> 'X::order set \<Rightarrow> bool" where
  "IsLeast m A \<equiv> ((m \<in> A) \<and> (IsLowerBound m A))"

definition HasLeast :: "'X::order set \<Rightarrow> bool" where
  "HasLeast A  \<equiv> \<exists>m. IsLeast m A"

definition Least :: "'X::order set \<Rightarrow> 'X::order" where
  "Least A = (THE m. (IsLeast m A))"


subsection MaximaAndMinima
subsubsection Maxima

definition IsMaximal1:: "'X::order \<Rightarrow> 'X::order set \<Rightarrow> bool" where
  "IsMaximal1 m A \<equiv> (m \<in> A) \<and>  (\<forall>a \<in> A. m \<le> a \<longrightarrow> m=a)"

definition IsMaximal2:: "'X::order \<Rightarrow> 'X::order set \<Rightarrow> bool" where
  "IsMaximal2 m A \<equiv>  (m \<in> A) \<and>  (\<forall>a \<in> A. \<not>(m<a))"

subsubsection Minima

definition IsMinimal1:: "'X::order \<Rightarrow> 'X::order set \<Rightarrow> bool" where
  "IsMinimal1 m A \<equiv> (m \<in> A) \<and> (\<forall>a \<in> A. m \<ge>  a \<longrightarrow> m=a)"

definition IsMinimal2:: "'X::order \<Rightarrow> 'X::order set \<Rightarrow> bool" where
  "IsMinimal2 m A \<equiv>  (m \<in> A) \<and>  (\<forall>a \<in> A. \<not>(m>a))"


subsection Suprema
subsubsection Sup1

definition Sup1 :: "'X::order set \<Rightarrow> 'X::order set  \<Rightarrow> 'X::order" where
  "Sup1 A X =  (Least  (UpperBoundsIn A X)) "

definition HasASup1:: "'X::order set \<Rightarrow> 'X::order set \<Rightarrow> bool" where
  "HasASup1 A X  = HasLeast (UpperBoundsIn A X)"


subsubsection Sup2
definition IsSup2 :: "'X::order \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set \<Rightarrow> bool" where
  "IsSup2 m A X \<equiv>  ( (m \<in> (UpperBoundsIn A X))  \<and>  (\<forall>z \<in> X. ((\<forall>a \<in> A. z \<ge> a)\<longrightarrow> (z \<ge> m) ))  ) "

definition HasASup2 :: "'X::order set \<Rightarrow>'X::order set \<Rightarrow>  bool" where
  "HasASup2 A X  \<equiv> \<exists>m. IsSup2 m A X"

definition Sup2 :: "'X::order set \<Rightarrow> 'X::order set  \<Rightarrow> 'X::order" where
  "Sup2 A X =  (THE m. (IsSup2 m A X))"



subsubsection Sup3
definition IsSup3:: "'X::order \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set \<Rightarrow> bool" where
  "IsSup3 m A X \<equiv> (  (m \<in> X) \<and>  (\<forall>z \<in> X. ((z \<ge> m) \<longleftrightarrow> (\<forall>a \<in> A. z \<ge> a))) ) "

definition HasASup3 :: "'X::order set \<Rightarrow>'X::order set \<Rightarrow>  bool" where
  "HasASup3 A X  \<equiv> \<exists>m. IsSup3 m A X"

definition Sup3 :: "'X::order set \<Rightarrow> 'X::order set \<Rightarrow> 'X::order" where
  "Sup3 A X = (THE m. (IsSup3 m A X))"



subsection Infima

subsubsection Inf1

definition Inf1 :: "'X::order set \<Rightarrow> 'X::order set  \<Rightarrow> 'X::order" where
  "Inf1 A X =  (Greatest  (LowerBoundsIn A X)) "

definition HasAnInf1:: "'X::order set \<Rightarrow> 'X::order set \<Rightarrow> bool" where
  "HasAnInf1 A X  = HasGreatest (LowerBoundsIn A X)"



subsubsection Inf2
definition IsInf2 :: "'X::order \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set \<Rightarrow> bool" where
  "IsInf2 m A X \<equiv>  ( (m \<in> (LowerBoundsIn A X))  \<and>  (\<forall>z \<in> X. ((\<forall>a \<in> A. z \<le>  a)\<longrightarrow> (z \<le>  m) ))  ) "

definition HasAnInf2 :: "'X::order set \<Rightarrow>'X::order set \<Rightarrow>  bool" where
  "HasAnInf2 A X  \<equiv> \<exists>m. IsInf2 m A X"

definition Inf2 :: "'X::order set \<Rightarrow> 'X::order set  \<Rightarrow> 'X::order" where
  "Inf2 A X =  (THE m. (IsInf2 m A X))"


subsubsection Inf3
definition IsInf3:: "'X::order \<Rightarrow> 'X::order set \<Rightarrow> 'X::order set \<Rightarrow> bool" where
  "IsInf3 m A X \<equiv> (  (m \<in> X) \<and>  (\<forall>z \<in> X. ((z \<le> m) \<longleftrightarrow> (\<forall>a \<in> A. z \<le> a))) ) "

definition HasAnInf3 :: "'X::order set \<Rightarrow>'X::order set \<Rightarrow>  bool" where
  "HasAnInf3 A X  \<equiv> \<exists>m. IsInf3 m A X"

definition Inf3 :: "'X::order set \<Rightarrow> 'X::order set \<Rightarrow> 'X::order" where
  "Inf3 A X = (THE m. (IsInf3 m A X))"


subsection FunctionsOnPosets

definition antitone :: "('X::order \<Rightarrow> 'Y::order) \<Rightarrow> bool" where
"antitone f \<longleftrightarrow> (\<forall>x y. x \<le> y \<longrightarrow> f y \<le> f x)"

definition comp_extensive :: "('X::order \<Rightarrow> 'Y::order) \<Rightarrow> ('Y::order \<Rightarrow> 'X::order) \<Rightarrow> bool" where
"comp_extensive f g \<longleftrightarrow> (\<forall>x. x \<le> g (f x)) \<and> (\<forall>y. y \<le> f (g y))"

definition extensive :: "('X::order \<Rightarrow> 'X::order) \<Rightarrow> bool" where
  "extensive f \<equiv>  (\<forall>x . (x \<le> f x))" 

definition extensive_in :: "('X::order \<Rightarrow> 'X::order) \<Rightarrow> 'X::order set  \<Rightarrow> bool" where
  "extensive_in f X \<equiv>  (\<forall>x \<in> X. (x \<le> f x))" 

definition isotone :: "('X::order \<Rightarrow> 'Y::order) \<Rightarrow> bool" where
  "isotone f \<equiv> (\<forall>x1 x2. ((x1 \<le> x2) \<longrightarrow> (f x1 \<le> f x2)))"

definition isotone_in :: "('X::order \<Rightarrow> 'X::order) \<Rightarrow> 'X::order set  \<Rightarrow> bool" where
  "isotone_in f X \<equiv> (\<forall>x1 \<in> X.\<forall>x2 \<in> X. ((x1 \<le> x2) \<longrightarrow> (f x1 \<le> f x2)))"

definition idempotent:: "('X \<Rightarrow> 'X) \<Rightarrow> bool" where
  "idempotent f \<equiv>  (\<forall>x. f (f x) = f x)"

definition idempotent_in :: "('X::order \<Rightarrow> 'X::order) \<Rightarrow> 'X::order set  \<Rightarrow> bool" where
  "idempotent_in f X \<equiv>  (\<forall>x \<in> X. f (f x) = f x)"


definition pseudo_closure:: "('X::order \<Rightarrow> 'X::order) \<Rightarrow> bool" where
  "pseudo_closure f \<equiv> (isotone f) \<and> (extensive f)"


definition pseudo_closure_in:: "('X::order \<Rightarrow> 'X::order) \<Rightarrow> 'X::order set \<Rightarrow> bool" where
  "pseudo_closure_in f X \<equiv> (isotone_in f X) \<and> (extensive_in f X)"


definition closure:: "('X::order \<Rightarrow> 'X::order) \<Rightarrow> bool" where
  "closure f \<equiv> (pseudo_closure f) \<and> (idempotent f)"


definition closure_on:: "('X::order \<Rightarrow> 'X::order) \<Rightarrow>  'X::order set  \<Rightarrow> bool" where
  "closure_on f X \<equiv> (closure  f) \<and> (f`X \<subseteq> X) "


definition closure_in:: "('X::order \<Rightarrow> 'X::order) \<Rightarrow>'X::order set \<Rightarrow> bool" where
  "closure_in f X \<equiv> (pseudo_closure_in f X) \<and> (idempotent_in f X)"



subsection FiltersAndIdeals


definition principal_filter :: "'X::order \<Rightarrow> ('X::order set)" where
  "principal_filter a = {x. x \<ge> a}"

definition principal_ideal :: "'X::order \<Rightarrow> ('X::order set)" where
  "principal_ideal a = {x. x \<le> a}"


definition principal_filter_in :: "'X::order\<Rightarrow> 'X::order set \<Rightarrow> ('X::order set)" where
  "principal_filter_in a X = {x \<in> X. x \<ge> a}"

definition principal_ideal_in :: "'X::order\<Rightarrow> 'X::order set  \<Rightarrow> ('X::order set)" where
  "principal_ideal_in a X = {x \<in> X. x \<le> a}"


definition is_down_closed :: "'X::order set \<Rightarrow>  'X::order set \<Rightarrow> bool" where
  "is_down_closed A X  \<equiv>  (\<forall>x \<in> X. (\<forall>a \<in> A.( x\<le> a \<longrightarrow> x \<in> A)))"

definition is_up_closed :: "'X::order set \<Rightarrow>  'X::order set \<Rightarrow> bool" where
  "is_up_closed A X  \<equiv>  (\<forall>x. \<forall> a.  ((a \<in> A) \<and> (x\<ge> a) \<longrightarrow> x \<in> A))"


definition is_closure_range:: "'X::order set \<Rightarrow> 'X::order set  \<Rightarrow> bool" where
  "is_closure_range A X  \<equiv> ((A \<in> Pow X) \<and> (\<forall>x \<in> X. HasLeast(principal_filter_in x A)))"
 

section Lemmas

subsection Bounds
lemma subset_nonempty:
  assumes "A \<noteq> {}" and "A \<in> Pow X" shows "X \<noteq> {}"
  using assms(1) assms(2) by auto

lemma upper_bounded_equiv:
  "HasUpperBound1 A X \<longleftrightarrow> HasUpperBound2 A X"
proof-
  have A0: "HasUpperBound1 A X \<longrightarrow>  HasUpperBound2 A X"
    by (metis (no_types, lifting) Collect_empty_eq HasUpperBound1_def HasUpperBound2_def IsUpperBound_def UpperBoundsIn_def)
  have A1: "HasUpperBound2 A X \<longrightarrow>  HasUpperBound1 A X"
    by (smt (verit, best) Collect_empty_eq HasUpperBound1_def HasUpperBound2_def IsUpperBound_def UpperBoundsIn_def)
  with A0 A1 show ?thesis by auto
qed

lemma upper_bounds_are_upper_bounds:
  fixes A::"'X::order set"
  fixes X::"'X::order set"
  shows "(x \<in> (UpperBoundsIn A X)) \<longleftrightarrow> ((IsUpperBound x A) \<and> (x \<in> X))"
proof - 
  have B0: "x \<in> (UpperBoundsIn A X) \<longrightarrow> ( \<forall>a \<in> A. a\<le> x)"
    by (simp add: UpperBoundsIn_def)
  have B1:  "x \<in> (UpperBoundsIn A X) \<longrightarrow> (x \<in> X )"
    using UpperBoundsIn_def by blast
  have B2: "x \<in> (UpperBoundsIn A X) \<longrightarrow> ((IsUpperBound x A) \<and> (x \<in> X)) "
    by (simp add: B0 B1 IsUpperBound_def)
  have B3: "(x \<in> X  \<and> (\<forall>a \<in>A. a\<le> x)) \<longrightarrow> x \<in> (UpperBoundsIn A X)"
    using UpperBoundsIn_def by blast
  have B4: "(x \<in> X  \<and> (IsUpperBound x A)) \<longrightarrow> x \<in> (UpperBoundsIn A X)"
    by (simp add: B3 IsUpperBound_def)
  with B2 B4 show ?thesis by blast
qed

lemma upper_bounds_are_upper_bounds2:
  fixes A::"'X::order set"
  fixes X::"'X::order set"
  shows "(x \<in> (UpperBoundsIn A X)) \<longleftrightarrow> ((\<forall>a \<in> A. a \<le> x) \<and> (x \<in> X))"
  by (simp add: IsUpperBound_def upper_bounds_are_upper_bounds)  


lemma ub_in_ub_set:
  assumes A0:"A \<noteq> {}" and
          A1: "A \<in> Pow X"
  shows "\<forall>m \<in> X. (\<forall>a \<in> A. a\<le>m) \<longrightarrow> m \<in> UpperBoundsIn A X"
proof -
  have "\<forall>a. \<exists>aa. a \<notin> X \<or> a \<in> UpperBoundsIn A X \<or> aa \<in> A \<and> \<not> aa \<le> a"
    using upper_bounds_are_upper_bounds2 by auto
  then show ?thesis
    by auto
qed


lemma lower_bounded_equiv:
  "HasLowerBound1 A X \<longleftrightarrow> HasLowerBound2 A X"
proof-
  have L0: "HasLowerBound1 A X \<longrightarrow>  HasLowerBound2 A X"
    by (metis (no_types, lifting) Collect_empty_eq HasLowerBound1_def HasLowerBound2_def IsLowerBound_def LowerBoundsIn_def)
  have L1: "HasLowerBound2 A X \<longrightarrow>  HasLowerBound1 A X"
    by (smt (verit, best) Collect_empty_eq HasLowerBound1_def HasLowerBound2_def IsLowerBound_def LowerBoundsIn_def)
  with L0 L1 show ?thesis by auto
qed

lemma lower_bounds_are_lower_bounds:
  fixes A::"'X::order set"
  fixes X::"'X::order set"
  shows "(x \<in> (LowerBoundsIn A X)) \<longleftrightarrow> ((IsLowerBound x A) \<and> (x \<in> X))"
proof - 
  have L0: "x \<in> (LowerBoundsIn A X) \<longrightarrow> ( \<forall>a \<in> A. a \<ge> x)"
    by (simp add: LowerBoundsIn_def)
  have L1:  "x \<in> (LowerBoundsIn A X) \<longrightarrow> (x \<in> X )"
    using LowerBoundsIn_def by blast
  have L2: "x \<in> (LowerBoundsIn A X) \<longrightarrow> ((IsLowerBound x A) \<and> (x \<in> X)) "
    by (simp add: L0 L1 IsLowerBound_def)
  have L3: "(x \<in> X  \<and> (\<forall>a \<in>A. a \<ge> x)) \<longrightarrow> x \<in> (LowerBoundsIn A X)"
    using LowerBoundsIn_def by blast
  have L4: "(x \<in> X  \<and> (IsLowerBound x A)) \<longrightarrow> x \<in> (LowerBoundsIn A X)"
    by (simp add: L3 IsLowerBound_def)
  with L2 L4 show ?thesis by blast
qed

lemma lower_bounds_are_lower_bounds2:
  fixes A::"'X::order set"
  fixes X::"'X::order set"
  shows "(x \<in> (LowerBoundsIn A X)) \<longleftrightarrow> ((\<forall>a \<in> A. a \<ge> x) \<and> (x \<in> X))"
  by (simp add: IsLowerBound_def lower_bounds_are_lower_bounds)  

lemma lb_in_lb_set:
  assumes A0: "A \<noteq> {}" and
          A1: "A \<in> Pow X"
  shows "\<forall>m \<in> X. (\<forall>a \<in> A. a \<ge> m) \<longrightarrow> m \<in> LowerBoundsIn A X"
proof -
  have "\<forall>a. \<exists>aa. a \<notin> X \<or> a \<in> LowerBoundsIn A X \<or> aa \<in> A \<and> \<not> aa \<ge> a"
    using lower_bounds_are_lower_bounds2 by auto
  then show ?thesis
    by auto
qed

lemma lower_bounds_unique: 
  assumes A0:"HasLowerBound1 X X"
  shows "\<exists>!b \<in> X. IsLowerBound b X"
  by (meson HasLowerBound2_def IsLowerBound_def antisym assms lower_bounded_equiv)



subsection GreatestAndLeast
lemma set_max_not_empty: assumes "HasGreatest A" shows "A\<noteq>{}"
  using HasGreatest_def IsGreatest_def assms by auto

lemma set_min_not_empty: assumes "HasLeast A" shows "A\<noteq>{}"
  using HasLeast_def IsLeast_def assms by auto

lemma maximum_is_unique: assumes  A2: "HasGreatest A"
  shows "\<exists>!M. M\<in>A \<and> (\<forall>x\<in>A. x \<le> M)"
  by (meson A2 HasGreatest_def IsGreatest_def IsUpperBound_def order_antisym)

lemma minimum_is_unique: assumes A2: "HasLeast A"
  shows "\<exists>!M. M\<in>A \<and> (\<forall>x\<in>A. x \<ge> M)"
  by (meson A2 HasLeast_def IsLeast_def IsLowerBound_def order_antisym)

lemma greatest_is_maximum:
  assumes A0: "HasGreatest A"
  shows "((Greatest A) \<in> A) \<and> (\<forall>x \<in> A. x \<le> (Greatest A))"
proof - 
  have B0:"A \<noteq> {}"
    using A0 set_max_not_empty by blast
  have B1:"(Greatest A) \<in> A"
    by (metis Posets.Greatest_def IsGreatest_def IsUpperBound_def maximum_is_unique assms theI')
  have B2:"(\<forall>x \<in> A. x \<le> (Greatest A))"
    by (metis Posets.Greatest_def IsGreatest_def IsUpperBound_def maximum_is_unique assms theI')
  with B1 B2  show ?thesis by auto
qed

lemma least_is_minimum:
  assumes A0: "HasLeast A"
  shows "((Least  A) \<in> A) \<and> (\<forall>x \<in> A. x \<ge> (Least A))"
proof - 
  have B0:"A \<noteq> {}"
    using A0 set_min_not_empty by blast
  have B1:"(Least A) \<in> A"
    by (metis Posets.Least_def IsLeast_def IsLowerBound_def minimum_is_unique assms theI')
  have B2:"(\<forall>x \<in> A. x \<ge> (Least A))"
    by (metis Posets.Least_def IsLeast_def IsLowerBound_def minimum_is_unique assms theI')
  with B1 B2  show ?thesis by auto
qed


lemma lower_bound_lt_least: 
  assumes A0:"HasLeast A" and
          A1:"\<forall>a\<in>A. L \<le> a"
  shows "L  \<le> Least A "
  using A0 A1 least_is_minimum by blast


lemma upper_bound_gt_greatest: 
  assumes A0:"HasGreatest A" and
          A1:"\<forall>a\<in>A. M \<ge> a"
  shows "M  \<ge>  Greatest A "
  by (simp add: A0 A1 greatest_is_maximum)

lemma maximum_is_greatest: 
  assumes A0: "M \<in> A" and 
          A1: "\<forall>a\<in>A. a\<le> M"
  shows "M=Greatest A"
proof -
  from A0 A1 have A2: "HasGreatest A"
    by (meson HasGreatest_def IsGreatest_def IsUpperBound_def) 
  have A3:"\<exists>!M. M\<in>A \<and> (\<forall>x\<in>A. x\<le> M)"
    by (simp add: A2 maximum_is_unique)
  have A4:"M\<in>A \<and> (\<forall>x\<in>A. x\<le> M)"
    by (simp add: A0 A1)
  have A5:"(Greatest A) \<in> A"
    using A2 greatest_is_maximum by blast
  have A6:" (\<forall>x\<in>A. x\<le> (Greatest A))"
    by (simp add: A2 greatest_is_maximum)
   have A7:"(Greatest A) = M"
    using A0 A1 A5 A6 order_class.order_eq_iff by blast
  with A7 show ?thesis by auto
qed

lemma minimum_is_least: 
  assumes A0: "m \<in> A" and 
          A1: "\<forall>a\<in>A. a \<ge> m"
  shows "m = Least A"
proof -
  from A0 A1 have A2: "HasLeast A"
    by (meson HasLeast_def IsLeast_def IsLowerBound_def) 
  have A3: "\<exists>!m. m \<in> A \<and> (\<forall>x \<in> A. x \<ge> m)"
    by (simp add: A2 minimum_is_unique)
  have A4: "m \<in> A \<and> (\<forall>x \<in> A. x \<ge> m)"
    by (simp add: A0 A1)
  have A5: "(Least A) \<in> A"
    using A2 least_is_minimum by blast
  have A6: "(\<forall>x \<in> A. x \<ge> (Least A))"
    by (simp add: A2 least_is_minimum)
  have A7: "(Least A) = m"
    using A0 A1 A5 A6 order_class.order_eq_iff by blast
  with A7 show ?thesis by auto
qed

lemma least_subset:
  assumes A0: "A \<noteq> {} \<and> B \<noteq> {}" and
          A1: "(HasLeast A ) \<and> (HasLeast B) " and
          A2: "(A \<in> Pow X) \<and> (B \<in> Pow X)"  and
          A3: "A \<subseteq> B"
  shows "(Least B) \<le> (Least A)"
  using A1 A3 least_is_minimum by auto

lemma greatest_subset:
  assumes A0: "A \<noteq> {} \<and> B \<noteq> {}"
      and A1: "(HasGreatest A ) \<and> (HasGreatest B)"
      and A2: "(A \<in> Pow X) \<and> (B \<in> Pow X)"
      and A3: "A \<subseteq> B"
  shows "(Greatest A) \<le> (Greatest B)"
  using A1 A3 greatest_is_maximum by auto

lemma lb_lt_least:
   assumes A0:"HasLeast A" and 
           A1: "A \<in> Pow X"
   shows "\<forall>L \<in> X.  ((\<forall>a\<in>A. L \<le> a) \<longrightarrow> (L  \<le> Least A)) "
  by (simp add: A0 least_is_minimum)

lemma ub_gt_greatest:
   assumes A0:"HasGreatest A" and 
           A1: "A \<in> Pow X"
   shows "\<forall>M \<in> X.  ((\<forall>a\<in>A. M \<ge> a) \<longrightarrow> (M  \<ge>  Greatest A)) "
  by (simp add: A0 greatest_is_maximum)


lemma glb_is_maxlb: 
  assumes A0: "HasGreatest (LowerBoundsIn A X)"
  shows  "((Greatest (LowerBoundsIn A X)) \<in> (LowerBoundsIn A X)) \<and>
           (\<forall>x \<in> (LowerBoundsIn A X). x \<le> (Greatest (LowerBoundsIn A X)))"
  using assms greatest_is_maximum by blast

lemma lub_is_minub: 
  assumes A0: "HasLeast (UpperBoundsIn A X)"
  shows  "((Least (UpperBoundsIn A X)) \<in> (UpperBoundsIn A X)) \<and>
           (\<forall>x \<in> (UpperBoundsIn A X). x \<ge> (Least (UpperBoundsIn A X)))"
  using assms least_is_minimum by blast


lemma element_ub_is_greatest:
  assumes A0: "M \<in> A" and
          A1: "A \<in> Pow X"
  shows  "(\<forall>a\<in>A. a\<le> M) \<longrightarrow> (M=Greatest A)"
  by (meson A0 HasGreatest_def IsGreatest_def IsUpperBound_def greatest_is_maximum order_antisym)


lemma element_lb_is_least:
  assumes A0: "M \<in> A" and
          A1: "A \<in> Pow X"
  shows  "(\<forall>a\<in>A. a\<ge> M) \<longrightarrow> (M=Least A)"
  by (meson A0 HasLeast_def IsLeast_def IsLowerBound_def least_is_minimum order_antisym)

lemma element_ub_is_greatest_alt:
  "\<forall>M \<in> A. (\<forall>a\<in>A. a\<le> M) \<longrightarrow> (M=Greatest A)"
  using element_ub_is_greatest by auto

lemma element_lb_is_least_alt:
  "\<forall>L \<in> A. (\<forall>a\<in>A. a\<ge>  L) \<longrightarrow> (L=Least A)"
  using element_lb_is_least by auto

lemma bounded_above_then_has_greatest:
  assumes A0:"X \<noteq> {}" and
          A1: "HasUpperBound1 X X"
  shows "HasGreatest X"
  by (meson A1 HasGreatest_def HasUpperBound2_def IsGreatest_def upper_bounded_equiv)

lemma bounded_below_then_has_least:
  assumes A0:"X \<noteq> {}" and
          A1: "HasLowerBound1 X X"
  shows "HasLeast X"
  by (meson A1 HasLeast_def IsLeast_def lower_bounds_unique)

subsection MaximaAndMinima

lemma max1_equiv_max2:
  "(IsMaximal1 m X) \<longleftrightarrow> (IsMaximal2 m X)"
proof-
  have B0: "IsMaximal1 m X \<longrightarrow> IsMaximal2 m X"
    by (simp add: IsMaximal1_def IsMaximal2_def nless_le) 
  have B1: "IsMaximal2 m X \<longrightarrow> IsMaximal1 m X"
    by (simp add: IsMaximal1_def IsMaximal2_def nless_le)
  with B0 B1 show ?thesis by auto
qed


lemma greatest_then_unique_maxima:
  assumes A0: "HasGreatest X"
  shows "\<exists>!m. IsMaximal1 m X"
  by (metis IsMaximal1_def antisym assms maximum_is_unique)


lemma min1_equiv_min2:
  "(IsMinimal1  m X) \<longleftrightarrow> (IsMinimal2 m X)"
proof-
  have B0: "IsMinimal1 m X \<longrightarrow> IsMinimal2 m X"
    by (metis IsMinimal1_def IsMinimal2_def nless_le)
 have B1: "IsMinimal2 m X \<longrightarrow> IsMinimal1 m X"
   by (simp add: IsMinimal1_def IsMinimal2_def dual_order.order_iff_strict)
 with B0 B1 show ?thesis by auto
qed

lemma least_then_unique_minima:
  assumes A0: "HasLeast X"
  shows "\<exists>!m. IsMinimal1  m X"
  by (metis IsMinimal1_def assms dual_order.antisym minimum_is_unique)



subsection SupInf1
subsubsection Sup1

lemma sup_lt_upperbound:
  assumes A0: "A\<noteq>{}" and
          A1: "HasLeast (UpperBoundsIn A X)" and 
          A2: "\<forall>a\<in>A. a\<le> u" and
          A3: "u \<in> X"
  shows "Sup1 A X \<le> u"
proof-
  let ?U ="UpperBoundsIn A X"
  from A2 have A4:"\<forall>a\<in>A. a \<le> u"
    by blast 
  have A5: "u\<in>?U"
    by (simp add: A3 A4 UpperBoundsIn_def)
  have A6:"Sup1 A X \<le> u"
    by (simp add: A1 A5 least_is_minimum Sup1_def)
  with A6 show ?thesis by auto
qed

lemma lub_then_sup1: 
  assumes A0:"A \<noteq> {}" and
          A1:"\<forall>x \<in>A. x \<le> z" and
          A2:"\<forall>y. (\<forall>x \<in> A. x \<le> y) \<longrightarrow> z \<le> y" and
          A3:"z \<in> X"
  shows "HasLeast (UpperBoundsIn A X) \<and> z = Sup1 A X" 
proof - 
  let ?U = "(UpperBoundsIn A X)"
  have B0: "z \<in> ?U"
    by (simp add: A1 A3 UpperBoundsIn_def)
  have B1: "\<forall>y \<in> ?U. z \<le> y"
    by (simp add: A2 IsUpperBound_def upper_bounds_are_upper_bounds)
  have B2:"HasLeast (UpperBoundsIn A X)"
    by (meson B0 B1 HasLeast_def IsLeast_def IsLowerBound_def)
  have B3:"z = Sup1 A X"
    by (simp add: B0 B1 Sup1_def minimum_is_least)
  with B2 B3 show ?thesis by simp
qed


lemma greatest_then_sup1:
  assumes A0:"A \<noteq> {}" and
          A1:"HasGreatest A" and 
          A2:"A \<in> Pow X"
  shows "(HasLeast (UpperBoundsIn A X)) \<and> (Greatest A = Sup1 A X) "
proof-
  let ?M = "Greatest A"
  have B0:"?M \<in> A"
    by (simp add: A1 greatest_is_maximum)
  have B1:"\<forall>x \<in> A. x \<le> ?M"
    by (simp add: A1 greatest_is_maximum)
  have B2:"\<forall>y. (\<forall>x \<in> A. x \<le> y) \<longrightarrow> ?M\<le>y"
    using B0 by blast
  with A0 B1 have B3: "HasLeast (UpperBoundsIn A X)"
    by (meson A2 B0 PowD lub_then_sup1 subsetD)
  have B4: "?M = Sup1 A X"
    by (meson A0 A2 B0 B1 Pow_iff lub_then_sup1 subsetD)
  with B3 B4 show ?thesis by auto
qed


lemma sup1_subset:
  assumes A0: "A \<noteq> {} \<and> B \<noteq> {}" and
          A1: "(HasLeast (UpperBoundsIn A X)) \<and> (HasLeast (UpperBoundsIn B X)) " and
          A2: "(A \<in> Pow X) \<and> (B \<in> Pow X)"  and
          A3: "A \<subseteq> B"
  shows "(Sup1 A X) \<le> (Sup1 B X)"
proof-
  have B0:"\<forall>x \<in> X. (\<forall>b \<in> B. x\<ge>b) \<longrightarrow> (\<forall>a \<in>A. x\<ge> a)"
    using A3 by blast
  from B0 have B1:" (UpperBoundsIn B X) \<subseteq> (UpperBoundsIn A X)"
    by (metis IsUpperBound_def subsetI upper_bounds_are_upper_bounds)
  have B2:"(Least (UpperBoundsIn A X)) \<le> (Least (UpperBoundsIn B X))"
    using A1 B1 least_is_minimum by blast
  have B3: "(Sup1 A X) \<le> (Sup1 B X)"
    by (simp add: B2 Sup1_def)
  with B3 show ?thesis by auto
qed

lemma has_sup1_yields_sup1:
  assumes A0: "A \<noteq> {} \<and> X \<noteq> {}" and
          A1: "A \<in> Pow X" and
          A2: "(HasASup1 A X)"
  shows "( ( IsUpperBound (Sup1 A X) A) \<and>  (\<forall>z \<in> X. ((\<forall>a \<in> A. z \<ge> a)\<longrightarrow> (z \<ge> (Sup1 A X)) ))  )"
proof-
  let ?U="UpperBoundsIn A X"
  let ?m="Least ?U"
  have B0: "\<forall>u \<in> ?U. ?m \<le> u"
    using A2 HasASup1_def least_is_minimum by auto
  have B1:"\<forall>z \<in> X. (\<forall>a \<in> A. z\<ge>a) \<longrightarrow> z \<in> UpperBoundsIn A X"
    by (simp add: IsUpperBound_def upper_bounds_are_upper_bounds)
  have B2:"\<forall>z \<in> X. ((\<forall>a \<in> A. z\<ge>a) \<longrightarrow> (?m \<le> z))"
    using B0 B1 by blast
  have B3:"(Sup1 A X) = ?m"
    by (simp add: Sup1_def)
  have B4:"IsUpperBound ?m A"
    using A2 HasASup1_def least_is_minimum upper_bounds_are_upper_bounds by blast
  have B5:"( ( IsUpperBound ?m A) \<and>  (\<forall>z \<in> X. ((\<forall>a \<in> A. z \<ge> a)\<longrightarrow> (z \<ge> ?m) ))  )"
    using B2 B4 by blast
  have B6: "( ( IsUpperBound (Sup1 A X) A) \<and>  (\<forall>z \<in> X. ((\<forall>a \<in> A. z \<ge> a)\<longrightarrow> (z \<ge> (Sup1 A X)) ))  )"
    using B3 B5 by presburger
  with B6 show ?thesis by simp
qed


lemma sup1_in_space:
  assumes A0: "HasASup1 A X"
  shows  "(Sup1 A X) \<in> X"
  by (metis HasASup1_def Sup1_def assms lub_is_minub upper_bounds_are_upper_bounds)

lemma sup1_is_ub:
 assumes "HasASup1 A X"
 shows "(IsUpperBound (Sup1 A X) A)"
  by (metis (no_types) HasASup1_def Sup1_def assms least_is_minimum upper_bounds_are_upper_bounds)


lemma sup1_apply_ub:
  assumes "HasASup1 A X"
  shows "(\<forall>z \<in> X. ((\<forall>a \<in> A. z \<ge> a)\<longrightarrow> (z \<ge>  (Sup1 A X)) ))"
  by (metis HasASup1_def Sup1_def assms least_is_minimum upper_bounds_are_upper_bounds2)


lemma sup1_is_ub_lb:
  assumes A0: "(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1: "A  \<in> (Pow X)" and
          A2: "HasASup1 A X"
  shows "(\<forall>x \<in> {y \<in> X. \<forall>a \<in> A. y \<ge> a}. x \<ge> (Sup1 A X))"
  by (simp add: A2 sup1_apply_ub)


lemma sup_in_sub:
  assumes A0: "A \<noteq> {}" and 
          A1: "A \<subseteq> B"  and
          A2: "B \<in> Pow X" and
          A3: "HasASup1 A X" and 
          A4: "HasASup1 A B" 
  shows " Sup1 A B \<ge> Sup1 A X"
proof-
  let ?SX="UpperBoundsIn A X"
  let ?SB="UpperBoundsIn A B"
  have B0: "?SB \<noteq> {} \<and> ?SX \<noteq> {}"
    using A3 A4 HasASup1_def set_min_not_empty by auto
  have B1: "(HasLeast ?SB ) \<and> (HasLeast  ?SX)"
    using A3 A4 HasASup1_def by auto
  have B2: "?SB  \<subseteq> ?SX"
    by (meson A2 PowD subsetD subsetI upper_bounds_are_upper_bounds2)
  have B3: "Least ?SB \<ge> Least ?SX"
    using B1 B2 least_is_minimum by auto
  have B4: "Least (UpperBoundsIn A B) \<ge> Least (UpperBoundsIn A X)"
    by (simp add: B3)
  have B5: " Sup1 A B \<ge> Sup1 A X"
    by (simp add: B4 Sup1_def)
  with B5 show ?thesis by simp
qed

lemma sup_sub_suff:
  assumes  A0: "A \<noteq> {}" and 
           A1: "A \<subseteq> B"  and
           A2: "B \<in> Pow X" and
           A3: "HasASup1 A X" and 
           A4: "HasASup1 A B" and
           A5: "Sup1 A X \<in> B"
  shows "Sup1 A B = Sup1 A X"
proof-
  let ?SB="Sup1 A B"
  let ?SX="Sup1 A X"
  have B0: "?SX \<le> ?SB"
    by (meson A0 A1 A2 A3 A4 sup_in_sub)
  have B1:"?SB \<in> UpperBoundsIn A B"
    by (simp add: A4 sup1_in_space sup1_is_ub upper_bounds_are_upper_bounds)
  have B2: "?SB \<le> ?SX"
    by (meson A3 A4 A5 IsUpperBound_def sup1_apply_ub sup1_is_ub)
  have B3: "?SB = ?SX"
    by (simp add: B0 B2 dual_order.eq_iff)
  with B3 show ?thesis by simp
qed 


subsubsection Inf1

lemma inf_lt_lowerbound:
  assumes A0: "A\<noteq>{}" and
          A1: "HasGreatest (LowerBoundsIn A X)" and 
          A2: "\<forall>a\<in>A. a \<ge> l" and
          A3: "l \<in> X"
  shows "Inf1 A X \<ge> l"
proof-
  let ?L ="LowerBoundsIn A X"
  from A2 have A4:"\<forall>a\<in>A. a \<ge> l"
    by blast 
  have A5: "l \<in> ?L"
    by (simp add: A3 A4 LowerBoundsIn_def)
  have A6: "Inf1 A X \<ge> l"
    by (simp add: A1 A5 greatest_is_maximum Inf1_def)
  with A6 show ?thesis by auto
qed

lemma glb_then_inf1: 
  assumes A0:"A \<noteq> {}" and
          A1:"\<forall>x \<in>A. x \<ge> z" and
          A2:"\<forall>y. (\<forall>x \<in> A. x \<ge> y) \<longrightarrow> z \<ge> y" and
          A3:"z \<in> X"
  shows "HasGreatest (LowerBoundsIn A X) \<and> z = Inf1 A X" 
proof - 
  let ?L = "(LowerBoundsIn A X)"
  have B0: "z \<in> ?L"
    by (simp add: A1 A3 LowerBoundsIn_def)
  have B1: "\<forall>y \<in> ?L. z \<ge> y"
    by (simp add: A2 IsLowerBound_def lower_bounds_are_lower_bounds)
  have B2:"HasGreatest (LowerBoundsIn A X)"
    by (meson B0 B1 HasGreatest_def IsGreatest_def IsUpperBound_def)
  have B3:"z = Inf1 A X"
    by (simp add: B0 B1 Inf1_def maximum_is_greatest)
  with B2 B3 show ?thesis by simp
qed

lemma least_then_inf1:
  assumes A0:"A \<noteq> {}" and
          A1:"HasLeast A" and 
          A2:"A \<in> Pow X"
  shows "(HasGreatest (LowerBoundsIn A X)) \<and> (Least  A = Inf1 A X) "
proof-
  let ?M = "Least A"
  have B0:"?M \<in> A"
    by (simp add: A1 least_is_minimum)
  have B1:"\<forall>x \<in> A. x \<ge> ?M"
    by (simp add: A1 least_is_minimum)
  have B2:"\<forall>y. (\<forall>x \<in> A. x \<ge> y) \<longrightarrow> ?M\<ge>y"
    using B0 by blast
  with A0 B1 have B3: "HasGreatest (LowerBoundsIn A X)"
    by (meson A2 B0 PowD glb_then_inf1 subsetD)
  have B4: "?M = Inf1 A X"
    by (meson A0 A2 B0 B1 Pow_iff glb_then_inf1 subsetD)
  with B3 B4 show ?thesis by auto
qed

lemma inf1_subset:
  assumes A0: "A \<noteq> {} \<and> B \<noteq> {}"
      and A1: "(HasGreatest (LowerBoundsIn A X)) \<and> (HasGreatest (LowerBoundsIn B X))"
      and A2: "(A \<in> Pow X) \<and> (B \<in> Pow X)"
      and A3: "A \<subseteq> B"
  shows "(Inf1 A X) \<ge> (Inf1 B X)"
proof-
  have B0: "\<forall>x \<in> X. (\<forall>b \<in> B. x \<le> b) \<longrightarrow> (\<forall>a \<in> A. x \<le> a)"
    using A3 by blast
  from B0 have B1: "(LowerBoundsIn B X) \<subseteq> (LowerBoundsIn A X)"
    by (metis IsLowerBound_def subsetI lower_bounds_are_lower_bounds)
  have B2: "(Greatest (LowerBoundsIn A X)) \<ge> (Greatest (LowerBoundsIn B X))"
    using A1 B1 greatest_is_maximum by blast
  have B3: "(Inf1 A X) \<ge> (Inf1 B X)"
    by (simp add: B2 Inf1_def)
  with B3 show ?thesis by auto
qed


lemma has_inf1_yields_inf1:
  assumes A0: "A \<noteq> {} \<and> X \<noteq> {}" and
          A1: "A \<in> Pow X" and
          A2: "(HasASup1 A X)"
  shows "( ( IsUpperBound (Sup1 A X) A) \<and>  (\<forall>z \<in> X. ((\<forall>a \<in> A. z \<ge> a)\<longrightarrow> (z \<ge> (Sup1 A X)) ))  )"
proof-
  let ?U="UpperBoundsIn A X"
  let ?m="Least ?U"
  have B0: "\<forall>u \<in> ?U. ?m \<le> u"
    using A2 HasASup1_def least_is_minimum by auto
  have B1:"\<forall>z \<in> X. (\<forall>a \<in> A. z\<ge>a) \<longrightarrow> z \<in> UpperBoundsIn A X"
    by (simp add: IsUpperBound_def upper_bounds_are_upper_bounds)
  have B2:"\<forall>z \<in> X. ((\<forall>a \<in> A. z\<ge>a) \<longrightarrow> (?m \<le> z))"
    using B0 B1 by blast
  have B3:"(Sup1 A X) = ?m"
    by (simp add: Sup1_def)
  have B4:"IsUpperBound ?m A"
    using A2 HasASup1_def least_is_minimum upper_bounds_are_upper_bounds by blast
  have B5:"( ( IsUpperBound ?m A) \<and>  (\<forall>z \<in> X. ((\<forall>a \<in> A. z \<ge> a)\<longrightarrow> (z \<ge> ?m) ))  )"
    using B2 B4 by blast
  have B6: "( ( IsUpperBound (Sup1 A X) A) \<and>  (\<forall>z \<in> X. ((\<forall>a \<in> A. z \<ge> a)\<longrightarrow> (z \<ge> (Sup1 A X)) ))  )"
    using B3 B5 by presburger
  with B6 show ?thesis by simp
qed

lemma inf1_in_space:
  assumes A0: "HasAnInf1 A X"
  shows  "(Inf1 A X) \<in> X"
proof -
  have "HasGreatest (LowerBoundsIn A X)"
    using HasAnInf1_def assms by blast
  then have "Inf1 A X \<in> LowerBoundsIn A X"
    by (simp add: Inf1_def glb_is_maxlb)
  then show ?thesis
    by (simp add: lower_bounds_are_lower_bounds)
qed


lemma inf1_is_lb:
 assumes "HasAnInf1 A X"
 shows "(IsLowerBound (Inf1 A X) A)"
  by (metis HasAnInf1_def Inf1_def assms greatest_is_maximum lower_bounds_are_lower_bounds)

lemma inf1_apply_lb:
  assumes "HasAnInf1 A X"
  shows "(\<forall>z \<in> X. ((\<forall>a \<in> A. z \<le> a) \<longrightarrow> (z \<le> (Inf1 A X))))"
  by (metis HasAnInf1_def Inf1_def assms greatest_is_maximum lower_bounds_are_lower_bounds2)


lemma inf11_is_lb_ub:
  assumes A0: "(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1: "A \<in> (Pow X)" and
          A2: "HasAnInf1 A X"
  shows "(\<forall>x \<in> {y \<in> X. \<forall>a \<in> A. y \<le> a}. x \<le> (Inf1 A X))"
  by (simp add: A2 inf1_apply_lb)

lemma inf_in_sub:
  assumes A0: "A \<noteq> {}" and 
          A1: "A \<subseteq> B"  and
          A2: "B \<in> Pow X" and
          A3: "HasAnInf1 A X" and 
          A4: "HasAnInf1 A B" 
  shows " Inf1 A B  \<le> Inf1 A X"
proof-
  let ?SX="LowerBoundsIn A X"
  let ?SB="LowerBoundsIn A B"
  have B0: "?SB \<noteq> {} \<and> ?SX \<noteq> {}"
    using A3 A4 HasAnInf1_def set_max_not_empty by auto
  have B1: "(HasGreatest ?SB ) \<and> (HasGreatest  ?SX)"
    using A3 A4 HasAnInf1_def by auto
  have B2: "?SB  \<subseteq> ?SX"
    by (smt (verit, best) A2 PowD lower_bounds_are_lower_bounds2 subsetD subsetI)
  have B3: "Greatest ?SB \<le> Greatest ?SX"
    using B1 B2 glb_is_maxlb by blast
  have B4: "Greatest (LowerBoundsIn A B) \<le> Greatest (LowerBoundsIn A X)"
    by (simp add: B3)
  have B5: " Inf1 A B \<le> Inf1 A X"
    by (simp add: B4 Inf1_def)
  with B5 show ?thesis by simp
qed

lemma inf_sub_suff:
  assumes  A0: "A \<noteq> {}" and 
           A1: "A \<subseteq> B"  and
           A2: "B \<in> Pow X" and
           A3: "HasAnInf1 A X" and 
           A4: "HasAnInf1 A B" and
           A5: "Inf1 A X \<in> B"
  shows "Inf1 A B = Inf1 A X"
proof-
  let ?SB="Inf1 A B"
  let ?SX="Inf1 A X"
  have B0: "?SB \<le> ?SX"
    by (meson A0 A1 A2 A3 A4 inf_in_sub)
  have B1:"?SX \<in> LowerBoundsIn A B"
    by (simp add: A3 A5 inf1_is_lb lower_bounds_are_lower_bounds)
  have B2: "?SX \<le> ?SB"
    using A4 B1 inf1_apply_lb lower_bounds_are_lower_bounds2 by blast
  have B3: "?SX = ?SB"
    by (simp add: B0 B2 dual_order.eq_iff)
  with B3 show ?thesis by simp
qed 



subsection Def1EquivDef2

subsubsection Sup1EquivSup2

lemma sup1_is_sup2:
  assumes A0: "(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1: "A  \<in> (Pow X)" and
          A2: "HasASup1 A X" and
          A3: "HasASup2 A X"
  shows "IsSup2 (Sup1 A X) A X"
proof-
  have B0: "(Sup1 A X) \<in> X"
    by (simp add: A2 sup1_in_space)
  have B1: "(IsUpperBound (Sup1 A X) A)"
    by (simp add: A2 sup1_is_ub)
  have B2: "(\<forall>z \<in> X. ((\<forall>a \<in> A. z \<ge> a)\<longrightarrow> (z \<ge>  (Sup1 A X)) ))"
    by (simp add: A2 sup1_apply_ub)
  have B3: "IsSup2 (Sup1 A X) A X"
    by (simp add: B0 B1 B2 IsSup2_def upper_bounds_are_upper_bounds)
  with B3 show ?thesis by blast
qed

lemma sup2_req_imp_lub:
  assumes A0:"A \<noteq> {}" and
          A1: "A \<in> Pow X"
  shows "\<forall>m \<in> X. ((m \<in> UpperBoundsIn A X) \<and> (\<forall>y \<in>X. (\<forall>a \<in> A. a\<le>y) \<longrightarrow> (y \<ge> m) )) \<longrightarrow> m=Least (UpperBoundsIn A X)"
  by (simp add: minimum_is_least upper_bounds_are_upper_bounds2)
 
lemma is_sup2_then_in_ub_set:
  assumes A0:"(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1:"A \<in> Pow X" and
          A2:"HasASup2 A X" 
  shows "\<forall>m \<in> X. (IsSup2 m A X)\<longrightarrow> m \<in> (UpperBoundsIn A X)"
proof-
  have B0:"\<forall>x \<in> X. ((x \<in> UpperBoundsIn A X) \<longleftrightarrow> (\<forall>a \<in> A. x \<ge> a))"
    by (simp add: upper_bounds_are_upper_bounds2)
  have B1: "\<forall>m \<in> X. ((IsSup2 m A X) \<longleftrightarrow> ((m \<in> (UpperBoundsIn A X))  \<and>  (\<forall>z \<in> X. ((\<forall>a \<in> A. z \<ge> a)\<longrightarrow> (z \<ge> m) ))))"
    using IsSup2_def by blast
  with B1 show ?thesis by auto
qed

lemma is_sup2_imp_sup1:
  assumes A0:"(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1:"A \<in> Pow X" and
          A2:"HasASup2 A X" and
          A3:"HasASup1 A X"
  shows "\<forall>m \<in> X. (IsSup2 m A X)\<longrightarrow> m=(Sup1 A X)"
  by (smt (verit, best) A0 A1 IsSup2_def Sup1_def sup2_req_imp_lub)

lemma has_sup2_imp_has_sup1_eq:
  assumes A0:"(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1:"A \<in> Pow X" and
          A2:"HasASup2 A X"
  shows "HasASup1 A X \<and> (\<forall>m \<in> X. ((IsSup2 m A X) \<longleftrightarrow> (m=Sup1 A X)))"
proof-
  from A0 A1 A2 have B0: "\<exists>m. (m \<in> X) \<and> (IsSup2 m A X)"
    by (metis HasASup2_def IsSup2_def upper_bounds_are_upper_bounds2)
  let ?m="SOME m. IsSup2 m A X"
  have B1: "\<forall>m \<in> X. ((IsSup2 m A X) \<longleftrightarrow> ((m \<in> (UpperBoundsIn A X))  \<and>  (\<forall>z \<in> X. ((\<forall>a \<in> A. z \<ge> a)\<longrightarrow> (z \<ge> m) ))))"
    using IsSup2_def by blast
  have B2: "\<forall>m \<in> X. ((IsSup2 m A X) \<longleftrightarrow> ((m \<in> (UpperBoundsIn A X))  \<and>  (\<forall>z \<in>(UpperBoundsIn A X).  (z \<ge> m) )))"
    by (metis B1 upper_bounds_are_upper_bounds2)
  let ?U="UpperBoundsIn A X"
  have B3: "\<forall>m \<in> X.  ((IsSup2 m A X) \<longleftrightarrow> (m \<in> ?U \<and> (IsLeast m ?U)))"
    by (simp add: B2 IsLeast_def IsLowerBound_def)
  have B4: "\<forall>m \<in> X.  ((IsSup2 m A X) \<longleftrightarrow> (IsLeast m ?U))"
    by (simp add: B3 IsLeast_def)
  have B5: "\<forall>m \<in> X. ((IsSup2 m A X) \<longleftrightarrow> (m=Sup1 A X))"
    by (metis B0 B2 Sup1_def element_lb_is_least_alt)
  have B6:"\<exists>m. IsSup2 m A X \<longrightarrow>( \<exists>m. m=Sup1 A X)"
    by simp
  have B7: "HasASup2 A X \<longrightarrow> ( \<exists>m. m=Sup1 A X)"
    by simp
  have B8: "(HasASup2 A X) \<longrightarrow> (HasASup1 A X)"
    using B0 B4 HasASup1_def HasLeast_def by blast
  show ?thesis
    by (simp add: A2 B5 B8)
qed



lemma has_sup1_iff_has_sup2:
  assumes A0:"(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1:"A \<in> Pow X"
  shows "HasASup1 A X \<longleftrightarrow> HasASup2 A X"
  by (metis A0 A1 HasASup1_def HasASup2_def IsSup2_def Sup1_def element_lb_is_least_alt sup1_apply_ub minimum_is_unique has_sup2_imp_has_sup1_eq)  

lemma has_sup1_then_sup1_eq_sup2:
  assumes A0:"(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1:"A \<in> Pow X" and 
          A2: "HasASup1 A X"
  shows "Sup1 A X = Sup2 A X"
  by (smt (verit, del_insts) A0 A1 A2 HasASup2_def IsSup2_def Sup2_def has_sup2_imp_has_sup1_eq has_sup1_iff_has_sup2 the_equality upper_bounds_are_upper_bounds)

lemma has_sup12_then_sup1_eq_sup2:
  assumes A0:"(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1:"A \<in> Pow X" and 
          A2: "HasASup2 A X \<or> HasASup1 A X"
  shows "Sup1 A X = Sup2 A X"
  by (smt (verit, del_insts) A0 A1 A2 HasASup2_def IsSup2_def Sup2_def has_sup2_imp_has_sup1_eq has_sup1_iff_has_sup2 the_equality upper_bounds_are_upper_bounds)


subsubsection Inf1equivInf2

lemma inf2_req_imp_glb:
  assumes A0: "A \<noteq> {}" and
          A1: "A \<in> Pow X"
  shows "\<forall>m \<in> X. ((m \<in> LowerBoundsIn A X) \<and> (\<forall>y \<in> X. (\<forall>a \<in> A. a \<ge> y) \<longrightarrow> (y \<le> m))) \<longrightarrow> m = Greatest (LowerBoundsIn A X)"
  by (simp add: maximum_is_greatest lower_bounds_are_lower_bounds2)

lemma is_inf2_then_in_lb_set:
  assumes A0: "(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1: "A \<in> Pow X" and
          A2: "HasAnInf2 A X"
  shows "\<forall>m \<in> X. (IsInf2 m A X) \<longrightarrow> m \<in> (LowerBoundsIn A X)"
proof -
  have B0: "\<forall>x \<in> X. ((x \<in> LowerBoundsIn A X) \<longleftrightarrow> (\<forall>a \<in> A. x \<le> a))"
    by (simp add: lower_bounds_are_lower_bounds2)
  have B1: "\<forall>m \<in> X. ((IsInf2 m A X) \<longleftrightarrow> ((m \<in> (LowerBoundsIn A X)) \<and> (\<forall>z \<in> X. ((\<forall>a \<in> A. z \<le> a) \<longrightarrow> (z \<le> m)))))"
    using IsInf2_def by blast
  with B1 show ?thesis by auto
qed

lemma is_inf2_imp_inf1:
  assumes A0: "(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1: "A \<in> Pow X" and
          A2: "HasAnInf2 A X" and
          A3: "HasAnInf1 A X"
  shows "\<forall>m \<in> X. (IsInf2 m A X) \<longrightarrow> m = (Inf1 A X)"
  by (smt (verit, best) A0 A1 IsInf2_def Inf1_def inf2_req_imp_glb)

lemma has_inf2_imp_has_inf1_eq:
  assumes A0: "(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1: "A \<in> Pow X" and
          A2: "HasAnInf2 A X"
  shows "HasAnInf1 A X \<and> (\<forall>m \<in> X. ((IsInf2 m A X) \<longleftrightarrow> (m = Inf1 A X)))"
proof -
  from A0 A1 A2 have B0: "\<exists>m. (m \<in> X) \<and> (IsInf2 m A X)"
    by (metis HasAnInf2_def IsInf2_def lower_bounds_are_lower_bounds2)
  let ?m = "SOME m. IsInf2 m A X"
  have B1: "\<forall>m \<in> X. ((IsInf2 m A X) \<longleftrightarrow> ((m \<in> (LowerBoundsIn A X))  \<and>  (\<forall>z \<in> X. ((\<forall>a \<in> A. z \<le> a) \<longrightarrow> (z \<le> m)))))"
    using IsInf2_def by blast
  have B2: "\<forall>m \<in> X. ((IsInf2 m A X) \<longleftrightarrow> ((m \<in> (LowerBoundsIn A X))  \<and>  (\<forall>z \<in> (LowerBoundsIn A X). (z \<le> m))))"
    by (metis B1 lower_bounds_are_lower_bounds2)
  let ?L = "LowerBoundsIn A X"
  have B3: "\<forall>m \<in> X. ((IsInf2 m A X) \<longleftrightarrow> (m \<in> ?L \<and> (IsGreatest m ?L)))"
    by (simp add: B2 IsGreatest_def IsUpperBound_def)
  have B4: "\<forall>m \<in> X. ((IsInf2 m A X) \<longleftrightarrow> (IsGreatest m ?L))"
    by (simp add: B3 IsGreatest_def)
  have B5: "\<forall>m \<in> X. ((IsInf2 m A X) \<longleftrightarrow> (m = Inf1 A X))"
    by (metis B0 B2 Inf1_def maximum_is_greatest)
  have B6: "\<exists>m. IsInf2 m A X \<longrightarrow> (\<exists>m. m = Inf1 A X)"
    by simp
  have B7: "HasAnInf2 A X \<longrightarrow> (\<exists>m. m = Inf1 A X)"
    by simp
  have B8: "(HasAnInf2 A X) \<longrightarrow> (HasAnInf1 A X)"
    using B0 B4 HasAnInf1_def HasGreatest_def by blast
  show ?thesis
    by (simp add: A2 B5 B8)
qed

lemma has_inf1_iff_has_inf2:
  assumes A0: "(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1: "A \<in> Pow X"
  shows "HasAnInf1 A X \<longleftrightarrow> HasAnInf2 A X"
  by (metis A0 A1 HasAnInf1_def HasAnInf2_def IsInf2_def Inf1_def element_ub_is_greatest_alt inf1_apply_lb maximum_is_unique has_inf2_imp_has_inf1_eq)

lemma has_inf1_then_inf1_eq_inf2:
  assumes A0: "(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1: "A \<in> Pow X" and 
          A2: "HasAnInf1 A X"
  shows "Inf1 A X = Inf2 A X"
  by (smt (verit, del_insts) A0 A1 A2 HasAnInf2_def IsInf2_def Inf2_def has_inf2_imp_has_inf1_eq has_inf1_iff_has_inf2 the_equality lower_bounds_are_lower_bounds)

lemma has_inf12_then_inf1_eq_inf2:
  assumes A0: "(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1: "A \<in> Pow X" and 
          A2: "HasAnInf2 A X \<or> HasAnInf1 A X"
  shows "Inf1 A X = Inf2 A X"
  by (smt (verit, del_insts) A0 A1 A2 HasAnInf2_def IsInf2_def Inf2_def has_inf2_imp_has_inf1_eq has_inf1_iff_has_inf2 the_equality lower_bounds_are_lower_bounds)


lemma inf1_is_inf2:
  assumes A0: "(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1: "A \<in> (Pow X)" and
          A2: "HasAnInf1 A X" and
          A3: "HasAnInf2 A X"
  shows "IsInf2 (Inf1 A X) A X"
proof-
  have B0: "(Inf1 A X) \<in> X"
    by (simp add: A2 inf1_in_space)
  have B1: "(IsLowerBound (Inf1 A X) A)"
    by (simp add: A2 inf1_is_lb)
  have B2: "(\<forall>z \<in> X. ((\<forall>a \<in> A. z \<le> a) \<longrightarrow> (z \<le> (Inf1 A X))))"
    by (simp add: A2 inf1_apply_lb)
  have B3: "IsInf2 (Inf1 A X) A X"
    by (simp add: B0 B1 B2 IsInf2_def lower_bounds_are_lower_bounds)
  with B3 show ?thesis by blast
qed


subsection Def2EquivDef3

subsubsection Sup2EquivSup3

lemma sup3_is_ub:
  assumes A0:"(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1:"A \<in> Pow X" and 
          A2:"IsSup3 m A X"
  shows "(\<forall>z \<in> X. ((z \<ge> m) \<longrightarrow> (\<forall>a \<in> A. z\<ge> a))) \<and> (\<forall>z \<in> X. ((\<forall>a \<in> A. z\<ge> a) \<longrightarrow>(z \<ge> m) ))"
  by (meson A2 IsSup3_def)

lemma sup3_unique:
  assumes A0:"(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1:"A \<in> Pow X" and 
          A2:"HasASup3  A X"
  shows "\<exists>!m. (IsSup3 m A X)"
  by (meson A2 HasASup3_def IsSup3_def order_antisym order_refl)

lemma sup3_is_ub2:
  assumes A0:"(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1:"A \<in> Pow X" and 
          A2:"HasASup3 A X"
  shows "\<forall>a \<in>A. a\<le> (Sup3 A X)"
proof-
  have B0:"\<exists>m. IsSup3 m A X"
    using A2 HasASup3_def by auto
  let ?m="THE m. IsSup3 m A X"
  have B1: "\<forall>a \<in> X. a \<le> a"
    by simp
  have B2: "IsSup3 ?m A X"
    by (metis A0 A1 B0 HasASup3_def sup3_unique theI)
  have B3: "\<forall>z \<in> X. ((z \<ge> ?m) \<longrightarrow> (\<forall>a \<in> A. z\<ge> a))"
    by (metis A0 A1 B2 sup3_is_ub)
  have B4: "\<forall>a \<in> A. (?m \<ge> a)"
    using B1 B2 B3 IsSup3_def by blast
  have B5:"\<forall>m \<in> X.  ((IsSup3 m A X) \<longrightarrow> (\<forall>a \<in>A. a\<le> m)) "
    by (meson IsSup3_def verit_comp_simplify1(2))
  have B6: "\<forall>a \<in>A. a\<le> (Sup3 A X)"
    by (simp add: B4 Sup3_def)
  with B6 show ?thesis by auto
qed
  

lemma sup3_then_sup2_1:
  assumes A0:"(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1:"A \<in> Pow X" and 
          A2:"HasASup3 A X"
  shows "((Sup3 A X) \<in> (UpperBoundsIn A X)) \<and> (\<forall>z \<in> X. ((\<forall>a \<in> A. z\<ge> a) \<longrightarrow>(z \<ge> (Sup3 A X))))"
proof-
  have B0: "\<forall>a \<in>A. a\<le> (Sup3 A X)"
    using A1 A2 sup3_is_ub2 by auto
  have B1:"\<exists>m. IsSup3 m A X"
    using A2 HasASup3_def by auto
  let ?m="THE m. IsSup3 m A X"
  have B2: "IsSup3 ?m A X"
    by (metis A0 A1 B1 HasASup3_def sup3_unique theI)
  have B3: "?m \<in> X"
    using B2 IsSup3_def by blast
  have B4:  "?m \<in>(UpperBoundsIn A X)"
    by (metis A0 A1 B0 B3 Sup3_def ub_in_ub_set)
  have B5: "(Sup3 A X) \<in> (UpperBoundsIn A X)"
    by (simp add: B4 Sup3_def)
  have B6: "(\<forall>z \<in> X. ((\<forall>a \<in> A. z\<ge> a) \<longrightarrow>(z \<ge>?m) ))"
    by (metis A0 A1 B2 sup3_is_ub)
  have B7: "(\<forall>z \<in> X. ((\<forall>a \<in> A. z\<ge> a) \<longrightarrow>(z \<ge> (Sup3 A X))))"
    by (simp add: B6 Sup3_def)
  with B5 B7 show ?thesis by auto
qed


lemma sup3_then_sup2_2:
  assumes A0:"(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1:"A \<in> Pow X" and 
          A2:"HasASup3 A X"
  shows "(HasASup2 A X) \<and> (IsSup2( Sup3 A X) A X)"
  by (metis A0 A1 A2 HasASup2_def IsSup2_def sup3_then_sup2_1)



lemma sup2_then_sup3_1:
  assumes A0:"(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1:"A \<in> Pow X" and 
          A2:"HasASup2 A X"  
  shows "(HasASup3 A X) \<and> (IsSup3 (Sup2 A X) A X)"
proof-
  have B0: "\<forall>a \<in> A. (Sup2 A X)\<ge>a"
    by (metis A0 A1 A2 IsUpperBound_def has_inf1_yields_inf1 has_sup2_imp_has_sup1_eq has_sup12_then_sup1_eq_sup2)
  have B1: "\<forall>z \<in> X.( (z \<ge> (Sup2 A X)) \<longrightarrow> (\<forall>a \<in> A. a\<le>z)) "
    using B0 dual_order.trans by blast
  have B2: "\<forall>z \<in> X. ((\<forall>a \<in> A. a\<le> z) \<longrightarrow> ( z\<ge> (Sup2 A X)))"
    by (metis A0 A1 A2 sup1_apply_ub has_sup2_imp_has_sup1_eq has_sup1_then_sup1_eq_sup2)
  have B3: "\<forall>z \<in> X. ((\<forall>a \<in> A. a\<le> z) \<longleftrightarrow> ( z\<ge> (Sup2 A X)))"
    using B1 B2 by fastforce
  have B4: "IsSup3 (Sup2 A X) A X"
    by (smt (verit, best) A0 A1 A2 B3 IsSup3_def sup1_in_space has_sup1_iff_has_sup2 has_sup1_then_sup1_eq_sup2)
  have B5: "\<exists>m. IsSup3 m A X"
    using B4 by auto
  have B6: "(HasASup3 A X)"
    by (simp add: B5 HasASup3_def)
  with B4 B6 show ?thesis by auto
qed


lemma has_sup23_imp_sup2_eq_sup3:
  assumes A0:"(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1:"A \<in> Pow X" and 
          A2: "HasASup2 A X \<or> HasASup3 A X"
  shows "Sup2 A X = Sup3 A X"
  by (smt (verit, del_insts) A0 A1 A2 IsSup2_def Sup2_def has_sup2_imp_has_sup1_eq has_sup12_then_sup1_eq_sup2 sup2_then_sup3_1 sup3_then_sup2_2 upper_bounds_are_upper_bounds2)



lemma has_sup3_iff_has_sup2:
  assumes A0:"(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1:"A \<in> Pow X" 
  shows "(HasASup3 A X) \<longleftrightarrow> (HasASup2 A X)"
  by (meson A0 A1 sup2_then_sup3_1 sup3_then_sup2_2)


subsubsection Inf2EquivInf3

lemma inf3_is_lb:
  assumes A0: "(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1: "A \<in> Pow X" and 
          A2: "IsInf3 m A X"
  shows "(\<forall>z \<in> X. ((z \<le> m) \<longrightarrow> (\<forall>a \<in> A. z \<le> a))) \<and> (\<forall>z \<in> X. ((\<forall>a \<in> A. z \<le> a) \<longrightarrow> (z \<le> m)))"
  by (meson A2 IsInf3_def)

lemma inf3_unique:
  assumes A0: "(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1: "A \<in> Pow X" and 
          A2: "HasAnInf3 A X"
  shows "\<exists>!m. (IsInf3 m A X)"
  by (meson A2 HasAnInf3_def IsInf3_def order_antisym order_refl)

lemma inf3_is_lb2:
  assumes A0: "(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1: "A \<in> Pow X" and 
          A2: "HasAnInf3 A X"
  shows "\<forall>a \<in> A. a \<ge> (Inf3 A X)"
proof-
  have B0: "\<exists>m. IsInf3 m A X"
    using A2 HasAnInf3_def by auto
  let ?m = "THE m. IsInf3 m A X"
  have B1: "\<forall>a \<in> X. a \<ge> a"
    by simp
  have B2: "IsInf3 ?m A X"
    by (metis A0 A1 B0 HasAnInf3_def inf3_unique theI)
  have B3: "\<forall>z \<in> X. ((z \<le> ?m) \<longrightarrow> (\<forall>a \<in> A. z \<le> a))"
    by (metis A0 A1 B2 inf3_is_lb)
  have B4: "\<forall>a \<in> A. (?m \<le> a)"
    using B1 B2 B3 IsInf3_def by blast
  have B5: "\<forall>m \<in> X. ((IsInf3 m A X) \<longrightarrow> (\<forall>a \<in> A. a \<ge> m))"
    by (meson IsInf3_def verit_comp_simplify1(2))
  have B6: "\<forall>a \<in> A. a \<ge> (Inf3 A X)"
    by (simp add: B4 Inf3_def)
  with B6 show ?thesis by auto
qed

lemma inf3_then_inf2_1:
  assumes A0: "(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1: "A \<in> Pow X" and 
          A2: "HasAnInf3 A X"
  shows "((Inf3 A X) \<in> (LowerBoundsIn A X)) \<and> (\<forall>z \<in> X. ((\<forall>a \<in> A. z \<le> a) \<longrightarrow> (z \<le> (Inf3 A X))))"
proof-
  have B0: "\<forall>a \<in> A. a \<ge> (Inf3 A X)"
    using A1 A2 inf3_is_lb2 by auto
  have B1: "\<exists>m. IsInf3 m A X"
    using A2 HasAnInf3_def by auto
  let ?m = "THE m. IsInf3 m A X"
  have B2: "IsInf3 ?m A X"
    by (metis A0 A1 B1 HasAnInf3_def inf3_unique theI)
  have B3: "?m \<in> X"
    using B2 IsInf3_def by blast
  have B4: "?m \<in> (LowerBoundsIn A X)"
    by (metis A0 A1 B0 B3 Inf3_def lb_in_lb_set)  (* Note: You would need to define lb_in_lb_set *)
  have B5: "(Inf3 A X) \<in> (LowerBoundsIn A X)"
    by (simp add: B4 Inf3_def)
  have B6: "\<forall>z \<in> X. ((\<forall>a \<in> A. z \<le> a) \<longrightarrow> (z \<le> ?m))"
    by (metis A0 A1 B2 inf3_is_lb)
  have B7: "\<forall>z \<in> X. ((\<forall>a \<in> A. z \<le> a) \<longrightarrow> (z \<le> (Inf3 A X)))"
    by (simp add: B6 Inf3_def)
  with B5 B7 show ?thesis by auto
qed


lemma inf3_then_inf2_2:
  assumes A0: "(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1: "A \<in> Pow X" and 
          A2: "HasAnInf3 A X"
  shows "(HasAnInf2 A X) \<and> (IsInf2 (Inf3 A X) A X)"
  by (metis A0 A1 A2 HasAnInf2_def IsInf2_def inf3_then_inf2_1)  (* Define inf3_then_inf2_1 *)


lemma inf2_then_inf3_1:
  assumes A0: "(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1: "A \<in> Pow X" and 
          A2: "HasAnInf2 A X"
  shows "(HasAnInf3 A X) \<and> (IsInf3 (Inf2 A X) A X)"
proof-
  have B0: "\<forall>a \<in> A. (Inf2 A X) \<le> a"
    by (metis A0 A1 A2 IsInf2_def inf1_is_inf2 has_inf1_iff_has_inf2 has_inf1_then_inf1_eq_inf2 lower_bounds_are_lower_bounds2)
  have B1: "\<forall>z \<in> X. ((z \<le> (Inf2 A X)) \<longrightarrow> (\<forall>a \<in> A. a \<ge> z))"
    using B0 dual_order.trans by blast
  have B2: "\<forall>z \<in> X. ((\<forall>a \<in> A. a \<ge> z) \<longrightarrow> (z \<le> (Inf2 A X)))"
    by (metis A0 A1 A2 inf1_apply_lb has_inf2_imp_has_inf1_eq has_inf12_then_inf1_eq_inf2)
  have B3: "\<forall>z \<in> X. ((\<forall>a \<in> A. a \<ge> z) \<longleftrightarrow> (z \<le> (Inf2 A X)))"
    using B1 B2 by fastforce
  have B4: "IsInf3 (Inf2 A X) A X"
    by (smt (verit, best) A0 A1 A2 B3 IsInf3_def inf1_in_space has_inf1_iff_has_inf2 has_inf1_then_inf1_eq_inf2)
  have B5: "\<exists>m. IsInf3 m A X"
    using B4 by auto
  have B6: "(HasAnInf3 A X)"
    by (simp add: B5 HasAnInf3_def)
  with B4 B6 show ?thesis by auto
qed

lemma has_inf23_imp_inf2_eq_inf3:
  assumes A0:"(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1:"A \<in> Pow X" and 
          A2: "HasAnInf2 A X \<or> HasAnInf3 A X"
  shows "Inf2 A X = Inf3 A X"
  by (metis A0 A1 A2  IsInf2_def has_inf2_imp_has_inf1_eq has_inf12_then_inf1_eq_inf2 inf2_then_inf3_1 inf3_then_inf2_2 lower_bounds_are_lower_bounds2)


lemma has_inf3_iff_has_inf2:
  assumes A0:"(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1:"A \<in> Pow X" 
  shows "(HasAnInf3 A X) \<longleftrightarrow> (HasAnInf2 A X)"
  by (meson A0 A1 inf2_then_inf3_1 inf3_then_inf2_2)

subsection Def1EquivDef2EquivDef3

subsubsection Sup1EquivSup2EquivSup3

lemma has_sup123_equiv:
  assumes A0:"(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1:"A \<in> Pow X" 
  shows "((HasASup3 A X) \<longleftrightarrow> (HasASup2 A X)) \<and>
         ((HasASup3 A X) \<longleftrightarrow> (HasASup1 A X)) \<and>
         ((HasASup2 A X) \<longleftrightarrow> (HasASup1 A X))"
  by (metis A0 A1 has_sup1_iff_has_sup2 has_sup3_iff_has_sup2)


subsubsection Inf1EquivInf2EquivInf3

lemma has_inf123_equiv:
  assumes A0:"(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1:"A \<in> Pow X" 
  shows "((HasAnInf3 A X) \<longleftrightarrow> (HasAnInf2 A X)) \<and>
         ((HasAnInf3 A X) \<longleftrightarrow> (HasAnInf1 A X)) \<and>
         ((HasAnInf2 A X) \<longleftrightarrow> (HasAnInf1 A X))"
  by (metis A0 A1 has_inf1_iff_has_inf2 has_inf3_iff_has_inf2)

lemma sup123_equivs:
  assumes A0:"(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1:"A \<in> Pow X" and
          A2: "(HasASup3 A X) \<or> (HasASup2 A X )\<or> (HasASup1 A X)"
  shows "(Sup3 A X = Sup2 A X) \<and> (Sup3 A X = Sup1 A X) \<and> (Sup2 A X = Sup1 A X)"
  by (metis A0 A1 A2 has_sup1_iff_has_sup2 has_sup1_then_sup1_eq_sup2 has_sup23_imp_sup2_eq_sup3 sup3_then_sup2_2)

lemma inf123_equivs:
  assumes A0:"(A \<noteq> {}) \<and> (X \<noteq> {})" and
          A1:"A \<in> Pow X" and
          A2: "(HasAnInf3 A X) \<or> (HasAnInf2 A X )\<or> (HasAnInf1 A X)"
  shows "(Inf3 A X = Inf2 A X) \<and> (Inf3 A X = Inf1 A X) \<and> (Inf2 A X = Inf1 A X)"
  by (metis A0 A1 A2 has_inf1_iff_has_inf2 has_inf1_then_inf1_eq_inf2 has_inf23_imp_inf2_eq_inf3 inf3_then_inf2_2)



subsection Lattices

lemma bounded_above_infs_then_sups:
  assumes A0: "X \<noteq> {}" and
          A1: "HasUpperBound1 X X" and
          A2: "\<forall>A \<in> Pow X. A \<noteq> {} \<longrightarrow> HasAnInf1 A X"
        shows "\<forall>A \<in> Pow X. A \<noteq> {} \<longrightarrow> HasASup1 A X"
proof-
  have B0: "HasGreatest X"
    by (simp add: A0 A1 bounded_above_then_has_greatest)
  have B1: "\<forall>A\<in>Pow X. A \<noteq> {} \<longrightarrow> UpperBoundsIn A X \<noteq> {}"
    by (metis B0 PowD empty_iff maximum_is_unique subsetD ub_in_ub_set)
  have B2: "\<forall>A\<in>Pow X. A \<noteq> {} \<longrightarrow> HasAnInf1 ( UpperBoundsIn A X) X"
    by (simp add: A2 B1 subset_iff upper_bounds_are_upper_bounds)
  have B3: "\<forall>A\<in>Pow X. A \<noteq> {} \<longrightarrow> (\<forall>a \<in> A. a \<le> Inf1 (UpperBoundsIn A X) X)"
    by (simp add: B2 inf1_apply_lb subsetD upper_bounds_are_upper_bounds2)
  have B4: "\<forall>A\<in>Pow X. A \<noteq> {} \<longrightarrow> IsUpperBound (Inf1 (UpperBoundsIn A X) X) A "
    by (simp add: B3 IsUpperBound_def)
  have B5: "\<forall>A \<in> Pow X. A \<noteq> {} \<longrightarrow> HasASup1 A X"
    by (metis B2 B4 HasASup1_def HasLowerBound1_def
        bounded_below_then_has_least empty_iff
        inf1_in_space inf1_is_lb
        lower_bounds_are_lower_bounds
        upper_bounds_are_upper_bounds)
  with B5 show ?thesis by auto
qed

lemma inf_sub_suff2:
  assumes  A0: "A \<noteq> {}" and 
           A1: "A \<subseteq> B"  and
           A2: "B \<in> Pow X" and
           A3: "HasAnInf1 A X" and 
           A5: "Inf1 A X \<in> B"
         shows "HasAnInf1 A B"
proof-
  have B0: "\<forall>a \<in> A. a \<ge> Inf1 A X"
    by (meson A3 IsLowerBound_def inf1_is_lb)
  have B1: " (\<forall>z \<in> X. ((\<forall>a \<in> A. z \<le>  a)\<longrightarrow> (z \<le>  Inf1 A X) ))"
    by (simp add: A3 inf1_apply_lb)
  have B2:" (\<forall>z \<in> B. ((\<forall>a \<in> A. z \<le>  a)\<longrightarrow> (z \<le>  Inf1 A X) ))"
    using A2 B1 by blast
  have B3:"IsInf2 (Inf1 A X) A B"
    by (simp add: A3 A5 B2 IsInf2_def inf1_is_lb lower_bounds_are_lower_bounds)
  have B4: "(Inf1 A X) = Inf2 A B"
    by (metis A0 A1 A5 B3 HasAnInf2_def Pow_iff emptyE has_inf12_then_inf1_eq_inf2 has_inf2_imp_has_inf1_eq)
  have B5: "HasAnInf1 A B"
    by (metis A0 A1 A5 B3 HasAnInf2_def PowI equals0D has_inf2_imp_has_inf1_eq)
  with B5 show ?thesis by auto
qed

lemma sup_sub_suff2:
  assumes  A0: "A \<noteq> {}" and 
           A1: "A \<subseteq> B"  and
           A2: "B \<in> Pow X" and
           A3: "HasASup1 A X" and 
           A5: "Sup1 A X \<in> B"
         shows "HasASup1 A B"
proof-
  have B0: "\<forall>a \<in> A. a \<le> Sup1 A X"
    by (meson A3 IsUpperBound_def sup1_is_ub)
  have B1: " (\<forall>z \<in> X. ((\<forall>a \<in> A. a \<le> z) \<longrightarrow> (Sup1 A X \<le> z) ))"
    by (simp add: A3 sup1_apply_ub)
  have B2:" (\<forall>z \<in> B. ((\<forall>a \<in> A. a \<le> z) \<longrightarrow> (Sup1 A X \<le> z) ))"
    using A2 B1 by blast
  have B3:"IsSup2 (Sup1 A X) A B"
    by (simp add: A3 A5 B2 IsSup2_def sup1_is_ub upper_bounds_are_upper_bounds)
  have B4: "(Sup1 A X) = Sup2 A B"
    by (metis A0 A1 A5 B3 HasASup2_def Pow_iff emptyE has_sup12_then_sup1_eq_sup2 has_sup2_imp_has_sup1_eq)
  have B5: "HasASup1 A B"
    by (metis A0 A1 A5 B3 HasASup2_def PowI equals0D has_sup2_imp_has_sup1_eq)
  with B5 show ?thesis by auto
qed


subsection SpecialSets
  



lemma down_set_is_down_closed:
  assumes A0: "((A \<noteq> {}) \<and> (A \<in> Pow X))" and
          A1: "is_down_closed A X" and
          A2: "(x \<in> X)" and 
          A3: "\<exists>a \<in> A. (x \<le> a)"
  shows "x \<in> A "
  by (meson A1 A2 A3 is_down_closed_def)

lemma up_set_is_up_closed:
  assumes A0: "((A \<noteq> {}) \<and> (A \<in> Pow X))" and
          A1: "is_up_closed A X" and
          A2: "(x \<in> X)" and 
          A3: "\<exists>a \<in> A. (x \<ge> a)"
  shows "x \<in> A "
  using A1 A3 is_up_closed_def by blast


lemma pideal_is_down_closed:
  "\<forall>a \<in> X. (is_down_closed (principal_ideal_in a X) X)"
proof-
  have B0:"\<forall>a \<in> X. (principal_ideal_in a X) = {x \<in> X. x \<le> a}"
    by (simp add: principal_ideal_in_def)
  have B1: "\<forall>a \<in> X. (\<forall>x \<in> X.  x \<le> a \<longrightarrow> (x \<in>  (principal_ideal_in a X)))"
    by (simp add: principal_ideal_in_def)
  have B2: "\<forall>a \<in> X. (is_down_closed (principal_ideal_in a X) X)"
    using B0 is_down_closed_def by fastforce
  with B2 show ?thesis by auto
qed



lemma order_iso_ideals:
  assumes A0: "X \<noteq> {}" and A1:"x1 \<in> X \<and> x2 \<in> X"
  shows "x1 \<le> x2 \<longleftrightarrow> (principal_ideal_in x1 X) \<subseteq> ( principal_ideal_in x2 X)"
proof -
  let ?E1="(principal_ideal_in x1 X )" 
  let ?E2="(principal_ideal_in x2 X)"
  have B0: "\<forall>a \<in> X. a \<le> x1 \<longrightarrow> a \<in> ?E1"
    by (simp add: principal_ideal_in_def)
  have B1:"\<forall>a \<in> X. a \<le> x2 \<longrightarrow> a \<in> ?E2"
    by (simp add: principal_ideal_in_def)
  have B2:"\<forall>a \<in> ?E1. a \<le> x1" 
    by (simp add: principal_ideal_in_def)
  have B3: "x1 \<le> x2 \<longrightarrow> (\<forall>a \<in> X. (a \<in> ?E1 \<longrightarrow> a\<le> x2))"
    using B2 order_trans by auto
  have B4: "x1 \<le> x2 \<longrightarrow> (\<forall>a \<in> X. (a \<in> ?E1 \<longrightarrow> a \<in> ?E2))"
    using B1 B3 by blast
  have B5: "x1 \<le> x2 \<longrightarrow> (principal_ideal_in x1 X) \<subseteq> ( principal_ideal_in x2 X)"
    using B4 principal_ideal_in_def by fastforce
  have B6:"?E1 \<subseteq> ?E2 \<longrightarrow> x1 \<in> ?E2 \<longrightarrow> x1 \<le> x2"
    by (simp add: principal_ideal_in_def)
  have B7: "(principal_ideal_in x1 X) \<subseteq> ( principal_ideal_in x2 X) \<longrightarrow> x1 \<le> x2 "
    by (simp add: A1 B0 B6 subsetD)
  with B5 B7 show ?thesis by auto
qed



lemma order_iso_filters:
  assumes A0: "X \<noteq> {}" and A1:"x1 \<in> X \<and> x2 \<in> X"
  shows "x1 \<le> x2 \<longleftrightarrow> (principal_filter_in x2 X) \<subseteq> ( principal_filter_in x1 X)"
proof -
  let ?E1="(principal_filter_in x1 X )" 
  let ?E2="(principal_filter_in x2 X)"
  have B0: "\<forall>a \<in> X. a \<ge>  x1 \<longrightarrow> a \<in> ?E1"
    by (simp add: principal_filter_in_def)
  have B1:"\<forall>a \<in> X. a \<ge>  x2 \<longrightarrow> a \<in> ?E2"
    by (simp add: principal_filter_in_def)
  have B2:"\<forall>a \<in> ?E2. a \<ge>  x2" 
    by (simp add: principal_filter_in_def)
  have B3: "x1 \<le> x2 \<longrightarrow> (\<forall>a \<in> X. (a \<in> ?E2 \<longrightarrow> a\<ge> x1))"
    using B2 order_trans by auto
  have B4: "x1 \<le> x2 \<longrightarrow> (\<forall>a \<in> X. (a \<in> ?E2 \<longrightarrow> a \<in> ?E1))"
    using B0 B3 by blast
  have B5: "x1 \<le> x2 \<longrightarrow> (principal_filter_in x2 X) \<subseteq> ( principal_filter_in x1 X)"
    using B4 principal_filter_in_def by fastforce
  have B6:"?E2 \<subseteq> ?E1 \<longrightarrow> x1 \<in> ?E2 \<longrightarrow> x2 \<le> x1"
    by (simp add: principal_filter_in_def)
  have B7: "(principal_filter_in x2 X) \<subseteq> ( principal_filter_in x1 X) \<longrightarrow> x1 \<le> x2 "
    by (simp add: A1 principal_filter_in_def subset_iff)
  with B5 B7 show ?thesis by auto
qed

subsection Closures

lemma closure_unfold:
  "(closure f) \<longleftrightarrow>  (extensive f \<and>  isotone f \<and> idempotent f)"
  using closure_def pseudo_closure_def by blast

lemma lem_cl1:
  assumes A0: "extensive f" and A1: "isotone f" and A2: "idempotent f"
  shows "\<forall>x y. (x \<le> f y) \<longrightarrow> (f x  \<le> f y)"
  by (metis A1 A2 idempotent_def isotone_def) 


lemma lem_cl2:
  assumes A0: "extensive f" and A1: "isotone f" and A2: "idempotent f"
  shows "\<forall>x y. (f x \<le> f y) \<longrightarrow> (x  \<le> f y)"
  by (meson A0 dual_order.trans extensive_def)

lemma closure_imp_closure_equiv:
  assumes A0: "extensive f" and A1: "isotone f" and A2: "idempotent f"
  shows "\<forall>x y. (f x \<le> f y) \<longleftrightarrow>  (x  \<le> f y)"
  by (meson A0 A1 A2 lem_cl1 lem_cl2)

lemma lem_cl3:
  assumes  A0:"\<forall>x y. (f x \<le> f y) \<longleftrightarrow>  (x  \<le> f y)"
  shows "extensive f"
  by (meson assms extensive_def order_refl)

lemma lem_c4:
  assumes  A0:"\<forall>x y. (f x \<le> f y) \<longleftrightarrow>  (x  \<le> f y)"
  shows "isotone f"
  by (metis assms dual_order.trans isotone_def order_refl)


lemma lem_c5:
  assumes  A0:"\<forall>x y. ((f::('X::order \<Rightarrow> 'X::order))  x \<le>  (f::('X::order \<Rightarrow> 'X::order)) y) \<longleftrightarrow>  (x  \<le>  (f::('X::order \<Rightarrow> 'X::order)) y)"
  shows "idempotent f"
  by (meson assms idempotent_def order_antisym order_refl)



lemma closure_equiv_imp_closure:
  assumes A0:"\<forall>x y. (f x \<le> f y) \<longleftrightarrow>  (x  \<le> f y)"
  shows "extensive f \<and>  isotone f \<and> idempotent f"
  by (simp add: assms lem_c4 lem_c5 lem_cl3)
  

lemma closure_equiv_equiv_closure:
  "(\<forall>x y. (f x \<le> f y) \<longleftrightarrow>  (x  \<le> f y)) \<equiv> (extensive f \<and>  isotone f \<and> idempotent f)"
  by (smt (verit) closure_imp_closure_equiv closure_equiv_imp_closure)


lemma closure_equivalence:
  "(closure f) \<equiv> (\<forall>x y. (f x \<le> f y) \<longleftrightarrow>  (x  \<le> f y)) "
  by (simp add: closure_equiv_equiv_closure closure_unfold)
  
lemma isotone_imp_pideal:
  assumes A0: "isotone f"  and A1: "range(f) = Y"
  shows "\<forall>b \<in> Y. (is_down_closed (f-` (principal_ideal_in b Y) ) X)"
  by (smt (verit, best) A0 A1 is_down_closed_def is_down_closed_def isotone_def pideal_is_down_closed rangeI vimageD vimageI)

lemma pideal_imp_isotone:
  assumes A0: "X \<noteq> {}" and
          A1: "Y \<noteq> {}" and 
          A2: "f`X = Y" and
          A3: "\<forall>x \<in> X. (is_down_closed ((f-`(principal_ideal_in (f x) Y))) X)"
  shows "\<forall>x1 \<in> X. \<forall>x2 \<in> X. ((x1 \<le> x2) \<longrightarrow> (f x1 \<le> f x2))"
  by (smt (verit) A2 A3 image_eqI is_down_closed_def mem_Collect_eq order_refl principal_ideal_in_def vimage_Collect_eq)

(*nitpick_params [verbose=true, debug=true, show_types=true, show_consts = true]*)

lemma infima_of_closed_are_closed:
  assumes A0: "A \<noteq> {}" and
          A1: "A \<in> Pow X" and
          A2: "\<forall>a \<in> A. (( f a) = a)" and 
          A3: "closure f" and
          A4: "HasAnInf1 A X" and
          A5: "f`(X) \<subseteq> X"
  shows "f(Inf1 A X) = (Inf1 A X)"
proof- 
  let ?m="Inf1 A X"
  have B0: "\<forall>a \<in> A. a \<ge> ?m"
    by (meson A4 IsLowerBound_def inf1_is_lb)
  have B1: "\<forall>a \<in> A. f(?m) \<le> f(a)"
    using B0 assms(4) closure_unfold isotone_def by blast
  have B2: "\<forall>a \<in> A. f(?m) \<le> a"
    using A2 B1 by auto
  have B3: "?m \<le> f(?m)"
    using A3 closure_unfold extensive_def by blast
  have B4: "(f(?m)) \<in> (LowerBoundsIn A X)"
    by (meson A4 A5 B2 IsLowerBound_def imageI inf1_in_space lower_bounds_are_lower_bounds subsetD)
  have B5: "f(?m) \<le> ?m"
    by (metis A4 B4 HasAnInf1_def Inf1_def greatest_is_maximum)
  have B6: "f(?m) = ?m"
    by (simp add: B3 B5 dual_order.eq_iff)
  with B6 show ?thesis by blast
qed


lemma maximal_then_closed:
  assumes A0: "closure f" and
          A1: "f`X \<subseteq> X"
  shows "IsMaximal1 m X \<longrightarrow> (f m) = m"
  by (metis A0 A1 IsMaximal1_def closure_unfold extensive_def image_subset_iff)

lemma greatest_then_closed:
  assumes A0: "closure f" and
          A1: "f`X \<subseteq> X"
  shows "IsGreatest m X \<longrightarrow> (f m) = m"
  by (meson A0 A1 IsGreatest_def IsUpperBound_def closure_unfold dual_order.eq_iff extensive_def image_subset_iff)

lemma closure_range_iff_closed:
  assumes A0: "closure_on f X"
  shows "\<forall>y \<in> X. ((y = f y) \<longleftrightarrow> (\<exists>x \<in> X. (y=f x)))"
proof- 
  have B0:  "\<forall>y \<in> X. ((y = f y) \<longrightarrow> (\<exists>x \<in> X. (y=f x)))"
    by blast
  have B1: "\<forall>y \<in> X. ((\<exists>x \<in> X. (y=f x)) \<longrightarrow>  (y = f y))"
    by (metis assms closure_on_def closure_unfold idempotent_def)
  have B2: "\<forall>y \<in> X. ((y = f y) \<longleftrightarrow> (\<exists>x \<in> X. (y=f x)))"
    using B0  B1 by blast
  with B2 show ?thesis by simp
qed


lemma inf_of_closure_image_is_closed:
  assumes A0: "closure_on f X" and
          A1: "A \<in> (Pow (f`X))" and
          A2: "A \<noteq> {}" and
          A3: "HasAnInf1 A X"
  shows "Inf1 A X \<in>  (f`X)"
proof-
  have B0: "\<forall>a \<in> A. (( f a) = a)"
  proof-
    have C0: "\<forall>a \<in> A. (\<exists>x \<in> X. (a=f x))"
      using A1 by blast
    have C1: "\<forall>a \<in> A. ((f a) = a)"
      by (metis A0 C0 closure_on_def closure_unfold idempotent_def)
    with C1 show ?thesis by auto
  qed 
  have B1: "closure f"
    using A0 closure_on_def by auto
  have B2: "f`(X) \<subseteq> X"
    by (meson A0 closure_on_def)
  let ?m="Inf1 A X"
  have B3:"f(?m) = ?m"
    by (smt (verit, best) A1 A2 A3 B0 B1 B2 Pow_iff dual_order.trans infima_of_closed_are_closed)
  have B4: "Inf1 A X \<in>  (f`X)"
    using A3 B3 inf1_in_space by force
  with B4 show ?thesis by simp
qed




lemma closure_range_of_complete_lattice_is_complete:
  assumes A0: "\<forall>A \<in> Pow X. A \<noteq> {} \<longrightarrow>( HasAnInf1 A X)" and
          A1: "closure_on f X" and
          A2: "HasGreatest X" and
          A3: "f`X \<noteq> {}"
  shows "\<forall>A \<in> (Pow (f`X)). A \<noteq> {} \<longrightarrow>(HasASup1 A (f`X) \<and> HasAnInf1 A (f`X))"
proof-
  let ?Y="f`X"
  have B0: "\<forall>A \<in> (Pow ?Y). A \<noteq> {} \<longrightarrow>  Inf1 A X= Inf1 A?Y "
  proof-
    have C0:"\<forall>A \<in> (Pow ?Y). (( A \<subseteq> ?Y) \<and> (?Y \<subseteq> X)) "
      by (meson A1 Pow_iff closure_on_def)
    have C1: "\<forall>A \<in> (Pow ?Y). A \<noteq> {} \<longrightarrow>  HasAnInf1 A X"
      by (meson A0 C0 PowI dual_order.trans)
    have C2: "\<forall>A \<in> (Pow ?Y). A \<noteq> {} \<longrightarrow> Inf1 A X \<in> ?Y "
      by (simp add: A1 C1 inf_of_closure_image_is_closed)
    have C3:  "\<forall>A \<in> (Pow ?Y). A \<noteq> {} \<longrightarrow> Inf1 A ?Y = Inf1 A X"
      by (meson C0 C1 C2 Pow_iff inf_sub_suff inf_sub_suff2)
    with C3 show ?thesis by simp
  qed
  have B1: "\<forall>A \<in> Pow ?Y. A \<noteq> {} \<longrightarrow>( HasAnInf1 A ?Y)"
    by (meson A0 A1 PowD PowI closure_on_def dual_order.trans inf_of_closure_image_is_closed inf_sub_suff2)
  have B2:"HasUpperBound1 X X"
    by (simp add: A2 HasUpperBound1_def greatest_then_sup1 set_max_not_empty set_min_not_empty)
  have B3: "IsGreatest (Greatest X) ?Y"
  proof-
    have D0: "\<forall>x \<in> X. x \<le> Greatest X"
      by (simp add: A2 greatest_is_maximum)
    have D1: "\<forall>y \<in> ?Y. y \<in> X"
      by (meson A1 closure_on_def in_mono)
    have D2: "\<forall>y \<in> ?Y. y \<le> Greatest X"
      using D0 D1 by blast
    have D3: "Greatest X \<in> ?Y"
      by (metis A1 A2 D1 closure_on_def closure_unfold extensive_def greatest_is_maximum image_eqI order_antisym)
    have D4:"IsGreatest (Greatest X) ?Y"
      by (simp add: D2 D3 IsGreatest_def IsUpperBound_def)
    with D4 show ?thesis by blast
  qed
  have B4:"HasUpperBound1 ?Y ?Y"
    by (meson B3 HasUpperBound2_def IsGreatest_def upper_bounded_equiv)
  have B5: "\<forall>A \<in> Pow ?Y. A \<noteq> {} \<longrightarrow>( HasASup1 A ?Y)"
    by (metis A3 B1 B4 bounded_above_infs_then_sups)
  with B1 B5 show ?thesis by auto
qed

lemma closure_range_of_complete_lattice_is_complete2:
  assumes A0: "\<forall>A \<in> Pow X. A \<noteq> {} \<longrightarrow>( HasAnInf1 A X)" and
          A1: "closure_on f X" and
          A2: "HasUpperBound1 X X" and
          A3: "f`X \<noteq> {}"
  shows "\<forall>A \<in> (Pow (f`X)). A \<noteq> {} \<longrightarrow>(HasASup1 A (f`X) \<and> HasAnInf1 A (f`X))"
  by (metis A0 A1 A2 A3 bounded_above_then_has_greatest closure_range_of_complete_lattice_is_complete image_is_empty)

lemma pfilters_have_least_imp_crange:
  assumes A0: "A \<in> Pow X" and
          A1: "A \<noteq> {}" and
          A2: "\<forall>x \<in> X. HasLeast (principal_filter_in x A) "
 shows "\<exists>f.  closure_in f X"
proof-
  let ?f = "\<lambda>x.  Least (principal_filter_in x A) "
  have B0: "isotone_in ?f X"
  proof-
    have C0: "\<forall>x1 \<in> X. \<forall>x2 \<in>X. ((x1 \<le> x2) \<longrightarrow> (principal_filter_in x2 X) \<subseteq> ( principal_filter_in x1 X))"
      by (metis empty_iff order_iso_filters)
    have C1: "\<forall>x1 \<in> X. \<forall>x2 \<in>X. ((x1 \<le> x2) \<longrightarrow> (principal_filter_in x2 A) \<subseteq> ( principal_filter_in x1 A))"
      by (smt (verit) mem_Collect_eq order_trans principal_filter_in_def subsetI)
    have C2:"\<forall>x1 \<in> X. \<forall>x2 \<in>X. ((x1 \<le> x2) \<longrightarrow>( Least (principal_filter_in x1 A)) \<le>( Least( principal_filter_in x2 A)))"
      by (meson A2 C1 least_is_minimum subset_iff)
    have C3:"\<forall>x1 \<in> X. \<forall> x2\<in>X. ((x1 \<le> x2) \<longrightarrow> (?f x1) \<le> (?f x2))"
      by (simp add: C2)
    with C3 show ?thesis
      by (simp add: isotone_in_def)
  qed
  have B1:"extensive_in ?f X"
    by (metis (no_types, lifting) A2 extensive_in_def lower_bound_lt_least mem_Collect_eq principal_filter_in_def)
  have B2:"idempotent_in ?f A"
    by (smt (verit) A0 A2 Pow_iff dual_order.refl idempotent_in_def mem_Collect_eq minimum_is_least minimum_is_unique order_trans principal_filter_in_def subset_iff)
  have B3:"\<forall>x \<in> X. (?f x = (?f (?f x)))"
    by (metis (no_types, lifting) A2 least_is_minimum mem_Collect_eq minimum_is_least principal_filter_in_def)
  have B4:"idempotent_in ?f X"
    by (metis (no_types, lifting) B3 idempotent_in_def)
  have B5:"closure_in ?f X"
    by (simp add: B0 B1 B4 closure_in_def pseudo_closure_in_def)
  with B5 show ?thesis by auto
qed

lemma crange_imp_pfilters_have_least:
  assumes A0:"closure_in f X" and
          A1: "(f`X) \<subseteq> X"
  shows "\<forall>x \<in> X. HasLeast((principal_filter_in x (f`X)))"
proof-
  have B0:"\<forall>x \<in> X. ((principal_filter_in x (f`X)) \<noteq> {}) "
  proof-
    have C0:"\<forall>x \<in> X. (f x)\<ge> x"
      by (meson A0 closure_in_def extensive_in_def pseudo_closure_in_def)
    have C1:"\<forall>x \<in>X. (f x) \<in> (f`X)"
      by blast
    have C2:"\<forall>x \<in> X. (f x) \<in>(principal_filter_in x (f`X)) "
      by (simp add: C0 principal_filter_in_def)
    with C2 show ?thesis by blast
  qed
  have B1: "\<forall>x \<in> X. \<forall>z \<in> ((principal_filter_in x (f`X))). x \<le> z"
    using principal_filter_in_def by auto
  have B2:"\<forall>x \<in> X. \<forall>z \<in> ((principal_filter_in x (f`X))). ((f x) \<le> (f z))"
    by (metis (no_types, lifting) A0 A1 closure_in_def isotone_in_def mem_Collect_eq principal_filter_in_def pseudo_closure_in_def subsetD)
  have B3:"\<forall>x \<in> X. \<forall>z \<in> ((principal_filter_in x (f`X))). ((f x) \<le> z )"
    by (metis (no_types, lifting) A0 B2 closure_in_def idempotent_in_def image_iff mem_Collect_eq principal_filter_in_def)
  have B4:"\<forall>x \<in> X. IsLeast (f x) (principal_filter_in x (f`X))"
    by (smt (verit) A0 B3 IsLeast_def IsLowerBound_def closure_in_def extensive_in_def imageI mem_Collect_eq principal_filter_in_def pseudo_closure_in_def)
  with B4 show ?thesis
    using HasLeast_def by blast
qed

end