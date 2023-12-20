theory Posets3
  imports Main
begin
hide_type Filter.filter
hide_const(open) List.list.Nil
no_notation List.list.Nil ("[]")  
no_notation Cons (infixr "#" 65)

declare [[show_types]]
definition is_upper_bound_of :: "'a::ord  \<Rightarrow> 'a::ord set  \<Rightarrow> bool" where
  "(is_upper_bound_of m A) \<equiv> (\<forall>a \<in> A. a \<le> m)"

definition upper_bounds_in :: " 'a::ord set \<Rightarrow> 'a::ord set  \<Rightarrow> 'a::ord set" where
  "(upper_bounds_in A X) =  {x\<in>X. \<forall>a \<in> A. x\<ge>a}"

definition upper_bounds_set::"'a::ord set \<Rightarrow> 'a::ord set" where
  "upper_bounds_set A = upper_bounds_in A UNIV"

definition has_ub_in ::" 'a::order set \<Rightarrow> 'a::order set  \<Rightarrow> bool" where
  "has_ub_in A X \<equiv>  \<exists>m \<in> X. is_upper_bound_of m A "

definition has_ub::" 'a::order set \<Rightarrow> bool" where
  "has_ub A \<equiv> has_ub_in A UNIV "


lemma upper_bounds_simp0:
  "\<And>A X. upper_bounds_in A X = (upper_bounds_set A  \<inter> X)"
  by (simp add: Collect_conj_eq inf_commute upper_bounds_in_def upper_bounds_set_def)


lemma upper_bounds_simp1:
  "\<And>x A X. x \<in> upper_bounds_in A X \<Longrightarrow> is_upper_bound_of x A"
  by (simp add: is_upper_bound_of_def upper_bounds_in_def)

lemma upper_bounds_simp2:
  "\<And>x A X. x \<in> upper_bounds_in A X \<Longrightarrow>  x \<in> X"
  by (simp add: is_upper_bound_of_def upper_bounds_in_def)

lemma upper_bounds_simp3:
  "\<And>x A X. is_upper_bound_of x A \<Longrightarrow> x \<in> X \<Longrightarrow> x \<in> upper_bounds_in A X"
  by (simp add: is_upper_bound_of_def upper_bounds_in_def)

lemma upper_bounds_simp4:
  assumes A0:"A \<subseteq> X" and
          A1:"A \<noteq> {}"
  shows "\<And>x . x \<in> upper_bounds_in A X \<longleftrightarrow> is_upper_bound_of x A \<and> x \<in> X"
proof
  fix x assume L:"x \<in> upper_bounds_in A X"
  show "is_upper_bound_of x A \<and> x \<in> X"
    using L upper_bounds_simp1 upper_bounds_simp2 by blast
  next
  fix x assume R:"is_upper_bound_of x A \<and> x \<in> X"
  show "x \<in> upper_bounds_in A X"
    by (simp add: R upper_bounds_simp3)
qed

lemma upper_bounds_in_trans0:
  "\<And>(x::'a::order set) A X. is_upper_bound_of x A \<Longrightarrow> y \<in> X \<Longrightarrow> x \<le> y \<Longrightarrow> y \<in> upper_bounds_in A X"
  by (meson dual_order.trans is_upper_bound_of_def upper_bounds_simp3)

lemma upper_bounds_in_trans1:
  "\<And>(x::'a::order set) A X.  x \<in> upper_bounds_in A X \<Longrightarrow> (y \<in> X \<and> x \<le> y) \<Longrightarrow> y \<in> upper_bounds_in A X"
  using upper_bounds_in_trans0 upper_bounds_simp1 by blast



subsubsection LowerBounds

definition is_lower_bound_of :: "'a::ord  \<Rightarrow> 'a::ord set  \<Rightarrow> bool" where
  "(is_lower_bound_of m A) \<equiv> (\<forall>a \<in> A. m \<le> a)"

definition lower_bounds_in :: " 'a::ord set \<Rightarrow> 'a::ord set  \<Rightarrow> 'a::ord set" where
  "(lower_bounds_in A X) =  {x\<in>X. \<forall>a \<in> A. x \<le> a}"

definition lower_bounds_set::"'a::ord set \<Rightarrow> 'a::ord set" where
  "lower_bounds_set A = lower_bounds_in A UNIV"

definition has_lb_in ::" 'a::ord set \<Rightarrow> 'a::ord set  \<Rightarrow> bool" where
  "has_lb_in A X \<equiv>  \<exists>m \<in> X. is_lower_bound_of m A "

definition has_lb::" 'a::ord set \<Rightarrow> bool" where
  "has_lb A \<equiv> has_lb_in A UNIV "

lemma lower_bounds_simp0:
  "\<And>A X. lower_bounds_in A X = (lower_bounds_set A \<inter> X)"
  by (simp add: Collect_conj_eq inf_commute lower_bounds_in_def lower_bounds_set_def)

lemma lower_bounds_simp1:
  "\<And>x A X. x \<in> lower_bounds_in A X \<Longrightarrow> is_lower_bound_of x A"
  by (simp add: is_lower_bound_of_def lower_bounds_in_def)

lemma lower_bounds_simp2:
  "\<And>x A X. x \<in> lower_bounds_in A X \<Longrightarrow> x \<in> X"
  by (simp add: is_lower_bound_of_def lower_bounds_in_def)

lemma lower_bounds_simp3:
  "\<And>x A X. is_lower_bound_of x A \<Longrightarrow> x \<in> X \<Longrightarrow> x \<in> lower_bounds_in A X"
  by (simp add: is_lower_bound_of_def lower_bounds_in_def)

lemma lower_bounds_simp4:
  assumes A0: "A \<subseteq> X" and
          A1: "A \<noteq> {}"
  shows "\<And>x . x \<in> lower_bounds_in A X \<longleftrightarrow> is_lower_bound_of x A \<and> x \<in> X"
proof
  fix x assume L: "x \<in> lower_bounds_in A X"
  show "is_lower_bound_of x A \<and> x \<in> X"
    using L lower_bounds_simp1 lower_bounds_simp2 by blast
  next
  fix x assume R: "is_lower_bound_of x A \<and> x \<in> X"
  show "x \<in> lower_bounds_in A X"
    by (simp add: R lower_bounds_simp3)
qed

lemma lower_bounds_in_trans0:
  "\<And>(x::'a::order set) A X. is_lower_bound_of x A \<Longrightarrow> y \<in> X \<Longrightarrow> x \<ge> y \<Longrightarrow> y \<in> lower_bounds_in A X"
  by (meson dual_order.trans is_lower_bound_of_def lower_bounds_simp3)


lemma upper_bounds_in_trans2:
  "\<And>(x::'a::order set) A X.  x \<in> lower_bounds_in A X \<Longrightarrow> (y \<in> X \<and> x \<ge> y) \<Longrightarrow> y \<in> lower_bounds_in A X"
  using lower_bounds_in_trans0 lower_bounds_simp1 by blast



subsection GreatestAndLeast

subsubsection Greatest
definition is_greatest::"'a::ord \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "is_greatest m A \<equiv> ((m \<in> A) \<and> (is_upper_bound_of m A))"

definition has_greatest :: "'a::ord set \<Rightarrow> bool" where
  "has_greatest A  \<equiv> \<exists>m. is_greatest m A"

definition greatest :: "'a::ord set \<Rightarrow> 'a::ord" where
  "greatest A = (THE m. (is_greatest m A))"

lemma greatest_unique0:
  assumes "has_greatest (A::'a::order set)"
  shows "\<And>m1 m2. (is_greatest m1 A)  \<and> (is_greatest m2 A) \<Longrightarrow> m1 = m2"
  by (simp add: dual_order.eq_iff is_greatest_def is_upper_bound_of_def)

lemma greatest_unique2:
  assumes "has_greatest (A::'a::order set)"
  shows "\<exists>!m. is_greatest m A"
  using assms greatest_unique0 has_greatest_def by blast

lemma greatest_simp0:
  fixes A::"'a::order set"
  assumes A0:"A \<noteq> {}" and A1:"has_greatest A"
  shows "is_greatest (greatest A) A"
  by (metis A1 greatest_def greatest_unique2 the_equality)

lemma maxset_not_empty: assumes "has_greatest A" shows "A\<noteq>{}"
  using assms has_greatest_def is_greatest_def by auto

lemma greatest_simp1:
  fixes A::"'a::order set"
  shows "\<lbrakk> x \<in> A; \<And>a. a \<in> A \<Longrightarrow> a \<le> x\<rbrakk> \<Longrightarrow> x=greatest A "
  by (metis empty_iff greatest_simp0 greatest_unique2 has_greatest_def is_greatest_def is_upper_bound_of_def)




subsubsection Least
definition is_least :: "'a::ord \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "is_least m A \<equiv> ((m \<in> A) \<and> (is_lower_bound_of m A))"

definition has_least :: "'a::ord set \<Rightarrow> bool" where
  "has_least A  \<equiv> \<exists>m. is_least m A"

definition least :: "'a::ord set \<Rightarrow> 'a::ord" where
  "least A = (THE m. (is_least m A))"

lemma least_unique0:
  assumes "has_least (A::'a::order set)"
  shows "\<And>m1 m2. (is_least m1 A) \<and> (is_least m2 A) \<Longrightarrow> m1 = m2"
  by (simp add: dual_order.eq_iff is_least_def is_lower_bound_of_def)

lemma least_unique1:
  assumes "has_least (A::'a::order set)"
  shows "\<exists>!m. is_least m A"
  using assms least_unique0 has_least_def by blast

lemma least_simp0:
  fixes A::"'a::order set"
  assumes A0: "A \<noteq> {}" and A1: "has_least A"
  shows "is_least (least A) A"
  by (metis A1 least_def least_unique1 the_equality)

lemma minset_not_empty: assumes "has_least A" shows "A \<noteq> {}"
  using assms has_least_def is_least_def by auto

lemma least_simp1:
  fixes A::"'a::order set"
  shows "\<lbrakk> x \<in> A; \<And>a. a \<in> A \<Longrightarrow> x \<le> a\<rbrakk> \<Longrightarrow> x = least A "
  by (metis empty_iff least_simp0 least_unique1 has_least_def is_least_def is_lower_bound_of_def)

subsection MaximaAndMinima
subsubsection Maxima

definition is_maximal:: "'a::ord \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "is_maximal m A \<equiv> (m \<in> A) \<and>  (\<forall>a \<in> A. \<not>(m<a))"

lemma is_maximal_in_order:
  fixes A::"'a::order set" and m::"'a::order"
  shows "is_maximal m A \<longleftrightarrow> ((m \<in> A) \<and> (\<forall>a \<in> A. m \<le> a\<longrightarrow> m=a))"
proof
  assume A0:"is_maximal m A"
  show "(m \<in> A) \<and> (\<forall>a \<in> A. m \<le> a\<longrightarrow> m=a)"
    by (meson A0 is_maximal_def order_neq_le_trans)
  next
  assume A1:"(m \<in> A) \<and> (\<forall>a \<in> A. m \<le> a\<longrightarrow> m=a)"
  show "is_maximal m A"
    by (simp add: A1 is_maximal_def nless_le)
qed


subsubsection Minima



definition is_minimal:: "'a::ord \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "is_minimal m A \<equiv> (m \<in> A) \<and>  (\<forall>a \<in> A. \<not>(m>a))"

lemma is_minimal_in_order:
  fixes A::"'a::order set" and m::"'a::order"
  shows "is_minimal m A \<longleftrightarrow> ((m \<in> A) \<and> (\<forall>a \<in> A. m \<ge> a\<longrightarrow> m=a))"
proof
  assume A0:"is_minimal m A"
  show "(m \<in> A) \<and> (\<forall>a \<in> A. m \<ge> a\<longrightarrow> m=a)"
    by (metis A0 is_minimal_def order_le_neq_trans)
   next
  assume A1:"(m \<in> A) \<and> (\<forall>a \<in> A. m \<ge> a\<longrightarrow> m=a)"
  show "is_minimal m A"
    by (metis A1 is_minimal_def nless_le)
qed

subsection Suprema
subsubsection Sup1

definition is_sup_in::"'a::ord \<Rightarrow> 'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "is_sup_in s A X \<equiv> is_least s (upper_bounds_in A X)"

definition is_sup::"'a::ord \<Rightarrow> 'a::ord set  \<Rightarrow> bool" where
  "is_sup s A \<equiv> (is_least s (upper_bounds_in A UNIV))"

definition SupIn :: "'a::ord set \<Rightarrow> 'a::ord set  \<Rightarrow> 'a::ord" where
  "SupIn A X =  least (upper_bounds_in A X)"

definition Sup::"'a::ord set \<Rightarrow>  'a::ord" where
  "Sup A = SupIn A UNIV"

definition has_a_sup_in:: "'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "has_a_sup_in A X  = has_least (upper_bounds_in A X)"

definition has_a_sup:: "'a::ord set  \<Rightarrow> bool" where
  "has_a_sup A  = has_a_sup_in A UNIV"

definition least_upperbound_in::"'a::ord \<Rightarrow> 'a::ord set \<Rightarrow> 'a::ord set\<Rightarrow> bool" where
  "least_upperbound_in m A X \<equiv>  (\<forall>z \<in> X. ((\<forall>a \<in> A. z \<ge> a)\<longrightarrow> (z \<ge> m) ))"

definition least_upperbound::"'a::ord  \<Rightarrow> 'a::ord set\<Rightarrow> bool" where
  "least_upperbound m A = least_upperbound_in m A UNIV"


lemma supin_simp0:
  fixes A::"'a::order set" and X::"'a::order set"
  assumes A0:"has_a_sup_in A X" and A1:"A \<subseteq> X"
  shows "has_least  (upper_bounds_in A X)"
  using A0 has_a_sup_in_def by blast

lemma supin_simp1:
  fixes A::"'a::order set" and X::"'a::order set"
  assumes A0:"has_a_sup_in A X" and A1:"A \<subseteq> X"
  shows " is_least (SupIn A X) (upper_bounds_in A X)"
  by (simp add: A0 A1 SupIn_def least_simp0 minset_not_empty supin_simp0) 

lemma supin_simp2:
  fixes A::"'a::order set" and X::"'a::order set"
  assumes A0:"has_a_sup_in A X" and A1:"A \<subseteq> X"
  shows "(SupIn A X) \<in> X"
  by (meson A0 A1 is_least_def supin_simp1 upper_bounds_simp2)

lemma sup_simp0:
  fixes A::"'a::order set"
  assumes A0:"has_a_sup A" 
  shows "has_least  (upper_bounds_set A)"
  by (metis assms has_a_sup_def has_a_sup_in_def upper_bounds_set_def)

lemma sup_simp1:
  fixes A::"'a::order set"
  assumes A0:"has_a_sup A"
  shows " is_least (Sup A) (upper_bounds_set A)"
  by (metis Sup_def assms has_a_sup_def supin_simp1 top_greatest upper_bounds_set_def)

lemma sup_is_lb:
  fixes A::"'a::order set"
  assumes A0:"has_a_sup A"
  shows "Sup A \<in> upper_bounds_set A"
  using assms is_least_def sup_simp1 by blast

lemma supin_is_lb:
  fixes A::"'a::order set" and X::"'a::order set"
  assumes A0:"has_a_sup_in A X" and A1:"A \<subseteq> X"
  shows "SupIn A X \<in> upper_bounds_in A X"
  by (meson A0 A1 is_least_def supin_simp1)

lemma sup_is_unique0:
  assumes "has_a_sup (A::'a::order set)"
  shows "\<And>m1 m2. (is_sup m1 A) \<and> (is_sup m2 A) \<Longrightarrow> m1 = m2"
  by (meson has_least_def is_sup_def least_unique0)

lemma supin_is_unique0:
  assumes "has_a_sup_in (A::'a::order set)  (X::'a::order set)"
  shows "\<And>m1 m2. (is_sup_in m1 A X) \<and> (is_sup_in m2 A X) \<Longrightarrow> m1 = m2"
  by (meson has_least_def is_sup_in_def least_unique0)

lemma sup_is_unique1:
  assumes "has_a_sup (A::'a::order set)"
  shows "\<exists>!m. is_sup m A"
  by (metis assms is_sup_def sup_is_unique0 sup_simp1 upper_bounds_set_def)

lemma supin_is_unique1:
  assumes "has_a_sup_in (A::'a::order set) (X::'a::order set)"
  shows "\<exists>!m. is_sup_in m A X"
  by (metis assms has_a_sup_in_def is_sup_in_def least_unique1)

lemma ub_simp0:
  fixes A::"'a::order set" and X::"'a::order set"
  shows "(\<And>y. y \<in> A \<Longrightarrow> y \<le> x) \<Longrightarrow> is_upper_bound_of x A"
  by (simp add: is_upper_bound_of_def)

lemma ub_simp1:
  fixes A::"'a::order set"
  shows "(\<And>y. y \<in> A \<Longrightarrow> y \<le> x) \<Longrightarrow> x \<in> upper_bounds_set A"
  by (simp add: is_upper_bound_of_def upper_bounds_set_def upper_bounds_simp3)


lemma ub_in_simp0:
  fixes A::"'a::order set" and X::"'a::order set"
  assumes A0:"A \<subseteq> X" and A1:"A \<noteq> {}"
  shows "x \<in> X \<Longrightarrow> (\<And>y. y \<in> A \<Longrightarrow> y \<le> x) \<Longrightarrow> is_upper_bound_of x A "
  by (simp add: ub_simp0)

lemma ub_in_simp1:
  fixes A::"'a::order set" and X::"'a::order set"
  assumes A0:"A \<subseteq> X" and A1:"A \<noteq> {}"
  shows "(\<And>y. y \<in> A \<Longrightarrow> y \<le> x) \<Longrightarrow> x \<in> X \<Longrightarrow> x \<in> upper_bounds_in A X"
  by (simp add: ub_simp0 upper_bounds_simp3)




lemma lb_simp0:
  fixes A::"'a::order set" and X::"'a::order set"
  shows "(\<And>y. y \<in> A \<Longrightarrow> y \<ge> x) \<Longrightarrow> is_lower_bound_of x A"
  by (simp add: is_lower_bound_of_def)

lemma lb_simp1:
  fixes A::"'a::order set"
  shows "(\<And>y. y \<in> A \<Longrightarrow> y \<ge> x) \<Longrightarrow> x \<in> lower_bounds_set A"
  by (simp add: is_lower_bound_of_def lower_bounds_set_def lower_bounds_simp3)



lemma supin_simp3:
  fixes A::"'a::order set" and X::"'a::order set"
  assumes A0:"has_a_sup_in A X" and A1:"A \<subseteq> X"
  shows "(\<And>y. (\<And>z. z \<in> A \<Longrightarrow> z \<le> y) \<Longrightarrow> x \<le> y) \<Longrightarrow> is_lower_bound_of x (upper_bounds_in A X)"
  by (meson is_upper_bound_of_def lb_simp0 upper_bounds_simp1)
  
lemma sup_simp3:
  fixes A::"'a::order set"
  assumes A0:"has_a_sup A"
  shows "(\<And>y. (\<And>z. z \<in> A \<Longrightarrow> z \<le> y) \<Longrightarrow> x \<le> y) \<Longrightarrow> is_lower_bound_of x (upper_bounds_set A)"
  by (metis is_upper_bound_of_def lb_simp0 upper_bounds_set_def upper_bounds_simp1)
  

lemma sup_simp4:
  fixes A::"'a::order set"
  assumes A0:"has_a_sup A"
  shows "(\<And>y. y \<in> A \<Longrightarrow> y \<le> x) \<Longrightarrow> (\<And>y. (\<And>z. z \<in> A \<Longrightarrow> z \<le> y) \<Longrightarrow> x \<le> y) \<Longrightarrow> Sup A = x"
  by (meson assms has_least_def is_least_def least_unique0 sup_simp1 sup_simp3 ub_simp1)


lemma supin_simp4:
  fixes A::"'a::order set" and X::"'a::order set"
  assumes A0:"has_a_sup_in A X" and A1:"A \<subseteq> X" and A2:"A \<noteq> {}"
  shows "x \<in> X \<Longrightarrow> (\<And>y. y \<in> A \<Longrightarrow> y \<le> x) \<Longrightarrow> (\<And>y. (\<And>z. z \<in> A \<Longrightarrow> z \<le> y) \<Longrightarrow> x \<le> y) \<Longrightarrow> SupIn A X = x"
  by (metis SupIn_def is_upper_bound_of_def least_simp1 upper_bounds_simp1 upper_bounds_simp3)
  
subsubsection Sup2

lemma supin_eq1:
  fixes A::"'a::order set" and X::"'a::order set"
  assumes A0:"A \<subseteq> X" and A1:"A \<noteq> {}"
  shows "\<forall>m. is_sup_in m A X \<longleftrightarrow> (m \<in> upper_bounds_in A X) \<and> (least_upperbound_in m A X)"
proof-
  have LtR:"\<forall>m. is_sup_in m A X \<longrightarrow> (m \<in> upper_bounds_in A X) \<and> (least_upperbound_in m A X)"
    by (simp add: A0 A1 is_least_def is_lower_bound_of_def is_sup_in_def least_upperbound_in_def ub_in_simp1)
  have RtL:"\<forall>m. (m \<in> upper_bounds_in A X) \<and> (least_upperbound_in m A X)\<longrightarrow> is_sup_in m A X"
    by (simp add: is_least_def is_lower_bound_of_def is_sup_in_def least_upperbound_in_def upper_bounds_in_def)
  show ?thesis
    using LtR RtL by blast
qed

lemma sup_eq1:
  fixes A::"'a::order set"
  shows "\<forall>m. is_sup m A \<longleftrightarrow> (m \<in> upper_bounds_set A) \<and> (least_upperbound m A)"
  by (simp add: is_least_def is_lower_bound_of_def is_sup_def least_upperbound_def least_upperbound_in_def upper_bounds_in_def upper_bounds_set_def)

lemma supin_eq2:
  fixes A::"'a::order set" and X::"'a::order set"
  assumes A0:"A \<subseteq> X" and A1:"A \<noteq> {}"
  shows "\<forall>m. is_sup_in m A X \<longleftrightarrow> ((m \<in> X) \<and>  (\<forall>z \<in> X. ((z \<ge> m) \<longleftrightarrow> (\<forall>a \<in> A. z \<ge> a))) )"
proof-
  have LtR:"\<forall>m. is_sup_in m A X \<longrightarrow> ((m \<in> X) \<and>  (\<forall>z \<in> X. ((z \<ge> m) \<longleftrightarrow> (\<forall>a \<in> A. z \<ge> a))) )"
    by (meson dual_order.trans is_least_def is_lower_bound_of_def is_sup_in_def is_upper_bound_of_def ub_in_simp1 upper_bounds_simp1 upper_bounds_simp2 upper_bounds_simp3)
  have RtL:"\<forall>m. ((m \<in> X) \<and>  (\<forall>z \<in> X. ((z \<ge> m) \<longleftrightarrow> (\<forall>a \<in> A. z \<ge> a))))  \<longrightarrow>  (is_sup_in m A X)"
    by (metis A0 A1 least_upperbound_in_def order_refl supin_eq1 ub_in_simp0 upper_bounds_simp3)
  show ?thesis
    using LtR RtL by blast
qed



subsection Infima

subsubsection Inf1

end
