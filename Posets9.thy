theory Posets9
  imports Main
begin

section Notation
hide_const(open) List.list.Nil
no_notation List.list.Nil ("[]")  
no_notation Cons (infixr "#" 65) 
hide_type list
hide_const rev

declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]

section Fpow
abbreviation Fpow_ne::"'a set \<Rightarrow> 'a set set" where
  "Fpow_ne A \<equiv> (Fpow A)-{{}}"

abbreviation Dpow::"'a set \<Rightarrow> 'a set set set" where
  "Dpow A \<equiv> (Pow (Pow A))"

abbreviation Pow_ne::"'a set \<Rightarrow> 'a set set" where
  "Pow_ne A \<equiv> (Pow A) - {{}}"

lemma pow_ne_imp:
  "a \<in> Pow_ne A \<Longrightarrow> a \<noteq> {}"
  by blast

lemma fpow_ne_imp:
  "a \<in> Fpow_ne A \<Longrightarrow> a \<noteq> {}"
  by blast

lemma pow_ne_imp2:
  "a \<in> Pow_ne A \<Longrightarrow> a \<subseteq> A"
  by blast

lemma fpow_ne_imp2:
  "a \<in> Fpow_ne A \<Longrightarrow> a \<subseteq> A"
  by (simp add: Fpow_Pow_finite)

lemma pow_ne_imp3:
  "a \<in> Pow_ne A \<Longrightarrow> a \<in> Pow A"
  by blast

lemma fpow_ne_imp3:
  "a \<in> Fpow_ne A \<Longrightarrow> a \<in> Pow A"
  by (simp add: fpow_ne_imp2)

lemma pow_ne_imp4:
  "C \<subseteq> X \<Longrightarrow> A \<in> Pow_ne C \<Longrightarrow> A \<in> Pow_ne X"
  by blast

lemma fpow_ne_imp4:
  "C \<subseteq> X \<Longrightarrow> A \<in> Fpow_ne C \<Longrightarrow> A \<in> Fpow_ne X"
  using Fpow_mono by auto

lemma pow_ne_if:
  "a \<noteq> {} \<Longrightarrow> a \<in> Pow A \<Longrightarrow>  a \<in> Pow_ne A"
  by blast

lemma fpow_ne_if:
  "a \<noteq> {} \<Longrightarrow> a \<in> Pow A \<Longrightarrow> finite a \<Longrightarrow>  a \<in> Fpow_ne A"
  by (simp add: Fpow_Pow_finite)
          
lemma fpow_ne_mem_iff:
  "a \<in> Fpow_ne A \<longleftrightarrow> (finite a \<and> a \<subseteq> A \<and> a \<noteq> {})"
  using Fpow_def by blast
 

abbreviation is_ne::"'a set \<Rightarrow> bool" where
  "is_ne A \<equiv> A  \<noteq> {}"


section Bounds
subsection BoundPredicate
definition lb::"'a::ord \<Rightarrow> 'a::ord set \<Rightarrow> bool"  (infix "lb" 50) where
  "b lb A \<equiv> (\<forall>a \<in> A. b \<le> a)"

lemma is_lb_simp1:
  "b lb A \<Longrightarrow> a \<in> A \<Longrightarrow> b \<le> a"
  by (simp add: lb_def)

lemma lb_subset:
  "b lb A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> b lb B"
  by (simp add: in_mono lb_def)

lemma is_lb_simp2:
  "\<And>b. (\<And>a. a \<in> A \<Longrightarrow> b \<le> a) \<Longrightarrow> b lb A"
  by (simp add: lb_def)

definition ub::"'a::ord \<Rightarrow> 'a::ord set \<Rightarrow> bool"  (infix "ub" 50) where
  "b ub A \<equiv> (\<forall>a \<in> A. a \<le> b)"

lemma is_ub_simp1:
  "b ub A \<Longrightarrow> a \<in> A \<Longrightarrow> a \<le> b"
  by (simp add: ub_def)

lemma ub_subset:
  "b ub A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> b ub B"
  by (simp add: in_mono ub_def)

lemma is_ub_simp2:
  "\<And>b. (\<And>a. a \<in> A \<Longrightarrow> a \<le> b) \<Longrightarrow> b ub A"
  by (simp add: ub_def)

lemma ub_singleton_simp:
  "(a::'a::order) ub {a}"
  by (simp add: ub_def)

lemma lb_singleton_simp:
  "(a::'a::order) lb {a}"
  by (simp add: lb_def)

definition has_lb::"'a::ord set \<Rightarrow>  'a::ord set \<Rightarrow> bool" where
  "has_lb A B \<equiv> (\<exists>b \<in> B. b lb A)"

definition has_ub::"'a::ord set \<Rightarrow>  'a::ord set \<Rightarrow> bool" where
  "has_ub A B \<equiv> (\<exists>b \<in> B. b ub A)"


subsection SetOfBounds
definition ub_set::"'a::ord set \<Rightarrow> 'a::ord set  \<Rightarrow> 'a::ord set" where
  "ub_set A B \<equiv> {b \<in> B. b ub A}"

definition lb_set::"'a::ord set \<Rightarrow> 'a::ord set  \<Rightarrow> 'a::ord set" where
  "lb_set A B \<equiv> {b \<in> B. b lb A}"

lemma ub_set_subset_space:
  "ub_set A B \<subseteq> B"
  by (simp add: ub_set_def)

lemma lb_set_subset_space:
  "lb_set A B \<subseteq> B"
  by (simp add: lb_set_def)

lemma ub_set_memd:
  "b \<in> ub_set A B \<Longrightarrow> x \<in> A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> x \<le> b \<and> b \<in> B"
  by (simp add: ub_def ub_set_def)

lemma lb_set_memd:
  "b \<in> lb_set A B \<Longrightarrow> x \<in> A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> x \<ge> b \<and> b \<in> B"
  by (simp add: lb_def lb_set_def)

lemma ub_set_restrict1:
  "X \<subseteq> Y \<Longrightarrow>  ub_set A X = X \<inter> ub_set A Y"
  by(auto simp add:ub_set_def)

lemma lb_set_restrict1:
  " X \<subseteq> Y \<Longrightarrow>  lb_set A X = X \<inter> lb_set A Y"
  by(auto simp add:lb_set_def)

lemma has_ub_iff:
  "has_ub A B \<longleftrightarrow> is_ne (ub_set A B)"
  by(auto simp add:has_ub_def ub_set_def)

lemma has_lb_iff:
  "has_lb A B \<longleftrightarrow> is_ne (lb_set A B)"
  by(auto simp add:has_lb_def lb_set_def)

lemma ub_set_mem:
  "\<And>(A::'a::order set) X x u. (u \<in> ub_set A X  \<and> x \<in> A) \<Longrightarrow> (x \<le> u \<and> u \<in> X) "
  by (simp add: ub_set_def ub_def)

lemma lb_set_mem:
  "\<And>(A::'a::order set) X x l. (l \<in> lb_set A X  \<and> x \<in> A) \<Longrightarrow> (l \<le> x \<and> l \<in> X) "
  by (simp add: lb_set_def lb_def)

lemma ub_set_subset2:
  "B \<subseteq> X \<Longrightarrow> ub_set A B \<subseteq> X"
  by (simp add: Collect_conj_eq inf.coboundedI1 ub_set_def)

lemma lb_set_subset2:
  "B \<subseteq> X \<Longrightarrow> lb_set A B \<subseteq> X"
  by (simp add: Collect_conj_eq inf.coboundedI1 lb_set_def)

lemma ub_set_imp:
  "\<And>(A::'a::order set) X u. (u \<in> ub_set A X) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> x \<le> u)"
  by (simp add: ub_set_def ub_def)

lemma lb_set_imp:
  "\<And>(A::'a::order set) X l. (l \<in> lb_set A X) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> l \<le> x)"
  by (simp add: lb_set_def lb_def)

lemma ub_set_imp1:
  "u \<in> ub_set A X \<Longrightarrow> u ub A"
  by (simp add: ub_set_def)

lemma ub_set_if:
  " u ub A \<Longrightarrow> u \<in> X \<Longrightarrow> u \<in> ub_set A X"
  by (simp add: ub_set_def)

lemma lb_set_imp1:
  "l \<in> lb_set A X \<Longrightarrow> l lb A"
  by (simp add: lb_set_def)

lemma lb_set_if:
  "l lb A \<Longrightarrow> l \<in> X \<Longrightarrow> l \<in> lb_set A X"
  by (simp add: lb_set_def)

lemma ub_set_imp2:
  "u \<in> ub_set A X \<Longrightarrow> u \<in> X"
  by (simp add: ub_set_def)

lemma lb_set_imp2:
  "l \<in> lb_set A X \<Longrightarrow> l \<in> X"
  by (simp add: lb_set_def)

lemma ub_set_elm:
  "\<And>(A::'a::order set) X u. (\<And>a. a \<in> A \<Longrightarrow> a \<le> u) \<Longrightarrow> u \<in> X \<Longrightarrow> u \<in> ub_set A X"
  by (simp add: ub_set_def ub_def)

lemma lb_set_elm:
  "\<And>(A::'a::order set) X l. (\<And>a. a \<in> A \<Longrightarrow> l \<le> a) \<Longrightarrow> l \<in> X \<Longrightarrow> l \<in> lb_set A X"
  by (simp add: lb_set_def lb_def)

lemma ub_set_mem_iff:
  "\<forall>x. x \<in> ub_set A B \<longleftrightarrow> (x \<in> B) \<and> (\<forall>a. a \<in> A \<longrightarrow> a \<le> x )"
  using ub_def ub_set_def by fastforce

lemma lb_set_mem_iff:
  "\<forall>x. x \<in> lb_set A B \<longleftrightarrow> (x \<in> B) \<and> (\<forall>a. a \<in> A \<longrightarrow> x \<le> a )"
  using lb_def lb_set_def by fastforce

lemma lb_set_exp:
  "lb_set A B = {b \<in> B. (\<forall>a. a \<in> A \<longrightarrow> b \<le> a)}"
  by(auto simp add:lb_set_def lb_def)

lemma ub_set_exp:
  "ub_set A B = {b \<in> B. (\<forall>a. a \<in> A \<longrightarrow> b \<ge> a)}"
  by(auto simp add:ub_set_def ub_def)

subsection SetOfBoundsAsOperator

lemma ub_set_antitone1:
  " A \<subseteq> B \<Longrightarrow>  ub_set B X \<subseteq> ub_set A X"
  by(simp add: subset_eq ub_set_def ub_def)

lemma lb_set_antitone1:
  " A \<subseteq> B \<Longrightarrow>  lb_set B X \<subseteq> lb_set A X"
  by(simp add: subset_eq lb_set_def lb_def)

lemma ub_set_in_isotone2:
  "B \<subseteq> X \<Longrightarrow>  ub_set A B \<subseteq> ub_set A X"
  by(simp add: subset_eq ub_set_def ub_def)

lemma lb_set_in_isotone2:
  "B \<subseteq> X \<Longrightarrow>  lb_set A B \<subseteq> lb_set A X"
  by(simp add: subset_eq lb_set_def lb_def)

lemma ub_set_in_degenerate:
  "ub_set {} X = X"
  by (simp add: ub_set_def ub_def)

lemma lb_set_in_degenerate:
  "lb_set {} X = X"
  by (simp add: lb_set_def lb_def)

lemma ub_set_in_singleton:
  "ub_set {a} X  = {x \<in> X. a \<le> x}"
  by (simp add: set_eq_iff ub_set_mem_iff)

lemma ub_set_singleton_antitone:
  "(a::'a::order) \<le> b \<Longrightarrow> ub_set {b} X \<subseteq> ub_set {a} X"
  by(auto simp add:ub_set_def ub_def)

lemma lb_set_in_singleton:
  "lb_set {a} X  = {x \<in> X. x \<le> a}"
  by (simp add: set_eq_iff lb_set_mem_iff)

lemma lb_set_singleton_isotone:
  "(a::'a::order) \<le> b \<Longrightarrow> lb_set {a} X \<subseteq> lb_set {b} X"
  by(auto simp add:lb_set_def lb_def)

lemma singleton_in_lb_set:
  "(a::'a::order) \<in> X \<Longrightarrow> a \<in> ub_set {a} X"
  by (simp add: ub_set_if ub_singleton_simp)

lemma singleton_in_ub_set:
  "(a::'a::order) \<in> X \<Longrightarrow> a \<in> lb_set {a} X"
  by (simp add: lb_set_if lb_singleton_simp)

lemma lb_subset_imp_lt:
  "(a::'a::order) \<in> X \<and> b \<in> X \<Longrightarrow>  lb_set {a} X \<subseteq> lb_set {b} X \<Longrightarrow> a \<le> b"
  by (meson in_mono lb_set_imp singletonI singleton_in_ub_set)

lemma ub_subset_imp_gt:
  "(a::'a::order) \<in> X \<and> b \<in> X \<Longrightarrow>  ub_set {a} X \<subseteq> ub_set {b} X \<Longrightarrow> a \<ge> b"
  by (meson in_mono singletonI singleton_in_lb_set ub_set_imp)

lemma lb_embedding:
  "(a::'a::order) \<in> X \<and> b \<in> X  \<Longrightarrow>(lb_set {a} X \<subseteq> lb_set {b} X  \<longleftrightarrow> a \<le> b) "
  by (meson lb_set_singleton_isotone lb_subset_imp_lt)

lemma ub_embedding:
  "(a::'a::order) \<in> X \<and> b \<in> X  \<Longrightarrow>(ub_set {a} X \<subseteq> ub_set {b} X  \<longleftrightarrow> a \<ge> b) "
  by (meson ub_set_singleton_antitone ub_subset_imp_gt)

lemma ub_set_in_from_principal:
  "A \<noteq> {} \<Longrightarrow> ub_set A X = (\<Inter>a \<in> A. ub_set {a} X)"
  by(auto simp add:ub_set_def ub_def)

lemma lb_set_in_from_principal:
  "A \<noteq> {} \<Longrightarrow> lb_set A X = (\<Inter>a \<in> A. lb_set {a} X)"
  by(auto simp add:lb_set_def lb_def)

context fixes A X::"'a::ord set"  assumes A0:"A \<subseteq> X"
begin
lemma ul_extensive:
  "A \<subseteq> (ub_set (lb_set A X) X)"
  apply(auto simp add:ub_set_def ub_def lb_set_def lb_def) using A0 by blast

lemma lu_extensive:
  "A \<subseteq> (lb_set (ub_set A X) X)"
  apply(auto simp add:ub_set_def ub_def lb_set_def lb_def) using A0 by blast
end

lemma ul_isotone:
  "\<And>A B X.  A \<subseteq> B \<Longrightarrow>  (ub_set (lb_set A X) X) \<subseteq> (ub_set (lb_set B X) X)"
  by (simp add: lb_set_antitone1 ub_set_antitone1)

lemma lu_isotone:
  "\<And>A B X.  A \<subseteq> B \<Longrightarrow>  (lb_set (ub_set A X) X) \<subseteq> (lb_set (ub_set B X) X)"
  by (simp add: lb_set_antitone1 ub_set_antitone1)

lemma ulu_eq_u:
  "A \<subseteq> X \<Longrightarrow> ub_set (lb_set (ub_set A X) X) X = ub_set A X"
  by (simp add: lu_extensive subset_antisym ub_set_antitone1 ub_set_subset_space ul_extensive)

lemma lul_eq_l:
  "A \<subseteq> X \<Longrightarrow> lb_set (ub_set (lb_set A X) X) X = lb_set A X"
  by (simp add: lb_set_antitone1 lb_set_subset_space lu_extensive subset_antisym ul_extensive)

lemma lu_idempotent:
  "lb_set (ub_set (lb_set (ub_set A X) X ) X) X = lb_set (ub_set A X) X "
  by (simp add: lul_eq_l ub_set_subset_space)

lemma ul_idempotent:
  "ub_set (lb_set (ub_set (lb_set A X) X ) X) X = ub_set (lb_set A X) X "
  by (simp add: lb_set_subset_space ulu_eq_u)

lemma set_subset_lb_ub:
  "A \<subseteq> X \<Longrightarrow> b \<in> ub_set A X \<Longrightarrow> A \<subseteq> lb_set {b} X"
  by (simp add: lb_set_in_singleton subset_eq ub_set_mem_iff)

lemma set_subset_ub_lb:
  "A \<subseteq> X \<Longrightarrow> b \<in> lb_set A X \<Longrightarrow> A \<subseteq> ub_set {b} X"
  by (simp add: ub_set_in_singleton subset_eq lb_set_mem_iff)

section LeastGreatest

definition is_max::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_max m A \<equiv> m \<in> ub_set A A"

definition is_min::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_min m A \<equiv> m \<in> lb_set A A"

definition has_max::"'a::order set \<Rightarrow> bool" where
  "has_max A \<equiv> (\<exists>m. is_max m A)"

definition has_min::"'a::order set \<Rightarrow> bool" where
  "has_min A \<equiv> (\<exists>m. is_min m A)"

definition max::"'a::order set \<Rightarrow> 'a::order" where
  "max A \<equiv> (THE m. is_max m A)"

definition min::"'a::order set \<Rightarrow> 'a::order" where
  "min A \<equiv> (THE m. is_min m A)"

subsection PredicateIs

lemma is_max_imp:
  "is_max x A \<Longrightarrow> (x \<in> A \<and> x \<in> ub_set A UNIV)"
  by(simp add: is_max_def ub_set_mem_iff)

lemma is_max_imp1:
  "is_max x A \<Longrightarrow> x \<in> A"
  by(simp add: is_max_def ub_set_mem_iff)

lemma is_max_imp2:
  "is_max x A \<Longrightarrow>x \<in> ub_set A UNIV"
  by(simp add: is_max_def ub_set_mem_iff)    

lemma is_max_imp3:
  "\<And>A x. is_max x A \<Longrightarrow> A \<subseteq> X \<Longrightarrow> x \<in> ub_set A X"
  by(simp add: is_max_def in_mono ub_set_mem_iff)

lemma is_min_imp:
  "is_min x A \<Longrightarrow> (x \<in> A \<and> x \<in> lb_set A UNIV)"
  by(simp add: is_min_def lb_set_mem_iff)

lemma is_min_imp1:
  "is_min x A \<Longrightarrow> x \<in> A"
  by(simp add: is_min_def lb_set_mem_iff)

lemma is_min_imp2:
  "is_min x A \<Longrightarrow>x \<in> lb_set A UNIV"
  by(simp add: is_min_def lb_set_mem_iff)    

lemma is_min_imp3:
  "is_min x A \<Longrightarrow> A \<subseteq> X \<Longrightarrow> x \<in> lb_set A X"
  by(simp add: is_min_def in_mono lb_set_mem_iff)

lemma is_max_if1:
  "(x \<in> A \<and> x \<in> ub_set A UNIV) \<Longrightarrow> is_max x A"
  by (simp add: is_max_def ub_set_mem_iff)

lemma is_min_if1:
  "(x \<in> A \<and> x \<in> lb_set A UNIV) \<Longrightarrow> is_min x A"
  by (simp add: is_min_def lb_set_mem_iff)
                                   
lemma is_max_if2:
  " x \<in> A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> x) \<Longrightarrow> is_max x A"
  by (simp add: is_max_if1 ub_set_mem_iff)
                    
lemma is_min_if2:
  "x \<in> A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> x \<le> a) \<Longrightarrow> is_min x A"
  by (simp add: is_min_if1 lb_set_mem_iff)
           
lemma is_max_imp_has_max:
  "is_max m A \<Longrightarrow> has_max A"
  using has_max_def by auto

lemma is_min_imp_has_min:
  "is_min m A \<Longrightarrow> has_min A"
  using has_min_def by auto     

lemma is_max_iff:
  "is_max m A \<longleftrightarrow> m \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> a \<le> m )"
  by (simp add: is_max_def ub_set_mem_iff)

lemma is_max_iff2:
  "is_max m A \<longleftrightarrow> m \<in> A \<and> m ub A"
  by (simp add: is_max_def ub_set_def ub_def)

lemma is_min_iff:
  "is_min m A \<longleftrightarrow> m \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> m \<le> a )"
  by (simp add: is_min_def lb_set_mem_iff)

lemma is_min_iff2:
  "is_min m A \<longleftrightarrow> m \<in> A \<and> m lb A"
  by (simp add: is_min_def lb_set_def lb_def)

lemma max_imp_ne:
  "is_max m A \<Longrightarrow> A \<noteq> {}"
  using is_max_imp1 by auto

lemma min_imp_ne:
  "is_min m A \<Longrightarrow> A \<noteq> {}"
  using is_min_imp1 by auto

lemma has_max_imp_ne:
  "has_max A \<Longrightarrow> A \<noteq> {}"
  using has_max_def max_imp_ne by blast

lemma has_min_imp_ne:
  "has_min A \<Longrightarrow> A \<noteq> {}"
  using has_min_def min_imp_ne by blast

lemma is_max_isotone1:
  "\<And>A B ma mb. A \<subseteq> B \<and> (is_max ma A) \<and> ( is_max mb B) \<longrightarrow>  ma \<le> mb"
  using is_max_iff by blast

lemma is_max_isotone2:
  " A \<subseteq> B \<Longrightarrow> (is_max ma A) \<Longrightarrow> ( is_max mb B) \<Longrightarrow>  ma \<le> mb"
  using is_max_iff by blast

lemma is_min_antitone1:
  "\<And>A B ma mb. A \<subseteq> B \<and> (is_min ma A) \<and> ( is_min mb B) \<longrightarrow>  mb \<le> ma"
  using is_min_iff by blast

lemma is_min_antitone2:
  "A \<subseteq> B \<Longrightarrow> (is_min ma A) \<Longrightarrow> ( is_min mb B) \<Longrightarrow>  mb \<le> ma"
  using is_min_iff by blast

lemma is_max_top0:
  "(\<And>x. x \<le> t) \<Longrightarrow> is_max t UNIV"
  by (simp add: is_max_iff)

lemma is_max_top:
  fixes top::"'a::order"
  assumes is_top:"\<forall>x. x \<le> top"
  shows "is_max top UNIV"
  by (simp add: is_max_iff is_top)
     
lemma is_min_bot:
  fixes bot::"'a::order"
  assumes is_bot:"\<forall>x. bot \<le> x"
  shows "is_min bot UNIV"
  by (simp add: is_min_iff is_bot)
     
lemma is_max_singleton:
  "is_max x {x}"
  by (simp add: is_max_iff)

lemma is_min_singleton:
  "is_min x {x}"
  by (simp add: is_min_iff)

lemma is_max_lb_set_singleton1:
  "is_max x (lb_set {x} UNIV)"
  by (simp add: is_max_iff lb_set_imp singleton_in_ub_set)
  
lemma is_min_ub_set_singleton1:
  "is_min x (ub_set {x} UNIV)"
  by (simp add: is_min_iff ub_set_imp singleton_in_lb_set)
  
lemma is_max_lb_set_singleton2:
  "x \<in> X \<Longrightarrow> is_max x (lb_set {x} X)"
  by (simp add: is_max_iff lb_set_imp singleton_in_ub_set)
  
lemma is_min_ub_set_singleton2:
  "x \<in> X \<Longrightarrow> is_min x (ub_set {x} X)"
  by (simp add: is_min_iff ub_set_imp singleton_in_lb_set)
  
lemma is_max_imp_set:
  " is_max m X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> m \<in> ub_set A X"
  by (simp add: is_max_iff subset_eq ub_set_elm)

lemma is_min_imp_set:
  "is_min m X\<Longrightarrow>  A \<subseteq> X \<Longrightarrow> m \<in> lb_set A X"
  by (simp add: is_min_iff subset_eq lb_set_elm)

lemma is_max_subset:
  "is_max m B \<Longrightarrow>A \<subseteq> B  \<Longrightarrow>  m \<in> A \<Longrightarrow> is_max m A"
  by (simp add: in_mono is_max_iff)

lemma is_min_subset:
  "is_min m B\<Longrightarrow>  A \<subseteq> B \<Longrightarrow>  m \<in> A \<Longrightarrow> is_min m A"
  by (simp add: in_mono is_min_iff)

subsection ExistentialHas

lemma has_max_iff:
  "has_max A \<longleftrightarrow> (\<exists>m.  m \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> a \<le> m ))"
  by (simp add: has_max_def is_max_iff)

lemma has_min_iff:
  "has_min A \<longleftrightarrow> (\<exists>m.  m \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> m \<le> a ))"
  by (simp add: has_min_def is_min_iff)

lemma has_max_iff2:
  "has_max A \<longleftrightarrow> (\<exists>m. is_max m A)"
  by (simp add: has_max_def is_max_iff)

lemma has_min_iff2:
  "has_min A \<longleftrightarrow> (\<exists>m. is_min m A)"
  by (simp add: has_min_def is_min_iff)

lemma max_unique:
  "is_max m1 A \<Longrightarrow> is_max m2 A \<Longrightarrow> m1=m2"
  by (meson Orderings.order_eq_iff is_max_iff)  

lemma min_unique:
  "is_min m1 A \<Longrightarrow> is_min m2 A \<Longrightarrow> m1=m2"
  by (meson Orderings.order_eq_iff is_min_iff)  

lemma if_has_max_max_unique:
  "has_max (A::'a::order set) \<Longrightarrow> \<exists>!m. is_max m A"
  using has_max_iff2 max_unique by blast

lemma if_has_min_min_unique:
  "has_min (A::'a::order set) \<Longrightarrow> \<exists>!m. is_min m A"
  using has_min_iff2 min_unique by blast

lemma has_max_singleton:
  "has_max {x::'a::order}"
  using has_max_def is_max_singleton by auto

lemma has_min_singleton:
  "has_min {x::'a::order}"
  using has_min_def is_min_singleton by auto

lemma is_min_to_has_min1:
  "(\<And>m A. is_min m A \<Longrightarrow> P A m) \<Longrightarrow> (has_min A \<Longrightarrow> P A (min A))"
  by (metis min_def if_has_min_min_unique the_equality)

lemma is_max_to_has_max1:
  "(\<And>m A. is_max m A \<Longrightarrow> P A m) \<Longrightarrow> (has_max A \<Longrightarrow> P A (max A))"
  by (metis max_def if_has_max_max_unique the_equality)

subsection Operator

lemma max_top:
  fixes top::"'a::order"
  assumes is_top:"\<forall>x. x \<le> top"
  shows "has_max (UNIV::'a::order set)"
  using has_max_def is_max_top is_top by auto

lemma min_bot:
  fixes bot::"'a::order"
  assumes is_bot:"\<forall>x. bot \<le> x"
  shows "has_min (UNIV::'a::order set)"
  using has_min_def is_min_bot is_bot by auto

lemma max_if:
  "is_max m A \<Longrightarrow> m = max A"
  by (simp add: max_def max_unique the_equality)
 
lemma min_if:
  "is_min m A \<Longrightarrow> m = min A"
  by (simp add: min_def min_unique the_equality)
 
lemma max_if2:
  "x \<in> A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> x) \<Longrightarrow>  x = max A"
  by (simp add: is_max_if2 max_if)
          
lemma min_if2:
  "x \<in> A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> x \<le> a) \<Longrightarrow>  x = min A"
  by (simp add: is_min_if2 min_if)
           
lemma max_isotone2:
  "A \<subseteq> B \<Longrightarrow> (has_max A) \<Longrightarrow> (has_max B) \<Longrightarrow>  max A \<le> max B"
  by (metis if_has_max_max_unique max_if is_max_isotone1)

lemma min_antitone2:
  "A \<subseteq> B \<Longrightarrow> (has_min A) \<Longrightarrow> ( has_min B) \<Longrightarrow>  min B \<le> min A"
  by (metis if_has_min_min_unique min_if is_min_antitone1)

lemma max_singleton:
  "max {x} = x"
  by (metis is_max_singleton max_if)

lemma min_singleton:
  "min {x} = x"
  by (metis is_min_singleton min_if)

lemma max_lb_set_singleton1:
  "max (lb_set {x} UNIV) = x"
  by (metis is_max_lb_set_singleton1 max_if)
  
lemma min_ub_set_singleton1:
  "min (ub_set {x} UNIV) = x"
  by (metis is_min_ub_set_singleton1 min_if)

lemma max_lb_set_singleton2:
  "x \<in> X \<Longrightarrow> max (lb_set {x} X) = x"
  by (metis is_max_lb_set_singleton2 max_if)
  
lemma min_ub_set_singleton2:
  "x \<in> X \<Longrightarrow> min (ub_set {x} X) = x"
  using is_min_ub_set_singleton2 min_if by fastforce

lemma is_min_sanity_check:
  "is_min m A \<longleftrightarrow> (m \<in> A \<and> (\<forall>a \<in> A. m \<le> a))"
  by (auto simp add:min_def is_min_def lb_set_def lb_def)

lemma is_max_sanity_check:
  "is_max m A \<longleftrightarrow> (m \<in> A \<and> (\<forall>a \<in> A. m \<ge> a))"
  by (auto simp add:max_def is_max_def ub_set_def ub_def)

lemma ub_set_max:
  "is_max m X \<Longrightarrow> ub_set {m} X = {m}"
  by( auto simp add:is_max_def ub_set_def ub_def)

lemma ub_set_min1:
  "a \<in> X \<Longrightarrow> is_min a {x \<in> X. x \<ge> a}"
  by (metis ub_set_in_singleton is_min_ub_set_singleton2)


lemma lb_set_max1:
  "a \<in> X \<Longrightarrow> is_max a {x \<in> X. x \<le> a}"
  by (metis lb_set_in_singleton is_max_lb_set_singleton2)

lemma ub_set_space1:
  "is_max m X \<Longrightarrow> ub_set X X = {m}"
  by (metis emptyE insertI1 is_max_def max_unique subsetI subset_singleton_iff)

lemma lb_set_space1:
  "is_min m X \<Longrightarrow> lb_set X X = {m}"
  by (metis empty_iff insertI1 is_min_def min_unique subsetI subset_singleton_iff)

lemma ub_set_space2:
  "has_max X \<Longrightarrow> ub_set X X = {max X}"
  using if_has_max_max_unique max_if ub_set_space1 by blast

lemma lb_set_space2:
  "has_min X \<Longrightarrow> lb_set X X = {min X}"
  using if_has_min_min_unique lb_set_space1 min_if by blast

lemma max_gt_subset:
  "is_max m X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> a \<in> A \<Longrightarrow> a \<le> m"
  using is_max_sanity_check by auto

lemma min_lt_subset:
  "is_min m X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> a \<in> A \<Longrightarrow> a \<ge> m"
  using is_min_sanity_check by auto

lemma max_subset_ub:
  "is_max m X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> m ub A"
  by (simp add: max_gt_subset ub_def)
          
lemma min_subset_lb:
  "is_min m X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> m lb A"
  by (simp add: min_lt_subset lb_def)


section SupInf


definition is_sup::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_sup s A X \<equiv>  (is_min s (ub_set A X))"

definition is_inf::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_inf i A X \<equiv>  (is_max i (lb_set A X))"

definition has_sup::" 'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "has_sup A X \<equiv>  (has_min (ub_set A X))"

definition has_inf::" 'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "has_inf A X \<equiv>  (has_max (lb_set A X))"

definition Sup::"'a::order set \<Rightarrow>'a::order set \<Rightarrow> 'a::order" where
  "Sup A X = (THE s. is_sup s A X)"

definition Inf::"'a::order set \<Rightarrow>'a::order set \<Rightarrow> 'a::order" where
  "Inf A X = (THE i. is_inf i A X)"

definition is_inf_complete::"'a::order set \<Rightarrow> bool" where
  "is_inf_complete X \<equiv> (\<forall>A \<in> Pow_ne X. has_inf A X)"

definition is_sup_complete::"'a::order set \<Rightarrow> bool" where
  "is_sup_complete X \<equiv> (\<forall>A \<in> Pow_ne X. has_sup A X)"

subsection PredicateIs 

lemma is_sup_in_iff:
  "is_sup m A X \<longleftrightarrow> (is_min m ( ub_set A X))"
  by (simp add: is_sup_def)

lemma is_inf_in_iff:
  "is_inf m A X \<longleftrightarrow> (is_max m ( lb_set A X))"
  by (simp add: is_inf_def)

lemma is_sup_in_imp1:
  "\<And>m A X. is_sup m A X  \<Longrightarrow>  (m \<in>( ub_set A X) \<and> is_min m (ub_set A X))"
  by (simp add: is_min_imp is_sup_in_iff)

lemma is_inf_in_imp1:
  "\<And>m A X. is_inf m A X  \<Longrightarrow>  (m \<in>( lb_set A X) \<and> is_max m (lb_set A X))"
  by (simp add: is_max_imp is_inf_in_iff)

lemma is_sup_in_imp2:
  "\<And>m A X. is_sup m A X  \<Longrightarrow>   (\<And>a. a \<in> A \<Longrightarrow> a \<le> m)"
  using is_sup_in_imp1 ub_set_imp by blast

lemma is_inf_in_imp2:
  "\<And>m A X. is_inf m A X  \<Longrightarrow>   (\<And>a. a \<in> A \<Longrightarrow> m \<le> a)"
  using is_inf_in_imp1 lb_set_imp by blast

lemma is_sup_in_imp3:
  "\<And>m A X. is_sup m A X  \<Longrightarrow>  (\<And>u. u \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> u) \<Longrightarrow> m \<le> u)"
  by (simp add: is_min_iff is_sup_def ub_set_mem_iff)

lemma is_inf_in_imp3:
  "\<And>m A X. is_inf m A X  \<Longrightarrow>  (\<And>b. b \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> b \<le>a) \<Longrightarrow> b \<le> m)"
  by (simp add: is_max_iff is_inf_def lb_set_mem_iff)

lemma is_sup_in_set:
  "\<And>m A X. is_sup m A X \<Longrightarrow> m \<in> X"
  by (simp add: is_sup_def is_sup_in_imp1 is_min_iff ub_set_mem_iff)

lemma is_sup_imp_lt_ub:
  "is_sup m A X \<Longrightarrow> m lb (ub_set A X)"
  by (simp add: is_min_def is_sup_in_iff lb_set_imp1)

lemma is_inf_imp_gt_lb:
  "is_inf m A X \<Longrightarrow> m ub (lb_set A X)"
  by (simp add: is_max_def is_inf_in_iff ub_set_imp1)


lemma is_inf_in_set:
  "\<And>m A X. is_inf m A X \<Longrightarrow> m \<in> X"
  by (simp add: is_inf_def is_inf_in_imp1 is_max_iff lb_set_mem_iff)

lemma is_sup_if1:
  "\<And>m A X. m \<in> X \<Longrightarrow>  (m \<in>( ub_set A X) \<and> is_min m (ub_set A X)) \<Longrightarrow> is_sup m A X "
  by (simp add: is_sup_def)

lemma is_inf_if1:
  "\<And>m A X. m \<in> X \<Longrightarrow>  (m \<in>(lb_set A X) \<and> is_max m (lb_set A X)) \<Longrightarrow> is_inf m A X "
  by (simp add: is_inf_def)

lemma is_sup_if2:
  "\<And>m A X. m \<in> X \<Longrightarrow>  (\<And>a. a \<in> A \<Longrightarrow> a \<le> m) \<Longrightarrow> is_min m (ub_set A X) \<Longrightarrow> is_sup m A X "
  by (simp add: is_sup_def)

lemma is_sup_if3:
  "\<And>m A X. m \<in> X \<Longrightarrow>  (\<And>a. a \<in> A \<Longrightarrow> a \<le> m) \<Longrightarrow>  (\<And>b. b \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> b) \<Longrightarrow> m \<le> b) \<Longrightarrow> is_sup m A X "
  by (simp add: is_min_iff is_sup_def ub_set_mem_iff)

lemma is_inf_if3:
  "\<And>m A X. m \<in> X \<Longrightarrow>  (\<And>a. a \<in> A \<Longrightarrow> m \<le> a) \<Longrightarrow>  (\<And>b. b \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> b \<le> a) \<Longrightarrow> b \<le> m) \<Longrightarrow> is_inf m A X "
  by (simp add: is_max_iff is_inf_def lb_set_mem_iff)

lemma is_max_imp_is_sup:
  "A \<subseteq> X \<Longrightarrow> is_max m A \<Longrightarrow> is_sup m A X"
  by (simp add: in_mono is_max_iff is_sup_if3)

lemma is_min_imp_is_inf:
  "A \<subseteq> X \<Longrightarrow> is_min m A \<Longrightarrow> is_inf m A X"
  by (simp add: in_mono is_min_iff is_inf_if3)

lemma is_sup_in_set_imp_is_max:
  "A \<subseteq> X \<Longrightarrow> is_sup m A X \<Longrightarrow> m \<in> A \<Longrightarrow> is_max m A"
  by (simp add: is_max_iff is_sup_in_imp2)

lemma is_inf_in_set_imp_is_min:
  "A \<subseteq> X \<Longrightarrow> is_inf m A X \<Longrightarrow> m \<in> A \<Longrightarrow> is_min m A"
  by (simp add: is_min_iff is_inf_in_imp2)


subsection Uniqueness

lemma sup_unique:
  "\<And>(A::'a::order set) X m1 m2. is_sup m1 A X \<Longrightarrow> is_sup m2 A X \<Longrightarrow> m1=m2"
  by (simp add: is_sup_def min_unique)

lemma inf_unique:
  "\<And>(A::'a::order set) X m1 m2. is_inf m1 A X \<Longrightarrow> is_inf m2 A X \<Longrightarrow> m1=m2"
  by (simp add: is_inf_def max_unique)

lemma if_has_sup_unique:
  assumes "has_sup (A::'a::order set) X"
  shows "\<exists>!m. is_sup m A X"
  using assms has_sup_def if_has_min_min_unique is_sup_def by blast

lemma if_has_inf_unique:
  assumes "has_inf (A::'a::order set) X"
  shows "\<exists>!m. is_inf m A X"
  using assms has_inf_def if_has_max_max_unique is_inf_def by blast

lemma has_sup_has_lub:
  "\<And>A B.  has_sup A B \<Longrightarrow> has_min (ub_set A B)"
  by (simp add: has_sup_def)

lemma has_inf_has_glb:
  "\<And>A B.  has_inf A B \<Longrightarrow> has_max (lb_set A B)"
  by (simp add: has_inf_def)

lemma sup_obtain:
  assumes A0:"has_sup A B"
  obtains s where "is_sup s A B"
  using assms if_has_sup_unique by blast

lemma inf_obtain:
  assumes A0:"has_inf A B"
  obtains i where "is_inf i A B"
  using assms if_has_inf_unique by blast

lemma sup_is_sup:
  fixes A B::"'a::order set"
  assumes A0:"has_sup A B"
  shows "is_sup (Sup A B) A B"
  by (metis Sup_def assms if_has_sup_unique the_equality)

lemma inf_is_inf:
  assumes A0:"has_inf A B"
  shows "is_inf (Inf A B) A B"
  by (metis Inf_def assms if_has_inf_unique the_equality)

subsection ExistentialHas

lemma has_sup_in_imp1:
  "\<And>(A::'a::order set) X. has_sup A X  \<Longrightarrow>  ((Sup A X) \<in>( ub_set A X) \<and> is_min (Sup A X) (ub_set A X))"
  using is_sup_in_imp1 sup_is_sup by blast

lemma has_inf_in_imp1:
  "\<And>(A::'a::order set) X. has_inf A X  \<Longrightarrow>  ((Inf A X) \<in>(lb_set A X) \<and> is_max (Inf  A X) (lb_set A X))"
  using is_inf_in_imp1 inf_is_inf by blast

lemma has_sup_in_imp2:
  "\<And>(A::'a::order set) X. has_sup A X  \<Longrightarrow>  (\<And>a. a \<in> A \<Longrightarrow> a \<le> (Sup A X))"
  using is_sup_in_imp2 sup_is_sup by blast

lemma has_inf_in_imp2:
  "\<And>(A::'a::order set) X. has_inf A X  \<Longrightarrow>  (\<And>a. a \<in> A \<Longrightarrow> (Inf A X) \<le> a)"
  using is_inf_in_imp2 inf_is_inf by blast

lemma has_sup_imp3:
  "\<And>(A::'a::order set) X. has_sup A X  \<Longrightarrow> (\<And>b. b \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> b) \<Longrightarrow> (Sup A X) \<le> b)"
  using is_sup_in_imp3 sup_is_sup by blast

lemma has_inf_imp3:
  "\<And>(A::'a::order set) X. has_inf A X  \<Longrightarrow> (\<And>b. b \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> b \<le> a) \<Longrightarrow> b \<le> (Inf A X))"
  using is_inf_in_imp3 inf_is_inf by blast

lemma has_sup_iff:
  "has_sup A X \<longleftrightarrow> has_min (ub_set A X)"
  by (simp add: has_sup_def)

lemma has_inf_iff:
  "has_inf A X \<longleftrightarrow> has_max (lb_set A X)"
  by (simp add: has_inf_def)

lemma has_sup_in_set:
  "\<And>(A::'a::order set) X. has_sup A X \<Longrightarrow> (Sup A X) \<in> X"
  using is_sup_in_set sup_is_sup by blast

lemma has_inf_in_set:
  "\<And>(A::'a::order set) X. has_inf A X \<Longrightarrow> (Inf A X) \<in> X"
  using is_inf_in_set inf_is_inf by blast

lemma has_max_imp_has_sup:
  "A \<subseteq> X \<Longrightarrow> has_max A \<Longrightarrow> has_sup A X"
  by (meson has_sup_def if_has_max_max_unique is_max_imp_is_sup is_min_imp_has_min is_sup_in_iff)

lemma has_min_imp_has_inf:
  "A \<subseteq> X \<Longrightarrow> has_min A \<Longrightarrow> has_inf A X"
  by (meson has_inf_def if_has_min_min_unique is_inf_def is_max_imp_has_max is_min_imp_is_inf)

lemma sup_in_max:
  assumes "has_sup X X"
  shows "is_max (Sup X X) X"
  by (simp add: assms has_sup_in_imp2 has_sup_in_set is_max_if2)

lemma inf_in_min:
  assumes "has_inf X X"
  shows "is_min (Inf X X) X"
  by (simp add: assms has_inf_in_imp2 has_inf_in_set is_min_if2)

lemma has_min_ub_imp_has_sup:
  "has_min (ub_set A X) \<Longrightarrow> has_sup A X"
  by (simp add: has_sup_def)

lemma has_max_lb_imp_has_inf:
  "has_max (lb_set A X) \<Longrightarrow> has_inf A X"
  by (simp add: has_inf_def)

subsection Operators

lemma sup_in_degenerate:  
  "Sup {} X = min X"
  by (simp add: min_def Sup_def is_sup_in_iff ub_set_in_degenerate)

lemma inf_in_degenerate:  
  "Inf {} X = max X"
  by (simp add: max_def Inf_def is_inf_in_iff lb_set_in_degenerate)

lemma sup_in_degenerate2:
  "has_min X \<Longrightarrow> has_sup {} X"
  by (simp add: has_min_ub_imp_has_sup ub_set_in_degenerate)

lemma inf_in_degenerate2:
  "has_max X \<Longrightarrow> has_inf {} X"
  by (simp add: has_max_lb_imp_has_inf lb_set_in_degenerate)

lemma sup_in_degenerate3:
  "has_sup {} X \<Longrightarrow> has_min X"
  by (simp add: has_sup_def ub_set_in_degenerate)

lemma inf_in_degenerate3:
  "has_inf {} X \<Longrightarrow> has_max X"
  by (simp add: has_inf_def lb_set_in_degenerate)

lemma is_sup_singleton:
  "is_sup (x::'a::order) {x} UNIV"
  by (simp add: is_min_iff is_sup_def ub_set_mem_iff)

lemma is_inf_singleton:
  "is_inf (x::'a::order) {x} UNIV"
  by(simp add:is_max_iff is_inf_def lb_set_mem_iff)

lemma is_sup_singleton2:
  "(x::'a::order) \<in> X \<Longrightarrow> is_sup x {x} X"
  by (simp add: is_max_imp_is_sup is_max_singleton)

lemma is_inf_singleton2:
  "(x::'a::order) \<in> X \<Longrightarrow> is_inf x {x} X"
  by (simp add: is_min_imp_is_inf is_min_singleton)

lemma has_sup_singleton2:
  "(x::'a::order) \<in> X \<Longrightarrow> has_sup {x} X"
  by (simp add: has_max_imp_has_sup has_max_singleton)

lemma has_inf_singleton2:
  "(x::'a::order) \<in> X \<Longrightarrow> has_inf {x} X"
  by (simp add: has_min_imp_has_inf has_min_singleton)

lemma sup_eq_min_ub:
  "has_sup A UNIV \<Longrightarrow> Sup A UNIV = min (ub_set A UNIV)"
  by (simp add: has_sup_in_imp1 min_if)

lemma inf_eq_max_lb:
  "has_inf A UNIV \<Longrightarrow> Inf A UNIV = max (lb_set A UNIV)"
  by (simp add: has_inf_in_imp1 max_if)

lemma has_sup_singleton3:
  "has_sup {x} UNIV"
  by (simp add: has_sup_singleton2)

lemma has_inf_singleton3:
  "has_inf {x} UNIV"
  by (simp add: has_inf_singleton2)

lemma sup_singleton:
  "Sup {x::'a::order} UNIV = x"
  by (simp add: has_sup_singleton3 min_ub_set_singleton1 sup_eq_min_ub)

lemma inf_singleton:
  "Inf {x::'a::order} UNIV = x"
  by (simp add: has_inf_singleton3 inf_eq_max_lb max_lb_set_singleton1)


lemma sup_singleton2:
  "(x::'a::order) \<in> X \<Longrightarrow> Sup {x} X = x"
  by (meson has_sup_singleton2 sup_unique sup_is_sup is_sup_singleton2)

lemma inf_singleton2:
  "(x::'a::order) \<in> X \<Longrightarrow> Inf {x} X = x"
  by (meson has_inf_singleton2 inf_unique inf_is_inf is_inf_singleton2)

lemma sup_isotone1:
  "\<And>(A::'a::order set) B X. has_sup A X \<Longrightarrow> has_sup B X \<Longrightarrow> A \<subseteq> B \<Longrightarrow> Sup A X \<le> Sup B X"
  by (simp add: has_sup_imp3 has_sup_in_imp2 has_sup_in_set subset_eq)

lemma inf_antitone1:
  "\<And>(A::'a::order set) B X. has_inf A X \<Longrightarrow> has_inf B X \<Longrightarrow> A \<subseteq> B \<Longrightarrow> Inf B X \<le> Inf A X"
  by (simp add: has_inf_imp3 has_inf_in_imp2 has_inf_in_set subset_eq)

lemma sup_antitone2:
  "\<And>(A::'a::order set) B X. has_sup A X \<Longrightarrow> has_sup A B \<Longrightarrow> B \<subseteq> X \<Longrightarrow> Sup A X \<le> Sup A B"
  by (simp add: has_sup_imp3 has_sup_in_imp2 has_sup_in_set in_mono)

lemma inf_antitone2:
  "\<And>(A::'a::order set) B X. has_inf A X \<Longrightarrow> has_inf A B \<Longrightarrow> B \<subseteq> X \<Longrightarrow> Inf A B \<le> Inf A X"
  by (simp add: has_inf_imp3 has_inf_in_imp2 has_inf_in_set in_mono)

lemma is_sup_sup_eq:
  "\<And>(s::'a::order) A X. is_sup s A X \<Longrightarrow> (s = Sup A X)"
  by (simp add: Sup_def sup_unique the_equality)

lemma is_inf_inf_eq:
  "\<And>(i::'a::order) A X. is_inf i A X \<Longrightarrow> (i = Inf A X)"
  by (simp add: Inf_def inf_unique the_equality)

lemma is_inf_sanity_check0:
  "A \<noteq> {} \<Longrightarrow> has_inf A X \<Longrightarrow> i \<in> X \<Longrightarrow> (is_inf i A X \<longleftrightarrow> (\<forall>z \<in> X. (z \<le> i \<longleftrightarrow> (\<forall>a \<in> A. z \<le> a))))"
  by(auto simp add:is_inf_def is_max_def ub_set_def lb_set_def ub_def lb_def)

lemma is_sup_sanity_check0:
  "A \<noteq> {} \<Longrightarrow> has_sup A X \<Longrightarrow> s \<in> X \<Longrightarrow> (is_sup s A X \<longleftrightarrow> (\<forall>z \<in> X. (z \<ge> s \<longleftrightarrow> (\<forall>a \<in> A. z \<ge>a))))"
  by(auto simp add:is_sup_def is_min_def lb_set_def ub_set_def lb_def ub_def)

lemma sup_geq_rsup:
  "A \<subseteq> B \<Longrightarrow> B \<subseteq> C \<Longrightarrow> is_sup s1 A C \<Longrightarrow> is_sup s2 A B \<Longrightarrow> s1 \<le> s2"
  by (simp add: in_mono is_sup_in_imp2 is_sup_in_imp3 is_sup_in_set)

lemma inf_leq_rinf:
  "A \<subseteq> B \<Longrightarrow> B \<subseteq> C \<Longrightarrow> is_inf s1 A C \<Longrightarrow> is_inf s2 A B \<Longrightarrow> s2 \<le> s1"
  by (simp add: in_mono is_inf_in_imp2 is_inf_in_imp3 is_inf_in_set)

lemma inf_imp_gt_lb:
  "has_inf A X \<Longrightarrow> b \<in> lb_set A X \<Longrightarrow> b \<le> Inf A X"
  by (simp add: has_inf_imp3 lb_set_mem_iff)

lemma sup_imp_lt_ub:
  "has_sup A X \<Longrightarrow> b \<in> ub_set A X \<Longrightarrow> b \<ge> Sup A X"
  by (simp add: has_sup_imp3 ub_set_mem_iff)

lemma sup_eq_top1:
  "is_max m X \<Longrightarrow> is_sup m X X"
  by (simp add: is_max_imp_is_sup)

lemma sup_eq_top2:
  "has_max X \<Longrightarrow> Sup X X = max X"
  by (simp add: has_max_imp_has_sup max_if sup_in_max)

lemma inf_eq_bot1:
  "is_min m X \<Longrightarrow> is_inf m X X"
  by (simp add: is_min_imp_is_inf)

lemma inf_eq_bot2:
  "has_min X \<Longrightarrow> Inf X X = min X"
  by (simp add: has_min_imp_has_inf inf_in_min min_if)

lemma sup_empty_iff:
  "has_sup {} X \<longleftrightarrow> has_min X \<and> Sup {} X = min X"
  using sup_in_degenerate sup_in_degenerate2 sup_in_degenerate3 by blast

lemma inf_empty_iff:
  "has_inf {} X \<longleftrightarrow> has_max X \<and> Inf {} X = max X"
  using inf_in_degenerate inf_in_degenerate2 inf_in_degenerate3 by blast

lemma less_inf_imp1:
  "x \<in> X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_inf i A X \<Longrightarrow> x \<le> i \<Longrightarrow> a \<in> A \<Longrightarrow> x \<le> a"
  using is_inf_in_imp2 order.trans by blast

lemma less_inf_imp1b:
  "x \<in> X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> has_inf A X \<Longrightarrow> x \<le> Inf A X \<Longrightarrow> a \<in> A \<Longrightarrow> x \<le> a"
  using inf_is_inf less_inf_imp1 by blast

lemma less_inf_imp2:
  "x \<in> X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_inf i A X \<Longrightarrow> x \<le> i \<Longrightarrow> (\<forall>a \<in> A. x \<le> a)"
  using is_inf_in_imp2 order.trans by blast        

lemma less_inf_imp2b:
  "x \<in> X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> has_inf A X \<Longrightarrow> x \<le> Inf A X \<Longrightarrow> (\<forall>a \<in> A. x \<le> a)"
  using less_inf_imp1b by blast

lemma less_inf_imp3:
  "x \<in> X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_inf i A X \<Longrightarrow> x \<le> i \<Longrightarrow> x lb A"
  by (meson is_lb_simp2 less_inf_imp2)

lemma less_inf_imp3b:
  "x \<in> X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> has_inf A X \<Longrightarrow> x \<le> Inf A X \<Longrightarrow> x lb A"
  using inf_is_inf less_inf_imp3 by blast

lemma less_inf_if1:
  "x \<in> X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_inf i A X \<Longrightarrow> x lb A \<Longrightarrow>  x \<le> i"
  by (simp add: is_inf_in_imp3 lb_def)

lemma less_inf_if1b:
  "x \<in> X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> has_inf A X \<Longrightarrow> x lb A \<Longrightarrow>  x \<le> Inf A X"
  by (simp add: inf_imp_gt_lb lb_set_if)

lemma greater_sup_imp1:
  "x \<in> X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_sup s A X \<Longrightarrow> x \<ge> s \<Longrightarrow> a \<in> A \<Longrightarrow> x \<ge> a"
  using is_sup_in_imp2 order.trans by blast

lemma greater_sup_imp1b:
  "x \<in> X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> has_sup A X \<Longrightarrow> x \<ge> Sup A X \<Longrightarrow> a \<in> A \<Longrightarrow> x \<ge> a"
  by (meson greater_sup_imp1 sup_is_sup)

lemma greater_sup_imp2:
  "x \<in> X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_sup s A X \<Longrightarrow> x \<ge> s \<Longrightarrow> (\<forall>a \<in> A. a \<le> x)"
  using is_sup_in_imp2 order.trans by blast                

lemma greater_sup_imp2b:
  "x \<in> X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> has_sup A X \<Longrightarrow> x \<ge> Sup A X \<Longrightarrow> (\<forall>a \<in> A. a \<le> x)"
  using greater_sup_imp1b by blast

lemma greater_sup_imp3:
  "x \<in> X \<Longrightarrow> A \<subseteq> X \<Longrightarrow>is_sup s A X \<Longrightarrow> x \<ge> s \<Longrightarrow> x ub A"
  by (meson greater_sup_imp2 ub_def)
                                             
lemma greater_sup_imp3b:
  "x \<in> X \<Longrightarrow> A \<subseteq> X \<Longrightarrow>has_sup A X \<Longrightarrow> x \<ge> Sup A X \<Longrightarrow> x ub A"
  by (meson greater_sup_imp3 sup_is_sup)

lemma greater_sup_if1:
  "x \<in> X \<Longrightarrow> A \<subseteq> X \<Longrightarrow>is_sup s A X \<Longrightarrow> x ub A \<Longrightarrow>  s \<le> x "
  by (simp add: is_sup_in_imp3 ub_def)            

lemma greater_sup_if1b:
  "x \<in> X \<Longrightarrow> A \<subseteq> X \<Longrightarrow>has_sup A X \<Longrightarrow> x ub A \<Longrightarrow>  Sup A X \<le> x "
  by (simp add: sup_imp_lt_ub ub_set_if)


subsection Misc

lemma inf_in_expression:
  "is_inf m A X \<longleftrightarrow> m \<in> (ub_set (lb_set A X) X) \<inter> (lb_set A X)"
  by (metis inf_commute is_inf_def is_max_def lb_set_subset_space ub_set_restrict1)

lemma sup_in_expression:
  "is_sup m A X \<longleftrightarrow> m \<in> (lb_set (ub_set A X) X) \<inter> (ub_set A X)"
  by (metis inf_commute is_min_def is_sup_def lb_set_restrict1 ub_set_subset_space)

lemma inf_in_ul_:
  "is_inf m A X \<Longrightarrow>  m \<in> (ub_set (lb_set A X) X)"
  by (simp add: inf_in_expression)

lemma sup_in_lu_:
  "is_sup m A X \<Longrightarrow>  m \<in> (lb_set (ub_set A X) X)"
  by (simp add: sup_in_expression)

lemma inf_in_ul_super:
  "is_inf m A X \<Longrightarrow> A \<subseteq> B \<Longrightarrow>  m \<in> (ub_set (lb_set B X) X)"
  by (simp add: is_inf_in_imp3 is_inf_in_set ub_set_mem_iff subsetD lb_set_mem_iff)

lemma sup_in_lu_super:
  "is_sup m A X \<Longrightarrow> A \<subseteq> B \<Longrightarrow>  m \<in> (lb_set (ub_set B X) X)"
  by (simp add: is_sup_in_imp3 is_sup_in_set lb_set_mem_iff subsetD ub_set_mem_iff)


lemma lb_set_inf_from_principal:
  "A \<noteq> {} \<Longrightarrow> A \<subseteq> X \<Longrightarrow> has_inf A X \<Longrightarrow> lb_set {(Inf A X)} X = (\<Inter>a \<in> A. lb_set {a} X)"  
  apply(auto simp add:lb_set_def lb_def)
  using less_inf_imp1b apply blast
  by (simp add: has_inf_imp3)

lemma ub_set_sup_from_principal:
  "A \<noteq> {} \<Longrightarrow> A \<subseteq> X \<Longrightarrow> has_sup A X \<Longrightarrow> ub_set {(Sup A X)} X = (\<Inter>a \<in> A. ub_set {a} X)"  
  apply(auto simp add:ub_set_def ub_def)
  using greater_sup_imp1b apply blast
  by (simp add: has_sup_imp3)

lemma inf_subset_eq0:
  "A \<subseteq> B \<Longrightarrow> B \<subseteq> C \<Longrightarrow> is_inf i A C \<Longrightarrow> i \<in> B \<Longrightarrow> is_inf i A B"
  apply(auto simp add:is_inf_def) by (meson is_max_imp is_max_subset lb_set_if lb_set_imp1 lb_set_in_isotone2)

lemma inf_subset_eq1:
  "A \<subseteq> B \<Longrightarrow> B \<subseteq> C \<Longrightarrow> has_inf A C \<Longrightarrow> Inf A C \<in> B \<Longrightarrow> has_inf A B \<and> Inf A B = Inf A C"
  by (metis has_inf_def inf_is_inf inf_subset_eq0 is_inf_in_imp1 is_inf_inf_eq is_max_imp_has_max)


lemma sup_subset_eq0:
  "A \<subseteq> B \<Longrightarrow> B \<subseteq> C \<Longrightarrow> is_sup s A C \<Longrightarrow> s \<in> B \<Longrightarrow> is_sup s A B"
  apply(auto simp add:is_sup_def) by (meson is_min_imp is_min_subset ub_set_if ub_set_imp1 ub_set_in_isotone2)

lemma sup_subset_eq1:
  "A \<subseteq> B \<Longrightarrow> B \<subseteq> C \<Longrightarrow> has_sup A C \<Longrightarrow> Sup A C \<in> B \<Longrightarrow> has_sup A B \<and> Sup A B = Sup A C"
  by (metis has_sup_def is_min_imp_has_min is_sup_def is_sup_sup_eq sup_is_sup sup_subset_eq0)


context fixes A X::"'a::order set"
  assumes A0:"A \<subseteq> X" 
begin

lemma inf_ub_is_ub:
  "is_inf i (ub_set A X) X \<Longrightarrow> i ub A"
  apply(simp add:is_inf_def) by (meson A0 in_mono is_max_iff lu_extensive ub_def)

lemma is_inf_ub_in_ub_set:
  "is_inf i (ub_set A X) X \<Longrightarrow> i \<in> ub_set A X"
  by (simp add: inf_ub_is_ub is_inf_in_set ub_set_if)

lemma sup_lb_is_lb:
  "is_sup i (lb_set A X) X \<Longrightarrow> i lb A"
  apply(auto simp add:is_sup_def) by (meson A0 in_mono is_min_iff ul_extensive lb_def)

lemma is_sup_lb_in_lb_set:
  "is_sup s (lb_set A X) X \<Longrightarrow> s \<in> lb_set A X"
  by (simp add: sup_lb_is_lb is_sup_in_set lb_set_if)

lemma is_inf_ub_imp_is_sup:
  "is_inf i (ub_set A X) X \<Longrightarrow> is_sup i A X"
  by (simp add: is_inf_in_imp2 is_inf_in_set is_inf_ub_in_ub_set lb_set_elm sup_in_expression)

lemma is_sup_lb_imp_is_inf:
  "is_sup s (lb_set A X) X \<Longrightarrow> is_inf s A X"
  by (simp add: inf_in_expression is_sup_in_imp2 is_sup_in_set is_sup_lb_in_lb_set ub_set_elm)

lemma inf_ub_imp_has_sup:
  "has_inf (ub_set A X) X \<Longrightarrow> has_sup A X"
  using has_sup_def inf_is_inf is_inf_ub_imp_is_sup is_min_imp_has_min is_sup_def by blast

lemma sup_lb_imp_has_inf:
  "has_sup (lb_set A X) X \<Longrightarrow> has_inf A X"
  using has_inf_def is_inf_def is_max_imp_has_max is_sup_lb_imp_is_inf sup_is_sup by blast

lemma sup_in_eq_inf_in_ub:
  "has_inf (ub_set A X) X \<Longrightarrow> Sup A X = Inf(ub_set A X) X"
  by (simp add: has_sup_in_imp1 inf_ub_imp_has_sup is_inf_inf_eq is_min_imp_is_inf ub_set_subset_space)

lemma inf_in_eq_sup_in_lb:
  "has_sup (lb_set A X) X \<Longrightarrow> Inf A X = Sup(lb_set A X) X"
  by (simp add: has_inf_in_imp1 is_max_imp_is_sup is_sup_sup_eq sup_lb_imp_has_inf lb_set_subset_space)

end

lemma same_upper_bounds_imp_sup_eq:
  "has_sup A X  \<Longrightarrow> ub_set A X = ub_set B X \<Longrightarrow> has_sup B X \<and> Sup A X = Sup B X"
  apply(auto simp add:has_sup_def Sup_def) by (simp add: is_sup_in_iff)

lemma same_lower_bounds_imp_sup_eq:
  "has_inf A X \<Longrightarrow> lb_set A X = lb_set B X \<Longrightarrow>  has_inf B X \<and> Inf A X = Inf B X"
  apply(auto simp add:has_inf_def Inf_def) by (simp add: is_inf_in_iff)

context fixes A::"'a::order set set" and
              X::"'a::order set"
        assumes ex:"\<forall>Ai \<in> A. has_inf Ai X"
begin

lemma lb_infs_lb_un:
  assumes A0:"u \<in> lb_set  {s \<in> X. \<exists>Ai \<in> A. s = Inf Ai X } X"
  shows "u \<in> lb_set (\<Union>A) X"
proof-
  let ?B= "(\<Union>A)" let ?S="{s \<in> X. \<exists>Ai \<in> A. s = Inf Ai X }"
  have B0:"u \<in> X"
    using assms lb_set_mem_iff by blast
  have B1:"\<forall>Ai \<in> A. u \<le> Inf Ai X "
     using assms ex has_inf_in_set lb_set_imp by blast
  have B2:"u lb ?B"
    by (meson B1 UnionE dual_order.trans ex has_inf_in_imp2 is_lb_simp2)
  show ?thesis
    by (simp add: B0 B2 lb_set_if)
qed

lemma lb_un_lb_infs:
  assumes A0:"u \<in> lb_set (\<Union>A) X"
  shows "u \<in> lb_set  {s \<in> X. \<exists>Ai \<in> A. s = Inf Ai X } X"
proof-
  let ?B= "(\<Union>A)" let ?S="{s \<in> X. \<exists>Ai \<in> A. s = Inf Ai X }"
  have B0:"u \<in> X"
    using assms lb_set_mem_iff by blast
  have B1:"\<forall>s \<in> ?S. u \<le> s"
  proof 
    fix s assume A1:"s \<in> ?S"
    obtain Ai where B2:"Ai \<in> A \<and> s = Inf Ai X"
      using A1 by blast
    have B3:"\<forall>x \<in> Ai. u \<le> x"
      by (meson B2 UnionI assms lb_set_mem)
    show"u \<le> s"
      using B0 B2 B3 ex inf_is_inf is_inf_in_imp3 by blast
  qed
  show ?thesis
    using B0 B1 lb_set_elm by blast
qed

lemma lb_un_eq_lb_fp:
  "lb_set (\<Union>A) X = lb_set {s \<in> X. \<exists>Ai \<in> A. s = Inf Ai X } X"
  using lb_infs_lb_un lb_un_lb_infs by auto

lemma has_inf_imp_eq_inf_inf:
 "has_inf (\<Union>A) X \<Longrightarrow>has_inf {s \<in> X. \<exists>Ai \<in> A. s = Inf Ai X } X \<and> Inf {s \<in> X. \<exists>Ai \<in> A. s = Inf Ai X } X = Inf (\<Union>A) X"
  by (metis (mono_tags, lifting) lb_un_eq_lb_fp same_lower_bounds_imp_sup_eq)

lemma inf_inf_imp_has_inf_eq:
  "has_inf {s \<in> X. \<exists>Ai \<in> A. s = Inf Ai X } X \<Longrightarrow> has_inf  (\<Union>A) X \<and> Inf  {s \<in> X. \<exists>Ai \<in> A. s = Inf Ai X } X = Inf  (\<Union>A) X"
  by (simp add: has_inf_def has_inf_imp_eq_inf_inf lb_un_eq_lb_fp)

end

lemma insert_new_finf0:
  assumes A0:"finite E" and A1:"x \<in> X- E" and A2:"E \<noteq> {}" and A3:"has_inf E X" and A4:"has_inf {x, (Inf E X)} X"
  shows "has_inf (insert x E) X \<and>  Inf (insert x E) X = Inf {x, (Inf E X)} X"
proof-
  have B0:" (Inf E X) \<in> X"
    by (simp add: A3 has_inf_in_set)
  have B1:"has_inf  {x, (Inf E X)} X"
    using A1 B0 A4 by auto
  have B2:"Inf {x, (Inf E X)} X lb E"
    by (meson A3 B1 dual_order.trans has_inf_in_imp2 insert_iff lb_def)
  have B3:"Inf {x, (Inf E X)} X lb (insert x E)"
    by (metis B1 B2 has_inf_in_imp2 insertCI insertE lb_def)
  have B4:"Inf {x, (Inf E X)} X \<in> lb_set (insert x E) X"
    by (simp add: B1 B3 has_inf_in_set lb_set_if)
  have B5:"\<And>b. b \<in> lb_set (insert x E) X \<longrightarrow> b \<in> lb_set {x, (Inf E X)} X"
    by (simp add: A3 has_inf_imp3 lb_set_mem_iff)
  have B6:"is_inf (Inf {x, (Inf E X)} X) (insert x E) X"
    by (simp add: B1 B4 B5 has_inf_in_set inf_imp_gt_lb is_inf_if1 is_max_iff)
  show ?thesis
    by (metis B6 has_inf_def is_inf_def is_inf_inf_eq is_max_imp_has_max)
qed

lemma insert_new_finf:
  assumes binf:"\<And>a b. a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> has_inf {a, b} X" and A0:"finite E" and A1:"x \<in> X- E" and A2:"E \<noteq> {}" and A3:"has_inf E X"
  shows "has_inf  (insert x E) X \<and> Inf (insert x E) X = Inf {x, (Inf E X)} X"
  by (meson A0 A1 A2 A3 DiffE binf has_inf_in_set insert_new_finf0)


lemma insert_new_fsup0:
  assumes A0:"finite E" and A1:"x \<in> X- E" and A2:"E \<noteq> {}" and A3:"has_sup E X" and A4:"has_sup {x, (Sup E X)} X"
  shows "has_sup (insert x E) X \<and>  Sup (insert x E) X = Sup {x, (Sup E X)} X"
proof-
  have B0:" (Sup E X) \<in> X"
    by (simp add: A3 has_sup_in_set)
  have B1:"has_sup  {x, (Sup E X)} X"
    using A1 B0 A4 by auto
  have B2:"Sup {x, (Sup E X)} X ub E"
    by (meson A3 B1 dual_order.trans has_sup_in_imp2 insertCI ub_def)
  have B3:"Sup {x, (Sup E X)} X ub (insert x E)"
    by (metis B1 B2 has_sup_in_imp2 insert_iff ub_def)
  have B4:"Sup {x, (Sup E X)} X \<in> ub_set (insert x E) X"
    by (simp add: B1 B3 has_sup_in_set ub_set_if)
  have B5:"\<And>b. b \<in> ub_set (insert x E) X \<longrightarrow> b \<in> ub_set {x, (Sup E X)} X"
    by (simp add: A3 has_sup_imp3 ub_set_mem_iff)
  have B6:"is_sup (Sup {x, (Sup E X)} X) (insert x E) X"
    by (simp add: B1 B4 B5 has_sup_in_set sup_imp_lt_ub is_sup_if1 is_min_iff)
  show ?thesis
    by (metis B6 has_min_ub_imp_has_sup is_min_imp_has_min is_sup_in_imp1 is_sup_sup_eq)
qed

lemma insert_new_fsup:
  assumes bsup:"\<And>a b. a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> has_sup {a, b} X" and A0:"finite E" and A1:"x \<in> X- E" and A2:"E \<noteq> {}" and A3:"has_sup E X"
  shows "has_sup (insert x E) X \<and> Sup (insert x E) X = Sup {x, (Sup E X)} X"
  by (meson A0 A1 A2 A3 DiffD1 bsup has_sup_in_set insert_new_fsup0)


lemma finite_inf_ex:
  assumes A0: "\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> (has_inf {a1, a2} X)" and
          A1:"finite E" and 
          A2:"E \<noteq> {}" and 
          A3:"E \<subseteq> X"
  shows "(has_inf E X)"
  using A1 A2 A3 
proof (induct E rule: finite_ne_induct)
  case (singleton x)
  then show ?case
    by (simp add: has_min_imp_has_inf has_min_singleton)
next
  case (insert x F)
  then show ?case
    by (simp add: A0 has_inf_in_set insert_new_finf0)
qed


lemma finite_sup_ex:
  assumes A0: "\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> (has_sup {a1, a2} X)" and
          A1:"finite E" and 
          A2:"E \<noteq> {}" and
          A3:"E \<subseteq> X"
  shows "(has_sup E X)"
  using A1 A2 A3 
proof (induct E rule: finite_ne_induct)
  case (singleton x)
  then show ?case
    by (simp add: has_sup_singleton2)
next
  case (insert x F)
  then show ?case
    by (simp add: A0 insert_new_fsup)
qed

lemma finite_inf_closed:
  assumes A0: "\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> has_inf {a1,a2} X \<and> Inf {a1, a2} X \<in> C" and
          A1:"finite E" and 
          A2:"E \<noteq> {}" and 
          A3:"E \<subseteq> X"
  shows " has_inf E X \<and> (Inf E X) \<in> C"
  using A1 A2 A3 
proof (induct E rule: finite_ne_induct)
  case (singleton x)
  then show ?case
    using A0 by fastforce
next
  case (insert x F)
  have P0:" Inf F X \<in> X"
    using has_inf_in_set insert.hyps(4) insert.prems by auto
  have P1:"has_inf {x, Inf F X} X"
    using A0 P0 insert.prems by blast
  have P2:"Inf (insert x F) X = Inf {x, Inf F X} X"
    using P1 insert.hyps(1) insert.hyps(2) insert.hyps(3) insert.hyps(4) insert.prems insert_new_finf0 by auto
  then show ?case
    by (metis A0 Diff_iff P0 insert.hyps(1) insert.hyps(2) insert.hyps(3) insert.hyps(4) insert.prems insert_new_finf0 insert_subset)
qed


lemma finite_sup_closed:
  assumes A0: "\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> has_sup {a1,a2} X \<and> Sup {a1, a2} X \<in> C" and
          A1:"finite E" and 
          A2:"E \<noteq> {}" and 
          A3:"E \<subseteq> X"
  shows " has_sup E X \<and> (Sup E X) \<in> C"
  using A1 A2 A3 
proof (induct E rule: finite_ne_induct)
  case (singleton x)
  then show ?case
    using A0 by fastforce
next
  case (insert x F)
  have P0:" Sup F X \<in> X"
    using has_sup_in_set insert.hyps(4) insert.prems by auto
  have P1:"has_sup {x, Sup F X} X"
    using A0 P0 insert.prems by blast
  have P2:"Sup (insert x F) X = Sup {x, Sup F X} X"
    using P1 insert.hyps(1) insert.hyps(2) insert.hyps(3) insert.hyps(4) insert.prems insert_new_fsup0 by auto
  then show ?case
    by (metis A0 Diff_iff P0 insert.hyps(1) insert.hyps(2) insert.hyps(3) insert.hyps(4) insert.prems insert_new_fsup0 insert_subset)
qed


context fixes A::"'a::order set set" and
              X::"'a::order set"
        assumes  ex:"\<forall>Ai \<in> A. has_sup  Ai X"
begin

lemma ub_sup_ub_un:
  assumes A0:"u \<in> ub_set  {s \<in> X. \<exists>Ai \<in> A. s = Sup Ai X } X"
  shows "u \<in> ub_set (\<Union>A) X"
proof-
  let ?B= "(\<Union>A)" let ?S="{s \<in> X. \<exists>Ai \<in> A. s = Sup Ai X }"
  have B0:"u \<in> X"
    using assms ub_set_mem_iff by blast
  have B1:"\<forall>Ai \<in> A. Sup Ai X \<le> u"
    using assms ex has_sup_in_set ub_set_imp by blast
  have B2:"u ub ?B"
    by (meson B1 UnionE dual_order.trans ex has_sup_in_imp2 is_ub_simp2)
  show ?thesis
    by (simp add: B0 B2 ub_set_if)
qed

lemma ub_un_ub_sup:
  assumes A0:"u \<in> ub_set (\<Union>A) X"
  shows "u \<in> ub_set  {s \<in> X. \<exists>Ai \<in> A. s = Sup Ai X } X"
proof-
  let ?B= "(\<Union>A)" let ?S="{s \<in> X. \<exists>Ai \<in> A. s = Sup Ai X }"
  have B0:"u \<in> X"
    using assms ub_set_mem_iff by blast
  have B1:"\<forall>s \<in> ?S. s \<le> u"
  proof 
    fix s assume A1:"s \<in> ?S"
    obtain Ai where B2:"Ai \<in> A \<and> s = Sup Ai X"
      using A1 by blast
    have B3:"\<forall>x \<in> Ai. x \<le> u"
      by (metis B2 UnionI assms ub_set_imp)
    show "s \<le> u"
      by (simp add: B0 B2 B3 ex has_sup_imp3)
  qed
  show ?thesis
    using B0 B1 ub_set_elm by blast
qed

lemma ub_un_eq_ub_fp:
  "ub_set (\<Union>A) X = ub_set {s \<in> X. \<exists>Ai \<in> A. s = Sup Ai X } X"
  using ub_sup_ub_un ub_un_ub_sup by auto

lemma has_sup_imp_eq_sup_sup:
   "has_sup (\<Union>A) X \<Longrightarrow> has_sup {s \<in> X. \<exists>Ai \<in> A. s = Sup Ai X } X \<and> Sup {s \<in> X. \<exists>Ai \<in> A. s = Sup Ai X } X = Sup (\<Union>A) X"
  using same_upper_bounds_imp_sup_eq ub_un_eq_ub_fp by blast

lemma sup_sup_imp_has_sup_eq:
 "has_sup {s \<in> X. \<exists>Ai \<in> A. s = Sup Ai X } X \<Longrightarrow> has_sup  (\<Union>A) X \<and> Sup  {s \<in> X. \<exists>Ai \<in> A. s = Sup Ai X } X = Sup  (\<Union>A) X"
  by (simp add: has_sup_def has_sup_imp_eq_sup_sup ub_un_eq_ub_fp)


end


context fixes f::"'b \<Rightarrow> 'a::order set" and
              I::"'b set" and 
              X::"'a::order set"
        assumes ex:"\<forall>i \<in> I. has_inf (f i) X"
begin

lemma lb_infs_lb_un_indexed:
  assumes A0:"u \<in> lb_set {s \<in> X. \<exists>i \<in> I. s = Inf (f i) X } X"
  shows "u \<in> lb_set (\<Union>(f`I)) X"
proof-
  define A where "A=f`I"
  have B0:"\<forall>Ai \<in> A. has_inf Ai X"
    using A_def ex by blast
  show ?thesis using  lb_infs_lb_un[of "A" "X" "u"] A0 B0
    using A_def by fastforce
qed

lemma lb_un_lb_infs_indexed:
  assumes A0:"u \<in> lb_set  (\<Union>(f`I)) X"
  shows "u \<in> lb_set {s \<in> X. \<exists>i \<in> I. s = Inf (f i) X } X"
proof-
  define A where "A=f`I"
  have B0:"\<forall>Ai \<in> A. has_inf Ai X"
    using A_def ex by blast
  show ?thesis using  lb_un_lb_infs[of "A" "X" "u"] A0 B0
    using A_def by fastforce
qed


lemma has_inf_imp_eq_inf_inf_indexed:
  assumes "has_inf  (\<Union>(f`I)) X"
  shows "has_inf {s \<in> X. \<exists>i \<in> I. s = Inf (f i) X } X \<and> Inf {s \<in> X. \<exists>i \<in> I. s = Inf (f i) X } X = Inf  (\<Union>(f`I)) X"
  by (metis (no_types, lifting) assms has_inf_def has_inf_in_imp1 has_inf_in_set has_max_iff is_inf_if1 is_inf_inf_eq is_max_iff lb_infs_lb_un_indexed lb_un_lb_infs_indexed)

lemma inf_inf_imp_has_inf_eq_indexed:
  assumes "has_inf {s \<in> X. \<exists>i \<in> I. s = Inf (f i) X } X"
  shows "has_inf  (\<Union>(f`I)) X \<and> Inf {s \<in> X. \<exists>i \<in> I. s = Inf (f i) X } X = Inf  (\<Union>(f`I)) X"
  by (metis (no_types, lifting) assms has_inf_def has_inf_imp_eq_inf_inf_indexed has_max_iff lb_infs_lb_un_indexed lb_un_lb_infs_indexed)

end

context fixes f::"'b \<Rightarrow> 'a::order set" and
              I::"'b set" and 
              X::"'a::order set"
        assumes  ex:"\<forall>i \<in> I. has_sup (f i) X"
begin

lemma ub_sup_ub_un_indexed:
  assumes A0:"u \<in> ub_set {s \<in> X. \<exists>i \<in> I. s = Sup (f i) X } X"
  shows "u \<in> ub_set (\<Union>(f`I)) X"
proof-
  define A where "A=f`I"
  have B0:"\<forall>Ai \<in> A. has_sup Ai X"
    using A_def ex by blast
  show ?thesis using  ub_sup_ub_un[of "A" "X" "u"] A0 B0
    using A_def by fastforce
qed

lemma ub_un_ub_sup_indexed:
  assumes A0:"u \<in> ub_set (\<Union>(f`I)) X"
  shows "u \<in> ub_set {s \<in> X. \<exists>i \<in> I. s = Sup (f i) X } X"
proof-
  define A where "A=f`I"
  have B0:"\<forall>Ai \<in> A. has_sup Ai X"
    using A_def ex by blast
  show ?thesis using  ub_un_ub_sup[of "A" "X" "u"] A0 B0
    using A_def by fastforce
qed

lemma has_sup_imp_eq_sup_sup_indexed:
  assumes "has_sup (\<Union>(f`I)) X"
  shows "has_sup {s \<in> X. \<exists>i \<in> I. s = Sup (f i) X } X \<and> Sup {s \<in> X. \<exists>i \<in> I. s = Sup (f i) X } X = Sup (\<Union>(f`I)) X"
  by (metis (no_types, lifting) assms has_sup_def has_sup_in_imp1 has_sup_in_set has_min_iff is_sup_if1 is_sup_sup_eq is_min_iff ub_sup_ub_un_indexed ub_un_ub_sup_indexed)

lemma sup_sup_imp_has_sup_eq_indexed:
  assumes "has_sup {s \<in> X. \<exists>i \<in> I. s = Sup (f i) X } X"
  shows "has_sup (\<Union>(f`I)) X \<and> Sup {s \<in> X. \<exists>i \<in> I. s = Sup (f i) X } X = Sup (\<Union>(f`I)) X"
  by (metis (no_types, lifting) assms has_sup_def has_sup_imp_eq_sup_sup_indexed has_min_iff ub_sup_ub_un_indexed ub_un_ub_sup_indexed)

end

context fixes  A::"'a set set" and  X::"'a set"
begin

lemma sets_have_inf1:
  "is_inf (\<Inter>A) A UNIV"
  by(auto simp add:Inf_def is_inf_def is_max_def lb_set_def ub_set_def lb_def ub_def)

lemma sets_have_inf2:
  "has_inf A UNIV"
  using sets_have_inf1 has_inf_def is_inf_in_imp1 is_max_imp_has_max by blast

lemma sets_have_inf3:
  "Inf A UNIV = \<Inter>A"
  using is_inf_inf_eq sets_have_inf1 by blast

lemma sets_have_inf4:
  "is_inf ((\<Inter>A)\<inter> X) A (Pow X)"
  by(auto simp add:Inf_def is_inf_def is_max_def lb_set_def ub_set_def lb_def ub_def)

lemma sets_have_inf5:
  "has_inf A (Pow X)"
  using has_max_lb_imp_has_inf is_inf_in_iff is_max_imp_has_max sets_have_inf4 by blast

lemma sets_have_inf6:
  "Inf A (Pow X) = (\<Inter>A)\<inter> X"
  using is_inf_inf_eq sets_have_inf4 by blast

lemma sets_have_inf7:
  "is_inf UNIV {} UNIV"
  by(auto simp add: is_inf_def is_max_def lb_set_def ub_set_def lb_def ub_def)

lemma sets_have_inf8:
  "X \<noteq> {} \<Longrightarrow> A \<noteq> {} \<Longrightarrow> A \<subseteq> Pow X \<Longrightarrow> Inf A (Pow X) = (\<Inter>A)"
  using is_inf_inf_eq sets_have_inf4 by blast

lemma sets_have_sup1:
  "is_sup (\<Union>A) A UNIV"
  by(auto simp add:is_sup_def is_min_def lb_set_def ub_set_def lb_def ub_def)
      
lemma sets_have_sup2:
  "has_sup A UNIV"
  using sets_have_sup1 has_sup_def is_sup_in_imp1 is_min_imp_has_min by blast

lemma sets_have_sup3:
  "Sup A UNIV  =  (\<Union>A) "
  using is_sup_sup_eq sets_have_sup1 by blast

end


section Mappings
(*Probably should develop the theory of closures before trying to develop closures*)
subsection UtilityTriple
definition is_map::"('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow>bool" where
  "is_map f X Y \<equiv> ((f`X) \<subseteq> Y)"

abbreviation is_self_map::"('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_self_map f X \<equiv> is_map f X X"

lemma is_map_comp:
  "is_map f X Y \<Longrightarrow> is_map g Y Z \<Longrightarrow> is_map (g \<circ> f) X Z"
  by (simp add: image_subset_iff is_map_def)

lemma is_self_map_imp:
  "is_self_map f X \<Longrightarrow> f`X \<subseteq> X"
  by (simp add: is_map_def)

lemma is_self_map_imp2:
  "is_self_map f X \<Longrightarrow> x \<in> X \<Longrightarrow> f x \<in> X"
  by (simp add: image_subset_iff is_map_def)

lemma is_self_map_if:
  "X \<noteq> {} \<Longrightarrow> f`X \<subseteq> X \<Longrightarrow> is_self_map f X "
  by (simp add: is_map_def)

subsection Extensiveness

definition is_extensive_on::"('a::order \<Rightarrow> 'a::order)  \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_extensive_on f X \<equiv> (\<forall>x. x \<in> X \<longrightarrow> (x \<le> (f x))) \<and>  is_self_map f X"

lemma is_extensive_on_imp_map:
  "is_extensive_on f X \<Longrightarrow> is_self_map f X"
  by (simp add: is_extensive_on_def)

lemma is_ext_imp0:
  "is_extensive_on f X \<Longrightarrow> x \<in> X \<Longrightarrow> x \<le> f x"
  by (simp add: is_extensive_on_def)

lemma is_ext_imp1:
  "is_extensive_on f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> f x1 \<le> f x2 \<Longrightarrow> x1 \<le> f x2"
  using is_ext_imp0 order_trans by blast

lemma is_ext_imp2:
  "is_extensive_on f X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> b ub (f`A) \<Longrightarrow> b ub A"
  apply(auto simp add:ub_def) using is_ext_imp0 order.trans by blast

lemma is_ext_imp2b:
  "is_extensive_on f X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> ub_set (f`A) Y \<subseteq> ub_set A Y"
  by (simp add: Collect_mono_iff is_ext_imp2 ub_set_def)

lemma is_ext_imp3:
  "is_extensive_on f X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> b lb A \<Longrightarrow> b lb (f`A)"
  apply(auto simp add:lb_def) using is_ext_imp0 order_trans by blast

lemma is_ext_imp3b:
  "is_extensive_on f X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> lb_set A Y \<subseteq> lb_set (f`A) Y"
  by (simp add: Collect_mono_iff is_ext_imp3 lb_set_def)


subsection Isotonicity

definition is_isotone_on::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a::order set  \<Rightarrow> bool" where
  "is_isotone_on f X \<equiv> (\<forall>x1 x2. x1 \<in> X \<and> x2 \<in> X \<and> x1 \<le> x2 \<longrightarrow> (f x1) \<le> (f x2))"

lemma is_isotone_imp1:
  "is_isotone_on f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> f x1 \<le> f x2"
  by(simp add:is_isotone_on_def)

lemma is_isotone_imp2:
  "is_isotone_on f X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> b \<in> X \<Longrightarrow> b ub A \<Longrightarrow> (f b) ub (f`A)"
  by (simp add: in_mono is_isotone_on_def ub_def)

lemma is_isotone_imp3:
  "is_isotone_on f X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> b \<in> X \<Longrightarrow> b lb A \<Longrightarrow> (f b) lb (f`A)"
  by (simp add: in_mono is_isotone_on_def lb_def)

lemma is_iso_ext_imp1:
  "is_isotone_on f X \<Longrightarrow> is_extensive_on f X \<Longrightarrow> x \<in> X \<Longrightarrow> f x \<le> f (f x)"
  by(simp add:is_isotone_on_def is_extensive_on_def image_subset_iff is_map_def)

lemma is_iso_ext_imp2:
  "is_isotone_on f X \<Longrightarrow> is_extensive_on f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> f x2 \<Longrightarrow> f x1  \<le> f (f x2)"
  by(simp add:is_isotone_on_def is_extensive_on_def image_subset_iff is_map_def)

lemma is_iso_sup:
  "is_isotone_on f X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> has_sup A X \<Longrightarrow> has_sup (f`A) (f`X) \<Longrightarrow> Sup (f`A) (f`X) \<le> f (Sup A X)"
  by (meson has_sup_in_imp1 has_sup_in_set imageI is_isotone_imp2 sup_imp_lt_ub ub_set_if ub_set_imp1)

lemma is_iso_inf:
  "is_isotone_on f X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> has_inf A X \<Longrightarrow> has_inf (f`A) (f`X) \<Longrightarrow> f (Inf A X) \<le> Inf (f`A) (f`X)"
  by (metis equalityD1 has_inf_in_set imageI image_mono inf_antitone1 is_isotone_imp3 less_inf_if1b less_inf_imp3b)


subsection Antitonicity
definition is_antitone_on::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a::order set  \<Rightarrow> bool" where
  "is_antitone_on f X \<equiv> (\<forall>x1 x2. x1 \<in> X \<and> x2 \<in> X \<and> x1 \<le> x2 \<longrightarrow> (f x1) \<ge> (f x2))"


lemma antitone_comp:
  "is_map f X Y \<Longrightarrow> is_map g Y X \<Longrightarrow> is_antitone_on f X \<Longrightarrow> is_antitone_on g Y \<Longrightarrow> is_isotone_on (g \<circ> f) X"
  by(simp add:is_map_def is_antitone_on_def is_isotone_on_def image_subset_iff)


subsection Idempotency
definition is_idempotent_on::"('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_idempotent_on f X \<equiv> (\<forall>x. x \<in> X \<longrightarrow> f (f x) = f x) \<and> is_self_map f X"

lemma is_idempotent_imp1:
  "is_idempotent_on f X \<Longrightarrow> x \<in> X \<Longrightarrow> f x = (f (f x))"
  by(simp add:is_idempotent_on_def)

lemma is_idempotent_imp2:
  "is_idempotent_on f X \<Longrightarrow> x \<in> f`X \<Longrightarrow> f x =x"
  by(auto simp add:is_idempotent_on_def)

lemma is_idempotent_imp3:
  "is_idempotent_on f X \<Longrightarrow> is_self_map f X"
  by(simp add:is_idempotent_on_def)

lemma is_idempotent_imp4:
  "is_idempotent_on f X \<Longrightarrow> x \<in> X \<Longrightarrow> (f x) = x \<Longrightarrow> x \<in> f`X"
  by (simp add: rev_image_eqI)

lemma is_iso_idem_imp1:
  "is_isotone_on f X \<Longrightarrow> is_idempotent_on f X \<Longrightarrow> x \<in> X \<Longrightarrow> f x \<le> f (f x)"
  by(simp add:is_isotone_on_def is_idempotent_on_def image_subset_iff is_map_def)

lemma is_iso_idem_imp2:
  "is_isotone_on f X \<Longrightarrow> is_idempotent_on f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> f x2 \<Longrightarrow> f x1  \<le> f (f x2)"
  by (simp add: is_idempotent_imp3 is_isotone_imp1 is_self_map_imp2)

lemma is_iso_idem_imp3:
  "is_isotone_on f X \<Longrightarrow> is_idempotent_on f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> f x2 \<Longrightarrow> f x1  \<le> (f x2)"
   using is_iso_idem_imp2[of "f" "X" "x1" "x2"] is_idempotent_imp1[of "f" "X" "x2"] by fastforce 


subsection Projections
definition is_proj_on::"('a::order \<Rightarrow> 'a::order) \<Rightarrow> 'a::order set \<Rightarrow>  bool" where
  "is_proj_on f X \<equiv> (is_idempotent_on f X) \<and> (is_isotone_on f X)"

lemma is_proj_on_imp1:
  "is_proj_on f X \<Longrightarrow> is_idempotent_on f X" 
  by(simp add:is_proj_on_def) 

lemma is_proj_on_imp2:
  "is_proj_on f X \<Longrightarrow> is_isotone_on f X" 
  by(simp add:is_proj_on_def) 

lemma is_proj_on_imp3:
  "is_proj_on f X \<Longrightarrow> is_self_map f X" 
  by(simp add:is_idempotent_imp3 is_proj_on_imp1)

lemma proj_imp_lt_cl_lt:
  "is_proj_on f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> f x2 \<Longrightarrow> f x1 \<le> f x2"
  using is_iso_idem_imp3 is_proj_on_def by blast


subsection Closure
definition is_closure_on::"('a::order \<Rightarrow> 'a::order) \<Rightarrow> 'a::order set \<Rightarrow>  bool" where
  "is_closure_on f X \<equiv> is_proj_on f X \<and> (is_extensive_on f X)"

definition closure_eq::"('a::order \<Rightarrow> 'a::order) \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "closure_eq f X \<equiv> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. (( x1 \<le> f x2) \<longleftrightarrow> (f x1 \<le> f x2)))"


lemma closure_eq_imp1:
  "closure_eq f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> f x2 \<Longrightarrow> f x1 \<le> f x2"
  by (simp add: closure_eq_def)

lemma closure_eq_imp2:
  "closure_eq f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> f x1 \<le> f x2 \<Longrightarrow> x1 \<le> f x2"
  by (simp add: closure_eq_def)

lemma is_closure_imp_iso_imp1:
  "is_closure_on f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> f x1 \<le> f x2"
  using is_closure_on_def is_isotone_imp1 is_proj_on_imp2 by blast

lemma cl_eq_imp_ext1:
  "is_self_map f X \<Longrightarrow> closure_eq f X \<Longrightarrow> x \<in> X \<Longrightarrow>  x \<le> f x"
  by (simp add: closure_eq_imp2)

lemma cl_eq_imp_iso1:
  "is_self_map f X \<Longrightarrow> closure_eq f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> x1 \<le> f x2"
  using cl_eq_imp_ext1 order.trans by blast     

lemma cl_eq_imp_iso2:
  "is_self_map f X \<Longrightarrow> closure_eq f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> f x1 \<le> f x2"
  by (simp add: cl_eq_imp_iso1 closure_eq_imp1)

lemma cl_eq_imp_idemp:
  "is_self_map f X \<Longrightarrow> closure_eq f X \<Longrightarrow> x \<in> X \<Longrightarrow> f (f x) = f x"
  by (simp add: cl_eq_imp_ext1 closure_eq_imp1 dual_order.eq_iff is_self_map_imp2)

lemma closure_eq_imp_closure:
  "is_self_map f X \<Longrightarrow> closure_eq f X \<Longrightarrow> (is_extensive_on f X) \<and> (is_isotone_on f X) \<and> (is_idempotent_on f X)"
  by (simp add: cl_eq_imp_ext1 cl_eq_imp_idemp cl_eq_imp_iso2 is_extensive_on_def is_idempotent_on_def is_isotone_on_def)

lemma is_closure_on_imp1:
  "is_closure_on f X \<Longrightarrow> is_extensive_on f X" 
  by (simp add:is_closure_on_def)

lemma is_closure_on_imp2:
  "is_closure_on f X \<Longrightarrow> is_self_map f X" 
  using is_closure_on_imp1[of "f" "X"] is_extensive_on_imp_map[of "f" "X"] by blast

lemma is_closure_on_imp3:
  "is_closure_on f X \<Longrightarrow> is_isotone_on f X"
  by (simp add: is_closure_on_def is_proj_on_imp2) 

lemma is_closure_on_imp4:
  "is_closure_on f X \<Longrightarrow> is_idempotent_on f X"
  by (simp add: is_closure_on_def is_proj_on_imp1)

lemma closure_eq_if_closure_l:
  "is_closure_on f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> f x1 \<le> f x2 \<Longrightarrow> x1 \<le> f x2"
  using is_ext_imp1 is_closure_on_def by blast

lemma closure_eq_if_closure_r:
  "is_closure_on f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow>  x1 \<le> f x2 \<Longrightarrow> f x1 \<le> f x2"
  by(simp add:is_closure_on_def is_closure_on_imp2[of "f" "X"] proj_imp_lt_cl_lt[of "f" "X" "x1" "x2"])

lemma closure_eq_if_closure:
  "is_closure_on f X \<Longrightarrow> closure_eq f X"
  by(auto simp add:closure_eq_def closure_eq_if_closure_l closure_eq_if_closure_r)

lemma closure_if_cl_eq:
   "is_closure_on f X \<longleftrightarrow> (is_self_map f X \<and> closure_eq f X)"
  by (meson closure_eq_if_closure closure_eq_imp_closure is_closure_on_def is_closure_on_imp2 is_proj_on_def)

lemma closure_on_ineq1:
  "is_closure_on f X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> has_sup A X \<Longrightarrow> f (Sup A X) ub (f`A)"
  by (meson has_sup_in_imp1 has_sup_in_set is_closure_on_imp3 is_isotone_imp2 ub_set_imp1)

lemma lt_closed_point:
  "is_closure_on f X \<Longrightarrow> b \<in> f`X \<Longrightarrow> a \<in> X \<Longrightarrow> a \<le> b \<Longrightarrow> f a \<le> b"
  using closure_eq_if_closure_r by blast


lemma closure_on_ineq2:
  assumes A0:"is_closure_on f X" and A1:"A \<subseteq> X" and A2:"has_sup A X" and A3:"b \<in> ub_set (f`A) (f`X)"
  shows "f (Sup A X ) \<le> b"
proof-
  have B0:"b ub (f`A)"
    using assms(4) ub_set_imp1 by blast
  have B1:"b ub A"
    using A0 A1 B0 is_closure_on_imp1 is_ext_imp2 by blast
  have B2:"Sup A X \<le> b"
    by (meson A0 A2 A3 B1 in_mono is_closure_on_imp2 is_map_def sup_imp_lt_ub ub_set_if ub_set_imp2)
  show "f (Sup A X) \<le> b"
    by (meson A0 A2 A3 B2 has_sup_in_set lt_closed_point ub_set_imp2)
qed

lemma closure_on_ineq3:
  assumes A0:"is_closure_on f X" and A1:"A \<subseteq> X" and A2:"has_sup A X" 
  shows "is_sup (f (Sup A X)) (f`A) (f`X)"
  by (simp add: A0 A1 A2 closure_on_ineq1 closure_on_ineq2 has_sup_in_set is_min_if2 is_sup_def ub_set_if)

lemma closure_on_ineq4:
  assumes A0:"is_closure_on f X" and A1:"A \<subseteq> X" and A2:"has_sup A X" 
  shows "has_sup (f`A) (f`X)"
  by (meson A0 A1 A2 closure_on_ineq3 has_min_ub_imp_has_sup is_min_imp_has_min is_sup_in_imp1)

lemma closure_on_sup_eq1:
  assumes "is_closure_on f X" and "A \<subseteq> X" and "has_sup A X" 
  shows "has_sup (f`A) (f`X) \<and> (f (Sup A X) = (Sup (f`A) (f`X)))"
  by (simp add: assms(1) assms(2) assms(3) closure_on_ineq3 closure_on_ineq4 is_sup_sup_eq)

definition cl_sup_cond1::"('a::order \<Rightarrow> 'a::order) \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "cl_sup_cond1 f X \<equiv> (\<forall>A \<in> Pow X. has_sup A X \<longrightarrow> Sup A X \<le> f(Sup A X) \<and> f(Sup A X) = (Sup (f`A) (f`X)))"

lemma cl_imp_cl_sup_cond:
  "is_closure_on f X \<Longrightarrow> cl_sup_cond1 f X"
  by (meson Pow_iff cl_eq_imp_ext1 cl_sup_cond1_def closure_eq_if_closure closure_on_sup_eq1 has_sup_in_set is_closure_on_imp2)
  

subsection OrderEmbeddings

definition is_ord_embedding::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_ord_embedding f X \<equiv> (\<forall>x1 x2. x1 \<in> X \<and> x2 \<in> X \<longrightarrow> (x1 \<le> x2  \<longleftrightarrow> f x1 \<le> f x2))"

lemma ord_emb_is_inj:
  "is_ord_embedding f X \<Longrightarrow> inj_on f X"
  by (simp add: inj_on_def is_ord_embedding_def order_antisym)  


section Directedness

definition fin_inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow>  'a::order set" where
  "fin_inf_cl A X \<equiv> {x \<in> X. \<exists>F \<in> Fpow A. has_inf F X \<and> x = Inf F X}"

definition arb_sup_cl::"'a::order set \<Rightarrow>'a::order set \<Rightarrow> 'a::order set" where
  "arb_sup_cl A X \<equiv> {x \<in> X. \<exists>F \<in> Pow A. has_sup F X \<and> x = Sup F X}"

definition is_sup_closed::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow>  bool" where
  "is_sup_closed A X \<equiv> (\<forall>B \<in> Pow_ne A. has_sup B X \<longrightarrow> Sup B X \<in> A)"

definition is_inf_closed::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow>  bool" where
  "is_inf_closed A X \<equiv> (\<forall>B \<in> Pow_ne A. has_inf B X \<longrightarrow> Inf B X \<in> A)"

definition is_dwdir::"'a::ord set  \<Rightarrow> bool" where
   "is_dwdir A \<equiv> is_ne A \<and> (\<forall>a b. a \<in> A \<and>  b \<in> A \<longrightarrow>  (\<exists>c \<in> A. c lb {a, b}))"

definition is_updir::"'a::ord set  \<Rightarrow> bool" where
   "is_updir A \<equiv> is_ne A \<and> (\<forall>a b. a \<in> A \<and>  b \<in> A \<longrightarrow>  (\<exists>c \<in> A. c ub {a, b}))"

subsection PredicateIs

lemma is_dwdir_imp1:
  "is_dwdir A \<Longrightarrow> A \<noteq> {}"
  using is_dwdir_def by auto

lemma is_updir_imp1:
  "is_updir A \<Longrightarrow> A \<noteq> {}"
  using is_updir_def by auto

lemma is_dwdir_imp2:
  "is_dwdir A \<Longrightarrow>  (\<And>a b. a \<in> A \<and>  b \<in> A \<Longrightarrow>  (\<exists>c \<in> A. c lb {a, b}))"
  by (simp add: is_dwdir_def)

lemma is_dwdir_imp3:
  "is_dwdir A \<Longrightarrow>  (\<And>a b. a \<in> A \<and>  b \<in> A \<Longrightarrow>  (\<exists>c \<in> A. c \<le> a \<and> c \<le> b))"
  by (meson insert_iff is_dwdir_imp2 lb_def)

lemma is_updir_imp2:
  "is_updir A \<Longrightarrow>  (\<And>a b. a \<in> A \<and>  b \<in> A \<Longrightarrow>  (\<exists>c \<in> A. c ub {a, b}))"
  by (simp add: is_updir_def)

lemma is_updir_imp3:
  "is_updir A \<Longrightarrow>  (\<And>a b. a \<in> A \<and>  b \<in> A \<Longrightarrow>  (\<exists>c \<in> A. c \<ge> a \<and> c \<ge> b))"
  by (meson insert_iff is_updir_imp2 ub_def)

lemma is_dwdir_if1:
  " is_ne A  \<Longrightarrow> (\<forall>a b. a \<in> A \<and>  b \<in> A \<longrightarrow>  (\<exists>c \<in> A. c lb {a, b})) \<Longrightarrow> is_dwdir A"
  by (simp add: is_dwdir_def)

lemma is_dwdir_if2:
  " is_ne A  \<Longrightarrow> (\<forall>a b. a \<in> A \<and>  b \<in> A \<longrightarrow>  (\<exists>c \<in> A. c \<le> a \<and> c \<le> b)) \<Longrightarrow> is_dwdir A"
  by (simp add: is_dwdir_def lb_def)

lemma is_updir_if1:
  "is_ne A  \<Longrightarrow> (\<forall>a b. a \<in> A \<and>  b \<in> A \<longrightarrow>  (\<exists>c \<in> A. c ub {a, b})) \<Longrightarrow> is_updir A"
  by (simp add: is_updir_def)

lemma is_updir_if2:
  " is_ne A  \<Longrightarrow> (\<forall>a b. a \<in> A \<and>  b \<in> A \<longrightarrow>  (\<exists>c \<in> A. c \<ge> a \<and> c \<ge> b)) \<Longrightarrow> is_updir A"
  by (simp add: is_updir_def ub_def)

lemma up_dir_obtains:
  assumes "is_updir A" and "a \<in> A" and "b \<in> A"
  obtains c where "c \<in> A \<and> c ub {a, b}"
  using assms(1) assms(2) assms(3) is_updir_imp2 by blast

lemma dw_dir_obtains:
  assumes "is_dwdir A" and "a \<in> A" and "b \<in> A"
  obtains c where "c \<in> A \<and> c lb {a, b}"
  using assms(1) assms(2) assms(3) is_dwdir_imp2 by blast

lemma dw_dir_finite:
  assumes A0:"is_dwdir (A::'a::order set)"
  shows "finite F \<Longrightarrow> F \<subseteq> A \<Longrightarrow> (\<exists>c \<in> A. c lb F)"
proof(induct rule: finite_induct)
  case empty
  then show ?case
    using assms is_dwdir_imp1 is_lb_simp2 by fastforce
next
  case (insert x F)
  have P0:"\<And>a b. a \<in> A \<and>  b \<in> A \<Longrightarrow>  (\<exists>c \<in> A. c lb {a, b})"
    by (simp add: assms is_dwdir_imp2)
  then show ?case
  apply(simp add:lb_def)
    by (smt (verit, del_insts) insert.hyps(3) insert.prems insert_subset is_lb_simp1 order.trans)
qed


lemma updir_finite:
  assumes A0:"is_updir (A::'a::order set)"
  shows "finite F \<Longrightarrow> F \<subseteq> A \<Longrightarrow> (\<exists>c \<in> A. c ub F)"
proof(induct rule: finite_induct)
  case empty
  then show ?case
    using assms is_updir_imp1 is_ub_simp2 by fastforce
next
  case (insert x F)
  have P0:"\<And>a b. a \<in> A \<and>  b \<in> A \<Longrightarrow>  (\<exists>c \<in> A. c ub {a, b})"
    by (simp add: assms is_updir_imp2)
  then show ?case
  apply(simp add:ub_def)
    by (smt (verit, del_insts) insert.prems insert_subset local.insert(3) order.trans ub_set_if ub_set_mem)
qed


definition is_cofinal_in::"'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" (infix "is'_cofinal'_in" 50) where
  "A is_cofinal_in B \<equiv> (\<forall>a. a \<in> A \<longrightarrow> has_ub {a} B)"

lemma is_cofinal_in_imp:
  "\<And>A B. A is_cofinal_in B \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (\<exists>b \<in> B. a \<le> b))"
  by (simp add:is_cofinal_in_def has_ub_def ub_def)

lemma is_cofinal_in_if:
  "\<And>A B. (\<And>a. a \<in> A \<Longrightarrow> (\<exists>b \<in> B. a \<le> b)) \<Longrightarrow> A is_cofinal_in B "
  by (simp add: is_cofinal_in_def has_ub_def ub_def)

lemma is_cofinal_in_if_ub_in_ne:
  "\<And>A B. (\<And>a. a \<in> A \<Longrightarrow> (ub_set {a} B) \<noteq> {}) \<Longrightarrow> A is_cofinal_in B "
  by (simp add:is_cofinal_in_def has_ub_iff)

section UpDwClosure

definition up_cl::"'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> 'a::ord set" where
  "up_cl A X \<equiv> {x \<in> X. \<exists>a \<in> A. a \<le> x}"

definition dw_cl::"'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> 'a::ord set" where
  "dw_cl A X \<equiv> {x \<in> X. \<exists>a \<in> A. x \<le> a}"


definition is_up_cl::"'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "is_up_cl A X \<equiv> (up_cl A X = A)"

definition is_dw_cl::"'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "is_dw_cl A X \<equiv> (dw_cl A X = A)"

subsection PredicateIs
lemma is_upcl_in_imp0:
   "is_up_cl A X \<Longrightarrow> up_cl A X = A"
  by (simp add: is_up_cl_def) 

lemma is_dw_cl_imp0:
   "is_dw_cl A X \<Longrightarrow> dw_cl A X = A"
  by (simp add: is_dw_cl_def) 

lemma is_upclosed_in_if0:
  "up_cl A X = A \<Longrightarrow> is_up_cl A X "
  by (simp add: is_up_cl_def) 

lemma is_dwclosed_in_if0:
  "dw_cl A X = A \<Longrightarrow> is_dw_cl A X "
  by (simp add: is_dw_cl_def) 

lemma is_upclosed_in_imp1:
   "is_up_cl A X \<Longrightarrow> A = {x \<in> X. \<exists>a \<in> A. a \<le> x}"
  by (simp add: is_up_cl_def up_cl_def)

lemma is_dwclosed_in_imp1:
  "is_dw_cl A X \<Longrightarrow> A = {x \<in> X. \<exists>a \<in> A. x \<le> a}"
  by (simp add: is_dw_cl_def dw_cl_def)

lemma is_upclosed_in_if1:
   " A = {x \<in> X. \<exists>a \<in> A. a \<le> x} \<Longrightarrow> is_up_cl A X"
  by (simp add: is_up_cl_def up_cl_def)

lemma is_dwclosed_in_if1:
   " A = {x \<in> X. \<exists>a \<in> A. x \<le> a} \<Longrightarrow> is_dw_cl A X"
  by (simp add: is_dw_cl_def dw_cl_def)


lemma is_up_cl_imp2:
  "is_up_cl A X \<Longrightarrow> (\<And>a b. (b \<in> X \<and> a \<le> b \<and> a \<in> A) \<Longrightarrow> b \<in> A)"
  using is_upclosed_in_imp1 by auto

lemma is_dw_cl_imp2:
  "is_dw_cl A X \<Longrightarrow> (\<And>a b. (b \<in> X \<and> b \<le> a \<and> a \<in> A) \<Longrightarrow> b \<in> A)"
  using is_dwclosed_in_imp1 by auto

subsection Misc

lemma dwdir_inf:
  fixes A X::"'a::order set"
  assumes A0:"A \<subseteq> X" and A1:"is_dwdir A" and A2:"is_up_cl A X"
  shows "\<And>a b. (a \<in> A \<and> b \<in> A \<and>  has_inf {a, b} X) \<longrightarrow> ((Inf {a, b} X) \<in> A)"
proof
  fix a b assume A3:"a \<in> A \<and> b \<in> A \<and>  has_inf {a, b} X"
  obtain c where B0:"c \<in> A \<and> (c \<le> a) \<and> (c \<le> b)"
    using A1 A3 is_dwdir_imp3 by blast
  have B1:"c \<le> (Inf {a, b} X)"
    using A0 A3 B0 has_inf_imp3 by blast
  show "Inf {a, b} X \<in> A"
    using A2 A3 B0 B1 has_inf_in_set is_up_cl_imp2 by blast
qed

lemma dwdir_finf:
  fixes A X::"'a::order set"
  assumes A0:"A \<subseteq> X" and A1:"is_dwdir A" and A2:"is_up_cl A X"
  shows "\<And>E. (E \<in> Fpow_ne A \<and>  has_inf E X) \<longrightarrow> ((Inf E  X) \<in> A)"
proof
  fix E assume A3:" (E \<in> Fpow_ne A \<and>  has_inf E X)"
  obtain c where B1:"c \<in> A \<and> c lb E"
    by (meson A1 A3 dw_dir_finite fpow_ne_mem_iff)
  have B2:"c \<le> Inf E X"
    by (meson A0 A3 B1 has_inf_imp3 lb_def subsetD)
  show "(Inf E  X) \<in> A"
    using A2 A3 B1 B2 has_inf_in_set is_up_cl_imp2 by blast
qed

lemma updir_sup:
  fixes A X::"'a::order set"
  assumes A0:"A \<subseteq> X" and A1:"is_updir A" and A2:"is_dw_cl A X"
  shows "\<And>a b. (a \<in> A \<and> b \<in> A \<and>  has_sup {a, b} X) \<longrightarrow> ((Sup {a, b} X) \<in> A)"
proof
  fix a b assume A3:"a \<in> A \<and> b \<in> A \<and>  has_sup {a, b} X"
  obtain c where B0:"c \<in> A \<and> (c \<ge> a) \<and> (c \<ge> b)"
    using A1 A3 is_updir_imp3 by blast
  have B1:"(Sup {a, b} X) \<le> c"
    using A0 A3 B0 has_sup_imp3 by blast
  show "Sup {a, b} X \<in> A"
    using A2 A3 B0 B1 has_sup_in_set is_dw_cl_imp2 by blast
qed

lemma up_closure_in_imp:
  "\<And>A x. x \<in> X \<Longrightarrow> (\<exists>a \<in> A. a \<le> x) \<Longrightarrow> x \<in> up_cl A X"
  by (simp add: up_cl_def)

lemma down_closure_in_imp:
  "\<And>A x. x \<in> X \<Longrightarrow> (\<exists>a \<in> A. x \<le> a) \<Longrightarrow> x \<in> dw_cl A X"
  by (simp add: dw_cl_def)
           
lemma up_cl_if:
  "\<And>A x.  x \<in> X \<Longrightarrow> x \<in> up_cl A X \<Longrightarrow> (\<exists>a \<in> A. a \<le> x)"
  by (simp add: up_cl_def)

lemma dw_cl_if:
  "\<And>A x.  x \<in> X \<Longrightarrow> x \<in> dw_cl A X \<Longrightarrow> (\<exists>a \<in> A. x \<le> a)"
  by (simp add: dw_cl_def)

lemma up_cl_ub:
  "up_cl {x} X = ub_set {x} X"
  by(simp add:up_cl_def ub_set_def ub_def)
  

subsection AsOperator
lemma up_cl_in_carrier1:
  "\<And>A x.  x \<in> up_cl A X \<Longrightarrow> (x \<in> A \<or> x \<in> X)"
  by (simp add: up_cl_def)

lemma up_cl_in_carrier2:
  "\<And>A x.  x \<in> up_cl A X \<Longrightarrow> A \<subseteq> X \<Longrightarrow>  x \<in> X"
  using up_cl_def by auto

lemma dw_cl_in_carrier1:
  "\<And>A x.  x \<in> dw_cl A X \<Longrightarrow> (x \<in> A \<or> x \<in> X)"
  by (simp add: dw_cl_def)

lemma dw_cl_in_carrier2:
  "\<And>A x.  x \<in> dw_cl A X \<Longrightarrow> A \<subseteq> X \<Longrightarrow>  x \<in> X"
  using dw_cl_def by auto

lemma up_cl_in_obtain0:
  "x \<in> up_cl A X \<Longrightarrow> (\<exists>a \<in> A. a \<le> x)"
  by (simp add: up_cl_def)

lemma dw_cl_in_obtain0:
  "x \<in> dw_cl A X \<Longrightarrow> (\<exists>a \<in> A. x \<le> a)"
  by (simp add: dw_cl_def)
 
lemma up_cl_in_obtai1:
  assumes "x \<in> up_cl A X "
  obtains a where "a \<in> A \<and> a \<le> x"
  using assms up_cl_in_obtain0 by blast

lemma dw_cl_in_obtai1:
  assumes "x \<in> dw_cl A X "
  obtains a where "a \<in> A \<and> x \<le> a"
  using assms dw_cl_in_obtain0 by blast

lemma up_cl_in_extensive:
  "(A::'a::order set) \<subseteq> X \<Longrightarrow> A \<subseteq> up_cl A X"
  by (meson dual_order.refl subset_eq up_closure_in_imp)

lemma dw_cl_in_extensive:
  "(A::'a::order set) \<subseteq> X \<Longrightarrow> A \<subseteq> dw_cl A X"
  using down_closure_in_imp by blast

lemma up_cl_in_isotone:
 "A \<subseteq> B \<Longrightarrow> B \<subseteq> X \<Longrightarrow> up_cl A X \<subseteq> up_cl B X"
 apply(simp add:up_cl_def)
 by blast

lemma dw_cl_in_isotone:
 "A \<subseteq> B \<Longrightarrow> B \<subseteq> X \<Longrightarrow> dw_cl A X \<subseteq> dw_cl B X"
 apply(simp add:dw_cl_def)
 by blast


context fixes A X::"'a::order set"
        assumes A0:"A \<subseteq> X"
begin

lemma up_cl_idempotent:
 "up_cl A X = up_cl (up_cl A X) X"
 apply(simp add:up_cl_def)
  using dual_order.trans by auto

lemma dw_cl_idempotent:
  "dw_cl A X = dw_cl (dw_cl A X) X"
 apply(simp add:dw_cl_def)
  using dual_order.trans by auto

lemma lb_is_downset:
   "is_dw_cl (lb_set A X) X"
  apply(auto simp add:is_dw_cl_def dw_cl_def)
  apply (meson dual_order.trans lb_set_mem_iff)
  using lb_set_mem_iff by blast

lemma ub_is_upset:
   "is_up_cl (ub_set A X) X"
  apply(auto simp add:is_up_cl_def up_cl_def)
  apply (meson dual_order.trans ub_set_mem_iff)
  using ub_set_mem_iff by blast


lemma down_closure_has_same_ub:
   "ub_set (dw_cl A X) X = ub_set A X"
  apply(auto simp add:ub_set_def dw_cl_def ub_def)
  using A0 by blast

lemma up_closure_has_same_lb:
  "lb_set (up_cl A X) X = lb_set A X"
  apply(auto simp add:lb_set_def is_up_cl_def up_cl_def lb_def)
  using A0 by blast

end

subsection FixedPoints

definition dw_sets_in::"'a::order set \<Rightarrow> 'a::order set set" where
  "dw_sets_in X \<equiv> {D. is_dw_cl D X}"

definition up_sets_in::"'a::order set \<Rightarrow> 'a::order set set" where
  "up_sets_in X \<equiv> {D. is_up_cl D X}"

lemma in_downsets_in_imp_subset:
  "E \<in> dw_sets_in X  \<Longrightarrow> E \<subseteq> X"
  apply (simp add: dw_sets_in_def) using is_dwclosed_in_imp1 by auto

lemma in_upsets_in_imp_subset:
  "E \<in> up_sets_in X  \<Longrightarrow> E \<subseteq> X"
  apply (simp add: up_sets_in_def) using is_upclosed_in_imp1 by auto

lemma is_downclosed_in_imp2:
  "\<And>A X. A \<in> dw_sets_in X \<Longrightarrow> is_dw_cl A X"
  by (simp add: dw_sets_in_def)

lemma is_upclosed_in_imp2:
  "\<And>A X. A \<in> up_sets_in X \<Longrightarrow> is_up_cl A X"
  by (simp add: up_sets_in_def)

lemma downset_transitive:
  fixes A B X::"'a::order set"
  assumes A0:"A \<in> dw_sets_in X" and A1:"B  \<in> dw_sets_in A"
  shows "B \<in> dw_sets_in X"
proof-
  have B0:"B \<subseteq> A \<and> A \<subseteq> X" 
    by (simp add: A0 A1 in_downsets_in_imp_subset)
  have B1:"\<forall>a \<in> A. \<forall>b \<in> B. (a \<le> b) \<longrightarrow> a \<in> B"
    using A1 is_downclosed_in_imp2 is_dw_cl_imp2 by blast
  have B2:"\<forall>x \<in> X. \<forall>a \<in> A. (x \<le> a) \<longrightarrow> x \<in> A"
    using A0 is_downclosed_in_imp2 is_dw_cl_imp2 by blast
  have B30:"\<And>x b. (x \<in>X \<and> b \<in> B \<and>  x \<le> b) \<longrightarrow> x \<in> B"
  proof
    fix x b  assume A2:"x \<in>  X \<and> b \<in> B \<and> x \<le> b" 
    have B21:"b \<in> A"
      using A2 B0 by blast
    have B22:"x \<in> X \<and> b \<in> A \<and> x \<le> b"
      by (simp add: A2 B21)
    show "x \<in> B"
      using A2 B1 B2 B21 by blast
  qed
  have B3:"is_dw_cl B X"
    by (meson B0 B30 dual_order.trans dw_cl_if dw_cl_in_carrier2 dw_cl_in_extensive is_dwclosed_in_if0 subsetI subset_antisym)
  have B4:"B \<subseteq> X"
    using B0 by blast
  show ?thesis
    by (simp add: B3 B4 dw_sets_in_def)
qed

lemma upset_transitive:
fixes A B X::"'a::order set"
assumes A0:"A \<in> up_sets_in X" and A1:"B \<in> up_sets_in A"
shows "B \<in> up_sets_in X"
proof-
  have B0:"B \<subseteq> A \<and> A \<subseteq> X" 
    by (simp add: A0 A1 in_upsets_in_imp_subset)
  have B1:"\<forall>a \<in> A. \<forall>b \<in> B. (b \<le> a) \<longrightarrow> a \<in> B"
    using A1 up_sets_in_def is_up_cl_imp2 by blast
 have B30:"\<And>x b. (x \<in> X \<and> b \<in> B \<and> b \<le> x) \<longrightarrow> x \<in> B"
  proof
    fix x b assume A2:"x \<in> X \<and> b \<in> B \<and> b \<le> x" 
    have B21:"b \<in> A"
      using A2 B0 by blast
    have B22:"x \<in> X \<and> b \<in> A \<and> b \<le> x"
      by (simp add: A2 B21)
    show "x \<in> B"
      using A0 A2 B1 B22 is_up_cl_imp2 is_upclosed_in_imp2 by blast
  qed
  have B2:"\<forall>x \<in> X. \<forall>a \<in> A. (a \<le> x) \<longrightarrow> x \<in> A"
    using A0 is_up_cl_imp2 is_upclosed_in_imp2 by blast
  have B3:"is_up_cl B X"
    by (meson B0 B30 dual_order.trans is_upclosed_in_if0 subsetI subset_antisym up_cl_if up_cl_in_carrier2 up_cl_in_extensive)
  have B4:"B \<subseteq> X"
    using B0 by blast
  show ?thesis
    by (simp add: B3 up_sets_in_def)
qed

lemma in_downsets_imp_complement_in_upsets:
  "D \<in> dw_sets_in X  \<Longrightarrow> (X - D) \<in> up_sets_in X "
  apply(auto simp add:up_sets_in_def is_up_cl_def up_cl_def) using is_downclosed_in_imp2 is_dw_cl_imp2 by blast

lemma complement_in_upsets_imp_in_downsets:
  "D \<subseteq> X \<Longrightarrow> (X - D) \<in> up_sets_in X  \<Longrightarrow>D \<in> dw_sets_in X "
  by(auto simp add:up_sets_in_def dw_sets_in_def is_up_cl_def up_cl_def is_dw_cl_def dw_cl_def)


lemma in_downsets_iff_complement_in_upsets:
  assumes "D \<subseteq> X"
  shows "D \<in> dw_sets_in X \<longleftrightarrow> (X - D) \<in> up_sets_in X" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L show ?R
    by (simp add: L in_downsets_imp_complement_in_upsets)
  next 
  assume R:?R show ?L
    by (simp add: R assms complement_in_upsets_imp_in_downsets)
qed


lemma up_sets_inter_closed:
  assumes "EF \<subseteq> up_sets_in X" and "EF \<noteq> {}"
  shows "\<Inter>EF \<in> up_sets_in X"
  apply(auto simp add:assms up_sets_in_def is_up_cl_def up_cl_def)
  apply (meson assms(1) is_up_cl_imp2 is_upclosed_in_imp2 subsetD)
  by (meson assms(1) assms(2) bot.extremum_uniqueI in_mono in_upsets_in_imp_subset subset_emptyI)


lemma up_sets_un_closed:
  assumes "EF \<subseteq> up_sets_in X" and "EF \<noteq> {}"
  shows "\<Union>EF \<in> up_sets_in X"
  apply(auto simp add:assms up_sets_in_def is_up_cl_def up_cl_def)
  apply (meson assms(1) in_mono is_up_cl_imp2 is_upclosed_in_imp2)
  using assms(1) in_upsets_in_imp_subset by blast

lemma dw_sets_inter_closed:
  assumes "EF \<subseteq> dw_sets_in X" and "EF \<noteq> {}"
  shows "\<Inter>EF \<in> dw_sets_in X"
  apply(auto simp add:assms dw_sets_in_def is_dw_cl_def dw_cl_def)
  apply (meson assms(1) in_mono is_downclosed_in_imp2 is_dw_cl_imp2)
  by (meson assms(1) assms(2) bot.extremum_uniqueI in_downsets_in_imp_subset in_mono subset_emptyI)

lemma dw_sets_un_closed:
  assumes "EF \<subseteq> dw_sets_in X" and "EF \<noteq> {}"
  shows "\<Union>EF \<in> dw_sets_in X"
  apply(auto simp add:assms dw_sets_in_def is_dw_cl_def dw_cl_def)
  apply (meson assms(1) is_downclosed_in_imp2 is_dw_cl_imp2 subsetD)
  using assms(1) in_downsets_in_imp_subset by blast

lemma has_sup_in_imp_downclosure_has_sup_in:
  assumes A0:"has_sup A X" and A1:"A \<subseteq> X"
  shows "has_sup (dw_cl A X) X \<and> Sup A X = Sup (dw_cl A X) X"
  by (metis A0 A1 down_closure_has_same_ub same_upper_bounds_imp_sup_eq)

lemma has_inf_in_imp_upclosure_has_inf_in:
  assumes A0:"has_inf A X" and A1:"A \<subseteq> X"
  shows "has_inf (up_cl A X) X \<and> Inf A X = Inf (up_cl A X) X"
  using A0 A1 same_lower_bounds_imp_sup_eq up_closure_has_same_lb by blast

lemma is_up_cl_if2:
  "(A::'a::order set) \<subseteq> X \<Longrightarrow> (\<And>a b. (b \<in> X \<and> a \<le> b \<and> a \<in> A) \<Longrightarrow> b \<in> A) \<Longrightarrow> is_up_cl A X"
  by (meson is_upclosed_in_if0 subsetI subset_antisym up_cl_if up_cl_in_carrier2 up_cl_in_extensive)

lemma is_dw_cl_if2:
  "(A::'a::order set) \<subseteq> X \<Longrightarrow> (\<And>a b. (b \<in> X \<and> a \<ge> b \<and> a \<in> A) \<Longrightarrow> b \<in> A) \<Longrightarrow> is_dw_cl A X"
  by (meson is_dwclosed_in_if0 subsetI subset_antisym dw_cl_if dw_cl_in_carrier2 dw_cl_in_extensive)

lemma in_up_cl_set_if:
  "is_up_cl A X \<Longrightarrow> x \<in> X \<Longrightarrow> (\<exists>a \<in> A. a \<le> x) \<Longrightarrow> x \<in> A"
  using is_up_cl_imp2 by auto

lemma in_dw_cl_set_if:
  "is_dw_cl A X \<Longrightarrow> x \<in> X \<Longrightarrow> (\<exists>a \<in> A. a \<ge> x) \<Longrightarrow> x \<in> A"
  using is_dw_cl_imp2 by auto

section FilterIdeals
subsection Filters
subsubsection GeneralFilters

definition is_filter::"'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "is_filter F X \<equiv> F \<subseteq> X \<and> is_dwdir F \<and> is_up_cl F X"

definition is_ideal::"'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "is_ideal I X \<equiv> I \<subseteq> X \<and> is_updir I \<and> is_dw_cl I X"

lemma is_filter_imp0:
  "is_filter F X \<Longrightarrow> is_dwdir F"
  by (simp add: is_filter_def)

lemma is_ideal_imp0:
  "is_ideal I X \<Longrightarrow> is_updir I"
  by (simp add: is_ideal_def)

lemma is_filter_imp01:
  "is_filter F X \<Longrightarrow>  (\<And>a b. a \<in> F \<and>  b \<in> F \<Longrightarrow>  (\<exists>c \<in> F. c \<le> a \<and> c \<le> b))"
  by (simp add: is_dwdir_imp3 is_filter_imp0)

lemma is_ideal_imp01:
  "is_ideal I X \<Longrightarrow>  (\<And>a b. a \<in> I \<and>  b \<in> I \<Longrightarrow>  (\<exists>c \<in> I. c \<ge> a \<and> c \<ge> b))"
  by (simp add: is_updir_imp3 is_ideal_imp0)

lemma is_filter_obtains:
  assumes "is_filter F X" and  "a \<in> F" and  "b \<in> F" 
  obtains c where  "c \<in> F \<and>  c \<le> a \<and> c \<le> b"
  by (meson assms(1) assms(2) assms(3) is_filter_imp01)

lemma is_ideal_obtains:
  assumes "is_ideal I X" and  "a \<in> I" and  "b \<in> I" 
  obtains c where  "c \<in> I \<and>  c \<ge> a \<and> c \<ge> b"
  by (meson assms(1) assms(2) assms(3) is_ideal_imp01)

lemma is_filter_imp1:
  "is_filter F X \<Longrightarrow> is_up_cl F X"
  by (simp add: is_filter_def)

lemma is_ideal_imp1:
  "is_ideal I X \<Longrightarrow> is_dw_cl I X"
  by (simp add:is_ideal_def)

lemma is_filter_imp20:
  "is_filter F X \<Longrightarrow> F \<subseteq> X"
  by (simp add: is_filter_def)    

lemma is_filter_imp21:
  "is_filter F X \<Longrightarrow> F \<in> Pow X"
  by (simp add: is_filter_def)

lemma is_ideal_imp20:
  "is_ideal I X \<Longrightarrow> I \<subseteq> X"
  by (simp add: is_ideal_def)    

lemma is_ideal_imp21:
  "is_ideal I X \<Longrightarrow> I \<in> Pow X"
  by (simp add: is_ideal_def)

lemma is_filter_imp3:
  "is_filter F X \<Longrightarrow> F \<noteq> {}"
  by (simp add: is_filter_def is_dwdir_imp1)

lemma is_ideal_imp3:
  "is_ideal I X \<Longrightarrow> I \<noteq> {}"
  by (simp add: is_ideal_def is_updir_imp1)

lemma is_filter_imp4:
  "is_filter F X \<Longrightarrow> F \<in> Pow_ne X"
  by (simp add: is_filter_def is_dwdir_imp1)

lemma is_ideal_imp4:
  "is_ideal I X \<Longrightarrow> I \<in> Pow_ne X"
  by (simp add: is_ideal_def is_updir_imp1)

lemma is_filter_if:
  "F \<subseteq> X \<Longrightarrow> is_dwdir F \<Longrightarrow> is_up_cl F X \<Longrightarrow> is_filter F X"
  by (simp add: is_filter_def)

lemma is_ideal_if:
  "I \<subseteq> X \<Longrightarrow> is_updir I \<Longrightarrow> is_dw_cl I X \<Longrightarrow> is_ideal I X"
  by (simp add: is_ideal_def)

lemma filter_contains_max0:
  "is_filter F X \<Longrightarrow> (\<exists>f. f \<in> F)"
  by (simp add: ex_in_conv is_filter_imp3)
  
lemma filter_contains_max1:
  "is_max m X \<Longrightarrow> is_filter F X \<Longrightarrow> (\<exists>f. f \<in> F \<and> f \<le> m)"
  by (meson is_filter_def filter_contains_max0 max_gt_subset)

lemma filter_contains_max:
  "is_max m X \<Longrightarrow> is_filter F X \<Longrightarrow> m \<in> F"
  using filter_contains_max1 is_filter_imp1 is_max_imp is_up_cl_imp2 by blast
   
lemma ideal_contains_min0:
  "is_ideal I X \<Longrightarrow> (\<exists>i. i \<in> I)"
  by (simp add: ex_in_conv is_ideal_imp3)
  
lemma ideal_contains_min1:
  "is_min m X \<Longrightarrow> is_ideal I X \<Longrightarrow> (\<exists>i. i \<in> I \<and> i \<ge> m)"
  by (meson ideal_contains_min0 is_ideal_imp20 min_lt_subset)

lemma ideal_contains_min:
  "is_min m X \<Longrightarrow> is_ideal I X \<Longrightarrow> m \<in> I"
  using ideal_contains_min1 is_dw_cl_imp2 is_ideal_imp1 is_min_imp by blast
   
lemma filter_inf_closed:
  "is_filter F X \<Longrightarrow> a \<in> F \<and> b \<in> F \<Longrightarrow> has_inf {a, b} X \<Longrightarrow> (Inf {a, b} X) \<in> F"
  by (simp add: is_filter_def dwdir_inf)

lemma filter_finf_closed:
  "is_filter F X \<Longrightarrow>  E \<in> Fpow_ne F \<Longrightarrow> has_inf E X \<Longrightarrow> (Inf E X) \<in> F"
  by (simp add: dwdir_finf is_filter_imp0 is_filter_imp1 is_filter_imp20)

subsubsection PrincipalFilters

definition is_principal_filter::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
   "is_principal_filter F X \<equiv> F \<subseteq> X \<and> is_filter F X \<and> has_min F "

definition is_principal_ideal::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
   "is_principal_ideal I X \<equiv> is_ideal I X \<and> has_max I "

lemma principal_filter_imp1:
  "is_principal_filter F X \<Longrightarrow> (\<exists>m. is_min m F)"
  using has_min_def is_principal_filter_def by blast

lemma principal_ideal_imp1:
  "is_principal_ideal I X \<Longrightarrow> (\<exists>m. is_max m I)"
  using has_max_def is_principal_ideal_def by blast

lemma principal_filter_obtains:
  assumes "is_principal_filter F X"
  obtains m where "m = min F"by simp

lemma principal_ideal_obtains:
  assumes "is_principal_ideal I X"
  obtains m where "m = max I" by simp

lemma principal_filter_imp2:
  "is_principal_filter F X \<Longrightarrow> x \<in> X \<Longrightarrow> x \<ge> min F \<Longrightarrow> x \<in> F"
  by (metis is_filter_imp1 is_min_imp is_principal_filter_def is_up_cl_imp2 min_if principal_filter_imp1) 

lemma principal_ideal_imp2:
  "is_principal_ideal I X \<Longrightarrow> x \<in> X \<Longrightarrow> x \<le> max I \<Longrightarrow> x \<in> I"
  by (metis is_ideal_imp1 is_max_imp is_principal_ideal_def is_dw_cl_imp2 max_if principal_ideal_imp1)

lemma principal_filter_imp3:
  "is_principal_filter F X \<Longrightarrow> x \<in> F \<Longrightarrow> x \<ge> min F"
  using is_min_imp lb_set_imp min_if principal_filter_imp1 by blast

lemma principal_ideal_imp3:
  "is_principal_ideal I X \<Longrightarrow> x \<in> I \<Longrightarrow> x \<le> max I"
  using is_max_imp ub_set_imp max_if principal_ideal_imp1 by blast


lemma principal_filter_imp4:
  "is_principal_filter F X \<Longrightarrow> F \<subseteq> X"
  by (simp add: is_principal_filter_def)

lemma principal_ideal_imp4:
  "is_principal_ideal I X \<Longrightarrow> I \<subseteq> X"
  by (simp add: is_ideal_def is_principal_ideal_def)


lemma principal_filter_imp5:
  assumes "is_principal_filter F X"
  shows "\<forall>x. x \<in> F \<longleftrightarrow> (x \<in> X \<and> x \<ge> min F)"
  using assms principal_filter_imp2 principal_filter_imp3 principal_filter_imp4 by blast

lemma principal_ideal_imp5:
  assumes "is_principal_ideal I X"
  shows "\<forall>x. x \<in> I \<longleftrightarrow> (x \<in> X \<and> x \<le> max I)"
  using assms principal_ideal_imp2 principal_ideal_imp3 principal_ideal_imp4 by blast


lemma principal_filter_imp6:
  "is_principal_filter F X \<Longrightarrow> F = {x \<in> X. x \<ge> min F}"
  by (simp add: Orderings.order_eq_iff principal_filter_imp5 subset_iff)

lemma principal_filter_imp6b:
  "is_principal_filter F X \<Longrightarrow> F = ub_set {min F} X"
  by (simp add: principal_filter_imp6 ub_set_in_singleton)

lemma principal_ideal_imp6:
  "is_principal_ideal I X \<Longrightarrow> I = {x \<in> X. x \<le> max I}"
  by (simp add: Orderings.order_eq_iff principal_ideal_imp5 subset_iff)

lemma principal_ideal_imp6b:
  "is_principal_ideal I X \<Longrightarrow> I = lb_set {max I} X"
  by (simp add: lb_set_in_singleton principal_ideal_imp6)

lemma principal_filter_imp7:
  "is_principal_filter F X \<Longrightarrow> is_filter F X"
  by (simp add: is_principal_filter_def)

lemma principal_ideal_imp7:
  "is_principal_ideal I X \<Longrightarrow> is_ideal I X"
  by (simp add: is_principal_ideal_def)

lemma principal_filter_imply70:
  "is_principal_filter F X \<Longrightarrow> is_dwdir F"
  using is_filter_imp0 principal_filter_imp7 by blast

lemma principal_ideal_imply70:
  "is_principal_ideal I X \<Longrightarrow> is_updir I"
  using is_ideal_imp0 principal_ideal_imp7 by blast


lemma principal_filter_if1:
  "(a::'a::order) \<in> X \<Longrightarrow> is_principal_filter (ub_set {a} X) X"
  apply(auto simp add:is_principal_filter_def is_filter_def is_dwdir_def is_up_cl_def)
  using ub_set_imp2 apply blast
  using is_sup_def is_sup_singleton2 min_imp_ne apply blast
  apply (metis empty_iff empty_subsetI has_lb_def has_lb_iff insert_subset is_min_imp_set is_min_ub_set_singleton2)
  apply (metis empty_subsetI insert_subset is_up_cl_def ub_is_upset)
  apply (meson subsetD ub_set_subset_space up_cl_in_extensive)
  by (simp add: has_sup_has_lub has_sup_singleton2)


lemma principal_ideal_if1:
  "a \<in> X \<Longrightarrow> is_principal_ideal (lb_set {a} X) X"
  apply(auto simp add:is_principal_ideal_def is_ideal_def is_updir_def is_dw_cl_def)
  apply (simp add: lb_set_mem_iff)
  using singleton_in_ub_set apply auto[1]
  apply (metis empty_not_insert empty_subsetI has_inf_def has_inf_singleton2 has_ub_def has_ub_iff insert_subset lb_set_in_degenerate ub_set_space2 ulu_eq_u)
  apply (metis Int_commute Int_empty_left inf_le1 insert_absorb insert_inter_insert is_dw_cl_def lb_is_downset)
  using dw_cl_in_extensive lb_set_subset_space apply auto[1]
  by (simp add: has_inf_has_glb has_inf_singleton2)

lemma principal_filter_if2:
  "a \<in> X \<Longrightarrow> is_principal_filter {x \<in> X. x \<ge> a} X"
  by (metis principal_filter_if1 ub_set_in_singleton)

lemma principal_ideal_if2:
  "a \<in> X \<Longrightarrow> is_principal_ideal {x \<in> X. x \<le> a} X"
  by (metis lb_set_in_singleton principal_ideal_if1)

lemma is_principal_filter_equiv:
  assumes A0:"F \<subseteq> X"
  shows "is_principal_filter F X \<longleftrightarrow> (\<exists>x \<in> X. F = up_cl {x} X)" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L 
  obtain m where B0:"is_min m F"
    using L principal_filter_imp1 by blast
  have B1:"\<forall>x \<in> F. m \<le> x"
    by (meson B0 is_min_iff)
  have B2:"\<forall>x \<in> X. m \<le> x \<longrightarrow> x \<in> F"
    using B0 L min_if principal_filter_imp2 by blast
  have B3:"F \<subseteq> up_cl {m} X"
    by (meson B1 assms singletonI subset_eq up_closure_in_imp)
  have B4:"up_cl {m} X \<subseteq> F"
    by (simp add: B2 subset_eq up_cl_def)
  show ?R
    using B0 B3 B4 assms is_min_imp by blast
 next
  assume R:?R 
  obtain x where B5:"x \<in> X \<and> F = up_cl {x} X"
    using R by blast
  have B6:"is_min x ( up_cl {x} X)"
    by (simp add: B5 is_min_ub_set_singleton2 up_cl_ub)
  have B7:"is_min x (ub_set {x} X)"
    by (simp add: B5 is_min_ub_set_singleton2)
  have B8:"F = ub_set {x} X"
    using B5 up_cl_ub[of "x" "X"]
    by meson
  show ?L
    by (metis B5 B8 principal_filter_if1)
qed


subsection ProperFilters

definition is_pfilter::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
   "is_pfilter F X \<equiv> is_filter F X \<and> F \<noteq> X " 

definition is_pideal::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
   "is_pideal I X \<equiv> is_ideal I X \<and> I \<noteq> X " 

lemma is_pfilter_in_imp:
  "\<And>F X. is_pfilter F X \<Longrightarrow>  (is_filter F X) \<and> (F \<noteq>  X)"
  by (simp add:is_pfilter_def)

lemma is_pfilter_if:
  "\<And>F X.  (is_filter F X) \<and> ( F \<noteq>  X) \<Longrightarrow> is_pfilter F X "
  by (simp add:is_pfilter_def)

lemma is_pfilter_in_imp2:
  "\<And>F X. is_pfilter F X \<Longrightarrow>  (F \<noteq> X \<and> F \<subseteq> X \<and> is_dwdir F \<and> is_up_cl F X)"
  by (auto simp add: is_pfilter_def is_filter_def)

lemma is_pfilter_in_if2:
  "\<And>F X.  (F \<noteq> X \<and>  F \<subseteq> X \<and> is_dwdir F \<and> is_up_cl F X) \<Longrightarrow> is_pfilter F X "
  by (simp add: is_pfilter_def is_filter_def)

lemma is_pideal_in_imp:
  "\<And>F X. is_pideal F X \<Longrightarrow>  (is_ideal F X) \<and> (F \<noteq>  X)"
  by (simp add:is_pideal_def)

lemma is_pideal_if:
  "\<And>F X.  (is_ideal F X) \<and> ( F \<noteq>  X) \<Longrightarrow> is_pideal F X "
  by (simp add:is_pideal_def)

lemma is_pideal_in_imp2:
  "\<And>F X. is_pideal F X \<Longrightarrow>  (F \<noteq> X \<and> F \<subseteq> X \<and> is_updir F \<and> is_dw_cl F X)"
  by (auto simp add: is_pideal_def is_ideal_def)

lemma is_pideal_in_if2:
  "\<And>F X.  (F \<noteq> X \<and>  F \<subseteq> X \<and> is_updir F \<and> is_dw_cl F X) \<Longrightarrow> is_pideal F X "
  by (simp add: is_pideal_def is_ideal_def)

lemma filter_with_bot:
  "is_filter F X \<Longrightarrow> is_min m X \<Longrightarrow> m \<in> F \<Longrightarrow> F=X"
  by (meson is_filter_imp1 is_filter_imp20 is_min_iff is_up_cl_imp2 order_class.order_eq_iff subsetI)

lemma ideal_with_top:
  "is_ideal I X \<Longrightarrow> is_max m X \<Longrightarrow> m \<in> I \<Longrightarrow> I=X"
  by (meson is_dw_cl_imp2 is_ideal_imp1 is_ideal_imp20 is_max_sanity_check subsetI subset_antisym)

lemma filter_no_bot_imp_proper:
  "is_filter F X \<Longrightarrow> is_min m X \<Longrightarrow> m \<notin> F \<Longrightarrow> is_pfilter F X"
  using is_min_iff is_pfilter_if by auto

lemma filter_no_bot_if_proper:
  "is_pfilter F X \<Longrightarrow> is_min m X \<Longrightarrow> m \<notin> F"
  using filter_with_bot is_pfilter_in_imp by blast

lemma ideal_no_top_imp_proper:
  "is_ideal I X \<Longrightarrow> is_max m X \<Longrightarrow> m \<notin> I \<Longrightarrow> is_pideal I X"
  using is_max_sanity_check is_pideal_def by auto

lemma ideal_no_top_if_proper:
  "is_pideal I X \<Longrightarrow> is_max m X \<Longrightarrow> m \<notin> I"
  using ideal_with_top is_pideal_in_imp by blast

subsection FiltersSetIdealSet

definition filters::"'a::order set \<Rightarrow> 'a::order set set" where
  "filters X \<equiv> {F \<in> Pow  X. is_filter F X}"

definition pfilters::"'a::order set \<Rightarrow> 'a::order set set" where
  "pfilters X \<equiv> {F \<in> Pow  X. is_pfilter F X}"

lemma filters_mem_iff:
  "A \<in> filters X \<longleftrightarrow> (A \<in> Pow X \<and> is_filter A X)"
  by (simp add: filters_def)

lemma pfilters_mem_iff:
  "A \<in> pfilters X \<longleftrightarrow> (A \<in> Pow X \<and> is_pfilter A X)"
  by (simp add: pfilters_def)

subsection CharacterizingMappings


section ClosureRanges

definition is_clr::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_clr C X \<equiv> (C \<noteq> {}) \<and> (C \<subseteq> X) \<and> (\<forall>x. x \<in> X \<longrightarrow> has_min (ub_set {x} C))"

definition is_moore_family::"'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_moore_family C X \<equiv> C \<in> Pow (Pow X) \<and> (\<forall>A \<in> Pow_ne C. (Inf A (Pow X)) \<in> C) \<and> (X \<in> C)"

definition closure_from_clr::"'a::order set \<Rightarrow> ('a::order \<Rightarrow> 'a::order)" where
  "closure_from_clr C \<equiv> (\<lambda>x. min (ub_set {x} C))"

definition clr_from_closure::"('a::order \<Rightarrow> 'a::order) \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "clr_from_closure f X \<equiv> (f`X)"

lemma is_clr_imp1:
  "is_clr C X \<Longrightarrow> (C \<noteq> {}) \<and> (C \<subseteq> X)"
  by(simp add:is_clr_def)

lemma is_clr_imp2:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> has_min (ub_set {x} C)"
  by(simp add:is_clr_def)

lemma is_clr_imp3:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> (ub_set {x} C) \<noteq> {}"
  apply(simp add:is_clr_def) 
  by (metis empty_iff has_min_iff)

lemma clr_is_cofinal:
  "is_clr C X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> ub_set {x} C \<noteq> {})"
  by (simp add: is_clr_imp3)
  
lemma is_clr_imp4:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> has_inf (ub_set {x} C) C"
  by (simp add: has_min_imp_has_inf is_clr_imp2 ub_set_subset_space)

lemma is_clr_imp5:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> Inf (ub_set {x} C) C \<in> C"
  by (simp add: has_inf_in_set is_clr_imp4)

lemma is_clr_imp6:
  "is_clr C X \<Longrightarrow> C \<subseteq> X \<Longrightarrow> x \<in> X \<Longrightarrow> Inf (ub_set {x} C) C \<in> X"
  by (simp add: has_inf_in_set in_mono is_clr_imp4)

lemma is_clr_imp_max:
  "has_max X \<Longrightarrow> is_clr C X \<Longrightarrow> has_max C"
proof-
  assume A0:"has_max X"
  obtain m where B0:"is_max m X"
    using A0 has_max_iff2 by auto
  show "is_clr C X \<Longrightarrow> has_max C"
  proof-
    assume A1:"is_clr C X"
    have B1:"(ub_set {m} C) \<noteq> {}"
      using A1 B0 clr_is_cofinal is_max_iff by blast
    have B2:"ub_set {m} C = {m}"
      by (metis A1 B0 B1 inf_le2 is_clr_def subset_singletonD ub_set_max ub_set_restrict1)
    have B3:"m \<in> C"
      using B2 ub_set_mem_iff by auto
  show ?thesis
    by (meson A1 B0 B3 is_clr_imp1 is_max_imp_has_max is_max_subset)
  qed
qed


lemma clr_obtains0:
  assumes "is_clr C X" and " x \<in> X "
  obtains m where "is_min m (ub_set {x} C)"
  using assms(1) assms(2) has_min_iff2 is_clr_imp2 by blast

lemma clr_obtains1:
  assumes "is_clr C X" and " x \<in> X "
  obtains m where "m \<in> C \<and> is_min m (ub_set {x} C)"
  by (meson assms(1) assms(2) clr_obtains0 is_min_imp ub_set_imp2)

locale closure_range=
  fixes C X::"'a::order set"                     
  assumes clr:"is_clr C X"
begin

abbreviation Cl::"'a::order \<Rightarrow> 'a::order" where
  "Cl x \<equiv> (closure_from_clr C) x"

lemma crange_is_ne:
  "C \<noteq> {}"
  using clr is_clr_imp1 by blast

lemma space_is_ne:
  "X \<noteq> {}"
  using crange_is_ne is_clr_def
  using clr by blast 

lemma Cl_maps_to:
  "Cl`X \<subseteq> X"
proof
  fix c assume A0:"c \<in> Cl`X"
  obtain x where B0:"c = Cl x" and B1:"x \<in> X" using A0 imageE[of "c" "Cl" "X"] by blast
  have B2:"is_min c (ub_set {x} C)" using B0 closure_from_clr_def
    by (metis B1 clr clr_obtains1 min_if)
  have B3:"c \<in> C"
    using B2 is_sup_in_iff is_sup_in_set by blast
  show "c \<in> X"
    using B3 clr is_clr_imp1 by blast
qed

lemma cl_is_self_map:
  "is_self_map Cl X"
  by(simp add:is_map_def Cl_maps_to space_is_ne)

lemma pr_fil_iso1:
  "x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> x \<le> y \<Longrightarrow> (ub_set {y} C) \<subseteq> (ub_set {x} C)"
  by (simp add: ub_set_singleton_antitone)

lemma cl_is_iso:
  "x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> x \<le> y \<Longrightarrow> (Cl x)  \<le>  (Cl y)"
  apply(auto simp add: closure_from_clr_def) using is_clr_imp2 min_antitone2 by (metis clr pr_fil_iso1)

lemma cl_is_iso_on:
  "is_isotone_on Cl X"
  by(simp add:is_isotone_on_def cl_is_iso)

lemma cl_is_ext:
  "x \<in> X \<Longrightarrow> x \<le> Cl x"
  by (metis closure_from_clr_def clr clr_obtains1 is_min_imp min_if singletonI ub_set_imp)

lemma cl_is_ext_on:
  "is_extensive_on Cl X"
  by(auto simp add:is_extensive_on_def cl_is_ext cl_is_self_map)

lemma cl_fp:
  "c \<in> C \<Longrightarrow> Cl c = c"
  proof-
    fix c assume A0:"c \<in> C"
    have B0:"is_min c (ub_set {c} C)"
      by(auto simp add:A0 is_min_def ub_set_def lb_set_def ub_def lb_def)
    show " Cl c =c"
      using B0 closure_from_clr_def min_if by metis
qed

lemma cl_is_idm:
  "x \<in> X \<Longrightarrow> (Cl (Cl x)) = Cl x "
proof-
  fix x assume A0:"x \<in> X"
  have B0:"Cl x \<in> C"
    by (metis A0 closure_from_clr_def clr clr_obtains1 min_if)
  show "(Cl (Cl x)) = Cl x " using A0 B0 cl_fp[of "Cl x"]
    by fastforce
qed

lemma cl_is_idm_on:
  "is_idempotent_on Cl X"
  by(simp add:cl_is_self_map is_idempotent_on_def cl_is_idm) 

lemma cl_is_closure:
  "is_closure_on Cl X"
  by(simp add:is_closure_on_def is_proj_on_def cl_is_idm_on cl_is_iso_on cl_is_ext_on)

end

locale closure= 
  fixes f::"'a::order \<Rightarrow> 'a::order" and X::"'a::order set"
  assumes is_cl:"is_closure_on f X" and ne:"X \<noteq> {}"
begin

abbreviation Cf::"'a::order set" where
  "Cf \<equiv> clr_from_closure f X"

lemma Cf_is_ne:
  "Cf \<noteq> {}"
  by (simp add: clr_from_closure_def ne)

lemma Cf_subseteq_space:
  "Cf \<subseteq> X"
  by (metis clr_from_closure_def closure_if_cl_eq is_cl is_self_map_imp) 

lemma cl_ub_im:
  "x \<in> X \<Longrightarrow> (f x) \<in> ub_set {x} Cf"
proof-
  fix x assume A0:"x \<in> X"
  have B0:"f x \<in> Cf" 
    by  (simp add:clr_from_closure_def A0 imageI[of "x" "X" "f"])
  have B1:"x \<le> f x" using is_cl is_closure_on_def is_extensive_on_def A0 by blast
  show "(f x) \<in> ub_set {x} Cf"
    by (simp add: B0 B1 ub_set_mem_iff)
qed

lemma cl_ub_is_ne:
  "x \<in> X \<Longrightarrow> ub_set {x} Cf \<noteq> {}"
  using cl_ub_im by blast

lemma cl_ub_min:
  "x \<in> X \<Longrightarrow> y \<in> ub_set {x} Cf \<Longrightarrow> f x \<le> y"
proof-
  fix x assume A0:"x \<in> X" show "y \<in> ub_set {x} Cf \<Longrightarrow> f x \<le> y"
  proof-
    fix y assume A1:"y \<in>  ub_set {x} Cf"
    have B0:"x \<le> y" 
      using A1 ub_set_def ub_def  by (simp add: ub_set_imp)
    have B1:"y \<in> Cf " 
       using A1 ub_set_imp2 by blast
    have B2:"y \<in> X"  
      using B1 Cf_subseteq_space by blast 
    have B3:"f x \<le> f y" 
      using A0 B2 B0 is_cl is_closure_imp_iso_imp1[of "f" "X" "x" "y"] by blast
    have B4:"... = y"
      by (metis B1 clr_from_closure_def is_cl is_closure_on_def is_idempotent_imp2 is_proj_on_def)
    show "f x \<le> y"
      using B3 B4 by auto
  qed
qed
   

lemma cl_is_min_ub:
  "x \<in> X \<Longrightarrow>  has_min (ub_set {x} Cf)"
  by (meson cl_ub_im cl_ub_min has_min_iff)

lemma Cf_is_clr:
  "is_clr Cf X"
  by(simp add:is_clr_def Cf_subseteq_space cl_is_min_ub Cf_is_ne)

end 

lemma closure_range_is_clr:
  fixes f::"'a::order \<Rightarrow> 'a::order" and X::"'a::order set"
  assumes is_cl:"is_closure_on f X" and ne:"X \<noteq> {}"
  shows "is_clr (f`X) X"
  by (metis closure.Cf_is_clr closure.intro clr_from_closure_def is_cl ne)
  
lemma clr_induces_closure:
  fixes C X::"'a::order set"                     
  assumes clr:"is_clr C X"
  shows "is_closure_on (closure_from_clr C) X"
  by (simp add: closure_range.cl_is_closure closure_range.intro clr) 

lemma cl_cr_cl_eq_cl:
  assumes A0:"is_closure_on f X" and A1:"a \<in> X"
  shows "closure_from_clr (clr_from_closure f X) a = f a"
proof-
    have B0:"f`X \<subseteq> X"
      by (simp add: A0 is_closure_on_imp2 is_self_map_imp)
    have B1:"min (ub_set {a} (f ` X)) = min {y \<in> f`X. a \<le> y}"
      by (simp add: ub_set_in_singleton)
    have B2:"f a \<in> f`X \<and> a \<le> f a "
      using A0 A1 closure_eq_if_closure closure_eq_imp2 by blast
    have B3:"\<forall>y. y\<in> f`X \<and> a \<le> y \<longrightarrow> f a \<le> y"
      using A0 A1 closure_eq_if_closure_r by blast
    have B4:"is_min (f a) (ub_set {a} (f ` X))"
      by (simp add: B2 B3 is_min_iff ub_set_mem_iff)
    show ?thesis
      by (metis B4 closure_from_clr_def clr_from_closure_def min_if)
qed
    
lemma cr_cl_cr_eq_cr:
  assumes A0:"is_clr C X"
  shows "clr_from_closure (closure_from_clr C) X = C"
proof-
  have T:"\<forall>y. y \<in> clr_from_closure (closure_from_clr C) X  \<longleftrightarrow> y \<in> C"
  proof
    fix y
    have B0:"y \<in> clr_from_closure (closure_from_clr C) X \<longleftrightarrow> (\<exists>x \<in> X.  (closure_from_clr C) x = y)"
      using clr_from_closure_def by auto
    have B1:"... \<longleftrightarrow> (\<exists>x \<in> X. y = min (ub_set {x} C))"
      by (metis closure_from_clr_def)
    have B2:"... \<longleftrightarrow> y \<in> C"
      by (metis assms clr_obtains1 is_clr_imp1 min_if min_ub_set_singleton2 subsetD)
    show " y \<in> clr_from_closure (closure_from_clr C) X  \<longleftrightarrow> y \<in> C"
      by (simp add: B0 B1 B2)
  qed
  show ?thesis
    using T by blast
qed

lemma cl_order_iso:
  fixes f1 f2::"'a::order \<Rightarrow> 'a::order" and X::"'a::order set"
  assumes A0:"is_closure_on f1 X"  and A1:"is_closure_on f2 X" and A3:"\<forall>x. x \<in> X \<longrightarrow> f1 x \<le> f2 x"
  shows "clr_from_closure f2 X \<subseteq> clr_from_closure f1 X"
proof
  fix x assume A4:"x \<in> clr_from_closure f2 X"
  have B0:"x \<le> f1 x"
    using A0 A1 A4 closure.Cf_subseteq_space closure.intro closure_eq_if_closure_l
    by (metis clr_from_closure_def image_is_empty order_refl subsetD) 
  have B1:"... \<le> f2 x"
    using A1 A3 A4 closure.Cf_subseteq_space closure.intro
    using clr_from_closure_def by blast
  have B2:"... = x"
    by (metis A1 A4 clr_from_closure_def is_closure_on_def is_idempotent_imp2 is_proj_on_def)
  have B3:"f1 x = x"
    using B0 B1 B2 by fastforce
  show "x \<in> clr_from_closure f1 X"
    by (metis A1 A4 B3 clr_from_closure_def imageI is_closure_on_imp2 is_map_def subsetD)
qed

lemma clr_order_iso:
  fixes C1 C2 X::"'a::order set"
  assumes A0:"is_clr C1 X" and A1:"is_clr C2 X" and A2:"C2 \<subseteq> C1"
  shows "\<And>x. x \<in> X \<longrightarrow> closure_from_clr C1 x \<le> closure_from_clr C2 x"
proof
  fix x assume A3:"x \<in> X"
  show "closure_from_clr C1 x \<le> closure_from_clr C2 x"
    by (metis A0 A1 A2 A3 closure_from_clr_def is_clr_imp2 min_antitone2 ub_set_in_isotone2)
qed

  
lemma top_is_closed1:
  assumes "is_closure_on f X" and "is_max m X"
  shows "f m = m"
  by (meson assms(1) assms(2) cl_eq_imp_ext1 closure_eq_if_closure is_closure_on_imp2 is_max_iff is_self_map_imp2 order_antisym)

lemma top_is_closed2:
  assumes "is_clr C X" and "is_max m X"
  shows "m \<in> C"
  by (metis assms(1) assms(2) clr_from_closure_def clr_induces_closure cr_cl_cr_eq_cr image_eqI is_max_iff top_is_closed1)


lemma clr_inf_closed:
  assumes "is_clr C X" and "A \<subseteq> C" and "has_inf A X"
  shows "Inf A X \<in> C"
proof(cases "A = {}")
  case True
  have B0:"has_max X"
    by (metis True assms(3) has_inf_def lb_set_in_degenerate)
  obtain m where "is_max m X"
    using B0 has_max_iff2 by blast
  then show ?thesis
    by (metis True assms(1) inf_in_degenerate max_if top_is_closed2) 
next
  case False
  let ?f="closure_from_clr C"
  have B0:"\<forall>a. a \<in> A \<longrightarrow> Inf A X \<le> a"
    using assms(3) has_inf_in_imp2 by blast
  have B1:"\<forall>a. a \<in> A \<longrightarrow> ?f(Inf A X ) \<le> ?f a"
    by (meson B0 assms(1) assms(2) assms(3) closure_range.cl_is_iso closure_range.intro has_inf_in_set in_mono is_clr_imp1)
  have B2:"\<forall>a. a \<in> A\<longrightarrow>  ?f(Inf A X ) \<le> a"
    by (metis B1 assms(1) assms(2) closure_range.cl_fp closure_range.intro in_mono)
  have B3:"?f(Inf A X ) \<le> Inf A X "
    by (simp add: B2 assms(1) assms(3) closure_range.cl_is_self_map closure_range.intro has_inf_imp3 has_inf_in_set is_self_map_imp2)
  have B4:"?f (Inf A X ) = (Inf A X )"
    using B3 assms(1) assms(3) closure_range.cl_is_ext closure_range.intro has_inf_in_set order_antisym_conv by blast
  then show ?thesis
    by (metis assms(1) assms(3) closure_from_clr_def clr_obtains1 has_inf_in_set min_if)
qed



section SupInfClosures
definition sup_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "sup_cl A X \<equiv> {x \<in> X. \<exists>E \<in> Pow_ne A. has_sup E X \<and> x = Sup E X}"

definition sup_cle::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "sup_cle A X \<equiv> {x \<in> X. \<exists>E \<in> Pow A. has_sup E X \<and> x = Sup E X}"

definition inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "inf_cl A X \<equiv> {x \<in> X. \<exists>E \<in> Pow_ne A. has_inf E X \<and> x = Inf E X}"

definition fne_inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow>  'a::order set" where
  "fne_inf_cl A X \<equiv> {x \<in> X. \<exists>F \<in> Fpow_ne A. has_inf F X \<and> x = Inf F X}"

lemma sup_cl_imp0:
  "x \<in> sup_cl A X \<Longrightarrow> x \<in> X "
  by (simp add: sup_cl_def)
lemma sup_cle_imp0:

  "x \<in> sup_cle A X \<Longrightarrow> x \<in> X "
  by (simp add: sup_cle_def)

lemma inf_cl_imp0:
  "x \<in> inf_cl A X \<Longrightarrow> x \<in> X "
  by (simp add: inf_cl_def)

lemma fin_inf_cl_imp0:
  "x \<in> fin_inf_cl A X \<Longrightarrow> x \<in> X"
  by (simp add: fin_inf_cl_def)

lemma fne_inf_cl_imp0:
  "x \<in> fne_inf_cl A X \<Longrightarrow> x \<in> X"
  by (simp add: fne_inf_cl_def)

lemma sup_cl_imp1:
  "x \<in> sup_cl A X \<Longrightarrow>  (\<exists>E \<in> Pow_ne A. has_sup E X \<and> x = Sup E X)"
   by (simp add: sup_cl_def) 

lemma sup_cle_imp1:
  "x \<in> sup_cle A X \<Longrightarrow>  (\<exists>E \<in> Pow A. has_sup E X \<and> x = Sup E X)"
   by (simp add: sup_cle_def) 

lemma inf_cl_imp1:
  "x \<in> inf_cl A X \<Longrightarrow>  (\<exists>E \<in> Pow_ne A. has_inf E X \<and> x = Inf E X)"
   by (simp add: inf_cl_def) 

lemma fin_inf_cl_imp1:
  "x \<in> fin_inf_cl A X \<Longrightarrow> (\<exists>F \<in> Fpow A. has_inf F X \<and> x = Inf F X)"
  by (simp add: fin_inf_cl_def)

lemma fne_inf_cl_imp1:
  "x \<in> fne_inf_cl A X \<Longrightarrow> (\<exists>F \<in> Fpow_ne A. has_inf F X \<and> x = Inf F X)"
  by (simp add: fne_inf_cl_def)

lemma sup_cl_if1:
  " x \<in> X \<Longrightarrow>  (\<exists>E \<in> Pow_ne A. has_sup E X \<and> x = Sup E X) \<Longrightarrow> x \<in> sup_cl A X"
   by (simp add: sup_cl_def) 

lemma sup_cle_if1:
  " x \<in> X \<Longrightarrow>  (\<exists>E \<in> Pow A. has_sup E X \<and> x = Sup E X) \<Longrightarrow> x \<in> sup_cle A X"
   by (simp add: sup_cle_def) 

lemma inf_cl_if1:
  " x \<in> X \<Longrightarrow>  (\<exists>E \<in> Pow_ne A. has_inf E X \<and> x = Inf E X) \<Longrightarrow> x \<in> inf_cl A X"
   by (simp add: inf_cl_def) 

lemma fin_inf_cl_if1:
  "x \<in> X \<Longrightarrow> (\<exists>F \<in> Fpow A. has_inf F X \<and> x = Inf F X) \<Longrightarrow> x \<in> fin_inf_cl A X"
  by (simp add: fin_inf_cl_def)

lemma fne_inf_cl_if1:
  "x \<in> X \<Longrightarrow> (\<exists>F \<in> Fpow_ne A. has_inf F X \<and> x = Inf F X) \<Longrightarrow> x \<in> fne_inf_cl A X"
  by (simp add: fne_inf_cl_def)

lemma sup_cl_obtains:
  assumes "x \<in> sup_cl A X"
  obtains Ex where "Ex \<in> Pow_ne A \<and> has_sup Ex X \<and> x = Sup Ex X"
  by (meson assms sup_cl_imp1)

lemma sup_cle_obtains:
  assumes "x \<in> sup_cle A X"
  obtains Ex where "Ex \<in> Pow A \<and> has_sup Ex X \<and> x = Sup Ex X"
  by (meson assms sup_cle_imp1)

lemma inf_cl_obtains:
  assumes "x \<in> inf_cl A X"
  obtains Ex where "Ex \<in> Pow_ne A \<and> has_inf Ex X \<and> x = Inf Ex X"
  by (meson assms inf_cl_imp1)

lemma fin_inf_cl_obtains:
  assumes "x \<in> fin_inf_cl A X"
  obtains F where "F \<in> Fpow A \<and> has_inf F X \<and> x = Inf F X"
  by (meson assms fin_inf_cl_imp1)

lemma fne_inf_cl_obtains:
  assumes "x \<in> fne_inf_cl A X"
  obtains F where "F \<in> Fpow_ne A \<and> has_inf F X \<and> x = Inf F X"
  by (meson assms fne_inf_cl_imp1)


definition is_sup_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_sup_cl A X \<equiv> (\<forall>E \<in> Pow_ne A. has_sup E X \<longrightarrow> Sup E X \<in> A)"

definition is_sup_cle::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_sup_cle A X \<equiv> (\<forall>E \<in> Pow A. has_sup E X \<longrightarrow> Sup E X \<in> A)"

definition is_inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_inf_cl A X \<equiv> (\<forall>E \<in> Pow_ne A. has_inf E X \<longrightarrow> Inf E X \<in> A)"

definition is_fin_inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_fin_inf_cl A X \<equiv> (\<forall>F \<in> Fpow A. has_inf F X \<longrightarrow> Inf F X \<in> A)"

definition is_fne_inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_fne_inf_cl A X \<equiv> (\<forall>F \<in> Fpow_ne A. has_inf F X \<longrightarrow> Inf F X \<in> A)"


lemma up_closed_supin_closed0:
  "is_up_cl A X \<Longrightarrow> E \<in> Pow_ne A \<Longrightarrow> has_sup E X  \<Longrightarrow> Sup E X \<in> A"
  using has_sup_in_imp2 has_sup_in_set is_up_cl_imp2 by blast

lemma up_closed_supin_closed:
  assumes A0:"is_up_cl A X"
  shows "is_sup_cl A X"
  using assms is_sup_cl_def up_closed_supin_closed0 by blast

lemma dw_closed_infin_closed0:
  "is_dw_cl A X \<Longrightarrow> E \<in> Pow_ne A \<Longrightarrow> has_inf E X  \<Longrightarrow> Inf E X \<in> A"
  using has_inf_in_imp2 has_inf_in_set is_dw_cl_imp2
  by blast

lemma down_closed_infin_closed:
  assumes "is_dw_cl A X"
  shows "is_inf_cl A X"
  using assms is_inf_cl_def dw_closed_infin_closed0 by blast




lemma sup_cl_extensive:
  assumes A0:"A \<subseteq> X"
  shows "A \<subseteq> sup_cl A X"
proof
  fix a assume A1:"a \<in> A"
  have B01:"{a} \<in> Pow_ne A"
    by (simp add: A1)
  have B02:"has_sup {a} X \<and> a = Sup {a} X"
    by (metis A1 assms has_sup_singleton2 in_mono sup_singleton2)
  have B1:"a \<in> X"
    using A1 assms by auto
  show "a \<in> sup_cl A X"
    by (metis B01 B02 B1 sup_cl_if1)
qed

lemma sup_cle_extensive:
  assumes A0:"A \<subseteq> X"
  shows "A \<subseteq> sup_cle A X"
proof
  fix a assume A1:"a \<in> A"
  have B0:"is_sup a {a} X"
    using A1 assms is_sup_singleton2 by blast
  have B1:" Sup {a} X = a"
    using B0 is_sup_sup_eq by fastforce
  have B2:"{a} \<in> Pow_ne A"
    by (simp add: A1)
  show "a \<in> sup_cle A X"
  apply(simp add:sup_cle_def)
    by (metis B0 B1 B2 DiffD1 has_sup_singleton2 is_sup_in_set)
qed


lemma inf_cl_extensive:
  assumes A0:"A \<subseteq> X"
  shows "A \<subseteq> inf_cl A X"
proof
  fix a assume A1:"a \<in> A"
  have B0:"is_inf a {a} X"
    using A1 assms is_inf_singleton2 by blast
  have B1:" Inf {a} X = a"
    using B0 is_inf_inf_eq by fastforce
  have B2:"{a} \<in> Pow_ne A"
    by (simp add: A1)
  show "a \<in> inf_cl A X"
  apply(simp add:inf_cl_def)
    by (metis B0 B1 B2 has_inf_singleton2 is_inf_in_set)
qed

lemma fin_inf_cl_extensive:
  assumes A0: "A \<subseteq> X"
  shows "A \<subseteq> fin_inf_cl A X"
proof
  fix a assume A1: "a \<in> A"
  have B0: "is_inf a {a} X"
    using A1 assms is_inf_singleton2 by blast
  have B1: "Inf {a} X = a"
    using B0 is_inf_inf_eq by fastforce
  have B2: "{a} \<in> Fpow A"
    by (simp add: A1 Fpow_def)
  show "a \<in> fin_inf_cl A X"
    apply(simp add:fin_inf_cl_def)
    by (metis B0 B1 B2 has_inf_singleton2 is_inf_in_set)
qed

lemma fne_inf_cl_extensive:
  assumes A0: "A \<subseteq> X"
  shows "A \<subseteq> fne_inf_cl A X"
proof
  fix a assume A1: "a \<in> A"
  have B0: "is_inf a {a} X"
    using A1 assms is_inf_singleton2 by blast
  have B1: "Inf {a} X = a"
    using B0 is_inf_inf_eq by fastforce
  have B2: "{a} \<in> Fpow_ne A"
    by (simp add: A1 Fpow_def)
  show "a \<in> fne_inf_cl A X"
    apply(simp add:fne_inf_cl_def)
    by (metis B0 B1 B2 has_inf_singleton2 is_inf_in_set)
qed


lemma sup_cl_isotone:
  assumes A0:"A \<subseteq> B \<and> B \<subseteq> X"
  shows "sup_cl A X \<subseteq> sup_cl B X"
  apply(simp add:sup_cl_def)
  using assms mem_Collect_eq order_trans by fastforce

lemma sup_cle_isotone:
  assumes A0:"A \<subseteq> B \<and> B \<subseteq> X"
  shows "sup_cle A X \<subseteq> sup_cle B X"
  apply(simp add:sup_cle_def)
  using assms mem_Collect_eq order_trans by fastforce

lemma inf_cl_isotone:
  assumes A0:"A \<subseteq> B \<and> B \<subseteq> X"
  shows "inf_cl A X \<subseteq> inf_cl B X"
  apply(simp add:inf_cl_def)
  using assms mem_Collect_eq order_trans by fastforce

lemma fin_inf_cl_isotone:
  assumes A0: "A \<subseteq> B \<and> B \<subseteq> X"
  shows "fin_inf_cl A X \<subseteq> fin_inf_cl B X"
  apply(auto  simp add:fin_inf_cl_def)
  using Fpow_mono assms by auto

lemma fne_inf_cl_isotone:
  assumes A0: "A \<subseteq> B \<and> B \<subseteq> X"
  shows "fne_inf_cl A X \<subseteq> fne_inf_cl B X"
  apply(auto  simp add:fne_inf_cl_def)
  using Fpow_mono assms by auto

lemma sup_cl_idempotent0:
  assumes "s \<in> sup_cl (sup_cl A X) X"
  obtains E where "E \<in> Pow_ne (sup_cl A X) \<and> has_sup E X \<and> Sup E X = s"
  by (metis assms sup_cl_imp1)

lemma sup_cle_idempotent0:
  assumes "s \<in> sup_cle (sup_cle A X) X"
  obtains E where "E \<in> Pow (sup_cle A X) \<and> has_sup E X \<and> Sup E X = s"
  by (metis assms sup_cle_imp1)

lemma inf_cl_idempotent0:
  assumes "s \<in> inf_cl (inf_cl A X) X"
  obtains E where "E \<in> Pow_ne (inf_cl A X) \<and> has_inf E X \<and> Inf E X = s"
  by (metis assms inf_cl_imp1)

lemma fin_inf_cl_idempotent0:
  assumes "s \<in> fin_inf_cl (fin_inf_cl A X) X"
  obtains F where "F \<in> Fpow (fin_inf_cl A X) \<and> has_inf F X \<and> Inf F X = s"
  by (metis assms fin_inf_cl_imp1)

lemma fne_inf_cl_idempotent0:
  assumes "s \<in> fne_inf_cl (fne_inf_cl A X) X"
  obtains F where "F \<in> Fpow_ne (fne_inf_cl A X) \<and> has_inf F X \<and> Inf F X = s"
  by (metis assms fne_inf_cl_imp1)

lemma sup_cl_idempotent1:
  assumes "E \<in> Pow_ne (sup_cl A X)"
  shows "\<forall>x \<in> E. \<exists>Ex. Ex \<in> Pow_ne A \<and> has_sup Ex X \<and> Sup Ex X = x"
  by (metis DiffD1 Pow_iff assms subset_iff sup_cl_imp1)

lemma sup_cle_idempotent1:
  assumes "E \<in> Pow (sup_cle A X)"
  shows "\<forall>x \<in> E. \<exists>Ex. Ex \<in> Pow A \<and> has_sup Ex X \<and> Sup Ex X = x"
  by (metis Pow_iff assms subset_iff sup_cle_imp1)

lemma inf_cl_idempotent1:
  assumes "E \<in> Pow_ne (inf_cl A X)"
  shows "\<forall>x \<in> E. \<exists>Ex. Ex \<in> Pow_ne A \<and> has_inf Ex X \<and> Inf Ex X = x"
  by (metis DiffD1 Pow_iff assms subset_iff inf_cl_imp1)

lemma fin_inf_cl_idempotent1:
  assumes "F \<in> Fpow (fin_inf_cl A X)"
  shows "\<forall>x \<in> F. \<exists>Fx. Fx \<in> Fpow A \<and> has_inf Fx X \<and> Inf Fx X = x"
  by (metis Fpow_Pow_finite Pow_iff assms fin_inf_cl_imp1 inf_le1 insert_absorb insert_subset)

lemma fne_inf_cl_idempotent1:
  assumes "F \<in> Fpow (fne_inf_cl A X)"
  shows "\<forall>x \<in> F. \<exists>Fx. Fx \<in> Fpow_ne A \<and> has_inf Fx X \<and> Inf Fx X = x"
  by (metis Fpow_Pow_finite Pow_iff assms fne_inf_cl_imp1 inf_le1 insert_absorb insert_subset)

lemma sup_cl_idempotent:
   "sup_cl (sup_cl A X) X = sup_cl A X "
  proof
    show " sup_cl A X  \<subseteq> sup_cl (sup_cl A X) X"
      by (meson subset_iff sup_cl_extensive sup_cl_imp0)
    next
    show " sup_cl (sup_cl A X) X \<subseteq> sup_cl A X"
  proof
    fix s assume P0:"s \<in>sup_cl (sup_cl A X) X"
    show "s \<in> (sup_cl A X)"
    proof-
      let ?P="\<lambda>E x. E \<in> Pow_ne A \<and> has_sup E X \<and> Sup E X = x"
      let ?f= "(\<lambda>x. SOME Ex. ?P Ex x)"
      obtain E where P1:"E \<in> Pow_ne (sup_cl A X) \<and> has_sup E X \<and> Sup E X = s"
        by (meson P0 sup_cl_idempotent0)
      have B0:"\<forall>x \<in> E. (\<exists>Ex. ?P Ex x)"
        using P1 sup_cl_idempotent1 by auto
      let ?fE="?f`E" let ?S="{s \<in> X. \<exists>Ai \<in> ?fE. s = Sup Ai X}"
      have B1:"\<forall>x \<in> E.  ?P (?f x) x"
        by (smt (verit, best) B0 someI)
      have B2:"?S = E"
      proof
        show "?S \<subseteq> E"
          proof
            fix s assume B6A0:"s \<in>?S"
            have B60:"\<exists>Ai \<in> ?fE. s = Sup Ai X"
              using B6A0 by blast
            show "s \<in> E"
              using B1 B60 by auto
          qed
        next  
        show "E \<subseteq> ?S"
          proof
            fix s assume B6A1:"s \<in> E"
            show "s \<in> ?S" using B1 B6A1 has_sup_in_set by fastforce
        qed
      qed
      have B11A0:"has_sup E X "
        by (simp add: P1)
      have B110:"has_sup ?S X"
        using B11A0 B2 by presburger
      have B8:"\<forall>Ai \<in> ?fE. has_sup  Ai X"
        using B1 by blast
      have B111:"has_sup  (\<Union>?fE) X \<and>  Sup (\<Union>?fE) X = Sup ?S X" 
        using B8 B110 sup_sup_imp_has_sup_eq[of "?fE" "X"]  by simp
      have B12:"Sup (\<Union>?fE) X = s"
        using B111 B2 P1 by fastforce
      have B13:"(\<Union>?fE) \<in> Pow_ne A"
      proof-
        have B130:"is_ne ?fE \<and> (\<forall>Ai \<in> ?fE. Ai \<in> Pow_ne A)"
          using B1 P1 by auto
        show ?thesis
          using B130 B2 by auto
      qed
      have B16:"\<exists>Ex. ?P Ex s"
        by (meson B111 B12 B13)
      show "s \<in> (sup_cl A X)"
        using B16 has_sup_in_set sup_cl_if1 by blast
    qed
  qed
qed

lemma sup_cle_idempotent:
   "sup_cle (sup_cle A X) X = sup_cle A X "
  proof
    show " sup_cle A X  \<subseteq> sup_cle (sup_cle A X) X"
      by (meson subset_iff sup_cle_extensive sup_cle_imp0)
    next
    show " sup_cle (sup_cle A X) X \<subseteq> sup_cle A X"
  proof
    fix s assume P0:"s \<in>sup_cle (sup_cle A X) X"
    show "s \<in> (sup_cle A X)"
    proof-
      let ?P="\<lambda>E x. E \<in> Pow A \<and> has_sup E X \<and> Sup E X = x"
      let ?f= "(\<lambda>x. SOME Ex. ?P Ex x)"
      obtain E where P1:"E \<in> Pow (sup_cle A X) \<and> has_sup E X \<and> Sup E X = s"
        by (meson P0 sup_cle_idempotent0)
      have B0:"\<forall>x \<in> E. (\<exists>Ex. ?P Ex x)"
        using P1 sup_cle_obtains by (metis PowD insert_absorb insert_subset)
      let ?fE="?f`E" let ?S="{s \<in> X. \<exists>Ai \<in> ?fE. s = Sup Ai X}"
      have B1:"\<forall>x \<in> E.  ?P (?f x) x"
        proof
          fix x assume A2:"x \<in> E"
          have B10:"\<exists>Ex. ?P Ex x"
            using A2 B0 by fastforce
          show "?P (?f x) x"
            using someI_ex[OF B10] by blast
        qed
      have B2:"?S = E"
      proof
        show "?S \<subseteq> E"
          proof
            fix s assume B6A0:"s \<in>?S"
            have B60:"\<exists>Ai \<in> ?fE. s = Sup Ai X"
              using B6A0 by blast
            show "s \<in> E"
              using B1 B60 by auto
          qed
        next  
        show "E \<subseteq> ?S"
          proof
            fix s assume B6A1:"s \<in> E"
            show "s \<in> ?S" using B1 B6A1 has_sup_in_set by fastforce
        qed
      qed
      have B11A0:"has_sup E X "
        by (simp add: P1)
      have B110:"has_sup ?S X"
        using B11A0 B2 by presburger
      have B8:"\<forall>Ai \<in> ?fE. has_sup  Ai X"
        using B1 by blast
      have B111:"has_sup  (\<Union>?fE) X \<and>  Sup (\<Union>?fE) X = Sup ?S X" 
        using B8 B110 sup_sup_imp_has_sup_eq[of "?fE" "X"]  by simp
      have B12:"Sup (\<Union>?fE) X = s"
        using B111 B2 P1 by fastforce
      have B13:"(\<Union>?fE) \<in> Pow A"
        using B1 by blast
      have B16:"\<exists>Ex. ?P Ex s"
        by (meson B111 B12 B13)
      show "s \<in> (sup_cle A X)"
        using B16 has_sup_in_set sup_cle_if1 by blast
    qed
  qed
qed


lemma inf_cl_idempotent:
   "inf_cl (inf_cl A X) X = inf_cl A X "
  proof
    show " inf_cl A X  \<subseteq> inf_cl (inf_cl A X) X"
      by (meson subset_iff inf_cl_extensive inf_cl_imp0)
    next
    show " inf_cl (inf_cl A X) X \<subseteq> inf_cl A X"
    proof
      fix s assume P0:"s \<in> inf_cl (inf_cl A X) X"
      show "s \<in> (inf_cl A X)"
    proof-
      let ?P="\<lambda>E x. E \<in> Pow_ne A \<and> has_inf E X \<and> Inf E X = x"
      let ?f= "(\<lambda>x. SOME Ex. ?P Ex x)"
      obtain E where P1:"E \<in> Pow_ne (inf_cl A X) \<and> has_inf E X \<and> Inf E X = s"
        by (meson P0 inf_cl_idempotent0)
      have B0:"\<forall>x \<in> E. (\<exists>Ex. ?P Ex x)"
        using P1 inf_cl_obtains by (metis DiffE PowD insert_absorb insert_subset)
      let ?fE="?f`E" let ?S="{s \<in> X. \<exists>Ai \<in> ?fE. s = Inf Ai X}"
      have B1:"\<forall>x \<in> E.  ?P (?f x) x"
        proof
          fix x assume A2:"x \<in> E"
          have B10:"\<exists>Ex. ?P Ex x"
            using A2 B0 by fastforce
          show "?P (?f x) x"
            using someI_ex[OF B10] by blast
        qed
      have B2:"?S = E"
      proof
        show "?S \<subseteq> E"
          proof
            fix s assume B6A0:"s \<in>?S"
            have B60:"\<exists>Ai \<in> ?fE. s = Inf Ai X"
              using B6A0 by blast
            show "s \<in> E"
              using B1 B60 by auto
          qed
        next  
        show "E \<subseteq> ?S"
          proof
            fix s assume B6A1:"s \<in> E"
            show "s \<in> ?S" using B1 B6A1 has_inf_in_set by fastforce
        qed
      qed
      have B11A0:"has_inf E X "
        by (simp add: P1)
      have B110:"has_inf ?S X"
      using B11A0 B2 by presburger
      have B8:"\<forall>Ai \<in> ?fE. has_inf  Ai X"
        using B1 by blast
      have B111:"has_inf  (\<Union>?fE) X \<and>  Inf (\<Union>?fE) X = Inf ?S X" 
        using B8 B110 inf_inf_imp_has_inf_eq[of "?fE" "X"]  by simp
      have B12:"Inf (\<Union>?fE) X = s"
        using B111 B2 P1 by fastforce
      have B13:"(\<Union>?fE) \<in> Pow_ne A"
      proof-
        have B130:"is_ne ?fE \<and> (\<forall>Ai \<in> ?fE. Ai \<in> Pow_ne A)"
          using B1 P1 by auto
        show ?thesis
          using B130 B2 by auto
      qed
      have B16:"\<exists>Ex. ?P Ex s"
        by (meson B111 B12 B13)
      show "s \<in> (inf_cl A X)"
        using B16 has_inf_in_set inf_cl_if1 by blast
    qed
  qed
qed

lemma fin_inf_cl_idempotent:
  "fin_inf_cl (fin_inf_cl A X) X = fin_inf_cl A X"
proof
  show "fin_inf_cl A X \<subseteq> fin_inf_cl (fin_inf_cl A X) X"
    by (meson subset_iff fin_inf_cl_extensive fin_inf_cl_imp0)
  next
  show "fin_inf_cl (fin_inf_cl A X) X \<subseteq> fin_inf_cl A X"
  proof
    fix s assume P0: "s \<in> fin_inf_cl (fin_inf_cl A X) X"
    show "s \<in> (fin_inf_cl A X)"
    proof-
      let ?P = "\<lambda>F x. F \<in> Fpow A \<and> has_inf F X \<and> Inf F X = x"
      let ?f = "(\<lambda>x. SOME Fx. ?P Fx x)"
      obtain F where P1: "F \<in> Fpow (fin_inf_cl A X) \<and> has_inf F X \<and> Inf F X = s"
        by (meson P0 fin_inf_cl_idempotent0)
      have B0: "\<forall>x \<in> F. (\<exists>Fx. ?P Fx x)"
        using P1 fin_inf_cl_obtains using fin_inf_cl_idempotent1 by blast
      let ?fF = "?f`F" let ?S = "{s \<in> X. \<exists>Ai \<in> ?fF. s = Inf Ai X}"
      have B1: "\<forall>x \<in> F. ?P (?f x) x"
        proof
          fix x assume A2: "x \<in> F"
          have B10: "\<exists>Fx. ?P Fx x"
            using A2 B0 by fastforce
          show "?P (?f x) x"
            using someI_ex[OF B10] by blast
        qed
      have B2: "?S = F"
      proof
        show "?S \<subseteq> F"
          proof
            fix s assume B6A0: "s \<in> ?S"
            have B60: "\<exists>Ai \<in> ?fF. s = Inf Ai X"
              using B6A0 by blast
            show "s \<in> F"
              using B1 B60 by auto
          qed
        next  
        show "F \<subseteq> ?S"
          proof
            fix s assume B6A1: "s \<in> F"
            show "s \<in> ?S" using B1 B6A1 has_inf_in_set by fastforce
        qed
      qed
      have B11A0: "has_inf F X"
        by (simp add: P1)
      have B110: "has_inf ?S X"
      using B11A0 B2 by presburger
      have B8: "\<forall>Ai \<in> ?fF. has_inf Ai X"
        using B1 by blast
      have B111: "has_inf (\<Union>?fF) X \<and> Inf (\<Union>?fF) X = Inf ?S X" 
        using B8 B110 inf_inf_imp_has_inf_eq[of "?fF" "X"] by simp
      have B12: "Inf (\<Union>?fF) X = s"
        using B111 B2 P1 by fastforce
      have B13: "(\<Union>?fF) \<in> Fpow A"
      proof-
        have B130: "(\<forall>Ai \<in> ?fF. Ai \<in> Fpow A)"
          using B1 P1 by blast
        have B131:"finite ?fF"
          using Fpow_def P1 by blast
        have B132:"finite (\<Union>?fF)"
          using B130 B131 Fpow_def by blast
        have B133:"(\<Union>?fF) \<in> Pow A"
          by (metis (mono_tags, lifting) B130 Fpow_Pow_finite Int_Collect PowD PowI Sup_le_iff)
        show ?thesis
          using B132 B133 Fpow_Pow_finite by blast
      qed
      have B16: "\<exists>Ex. ?P Ex s"
        by (meson B111 B12 B13)
      show "s \<in> (fin_inf_cl A X)"
        using B16 has_inf_in_set fin_inf_cl_if1 by blast
    qed
  qed
qed

lemma fne_inf_cl_idempotent:
  "fne_inf_cl (fne_inf_cl A X) X = fne_inf_cl A X"
proof
  show "fne_inf_cl A X \<subseteq> fne_inf_cl (fne_inf_cl A X) X"
    by (meson subset_iff fne_inf_cl_extensive fne_inf_cl_imp0)
  next
  show "fne_inf_cl (fne_inf_cl A X) X \<subseteq> fne_inf_cl A X"
  proof
    fix s assume P0: "s \<in> fne_inf_cl (fne_inf_cl A X) X"
    show "s \<in> (fne_inf_cl A X)"
    proof-
      let ?P = "\<lambda>F x. F \<in> Fpow_ne A \<and> has_inf F X \<and> Inf F X = x"
      let ?f = "(\<lambda>x. SOME Fx. ?P Fx x)"
      obtain F where P1: "F \<in> Fpow_ne (fne_inf_cl A X) \<and> has_inf F X \<and> Inf F X = s"
        by (meson P0 fne_inf_cl_idempotent0)
      have B0: "\<forall>x \<in> F. (\<exists>Fx. ?P Fx x)"
        using P1 fne_inf_cl_obtains using fne_inf_cl_idempotent1 by blast
      let ?fF = "?f`F" let ?S = "{s \<in> X. \<exists>Ai \<in> ?fF. s = Inf Ai X}"
      have B1: "\<forall>x \<in> F. ?P (?f x) x"
        proof
          fix x assume A2: "x \<in> F"
          have B10: "\<exists>Fx. ?P Fx x"
            using A2 B0 by fastforce
          show "?P (?f x) x"
            using someI_ex[OF B10] by blast
        qed
      have B2: "?S = F"
      proof
        show "?S \<subseteq> F"
          proof
            fix s assume B6A0: "s \<in> ?S"
            have B60: "\<exists>Ai \<in> ?fF. s = Inf Ai X"
              using B6A0 by blast
            show "s \<in> F"
              using B1 B60 by auto
          qed
        next  
        show "F \<subseteq> ?S"
          proof
            fix s assume B6A1: "s \<in> F"
            show "s \<in> ?S" using B1 B6A1 has_inf_in_set by fastforce
        qed
      qed
      have B11A0: "has_inf F X"
        by (simp add: P1)
      have B110: "has_inf ?S X"
      using B11A0 B2 by presburger
      have B8: "\<forall>Ai \<in> ?fF. has_inf Ai X"
        using B1 by blast
      have B111: "has_inf (\<Union>?fF) X \<and> Inf (\<Union>?fF) X = Inf ?S X" 
        using B8 B110 inf_inf_imp_has_inf_eq[of "?fF" "X"] by simp
      have B12: "Inf (\<Union>?fF) X = s"
        using B111 B2 P1 by fastforce
      have B13: "(\<Union>?fF) \<in> Fpow_ne A"
      proof-
        have B130: "(\<forall>Ai \<in> ?fF. Ai \<in> Fpow_ne A)"
          using B1 P1 by blast
        have B131:"finite ?fF"
          using Fpow_Pow_finite P1 by fastforce
        have B132:"finite (\<Union>?fF)"
          by (metis (no_types, lifting) B130 B131 DiffD1 Fpow_Pow_finite Int_Collect finite_Union)
        have B133:"(\<Union>?fF) \<in> Pow A"
          by (metis (no_types, lifting) B130 Fpow_Pow_finite Int_Collect PowD PowI Sup_le_iff empty_in_Fpow insertCI insert_Diff)
        have B134:"is_ne ?fF"
          using P1 by blast
        show ?thesis
          using B130 B132 B133 B134 Fpow_Pow_finite by auto
      qed
      have B16: "\<exists>Ex. ?P Ex s"
        by (meson B111 B12 B13)
      show "s \<in> (fne_inf_cl A X)"
        using B16 has_inf_in_set fne_inf_cl_if1 by blast
    qed
  qed
qed





definition is_galois_connection::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a::order set \<Rightarrow> ('b::order \<Rightarrow> 'a::order) \<Rightarrow> 'b::order set \<Rightarrow> bool" where
  "is_galois_connection f X g Y \<equiv> (is_map f X Y) \<and> (is_map g Y X) \<and> 
                                   (is_antitone_on f X) \<and> (is_antitone_on g Y) \<and>
                                   (is_extensive_on (f \<circ> g) Y) \<and> (is_extensive_on (g \<circ> f) X)" 

definition galois_equiv::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a::order set \<Rightarrow> ('b::order \<Rightarrow> 'a::order) \<Rightarrow> 'b::order set \<Rightarrow> bool" where
  "galois_equiv f X g Y \<equiv> (\<forall>x \<in> X. \<forall>y \<in> Y.  (x \<le> g y \<longleftrightarrow> y \<le> f x))"

lemma is_galois_connection_imp1:
  "is_galois_connection f X g Y \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> f x2 \<le> f x1"
  by(simp add:is_galois_connection_def is_antitone_on_def)

lemma is_galois_connection_imp2:
  "is_galois_connection f X g Y \<Longrightarrow> y1 \<in> Y \<Longrightarrow> y2 \<in> Y \<Longrightarrow> y1 \<le> y2 \<Longrightarrow> g y2 \<le> g y1"
  by(simp add:is_galois_connection_def is_antitone_on_def)

lemma is_galois_connection_imp3:
  "is_galois_connection f X g Y \<Longrightarrow> x \<in> X \<Longrightarrow> x \<le> (g \<circ> f) x "
  by(simp add:is_galois_connection_def is_extensive_on_def)

lemma is_galois_connection_imp4:
  "is_galois_connection f X g Y \<Longrightarrow> y \<in> Y \<Longrightarrow> y \<le> (f \<circ> g) y "
  by(simp add:is_galois_connection_def is_extensive_on_def)

lemma galois_equiv_imp1:
  "galois_equiv f X g Y \<Longrightarrow> (is_map f X Y) \<Longrightarrow> (is_antitone_on f X)"
  apply(auto simp add:is_antitone_on_def galois_equiv_def is_map_def)
  by (metis dual_order.trans image_subset_iff order_refl)

lemma galois_equiv_imp2:
  "galois_equiv f X g Y \<Longrightarrow> (is_map g Y X) \<Longrightarrow> (is_antitone_on g Y)"
  apply(auto simp add:is_antitone_on_def galois_equiv_def is_map_def)
  by (metis dual_order.trans image_subset_iff order_refl)

lemma galois_equiv_imp3:
  "galois_equiv f X g Y \<Longrightarrow> (is_map f X Y) \<Longrightarrow>  (is_map g Y X) \<Longrightarrow>(is_extensive_on (f \<circ> g) Y)"
  apply(auto simp add:is_extensive_on_def  galois_equiv_def is_map_def)
  apply blast
  by (simp add: image_subset_iff)

lemma galois_equiv_imp4:
  "galois_equiv f X g Y \<Longrightarrow> (is_map f X Y) \<Longrightarrow>  (is_map g Y X) \<Longrightarrow>(is_extensive_on (g \<circ> f) X)"
  apply(auto simp add:is_extensive_on_def  galois_equiv_def is_map_def)
  by (simp add: image_subset_iff)


lemma gc_imp_ge:
  assumes A0:"is_galois_connection f X g Y"
  shows   "galois_equiv f X g Y"
proof-
  have B0:"\<And>x y. (x \<in> X \<and> y \<in> Y) \<longrightarrow> (x \<le> g y \<longleftrightarrow> y \<le> f x)"
  proof
    fix x y assume A1:"(x \<in> X \<and> y \<in> Y)"  
    show "(x \<le> g y \<longleftrightarrow> y \<le> f x)"
  proof
    assume A2:"x \<le> g y"
    have B1:"y \<le> (f \<circ> g) y"
      using A1 assms is_galois_connection_imp4 by blast
    have B2:"... \<le> f x"
      by (metis A1 A2 assms comp_apply image_subset_iff is_galois_connection_def is_galois_connection_imp1 is_map_def)
    show "y \<le> f x"
      using B1 B2 by auto
  next
    assume A3:"y \<le> f x"
    have B3:"x \<le> (g \<circ> f) x"
      using A1 assms is_galois_connection_imp3 by blast
    have B4:"... \<le> g y"
      by (metis A1 A3 assms comp_apply image_subset_iff is_galois_connection_def is_galois_connection_imp2 is_map_def)
    show "x \<le> g y"
      using B3 B4 by auto
    qed
  qed
  show ?thesis
    by (simp add: B0 galois_equiv_def)
qed
    
  
lemma ge_imp_gc:
  assumes A0:"galois_equiv f X g Y \<and>  (is_map f X Y) \<and> (is_map g Y X)"
  shows "is_galois_connection f X g Y"
proof-
  have B0:" (is_antitone_on f X) \<and> (is_antitone_on g Y)"
    using assms galois_equiv_imp1 galois_equiv_imp2 by blast
  have B1:"(is_extensive_on (f \<circ> g) Y) \<and> (is_extensive_on (g \<circ> f) X)"
    using assms galois_equiv_imp3 galois_equiv_imp4 by blast 
  show ?thesis
    by (simp add: B0 B1 assms is_galois_connection_def)
qed
 
lemma galois_triple_comp1:
  assumes A0:"is_galois_connection f X g Y"
  shows "\<And>x. x \<in> X \<longrightarrow> (f \<circ> g \<circ> f) x = f x"
proof
  fix x assume A1:"x \<in> X"
  have B1:"f x \<le> (f \<circ> g \<circ>f) x"
    by (metis A1 assms comp_apply image_subset_iff is_extensive_on_def is_galois_connection_def is_map_def)
  have B2:"f x \<ge> (f \<circ> g \<circ>f) x"
    by (metis A1 assms comp_apply is_antitone_on_def is_extensive_on_def is_galois_connection_def is_self_map_imp2)
  show "(f \<circ> g \<circ> f) x = f x"
    using B1 B2 by auto
qed

lemma galois_triple_comp2:
  assumes A0:"is_galois_connection f X g Y"
  shows "\<And>y. y\<in> Y \<longrightarrow> (g \<circ> f \<circ> g) y = g y"
proof
  fix y assume A1:"y \<in> Y"
  have B1:"g y \<le> (g \<circ> f \<circ>g) y"
    by (metis A1 assms comp_apply image_subset_iff is_extensive_on_def is_galois_connection_def is_map_def)
  have B2:"g y \<ge> (g \<circ> f \<circ> g) y"
    by (metis A1 assms comp_apply is_antitone_on_def is_extensive_on_def is_galois_connection_def is_self_map_imp2)
  show "(g \<circ> f \<circ> g) y = g y"
    using B1 B2 by auto
qed

lemma galois_double_comp1_is_cl:
  assumes A0:"is_galois_connection f X g Y"
  shows "is_closure_on (f \<circ> g) Y \<and> is_closure_on (g \<circ> f) X"
proof-
  have B0:"is_extensive_on (f \<circ> g) Y \<and> is_extensive_on (g \<circ> f) X"
    using assms is_galois_connection_def by auto
  have B1:"is_isotone_on (f \<circ> g) Y \<and> is_isotone_on (g \<circ> f) X"
    by (metis antitone_comp assms is_galois_connection_def)
  have B2:"is_idempotent_on (f \<circ> g) Y \<and> is_idempotent_on (g \<circ> f) X"
    apply(auto simp add:is_idempotent_on_def )
    using assms galois_triple_comp2 apply fastforce
    apply (simp add: B0 is_extensive_on_imp_map)
    using assms galois_triple_comp1 apply fastforce
    by (simp add: B0 is_extensive_on_imp_map)
  show ?thesis
    by (simp add: B0 B1 B2 is_closure_on_def is_proj_on_def)
qed



lemma l_is_map:
  "is_map (\<lambda>A. lb_set A X) (Pow X) (Pow X)"
  by (simp add: Pow_not_empty image_subset_iff is_map_def lb_set_subset_space)

lemma u_is_map:
  "is_map (\<lambda>A. ub_set A X) (Pow X) (Pow X)"
  by (simp add: Pow_not_empty image_subset_iff is_map_def ub_set_subset_space)

lemma l_is_antitone:
  "is_antitone_on (\<lambda>A. lb_set A X) (Pow X)"
  by (simp add: is_antitone_on_def lb_set_antitone1)

lemma u_is_antitone:
  "is_antitone_on (\<lambda>A. ub_set A X) (Pow X)"
  by (simp add: is_antitone_on_def ub_set_antitone1)

lemma lu_is_map:
  "is_self_map ((\<lambda>A. lb_set A X) \<circ> (\<lambda>A. ub_set A X)) (Pow X)"
  using is_map_comp l_is_map u_is_map by blast

lemma ul_is_map:
  "is_self_map ((\<lambda>A. ub_set A X) \<circ> (\<lambda>A. lb_set A X)) (Pow X)"
  using is_map_comp l_is_map u_is_map by blast

lemma lu_is_extensive:
  "is_extensive_on ((\<lambda>A. lb_set A X) \<circ> (\<lambda>A. ub_set A X)) (Pow X)"
  by (simp add: is_extensive_on_def lu_extensive lu_is_map)

lemma ul_is_extensive:
  "is_extensive_on ((\<lambda>A. ub_set A X) \<circ> (\<lambda>A. lb_set A X)) (Pow X)"
  by (simp add: is_extensive_on_def ul_extensive ul_is_map)

lemma ul_is_galois:
  "is_galois_connection (\<lambda>A. lb_set A X) (Pow X) (\<lambda>A. ub_set A X) (Pow X)"
  by (simp add: is_galois_connection_def l_is_antitone l_is_map lu_is_extensive u_is_antitone u_is_map ul_is_extensive)

lemma lu_is_galois:
  "is_galois_connection (\<lambda>A. ub_set A X) (Pow X) (\<lambda>A. lb_set A X) (Pow X)"
  by (simp add: is_galois_connection_def l_is_antitone l_is_map lu_is_extensive u_is_antitone u_is_map ul_is_extensive)


definition is_inter_system::"'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_inter_system A X \<equiv> (A \<subseteq> Pow X) \<and> (\<forall>a \<in> Pow(A). \<Inter>a \<in> A)"

definition inter_sys_cl::"'a set set \<Rightarrow> 'a set \<Rightarrow> ('a set \<Rightarrow> 'a set)" where
  "inter_sys_cl A X \<equiv> (\<lambda>E. \<Inter>(ub_set {E} A))"

lemma inter_sys_ne:
  "is_inter_system A  X \<Longrightarrow> A \<noteq> {}"
  by (meson Pow_bottom empty_iff is_inter_system_def)

lemma inter_sys_imp1:
  "is_inter_system A  X \<Longrightarrow>  (A \<subseteq> Pow X)"
  by (simp add:is_inter_system_def)

lemma inter_sys_imp2:
 assumes A0:"is_inter_system A X"
  shows"(\<And>x. x\<subseteq>X \<Longrightarrow> is_min (\<Inter>(ub_set {x} A)) (ub_set {x} A))"
proof-
  fix x assume A1:"x \<subseteq> X"
  let ?i="\<Inter>(ub_set {x} A)"
  have B0:"?i \<in> A"
    by (meson Pow_iff assms is_inter_system_def ub_set_subset_space)
  have B1:"?i lb  (ub_set {x} A)"
    by (simp add: Inf_lower is_lb_simp2)
  have B2:"?i \<in> (ub_set {x} A)"
    by (meson B0 le_Inf_iff ub_set_elm ub_set_imp)
  have B3:"is_min ?i  (ub_set {x} A)"
    by (simp add: B2 is_inf_in_imp1 is_min_if1 sets_have_inf1)
  show "is_min (\<Inter>(ub_set {x} A)) (ub_set {x} A)"
    by (simp add: B3)
qed

lemma inter_sys_imp3:
 assumes A0:"is_inter_system A X"
  shows"(\<And>x. x\<subseteq>X \<Longrightarrow> has_min (ub_set {x} A))"
  using assms has_min_def inter_sys_imp2 by blast

lemma inter_system_is_clr:
  "is_inter_system A X \<Longrightarrow> is_clr A (Pow X)"
  by(auto simp add:is_clr_def inter_sys_ne inter_sys_imp1 inter_sys_imp3)

lemma inter_system_cl_is_cl1:
  "is_inter_system A X \<Longrightarrow> is_extensive_on (inter_sys_cl A X) (Pow X)"
  apply(auto simp add:is_extensive_on_def is_map_def inter_sys_cl_def is_inter_system_def)
  by (meson insertI1 subsetD ub_set_imp)

lemma inter_system_cl_is_cl2:
  "is_inter_system A X \<Longrightarrow> is_isotone_on (inter_sys_cl A X) (Pow X)"
  apply(auto simp add:is_isotone_on_def is_map_def inter_sys_cl_def is_inter_system_def)
  by (meson subset_iff ub_set_singleton_antitone)

lemma inter_system_cl_is_cl3:
  "is_inter_system A X \<Longrightarrow> is_idempotent_on (inter_sys_cl A X) (Pow X)"
  apply(auto simp add:is_idempotent_on_def is_map_def inter_sys_cl_def is_inter_system_def)
  apply (metis Inf_lower singletonD ub_set_elm ub_set_imp2)
  using subset_trans ub_set_imp by fastforce

lemma inter_system_cl_is_cl:
  "is_inter_system A X \<Longrightarrow> is_closure_on (inter_sys_cl A X) (Pow X)"
  by(simp add:is_closure_on_def is_proj_on_def inter_system_cl_is_cl1 inter_system_cl_is_cl2 inter_system_cl_is_cl3)

section Completeness


lemma sup_complete_imp0:
  "is_sup_complete X \<Longrightarrow> A \<in> Pow_ne X \<Longrightarrow> has_sup A X"
  using has_sup_in_set is_sup_complete_def by blast

lemma inf_complete_imp0:
  "is_inf_complete X \<Longrightarrow> A \<in> Pow_ne X \<Longrightarrow> has_inf A X"
  using has_inf_in_set is_inf_complete_def by blast

lemma sup_complete_imp1:
  "is_sup_complete X \<Longrightarrow> A \<in> Pow_ne X \<Longrightarrow> Sup A X \<in> X"
  using has_sup_in_set is_sup_complete_def by blast

lemma inf_complete_imp1:
  "is_inf_complete X \<Longrightarrow> A \<in> Pow_ne X \<Longrightarrow> Inf A X \<in> X"
  using has_inf_in_set is_inf_complete_def by blast

lemma inf_complete_imp2:
  "is_inf_complete X \<Longrightarrow> C \<subseteq> X \<Longrightarrow> A \<in> Pow_ne C \<Longrightarrow> has_inf A X"
  by (meson inf_complete_imp0 pow_ne_imp4)
            
lemma sup_complete_imp2:
  "is_sup_complete X \<Longrightarrow> C \<subseteq> X \<Longrightarrow> A \<in> Pow_ne C \<Longrightarrow> has_sup A X"
  by (meson pow_ne_imp4 sup_complete_imp0)

lemma inf_complete_imp3:
  "is_inf_complete X \<Longrightarrow> C \<subseteq> X \<Longrightarrow> A \<in> Pow_ne C \<Longrightarrow> Inf A X \<in> X"
  by (simp add: has_inf_in_set inf_complete_imp2)
             
lemma sup_complete_imp3:
  "is_sup_complete X \<Longrightarrow> C \<subseteq> X \<Longrightarrow> A \<in> Pow_ne C \<Longrightarrow> Sup A X \<in> X"
  by (simp add: has_sup_in_set sup_complete_imp2)

lemma inf_complete_min1:
   "is_inf_complete X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> is_min (Inf X X) X"
  by (simp add: inf_in_min is_inf_complete_def)

lemma sup_complete_max1:
   "is_sup_complete X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> is_max (Sup X X) X"
  by (simp add: sup_in_max is_sup_complete_def)

lemma inf_complete_min2:
   "is_inf_complete X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> has_min X"
  using has_min_def inf_complete_min1 by blast

lemma sup_complete_max2:
   "is_sup_complete X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> has_max X"
  using has_max_def sup_complete_max1 by auto

lemma has_max_imp_ub_ne:
  assumes A0:"has_max X" and A1:"A \<in> Pow X "
  shows " ub_set A X \<noteq> {}"
proof-
  obtain m where A2:"is_max m X"
    using A0 has_max_iff2 by auto
  have B0:"m \<in> (ub_set A X)"
    using A1 A2 is_max_imp_set by auto
  show ?thesis
    using B0 by auto
qed

lemma has_min_imp_lb_ne:
  assumes A0:"has_min X" and A1:"A \<in> Pow X "
  shows " lb_set A X \<noteq> {}"
proof-
  obtain m where A2:"is_min m X"
    using A0 has_min_iff2 by auto
  have B0:"m \<in> (lb_set A X)"
    using A1 A2 is_min_imp_set by auto
  show ?thesis
    using B0 by auto
qed


definition is_complete_lattice::"'a::order set \<Rightarrow> bool" where
  "is_complete_lattice X \<equiv> (is_sup_complete X) \<and> (is_inf_complete X)"

lemma is_complete_imp_max_and_inf:
  "is_complete_lattice X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> (is_inf_complete X \<and> has_max X)"
  by (simp add: is_complete_lattice_def sup_complete_max2)

lemma is_complete_imp_min_and_sup:
  "is_complete_lattice X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> (is_sup_complete X \<and> has_min X)"
  by (simp add: is_complete_lattice_def inf_complete_min2)

lemma max_imp_ub_set_ne:
  "has_max X \<Longrightarrow> A \<in> Pow_ne X \<Longrightarrow> ub_set A X \<noteq> {}"
  by (simp add: has_max_imp_ub_ne)

lemma min_imp_lb_set_ne:
  "has_min X \<Longrightarrow> A \<in> Pow_ne X \<Longrightarrow> lb_set A X \<noteq> {}"
  by (simp add: has_min_imp_lb_ne)

lemma inf_complete_max_exists_sup:
  "is_inf_complete X \<and> has_max X\<Longrightarrow> A \<in> Pow_ne X \<Longrightarrow> has_sup A X"
  by (simp add: inf_complete_imp0 inf_ub_imp_has_sup max_imp_ub_set_ne ub_set_subset_space)


lemma sup_complete_min_exists_inf:
  "is_sup_complete X \<and> has_min X\<Longrightarrow> A \<in> Pow_ne X \<Longrightarrow> has_inf A X"
  by (simp add: sup_complete_imp0 sup_lb_imp_has_inf min_imp_lb_set_ne lb_set_subset_space)

lemma inf_comp_max_imp_sup_comp_min:
 "(is_inf_complete X \<and> has_max X) \<Longrightarrow> (is_sup_complete X \<and> has_min X)"
  by (simp add: has_max_imp_ne inf_complete_max_exists_sup inf_complete_min2 is_sup_complete_def)

lemma sup_comp_max_imp_inf_comp_min:
 "(is_sup_complete X \<and> has_min X) \<Longrightarrow> (is_inf_complete X \<and> has_max X)"
  by (simp add: has_min_imp_ne is_inf_complete_def sup_complete_max2 sup_complete_min_exists_inf)


lemma sup_comp_min_imp_comp:
  "(is_sup_complete X \<and> has_min X) \<Longrightarrow> is_complete_lattice X"
  by (simp add: is_complete_lattice_def sup_comp_max_imp_inf_comp_min)

lemma inf_comp_max_imp_comp:
  "(is_inf_complete X \<and> has_max X) \<Longrightarrow> is_complete_lattice X"
  by (simp add: inf_comp_max_imp_sup_comp_min sup_comp_min_imp_comp)


section ClosureRangesAndCompleteness
context
  fixes C X::"'a::order set" 
  assumes A0:"is_inf_complete X" and
          A1:"C \<subseteq> X" and
          A2:"C \<noteq> {}"
begin

lemma clr_inf_complete1:
  "is_clr C X \<Longrightarrow> A \<in> Pow_ne C \<Longrightarrow> has_inf A X"
  using A0 A1 inf_complete_imp2 by blast

lemma clr_inf_complete2:
  "is_clr C X \<Longrightarrow> A \<in> Pow_ne C \<Longrightarrow> Inf A X \<in> C"
  using clr_inf_closed clr_inf_complete1 by blast

lemma clr_inf_complete3:
  "is_clr C X \<Longrightarrow> A \<in> Pow_ne C \<Longrightarrow>  Inf A C = Inf A X"
  by (simp add: A1 clr_inf_complete1 clr_inf_complete2 inf_subset_eq1)


lemma clr_inf_on_cinf_converse:
  assumes A3:"\<forall>A \<in> Pow_ne C. has_inf A C \<and> Inf A C = Inf A X" and
          A4:"\<forall>x \<in> X. ub_set {x} C \<noteq> {}" and
          A5:"C \<noteq> {}"
  shows "is_clr C X"
proof-
  have B0:"\<forall>x \<in> X. (has_min (ub_set {x} C))"
  proof
    fix x assume A5:"x \<in> X"
    let ?P="ub_set {x} C"
    have B0:"?P \<noteq> {}"
      by (simp add: A4 A5)
    have B2:"?P \<subseteq> X"
      by (simp add: A1 ub_set_subset2)
    have B3:"has_inf ?P X"
      by (simp add: A0 B0 B2 inf_complete_imp0)
    obtain i where B30:"is_inf i ?P X"
      using B3 inf_obtain by blast
    have B31:"i \<in> C \<and> i lb ?P"
      by (metis A3 B0 B30 PowI has_inf_in_set is_inf_in_imp1 is_inf_inf_eq lb_set_imp1 pow_ne_if ub_set_subset_space)
    have B32:"x \<le> i"
      by (meson A5 B30 insertCI is_inf_in_imp3 ub_set_mem)
    have B33:"i \<in> ?P"
      by (metis B31 B32 singletonI up_cl_ub up_closure_in_imp)
    have B10:"is_min i ?P"
      using B2 B30 B33 is_inf_in_set_imp_is_min by auto
    show "has_min (ub_set {x} C)"
      using B10 has_min_iff2 by blast
  qed
  show ?thesis
    by (simp add: A1 A5 B0 is_clr_def)
qed

lemma clr_on_comp_semilattice:
  assumes A2:"has_min X" and
          A3:"is_closure_on f X"
  shows "\<forall>x \<in> X. Inf {y \<in> (f`X). x \<le> f y} X = min (ub_set {x} (f`X))" 
proof
  fix x assume A2:"x \<in> X"
  let ?E1="{y \<in> (f`X). x \<le> (f y)}" let ?E2="ub_set {x} (f`X)"
  have B0:"?E1 = ?E2"
    apply(auto simp add:ub_set_def ub_def)
    using A3 is_closure_on_imp4 is_idempotent_imp1 apply fastforce
    by (metis A3 is_closure_on_imp4 is_idempotent_imp1)
  have B1:"has_min ?E2"
    using A2 A3 closure_range_is_clr is_clr_imp2 by blast
  have B2:"(min ?E2) lb ?E2"
    using B1 has_min_def is_sup_imp_lt_ub is_sup_in_iff min_if by blast
  have B3:"(min ?E2) \<in> X"
    by (metis A3 B1 has_sup_def has_sup_in_imp1 is_closure_on_imp2 is_self_map_imp min_if subsetD ub_set_subset_space)
  have B4:"\<forall>l \<in> lb_set ?E2 X. l \<le> (min ?E2)"
    by (metis B1 has_sup_def has_sup_in_imp1 lb_set_imp min_if)
  have B5:"(min ?E2) \<in> lb_set ?E2 X"
    using B2 B3 lb_set_if by blast
  have B6:"is_max (min ?E2) (lb_set ?E2 X)"
    by (simp add: B4 B5 is_max_if2)
  have B7:"is_inf (min ?E2) ?E2 X"
    by (simp add: B6 is_inf_def)
  have B8:"is_inf (min ?E2) ?E1 X"
    by (simp add: B0 B7)
  show "Inf {y \<in> (f`X). x \<le> f y} X = min (ub_set {x} (f`X))"
    using B8 is_inf_inf_eq by fastforce
qed
end

lemma clr_on_comp_semilattice2:
  fixes X::"'a::order set" 
  assumes A0:"is_inf_complete X" and
          A2:"has_min X" and
          A3:"is_closure_on f X"
  shows "\<forall>x \<in> X. Inf {y \<in> (f`X). x \<le> f y} X = f x" 
proof-
  have B0:"\<forall>x \<in> X. closure_from_clr (clr_from_closure f X) x = min (ub_set {x} (f`X))"
    by (simp add: closure_from_clr_def clr_from_closure_def)
  have B1:"\<forall>x \<in> X. closure_from_clr (clr_from_closure f X) x = f x"
    using A3 cl_cr_cl_eq_cl by auto
  have B2:"\<forall>x \<in> X. f x = min (ub_set {x} (f`X))"
    using B0 B1 by fastforce
  have B3:"\<forall>x \<in> X.  Inf {y \<in> (f`X). x \<le> f y} X =  min (ub_set {x} (f`X))"
    using A0 A2 A3 clr_on_comp_semilattice by blast
  have B4:"\<forall>x \<in> X. f x = min (ub_set {x} (f`X))"
    using B2 by blast
  show ?thesis
    using B3 B4 by fastforce
qed

context
  fixes C X::"'a::order set" 
  assumes A0:"is_complete_lattice X" and
          A1:" C \<subseteq> X"
begin

lemma complete_clr1:
  assumes A2:"is_clr C X"
  shows "\<And>A. A \<in> Pow C \<longrightarrow> Inf A X \<in> C"
proof
  fix A assume A3:"A \<in> Pow C"
  have B0:"A \<subseteq> C \<and> A \<subseteq> X"
    using A1 A3 by blast 
  have B1:"has_inf A X"
    proof(cases "A={}")
      case True
      then show ?thesis
        using A0 assms inf_in_degenerate2 is_clr_imp1 is_complete_imp_max_and_inf by blast
    next
      case False
      then show ?thesis
        using A0 B0 is_complete_lattice_def is_inf_complete_def by blast
    qed
  show "Inf A X \<in> C"
    by (simp add: B0 B1 assms clr_inf_closed)
qed

lemma complete_clr2:
  assumes "is_clr C X"
  shows "\<And>A. A \<in> Pow C \<longrightarrow> Inf A C = Inf A X"
proof
  fix A assume A3:"A \<in> Pow C"
  have B0:"A \<subseteq> C \<and> A \<subseteq> X"
    using A1 A3 by blast 
  show "Inf A C = Inf A X"
  proof(cases "A={}")
    case True
    then show ?thesis
      by (metis A0 A3 B0 assms complete_clr1 inf_in_degenerate2 inf_subset_eq1 is_clr_def is_complete_imp_max_and_inf subset_empty)
  next
    case False
    then show ?thesis
      by (metis A0 A3 assms clr_inf_complete3 is_clr_def is_complete_lattice_def pow_ne_if)
  qed
qed

lemma complete_clr3:
  assumes "\<And>A. A \<in> Pow C \<longrightarrow> Inf A X \<in> C"
  shows "is_clr C X"
proof-
  have B0:"\<forall>x \<in> X. has_min (ub_set {x} C)"
  proof
    fix x assume A3:"x \<in> X"
    have B1:"(max X) \<in> C"
      by (metis Pow_bottom assms inf_in_degenerate)
    have B2:"(max X) \<in> ub_set {x} C"
      by (metis A0 A3 B1 empty_iff has_max_iff is_complete_imp_max_and_inf max_if2 singletonD ub_set_elm)
    have B3:"ub_set {x} C \<noteq> {}"
      using B2 by auto
    have B4:" Inf (ub_set {x} C) X \<in> C"
      by (simp add: assms ub_set_subset_space)
    have B5:"x \<in> lb_set (ub_set {x} C) X"
      by (simp add: A3 lb_set_elm ub_set_imp)
    have B6:"x \<le> Inf (ub_set {x} C) X"
      by (meson A0 A1 B3 B5 PowI inf_complete_imp0 inf_imp_gt_lb is_complete_lattice_def pow_ne_if ub_set_subset2)
    have B7:"Inf (ub_set {x} C) X \<in> ub_set {x} C"
      by (simp add: B4 B6 ub_set_mem_iff)
    have B8:"Inf (ub_set {x} C) X lb (ub_set {x} C)"
      by (meson A0 A1 B3 Pow_iff has_inf_in_imp2 inf_complete_imp0 is_complete_lattice_def lb_def pow_ne_if ub_set_subset2)
    have B9:"is_min (Inf (ub_set {x} C) X) (ub_set {x} C)"
      by (simp add: B7 B8 is_min_def lb_set_if)
    show "has_min (ub_set {x} C)"
      using B9 is_min_imp_has_min by auto
   qed
  show ?thesis
    by (metis A1 B0 Pow_not_empty assms ex_in_conv is_clr_def)
qed
    
end



context
  fixes C X::"'a::order set" 
  assumes A0:"is_complete_lattice X" and
          A1:" C \<subseteq> X" and
          A2:"is_clr C X"
begin

lemma complete_clr_sup1:
  assumes A3:"A \<subseteq> C"
  shows "is_sup (Inf (ub_set A C) X) A C \<and> Sup A C =  (Inf (ub_set A C) C)"
proof-
  let ?U="ub_set A C" let ?I="Inf ?U X"
  have B0:"(ub_set A C \<noteq> {})"
    by (metis A0 A2 PowI assms closure_range.intro closure_range.space_is_ne has_max_imp_ub_ne is_clr_imp_max is_complete_imp_max_and_inf)
  have B1:"has_inf (ub_set A C) X"
    by (meson A0 A1 B0 PowI dual_order.trans is_complete_lattice_def is_inf_complete_def pow_ne_if ub_set_subset_space)
  have B2:"Inf (ub_set A C) X = Inf (ub_set A C) C "
    by (metis A0 A2 PowI complete_clr2 is_clr_imp1 ub_set_subset_space)
  have B3:"has_inf (ub_set A C) C"
    by (meson A1 A2 B1 clr_inf_closed inf_subset_eq1 ub_set_subset_space)
  have B4:"Sup A C =  (Inf (ub_set A C) C)"
    by (simp add: B3 assms sup_in_eq_inf_in_ub)
  have B5:"is_sup (Inf (ub_set A C) C) A C"
    by (simp add: B3 assms inf_is_inf is_inf_ub_imp_is_sup)
  show ?thesis
    by (simp add: B2 B4 B5)
qed

lemma complete_clr_sup2:
  assumes "A \<subseteq> C"
  shows "has_sup A C"
  by (meson A0 A1 A2 complete_clr_sup1 assms has_min_iff2 has_sup_def is_sup_in_imp1)

end

context
 fixes f::"'a::order \<Rightarrow> 'a::order" and 
       A X::"'a::order set" 
  assumes A0:"X \<noteq> {}" and 
          A1:"is_complete_lattice X" and
          A2:"is_closure_on f X"      
begin

lemma closure_of_min:
  "f (min X) = min (f`X)"
proof-
  let ?mx="min X" let ?Y="f`X" let ?my="min ?Y"
  have B0:"f ?mx \<in> ?Y"
    by (metis A0 A1 if_has_min_min_unique image_eqI is_complete_imp_min_and_sup is_min_imp min_if)
  have B1:"\<forall>y \<in> ?Y. (f ?mx) \<le> y"
  proof
    fix y assume A3:"y \<in> ?Y"
    obtain x where B1:"x \<in> X \<and> y = f x"
      using A3 by blast
    have B2:"?mx \<le> x"
      by (metis A0 A1 B1 has_min_iff2 is_complete_imp_min_and_sup is_min_iff min_if)
    have B3:"f ?mx \<le> f x"
      by (metis A0 A1 A2 B1 inf_complete_min1 is_closure_imp_iso_imp1 is_complete_lattice_def is_min_iff min_if)
    show "(f ?mx) \<le> y"
      by (simp add: B1 B3)
  qed
  have B2:"is_min (f ?mx) ?Y"
    by (simp add: B0 B1 is_min_if2)
  show ?thesis
    using B2 min_if by auto
qed

lemma complete_clr_sup3:
  assumes "A \<subseteq> X"
  shows "f (Sup A X) = f (Sup (f`A) X) \<and> f (Sup (f`A) (f`X)) = f (Sup (f`A) X)"
proof(cases "A={}")
  case True
  have B0:"Sup A X = min X"
    by (simp add: True sup_in_degenerate)
  have B1:"f`A = {}"
    by (simp add: True)
  have B2:"f (Sup (f`A) (f`X)) = f (Sup (f`A) X)"
    by (metis A1 A2 B1 True closure_of_min closure_range_is_clr complete_clr_sup2 empty_subsetI has_sup_in_set is_closure_on_imp4 is_clr_imp1 is_idempotent_imp2 sup_in_degenerate)
  then show ?thesis
    using True by fastforce
next
  case False
  have B2:"\<forall>a \<in> A. a \<le> f a"
    using A2 assms closure_eq_if_closure_l by blast
  have B3:"(f`A) \<subseteq> X"
    by (meson A2 assms dual_order.trans image_mono is_closure_on_imp2 is_self_map_imp)
  have B4:"has_sup (f`A) X"
    by (meson A0 A1 B3 False PowI image_is_empty is_complete_imp_min_and_sup is_sup_complete_def pow_ne_if)
  have B5:"\<forall>a \<in> A. f a \<le> Sup (f`A) X"
    using B4 has_sup_in_imp2 by blast
  have B6:"\<forall>a \<in> A. a \<le> Sup (f`A) X"
    using B2 B5 dual_order.trans by blast
  have B7:"Sup A X \<le> Sup (f`A) X"
    by (meson A0 A1 B4 B6 False PowI assms has_sup_imp3 has_sup_in_set is_complete_imp_min_and_sup is_sup_complete_def pow_ne_if)
  have B8:"f (Sup A X) \<le>  f (Sup (f`A) X)"
    by (meson A1 A2 B4 B7 False Pow_iff assms has_sup_in_set is_closure_imp_iso_imp1 is_complete_lattice_def pow_ne_if sup_complete_imp1)
  have B9:"f`X \<subseteq> X"
    by (simp add: A2 is_closure_on_imp2 is_self_map_imp)
  have B10:"Sup (f`A) X \<le> Sup (f`A) (f`X)"
    by (metis A0 A1 A2 B4 B9 assms closure_range_is_clr complete_clr_sup1 image_mono is_sup_sup_eq sup_geq_rsup sup_is_sup)
  have B11:"is_clr (f`X) X"
    by (simp add: A0 A2 closure_range_is_clr)
  have B12:"(f`A) \<subseteq> (f`X)"
    by (simp add: assms image_mono)
  have B13:"has_sup (f`A) (f`X)"
    by (meson A1 B11 B12 B9 complete_clr_sup2)
  have B14:"Sup (f`A) (f`X) \<in> X"
    by (metis B13 B9 has_sup_in_set subsetD)
  have B15:"f (Sup (f`A) X) \<le> f (Sup (f`A) (f`X))"
    using A2 B10 B14 B4 has_sup_in_set is_closure_imp_iso_imp1 by blast
  have B16:"\<forall>a \<in> A. a \<le> Sup A X"
    by (meson A0 A1 False PowI assms has_sup_in_imp2 is_complete_imp_min_and_sup is_sup_complete_def pow_ne_if)
  have B17:"\<forall>a \<in> A. f a \<le> f (Sup A X)"
    by (meson A1 A2 B16 False Pow_iff assms in_mono is_closure_imp_iso_imp1 is_complete_lattice_def pow_ne_if sup_complete_imp1)
  have B18:"f (Sup A X) \<in> (f`X)"
    by (simp add: A0 A1 False assms is_complete_imp_min_and_sup sup_complete_imp1)
  have B19:"Sup (f`A) (f`X) \<le> f (Sup A X)"
    using B13 B17 B18 has_sup_imp3 by fastforce
  have B20:"f (Sup (f`A) (f`X)) = f (Sup (f`A) X)"
    by (meson A2 B14 B15 B19 B4 B8 closure_eq_if_closure_r has_sup_in_set order_antisym_conv order_trans)
  have B21:"f (Sup A X) = f (Sup (f`A) X)"
    by (meson A1 A2 B10 B19 B4 B8 False Orderings.order_eq_iff Pow_iff assms closure_eq_if_closure_r has_sup_in_set is_complete_lattice_def order_trans pow_ne_if sup_complete_imp1)
  then show ?thesis
    using B20 by blast
qed

end

lemma closure_sups1:
  fixes f::"'a::order \<Rightarrow> 'a::order" and A X::"'a::order set" 
  assumes A0:"is_closure_on f X" and A1:"A \<subseteq> X" and  A2:"is_complete_lattice X" and A3:"X \<noteq> {}"
  shows "f (Sup A X) = (Sup (f`A) (f`X))"
  by (meson A0 A1 A2 A3 closure_on_sup_eq1 complete_clr_sup2 equalityD1 has_sup_has_lub has_sup_singleton2 is_clr_def)

lemma closure_sups2:
  fixes f::"'a::order \<Rightarrow> 'a::order" and A X::"'a::order set" 
  assumes A0:"is_closure_on f X" and A1:"A \<subseteq> (f`X)" and  A2:"is_complete_lattice X" and A3:"X \<noteq> {}"
  shows "Sup A (f`X) = f (Sup A X)"
  by (metis (full_types) A0 A1 A2 A3 closure_sups1 complete_clr_sup3 subset_imageE)

lemma is_moore_family_imp1:
  "is_moore_family C X \<Longrightarrow> a \<in> C \<Longrightarrow> a \<subseteq> X"
  using PowD is_moore_family_def by auto

lemma is_moore_family_imp2:
  "is_moore_family C X \<Longrightarrow> A \<subseteq> C \<Longrightarrow> a \<in> A \<Longrightarrow> a \<subseteq> X"
  by (meson PowD is_moore_family_def subsetD)

lemma is_moore_family_imp3:
  "is_moore_family (C::'a::order set set) X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> (\<Inter>(ub_set {A} C)) lb (ub_set {A} C)"
  by (simp add: Inter_lower is_lb_simp2)


lemma is_moore_family_inter:
  assumes "is_moore_family C X" and "A \<in> Pow_ne C" 
  shows " \<Inter>A \<in> C"
proof-
  have B0:"(Inf A (Pow X)) = \<Inter>A \<inter> X"
    by (simp add: sets_have_inf6)
  have B1:"... = \<Inter>A "
    using assms(1) assms(2) is_moore_family_imp1 by fastforce
  show ?thesis
    by (metis B0 B1 assms(1) assms(2) is_moore_family_def)
qed

lemma is_moore_family_imp4:
  "is_moore_family C X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> (\<Inter>(ub_set {A} C)) \<in> C"
  by (metis (full_types) Pow_iff bex_empty is_moore_family_def is_moore_family_inter pow_ne_if singletonI ub_set_subset_space up_cl_ub up_closure_in_imp)

lemma is_moore_family_imp5:
  "is_moore_family C X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> A \<subseteq> (\<Inter>(ub_set {A} C))"
  by (simp add: le_Inf_iff ub_set_imp)

lemma is_moore_family_imp6:
  "is_moore_family C  X \<Longrightarrow> A \<subseteq> X \<Longrightarrow>(\<Inter>(ub_set {A} C)) \<in> (ub_set {A} C)"
  by (simp add: is_moore_family_imp4 is_moore_family_imp5 ub_set_mem_iff)

lemma is_moore_family_imp7:
  "is_moore_family C X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_min (\<Inter>(ub_set {A} C))  (ub_set {A} C)"
  by (simp add: Inter_lower is_min_if2 is_moore_family_imp6)

lemma is_moore_family_imp8:
  "is_moore_family C X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> has_min (ub_set {A} C)"
  using has_min_iff2 is_moore_family_imp7 by blast

lemma is_moore_family_is_clr:
  "is_moore_family C X \<Longrightarrow> is_clr C (Pow X)"
  apply(auto simp add:is_clr_def)
  apply (simp add: is_moore_family_def)
  using is_moore_family_imp1 apply blast
  by (simp add: is_moore_family_imp8)
  

lemma lattice_inf_is_inf:
  "is_inf (inf (a::'a::lattice) b) {a, b} UNIV"
  by (simp add: is_inf_def is_max_iff lb_set_mem_iff)

lemma lattice_sup_is_sup:
  "is_sup (sup (a::'a::lattice) b) {a, b} UNIV"
  by (simp add: is_sup_def is_min_iff ub_set_mem_iff)

lemma order_bot_is_min:
  "is_min (bot::'a::order_bot) UNIV"
  by (simp add: is_min_bot)

definition filter_closure::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "filter_closure A X \<equiv> {x \<in> X. \<exists>F \<in> Fpow_ne A. Inf F X \<le> x}"

lemma filter_closure_mem_iff:
  "x \<in> filter_closure A X  \<longleftrightarrow> (x \<in> X \<and> (\<exists>F \<in> Fpow_ne A. Inf F X \<le> x))"
  by (simp add: filter_closure_def)

lemma filter_closure_obtains:
  assumes "x \<in>  filter_closure A X"
  obtains Fx where "Fx \<in> Fpow_ne A \<and> Inf Fx X \<le> x"
  by (meson assms filter_closure_mem_iff)


context
  fixes X::"'a::order set"
  assumes is_ne:"X \<noteq> {}" and
          toped:"has_max X" and
          csinf:"is_inf_complete X"
begin

lemma filter_csinf_moore_family1:
  assumes "EF \<in> Pow_ne (filters X)"
  shows "(\<Inter>EF) \<in> (filters X)"
proof-
  let ?I="(\<Inter>EF)"
  have B0:"\<forall>F \<in> EF. max X \<in> F"
    by (metis assms filter_contains_max filters_mem_iff if_has_max_max_unique max_if pow_ne_imp2 subset_eq toped)
  have B1:"is_dwdir ?I"
  proof-
    have B10:"\<And>a b. a \<in>?I \<and> b \<in> ?I\<longrightarrow> (\<exists>c\<in>?I. c lb {a, b})"
    proof
      fix a b assume A1:"a \<in>?I \<and> b \<in> ?I"
      have B11:"\<forall>F \<in> EF. a \<in> F \<and> b \<in> F"
        using A1 by blast
      have B12:"\<forall>F \<in> EF. F \<subseteq> X"
        by (meson PowD assms filters_mem_iff in_mono pow_ne_imp2)
      have B13:"a \<in> X \<and> b \<in> X"
        using B11 B12 assms by fastforce
      have B14:"\<forall>F \<in> EF. has_inf {a, b} X"
        by (simp add: B13 csinf inf_complete_imp0)
      have B15:"\<forall>F \<in> EF. Inf {a, b} X \<in> F"
        by (meson B11 B14 assms filter_inf_closed filters_mem_iff in_mono pow_ne_imp2)
      have B16:"Inf {a, b} X \<in> ?I"
        by (simp add: B15)
      have B17:"Inf {a, b} X lb {a, b}"
        by (metis B14 DiffD2 assms has_inf_in_imp2 insert_iff lb_def subset_empty subset_emptyI)
      show "\<exists>c\<in>?I. c lb {a, b}"
        using B16 B17 by blast
    qed
    show ?thesis
      by (metis B0 B10 InterI empty_iff is_dwdir_if1)
  qed
  have B2:"is_up_cl ?I X"
    apply(auto simp add:is_up_cl_def up_cl_def)
    apply (meson is_filter_def assms filters_mem_iff is_up_cl_imp2 pow_ne_imp2 subset_iff)
    by (metis DiffE Pow_iff all_not_in_conv assms filters_mem_iff in_mono insertI1)
  show ?thesis
    by (simp add: B1 B2 is_filter_def filters_mem_iff in_upsets_in_imp_subset up_sets_in_def)
qed

lemma filter_cl0:
  assumes A0:"A \<subseteq> X" and A1:"A \<noteq> {}" 
  shows "A \<subseteq> filter_closure A X"
proof
  fix a assume A2:"a \<in> A"
  have B0:"{a} \<in> Fpow_ne A"
    using A2 Fpow_def by blast
  have B1:"Inf {a} X \<le> a"
    by (metis A0 A2 inf_singleton2 order_class.order_eq_iff subsetD)
  show "a \<in> filter_closure A X"
    using A0 A2 B0 B1 filter_closure_def by blast
qed

lemma filter_cl1:
  assumes A0:"A \<subseteq> X" and A1:"A \<noteq> {}" 
  shows "is_up_cl (filter_closure A X) X"
proof-
  let ?ClA="(filter_closure A X)"
  have B0:"(\<And>a b. (b \<in> X \<and> a \<le> b \<and> a \<in> ?ClA) \<longrightarrow> b \<in> ?ClA)"
  proof
    fix a b assume A2:"b \<in> X \<and> a \<le> b \<and> a \<in> ?ClA"
    show "b \<in> ?ClA"
      by (smt (verit) A2 dual_order.trans filter_closure_def mem_Collect_eq ub_def)
  qed
  show ?thesis
    by (smt (verit) B0 filter_closure_def is_up_cl_if2 mem_Collect_eq subset_iff)
qed

lemma filter_cl2:
  assumes A0:"A \<subseteq> X" and A1:"A \<noteq> {}" 
  shows "is_dwdir (filter_closure A X)"
proof-
  let ?ClA="(filter_closure A X)"
  have B0:"\<And>a b. a \<in> ?ClA \<and> b \<in> ?ClA \<longrightarrow> (\<exists>c \<in> ?ClA. c lb {a, b})"
  proof
    fix a b assume A2:"a \<in> ?ClA \<and> b \<in> ?ClA" 
    obtain Fa Fb where B1:"Fa \<in> Fpow_ne A \<and> Inf Fa X \<le> a  \<and> Fb \<in> Fpow_ne A \<and>  Inf Fb X \<le> b"
      by (meson A2 filter_closure_obtains)
    let ?Fab="(Fa \<union> Fb)"
    have B2:"?Fab \<subseteq> A \<and> ?Fab \<subseteq> X"
      using A0 B1 fpow_ne_imp2 by auto
    have B3:"Inf ?Fab  X \<le> Inf Fa X \<and> Inf ?Fab X \<le> Inf Fb X"
      by (metis B1 B2 Diff_iff Pow_iff csinf inf_antitone1 is_inf_complete_def le_supE pow_ne_if sup_bot.eq_neutr_iff sup_ge1 sup_ge2)
    have B4:"Inf ?Fab X \<le> a \<and> Inf ?Fab X \<le> b"
      using B1 B3 dual_order.trans by blast
    have B5:"Inf ?Fab X \<le> Inf ?Fab X"
      by simp
    have B6:"?Fab \<in> Fpow_ne A"
      by (metis B1 B2 bot_eq_sup_iff finite_UnI fpow_ne_mem_iff)
    have B7:"Inf ?Fab X \<in> ?ClA "
      by (metis B2 B5 B6 Diff_iff PowI csinf filter_closure_mem_iff inf_complete_imp1)
    have B8:"Inf ?Fab X \<in> ?ClA \<and>  Inf ?Fab X lb {a, b}"
      using B4 B7 lb_def by auto
    show "(\<exists>c \<in> ?ClA. c lb {a, b})"
      using B8 by auto
  qed
  show ?thesis
    by (metis A0 A1 B0 bot.extremum_uniqueI filter_cl0 is_dwdir_def)
qed

lemma filter_cl_is_filter:
  assumes A0:"A \<subseteq> X" and A1:"A \<noteq> {}" 
  shows "is_filter (filter_closure A X) X"
  by (meson A0 A1 Posets9.is_filter_def filter_cl1 filter_cl2 filter_closure_mem_iff subsetI)

lemma filter_cl_least:
  assumes A0:"A \<subseteq> X" and A1:"A \<noteq> {}"  and A2:"is_filter F X" and A3:"A \<subseteq> F"
  shows "(filter_closure A X) \<subseteq> F"
proof
  fix x assume A4:"x \<in> (filter_closure A X)"
  obtain Fx where B0:"Fx  \<in> Fpow_ne A \<and> Inf Fx X \<le> x"
    using A4 filter_closure_obtains by blast
  have B1:"Fx \<subseteq> F"
    using A3 B0 fpow_ne_imp2 by blast 
  have B2:"Inf Fx X \<in> F"
    by (metis A2 A3 B0 DiffD2 DiffI csinf dwdir_finf fpow_ne_imp3 fpow_ne_imp4 inf_complete_imp2 is_filter_imp0 is_filter_imp1 is_filter_imp20)
  have B3:"Inf Fx X \<le> x"
    by (simp add: B0)
  show "x \<in> F"
    by (meson A2 A4 B2 B3 Posets9.is_filter_def filter_closure_mem_iff in_up_cl_set_if)
qed

lemma filter_cl_is_ub:
  "A \<subseteq> X \<Longrightarrow> A \<noteq> {} \<Longrightarrow>  (filter_closure A X) \<in>  (ub_set {A} (filters X))"
  by (metis filter_cl0 filter_cl_is_filter filters_mem_iff is_filter_imp21 singletonD ub_set_elm)

lemma filter_cl_lt_ub:
  "A \<subseteq> X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> F \<in>  (ub_set {A} (filters X)) \<Longrightarrow> (filter_closure A X) \<le> F"
  by (simp add: filter_cl_least filters_mem_iff ub_set_mem_iff)

lemma filter_cl_is_lub:
  "A \<subseteq> X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> is_inf (filter_closure A X) (ub_set {A} (filters X)) (Pow X)"
  by (metis filter_cl_is_filter filter_cl_is_ub filter_cl_lt_ub is_filter_imp21 is_inf_if3)

end



end