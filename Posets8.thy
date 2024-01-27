theory Posets8
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

lemma pow_ne_imp2:
  "a \<in> Pow_ne A \<Longrightarrow> a \<subseteq> A"
  by blast

lemma pow_ne_imp3:
  "a \<in> Pow_ne A \<Longrightarrow> a \<in> Pow A"
  by blast

lemma pow_ne_imp4:
  "C \<subseteq> X \<Longrightarrow> A \<in> Pow_ne C \<Longrightarrow> A \<in> Pow_ne X"
  by blast

lemma pow_ne_if:
  "a \<noteq> {} \<Longrightarrow> a \<in> Pow A \<Longrightarrow>  a \<in> Pow_ne A"
  by blast

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

definition has_lb::"'a::ord set \<Rightarrow>  'a::ord set \<Rightarrow> bool" where
  "has_lb A B \<equiv> (\<exists>b \<in> B. b lb A)"

definition has_ub::"'a::ord set \<Rightarrow>  'a::ord set \<Rightarrow> bool" where
  "has_ub A B \<equiv> (\<exists>b \<in> B. b ub A)"


subsection SetOfBounds
definition ub_set::"'a::ord set \<Rightarrow> 'a::ord set  \<Rightarrow> 'a::ord set" where
  "ub_set A B \<equiv> {b \<in> B. b ub A}"

definition lb_set::"'a::ord set \<Rightarrow> 'a::ord set  \<Rightarrow> 'a::ord set" where
  "lb_set A B \<equiv> {b \<in> B. b lb A}"

lemma ub_set_restrict1:
  " X \<subseteq> Y \<Longrightarrow>  ub_set A X = X \<inter> ub_set A Y"
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

lemma ub_set_subset:
  "ub_set A X \<subseteq> X"
  by (simp add: Collect_conj_eq ub_set_def ub_def)

lemma lb_set_subset:
  "lb_set A X \<subseteq> X"
  by (simp add: Collect_conj_eq lb_set_def lb_def)

lemma ub_set_subset2:
  "B \<subseteq> X \<Longrightarrow> ub_set A B \<subseteq> X"
  using ub_set_subset by blast

lemma lb_set_subset2:
  "B \<subseteq> X \<Longrightarrow> lb_set A B \<subseteq> X"
  using lb_set_subset by blast

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

subsection SetOfBoundsAsOperator

lemma ub_set_antitone1:
  "\<And>A B X. A \<subseteq> B \<Longrightarrow>  ub_set B X \<subseteq> ub_set A X"
  by(simp add: subset_eq ub_set_def ub_def)

lemma lb_set_antitone1:
  "\<And>A B X. A \<subseteq> B \<Longrightarrow>  lb_set B X \<subseteq> lb_set A X"
  by(simp add: subset_eq lb_set_def lb_def)

lemma ub_set_in_isotone2:
  "\<And>A  B X. B \<subseteq> X \<Longrightarrow>  ub_set A B \<subseteq> ub_set A X"
  by(simp add: subset_eq ub_set_def ub_def)

lemma lb_set_in_isotone2:
  "\<And>A  B X. B \<subseteq> X \<Longrightarrow>  lb_set A B \<subseteq> lb_set A X"
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

lemma ub_set_in_from_principal:
  assumes "A \<noteq> {}"
  shows "ub_set A X = (\<Inter>a \<in> A. ub_set {a} X)"
  apply(simp add:ub_set_def ub_def)
  using assms by auto

lemma lb_set_in_from_principal:
  assumes "A \<noteq> {}"
  shows "lb_set A X = (\<Inter>a \<in> A. lb_set {a} X)"
  apply(simp add:lb_set_def lb_def)
  using assms by auto

context fixes A X::"'a::ord set" 
        assumes A0:"A \<subseteq> X"
begin

lemma ul_extensive:
  "A \<subseteq> (ub_set (lb_set A X) X)"
  apply(auto simp add:ub_set_def ub_def lb_set_def lb_def)
  using A0 by blast

lemma lu_extensive:
  "A \<subseteq> (lb_set (ub_set A X) X)"
  apply(auto simp add:ub_set_def ub_def lb_set_def lb_def)
  using A0 by blast

end

lemma ul_isotone:
  "\<And>A B X.  A \<subseteq> B \<Longrightarrow>  (ub_set (lb_set A X) X) \<subseteq> (ub_set (lb_set B X) X)"
  by (simp add: lb_set_antitone1 ub_set_antitone1)

lemma lu_isotone:
  "\<And>A B X.  A \<subseteq> B \<Longrightarrow>  (lb_set (ub_set A X) X) \<subseteq> (lb_set (ub_set B X) X)"
  by (simp add: lb_set_antitone1 ub_set_antitone1)

lemma ulu_eq_u:
  "A \<subseteq> X \<Longrightarrow> ub_set (lb_set (ub_set A X) X) X = ub_set A X"
  by (simp add: lu_extensive subset_antisym ub_set_antitone1 ub_set_subset ul_extensive)

lemma lul_eq_l:
  "A \<subseteq> X \<Longrightarrow> lb_set (ub_set (lb_set A X) X) X = lb_set A X"
  by (simp add: lb_set_antitone1 lb_set_subset lu_extensive subset_antisym ul_extensive)

lemma lu_idempotent:
  "lb_set (ub_set (lb_set (ub_set A X) X ) X) X = lb_set (ub_set A X) X "
  by (simp add: lul_eq_l ub_set_subset)         

lemma ul_idempotent:
  "ub_set (lb_set (ub_set (lb_set A X) X ) X) X = ub_set (lb_set A X) X "
  by (simp add: ulu_eq_u lb_set_subset)

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
  "\<And>A x. is_max x A \<Longrightarrow> (x \<in> A \<and> x \<in> ub_set A UNIV)"
  by(simp add: is_max_def ub_set_mem_iff)

lemma is_min_imp:
  "\<And>A x. is_min x A \<Longrightarrow> (x \<in> A \<and> x \<in> lb_set A UNIV)"
  by(simp add: is_min_def lb_set_mem_iff)

lemma is_max_if1:
  "\<And>A x.  (x \<in> A \<and> x \<in> ub_set A UNIV) \<Longrightarrow> is_max x A"
  by (simp add: is_max_def ub_set_mem_iff)

lemma is_min_if1:
  "\<And>A x.  (x \<in> A \<and> x \<in> lb_set A UNIV) \<Longrightarrow> is_min x A"
  by (simp add: is_min_def lb_set_mem_iff)
                                   
lemma is_max_if2:
  "\<And>A x.  x \<in> A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> x) \<Longrightarrow> is_max x A"
  by (simp add: is_max_if1 ub_set_mem_iff)
                    
lemma is_min_if2:
  "\<And>A x.  x \<in> A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> x \<le> a) \<Longrightarrow> is_min x A"
  by (simp add: is_min_if1 lb_set_mem_iff)
           
lemma is_max_imp_has_max:
  "\<And>A m. is_max m A \<Longrightarrow> has_max A"
  using has_max_def by auto

lemma is_min_imp_has_min:
  "\<And>A m. is_min m A \<Longrightarrow> has_min A"
  using has_min_def by auto     

lemma is_max_iff:
  "is_max m A \<longleftrightarrow> m \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> a \<le> m )"
  by (simp add: is_max_def ub_set_mem_iff)

lemma is_min_iff:
  "is_min m A \<longleftrightarrow> m \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> m \<le> a )"
  by (simp add: is_min_def lb_set_mem_iff)

lemma max_imp_ne:
  assumes "\<exists>m. is_max m A"
  shows "A \<noteq> {}"
  using  assms is_max_def is_max_imp by auto

lemma min_imp_ne:
  assumes "\<exists>m. is_min m A"
  shows "A \<noteq> {}"
  using  assms is_min_def is_min_imp by auto

lemma max_isotone1:
  "\<And>A B ma mb. A \<subseteq> B \<and> (is_max ma A) \<and> ( is_max mb B) \<longrightarrow>  ma \<le> mb"
  using is_max_iff by blast

lemma min_antitone1:
  "\<And>A B ma mb. A \<subseteq> B \<and> (is_min ma A) \<and> ( is_min mb B) \<longrightarrow>  mb \<le> ma"
  using is_min_iff by blast

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
  "is_max (x::'a::order) {x}"
  by (simp add: is_max_iff)

lemma is_min_singleton:
  "is_min (x::'a::order) {x}"
  by (simp add: is_min_iff)

lemma is_max_imp_set:
  "A \<subseteq> X \<Longrightarrow> is_max m X \<Longrightarrow> m \<in> ub_set A X"
  by (simp add: is_max_iff subset_eq ub_set_elm)

lemma is_min_imp_set:
  "A \<subseteq> X \<Longrightarrow> is_min m X \<Longrightarrow> m \<in> lb_set A X"
  by (simp add: is_min_iff subset_eq lb_set_elm)

lemma is_max_subset:
  "A \<subseteq> B \<Longrightarrow> is_max m B \<Longrightarrow> m \<in> A \<Longrightarrow> is_max m A"
  by (simp add: in_mono is_max_iff)

lemma is_min_subset:
  "A \<subseteq> B \<Longrightarrow> is_min m B \<Longrightarrow> m \<in> A \<Longrightarrow> is_min m A"
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
  "\<And>(A::'a::order set) m1 m2. is_max m1 A \<Longrightarrow> is_max m2 A \<Longrightarrow> m1=m2"
  by (meson Orderings.order_eq_iff is_max_iff)  

lemma min_unique:
  "\<And>(A::'a::order set) m1 m2. is_min m1 A \<Longrightarrow> is_min m2 A \<Longrightarrow> m1=m2"
  by (meson Orderings.order_eq_iff is_min_iff)  

lemma if_has_max_max_unique:
  assumes "has_max (A::'a::order set)"
  shows "\<exists>!m. is_max m A"
  using assms has_max_iff2 max_unique by blast

lemma if_has_min_min_unique:
  assumes "has_min (A::'a::order set)"
  shows "\<exists>!m. is_min m A"
  using assms has_min_iff2 min_unique by blast

lemma has_max_singleton:
  "has_max {x::'a::order}"
  using has_max_def is_max_singleton by auto

lemma has_min_singleton:
  "has_min {x::'a::order}"
  using has_min_def is_min_singleton by auto

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
  "\<And>(A::'a::order set) m. is_max m A \<Longrightarrow> m = max A"
  by (simp add: max_def max_unique the_equality)
 
lemma min_if:
  "\<And>(A::'a::order set) m. is_min m A \<Longrightarrow> m = min A"
  by (simp add: min_def min_unique the_equality)
 
lemma max_if2:
  "\<And>(A::'a::order set) x.  x \<in> A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> x) \<Longrightarrow>  x = max A"
  by (simp add: is_max_if2 max_if)
          
lemma min_if2:
  "\<And>(A::'a::order set) x.  x \<in> A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> x \<le> a) \<Longrightarrow>  x = min A"
  by (simp add: is_min_if2 min_if)
           
lemma max_isotone2:
  "\<And>(A::'a::order set) B. A \<subseteq> B \<and> (has_max A) \<and> ( has_max B) \<longrightarrow>  max A \<le> max B"
  by (metis if_has_max_max_unique max_if max_isotone1)

lemma min_antitone2:
  "\<And>(A::'a::order set) B. A \<subseteq> B \<and> (has_min A) \<and> ( has_min B) \<longrightarrow>  min B \<le> min A"
  by(metis if_has_min_min_unique min_if min_antitone1)

lemma max_singleton[simp]:
  "max {x::'a::order} = x"
  apply(simp add: max_def is_max_def ub_set_def ub_def)
  by blast

lemma min_singleton[simp]:
  "min {x::'a::order} = x"
  apply(simp add: min_def is_min_def lb_set_def lb_def)
  by blast

lemma is_min_sanity_check:
  "is_min m A \<longleftrightarrow> (m \<in> A \<and> (\<forall>a \<in> A. m \<le> a))"
  by (auto simp add:min_def is_min_def lb_set_def lb_def)

lemma is_max_sanity_check:
  "is_max m A \<longleftrightarrow> (m \<in> A \<and> (\<forall>a \<in> A. m \<ge> a))"
  by (auto simp add:max_def is_max_def ub_set_def ub_def)

lemma ub_set_max:
  "is_max m X \<Longrightarrow> ub_set {m} X = {m}"
  by( auto simp add:is_max_def ub_set_def ub_def)

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

subsection Operators

lemma sup_in_degenerate:  
  "Sup {} X = min X"
  by (simp add: min_def Sup_def is_sup_in_iff ub_set_in_degenerate)

lemma inf_in_degenerate:  
  "Inf {} X = max X"
  by (simp add: max_def Inf_def is_inf_in_iff lb_set_in_degenerate)

lemma is_sup_singleton:
  "is_sup (x::'a::order) {x} UNIV"
  by (simp add: is_min_iff is_sup_def ub_set_mem_iff)

lemma is_inf_singleton:
  "is_inf (x::'a::order) {x} UNIV"
  by(simp add:is_max_iff is_inf_def lb_set_mem_iff)

lemma is_sup_singleton2:
  "(x::'a::order) \<in> X \<Longrightarrow> is_sup x {x} X"
  using is_sup_if3 by fastforce

lemma is_inf_singleton2:
  "(x::'a::order) \<in> X \<Longrightarrow> is_inf x {x} X"
  using is_inf_if3 by fastforce

lemma has_sup_singleton2:
  "(x::'a::order) \<in> X \<Longrightarrow> has_sup {x} X"
  using has_sup_def is_min_imp_has_min is_sup_def is_sup_singleton2 by blast

lemma has_inf_singleton2:
  "(x::'a::order) \<in> X \<Longrightarrow> has_inf {x} X"
  using has_inf_def is_max_imp_has_max is_inf_def is_inf_singleton2 by blast

lemma sup_singleton[simp]:
  "Sup {x::'a::order} UNIV = x"
  apply(simp add: Sup_def)
  using is_sup_singleton sup_unique by blast

lemma inf_singleton[simp]:
  "Inf {x::'a::order} UNIV = x"
  apply(simp add: Inf_def)
  using is_inf_singleton inf_unique by blast

lemma sup_singleton2:
  "(x::'a::order) \<in> X \<Longrightarrow> Sup {x} X = x"
  by (meson has_sup_singleton2 sup_unique sup_is_sup is_sup_singleton2)

lemma inf_singleton2:
  "(x::'a::order) \<in> X \<Longrightarrow> Inf {x} X = x"
  by (meson has_inf_singleton2 inf_unique inf_is_inf is_inf_singleton2)

lemma sup_isotone1:
  "\<And>(A::'a::order set) B X. has_sup A X \<Longrightarrow> has_sup B X \<Longrightarrow> A \<subseteq> B \<Longrightarrow> Sup A X \<le> Sup B X"
  by (meson sup_is_sup is_sup_in_imp1 is_min_iff ub_set_antitone1 subsetD)

lemma inf_antitone1:
  "\<And>(A::'a::order set) B X. has_inf A X \<Longrightarrow> has_inf B X \<Longrightarrow> A \<subseteq> B \<Longrightarrow> Inf B X \<le> Inf A X"
  by (meson inf_is_inf is_inf_in_imp1 is_max_iff lb_set_antitone1 subsetD)

lemma sup_antitone2:
  "\<And>(A::'a::order set) B X. has_sup A X \<Longrightarrow> has_sup A B \<Longrightarrow> B \<subseteq> X \<Longrightarrow> Sup A X \<le> Sup A B"
  by (meson is_sup_def min_antitone1 sup_is_sup ub_set_in_isotone2)

lemma inf_antitone2:
  "\<And>(A::'a::order set) B X. has_inf A X \<Longrightarrow> has_inf A B \<Longrightarrow> B \<subseteq> X \<Longrightarrow> Inf A B \<le> Inf A X"
  by (meson is_inf_def max_isotone1 inf_is_inf lb_set_in_isotone2)

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

subsection Misc

lemma inf_in_expression:
  "is_inf m A X \<longleftrightarrow> m \<in> (ub_set (lb_set A X) X) \<inter> (lb_set A X)"
  by (metis inf_commute is_inf_def is_max_def lb_set_subset ub_set_restrict1)

lemma sup_in_expression:
  "is_sup m A X \<longleftrightarrow> m \<in> (lb_set (ub_set A X) X) \<inter> (ub_set A X)"
  by (metis inf_commute is_min_def is_sup_def lb_set_restrict1 ub_set_subset)

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
  fixes A X::"'a::order set"
  assumes A0:"A \<noteq> {}" and A1:"has_inf A X" and A2:"A \<subseteq> X"
  shows "lb_set {(Inf A X)} X = (\<Inter>a \<in> A. lb_set {a} X)"
proof-
  obtain i where B0:"i = Inf A X"
    by simp
  show "lb_set { Inf A X} X = (\<Inter>a \<in> A. lb_set {a} X)"
     apply(auto simp add:lb_set_def lb_def)
    using A1 has_inf_in_imp2 order_trans apply blast
    using A0 apply blast
    by (meson A0 A1 bot.extremum_uniqueI has_inf_imp3 subset_emptyI)
qed

lemma ub_set_sup_from_principal:
  fixes A X::"'a::order set"
  assumes A0:"A \<noteq> {}" and A1:"has_sup A X" and A2:"A \<subseteq> X"
  shows "ub_set {(Sup A X)} X = (\<Inter>a \<in> A. ub_set {a} X)"
proof-
  obtain i where B0:"i = Sup A X"
    by simp
  show "ub_set { Sup A X} X = (\<Inter>a \<in> A. ub_set {a} X)"
     apply(auto simp add:ub_set_def ub_def)
    using A1 has_sup_in_imp2 order_trans apply blast
    using A0 apply blast
    by (meson A0 A1 bot.extremum_uniqueI has_sup_imp3 subset_emptyI)
qed


lemma inf_subset_eq0:
  assumes A0:"A \<subseteq> B" and A1:"B \<subseteq> C" and A2:"is_inf i A C" and A3:"i \<in> B"
  shows "is_inf i A B"
proof-
  have B0:"i \<in> lb_set A B"
    by (meson A2 A3 is_inf_in_imp2 lb_set_elm)
  have B1:"lb_set A B \<subseteq> lb_set A C"
    by (simp add: A1 lb_set_in_isotone2)
  have B2:"is_max i (lb_set A B)"
    by (meson A2 B0 B1 is_inf_in_imp1 is_max_iff subset_iff)
  show ?thesis
    by (simp add: B2 is_inf_def)
qed

lemma sup_subset_eq0:
  assumes A0:"A \<subseteq> B" and A1:"B \<subseteq> C" and A2:"is_sup s A C" and A3:"s \<in> B"
  shows "is_sup s A B"
proof-
  have B0:"s \<in> ub_set A B"
    by (meson A2 A3 is_sup_in_imp2 ub_set_elm)
  have B1:"ub_set A B \<subseteq> ub_set A C"
    by (simp add: A1 ub_set_in_isotone2)
  have B2:"is_min s (ub_set A B)"
    by (meson A2 B0 B1 is_sup_in_imp1 is_min_iff subset_iff)
  show ?thesis
    by (simp add: B2 is_sup_def)
qed

lemma inf_subset_eq:
  fixes A B C::"'a::order set"
  assumes A0:"A \<subseteq> B" and A1:"B \<subseteq> C" and A2:"has_inf A C" and A3:"Inf A C \<in> B"
  shows "has_inf A B \<and> Inf A B = Inf A C"
  using A0 A1 A2 A3 inf_subset_eq0[of "A" "B" "C"]
  by (metis has_inf_def inf_is_inf is_inf_def is_inf_inf_eq is_max_imp_has_max)

lemma sup_subset_eq:
  fixes A B C::"'a::order set"
  assumes A0:"A \<subseteq> B" and A1:"B \<subseteq> C" and A2:"has_sup A C" and A3:"Sup A C \<in> B"
  shows "has_sup A B \<and> Sup A B = Sup A C"
  using A0 A1 A2 A3 sup_subset_eq0[of "A" "B" "C"]
  by (metis has_sup_def sup_is_sup is_sup_def is_sup_sup_eq is_min_imp_has_min)


context fixes A X::"'a::order set"
  assumes A0:"A \<subseteq> X" 
begin

lemma inf_ub_is_ub:
  "is_inf i (ub_set A X) X \<Longrightarrow> i ub A"
  apply(simp add:is_inf_def)
  by (meson A0 in_mono is_max_iff lu_extensive ub_def)

lemma is_inf_ub_in_ub_set:
  "is_inf i (ub_set A X) X \<Longrightarrow> i \<in> ub_set A X"
  by (simp add: inf_ub_is_ub is_inf_in_set ub_set_if)

lemma sup_lb_is_lb:
  "is_sup i (lb_set A X) X \<Longrightarrow> i lb A"
  apply(auto simp add:is_sup_def)
  by (meson A0 in_mono is_min_iff ul_extensive lb_def)

lemma is_sup_lb_in_lb_set:
  "is_sup s (lb_set A X) X \<Longrightarrow> s \<in> lb_set A X"
  by (simp add: sup_lb_is_lb is_sup_in_set lb_set_if)

lemma is_inf_ub_imp_is_sup:
  assumes  A1:"is_inf i (ub_set A X) X"
  shows "is_sup i A X"
  by (simp add: assms is_inf_in_imp1 is_inf_ub_in_ub_set sup_in_expression)

lemma is_sup_lb_imp_is_inf:
  assumes  A1:"is_sup s (lb_set A X) X"
  shows "is_inf s A X"
  by (simp add: assms inf_in_expression is_sup_in_imp1 is_sup_lb_in_lb_set)

lemma inf_ub_imp_has_sup:
  assumes  A1:"has_inf (ub_set A X) X"
  shows "has_sup A X"
  using assms has_sup_def inf_is_inf is_inf_ub_imp_is_sup is_min_imp_has_min is_sup_def by blast

lemma sup_lb_imp_has_inf:
  assumes  A1:"has_sup (lb_set A X) X"
  shows "has_inf A X"
  using assms has_inf_def is_inf_def is_max_imp_has_max is_sup_lb_imp_is_inf sup_is_sup by blast

lemma sup_in_eq_inf_in_ub:
  assumes  A1:"has_inf (ub_set A X) X"
  shows "Sup A X = Inf(ub_set A X) X"
  by (metis assms inf_is_inf is_inf_ub_imp_is_sup is_sup_sup_eq)

lemma inf_in_eq_sup_in_lb:
  assumes A1:"has_sup (lb_set A X) X"
  shows "Inf A X = Sup(lb_set A X) X"
  by (metis is_sup_lb_imp_is_inf assms is_inf_inf_eq sup_is_sup)

lemma inf_complete_bounded_sup_eq1:
  assumes A1:"(ub_set A X \<noteq> {})" and
          A2:"has_inf (ub_set A X) X"
  shows "Sup A X = Inf (ub_set A X) X"
  by (simp add: A2 sup_in_eq_inf_in_ub)

lemma sup_complete_bounded_inf_eq1:
  assumes A1:"lb_set A X \<noteq> {}" and
          A2:"has_sup (lb_set A X) X"
  shows "Inf A X = Sup (lb_set A X) X"
  using A2 inf_in_eq_sup_in_lb by presburger

end

lemma same_upper_bounds_imp_sup_eq:
  "has_sup A X  \<Longrightarrow> ub_set A X = ub_set B X \<Longrightarrow> has_sup B X \<and> Sup A X = Sup B X"
  apply(auto simp add:has_sup_def Sup_def)
  by (simp add: is_sup_in_iff)

lemma same_lower_bounds_imp_sup_eq:
  "has_inf A X \<Longrightarrow> lb_set A X = lb_set B X \<Longrightarrow>  has_inf B X \<and> Inf A X = Inf B X"
  apply(auto simp add:has_inf_def Inf_def)
  by (simp add: is_inf_in_iff)

section Closures
(*Probably should develop the theory of closures before trying to develop closures*)

definition is_map::"('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow>bool" where
  "is_map f X Y \<equiv> ((f`X) \<subseteq> Y)"

lemma is_map_comp:
  "is_map f X Y \<Longrightarrow> is_map g Y Z \<Longrightarrow> is_map (g \<circ> f) X Z"
  by (simp add: image_subset_iff is_map_def)

abbreviation is_self_map::"('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_self_map f X \<equiv> is_map f X X"

definition is_idempotent_on::"('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_idempotent_on f X \<equiv> (\<forall>x. x \<in> X \<longrightarrow> f (f x) = f x) \<and> is_self_map f X"

definition is_extensive_on::"('a::order \<Rightarrow> 'a::order)  \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_extensive_on f X \<equiv> (\<forall>x. x \<in> X \<longrightarrow> (x \<le> (f x))) \<and>  is_self_map f X"

definition is_isotone_on::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a::order set  \<Rightarrow> bool" where
  "is_isotone_on f X \<equiv> (\<forall>x1 x2. x1 \<in> X \<and> x2 \<in> X \<and> x1 \<le> x2 \<longrightarrow> (f x1) \<le> (f x2))"

definition is_antitone_on::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a::order set  \<Rightarrow> bool" where
  "is_antitone_on f X \<equiv> (\<forall>x1 x2. x1 \<in> X \<and> x2 \<in> X \<and> x1 \<le> x2 \<longrightarrow> (f x1) \<ge> (f x2))"

definition is_idempotent::"('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_idempotent f \<equiv> is_idempotent_on f UNIV"

definition is_extensive::"('a::order \<Rightarrow> 'a::order)  \<Rightarrow> bool" where
  "is_extensive f \<equiv> is_extensive_on f UNIV"

definition is_isotone::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> bool" where
  "is_isotone f \<equiv> is_isotone_on f UNIV"

definition is_antitone::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> bool" where
  "is_antitone f \<equiv> is_antitone_on f UNIV"

definition is_proj_on::"('a::order \<Rightarrow> 'a::order) \<Rightarrow> 'a::order set \<Rightarrow>  bool" where
  "is_proj_on f X \<equiv> (is_idempotent_on f X) \<and> (is_isotone_on f X)"

definition is_proj::"('a::order \<Rightarrow> 'a::order) \<Rightarrow>  bool" where
  "is_proj f \<equiv>is_proj_on f UNIV"

definition is_closure_on::"('a::order \<Rightarrow> 'a::order) \<Rightarrow> 'a::order set \<Rightarrow>  bool" where
  "is_closure_on f X \<equiv> is_proj_on f X \<and> (is_extensive_on f X)"

definition is_closure::"('a::order \<Rightarrow> 'a::order) \<Rightarrow> bool" where
  "is_closure f \<equiv> is_closure_on f UNIV"

definition closure_eq::"('a::order \<Rightarrow> 'a::order) \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "closure_eq f X \<equiv> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. (( x1 \<le> f x2) \<longleftrightarrow> (f x1 \<le> f x2)))"

lemma closure_eq_imp1:
  "closure_eq f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> f x2 \<Longrightarrow> f x1 \<le> f x2"
  by (simp add: closure_eq_def)

lemma closure_eq_imp2:
  "closure_eq f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> f x1 \<le> f x2 \<Longrightarrow> x1 \<le> f x2"
  by (simp add: closure_eq_def)

lemma is_idempotent_simp:
  "is_idempotent f \<longleftrightarrow>  is_idempotent_on f UNIV"
  by (simp add: is_idempotent_def)

lemma is_self_map_imp:
  "is_self_map f X \<Longrightarrow> f`X \<subseteq> X"
  by (simp add: is_map_def)

lemma is_self_map_imp2:
  "is_self_map f X \<Longrightarrow> x \<in> X \<Longrightarrow> f x \<in> X"
  by (simp add: image_subset_iff is_map_def)

lemma is_self_map_if:
  "X \<noteq> {} \<Longrightarrow> f`X \<subseteq> X \<Longrightarrow> is_self_map f X "
  by (simp add: is_map_def)

lemma is_isotone_simp:
  "is_isotone f \<longleftrightarrow>  is_isotone_on f UNIV"
  by (simp add: is_isotone_def)

lemma is_extensive_simp:
  "is_extensive f \<longleftrightarrow>  is_extensive_on f UNIV"
  by (simp add: is_extensive_def)

lemma is_extensive_on_imp_map:
  "is_extensive_on f X \<Longrightarrow> is_self_map f X"
  by (simp add: is_extensive_on_def)

lemma is_antitone_simp:
  "is_antitone f \<longleftrightarrow>  is_antitone_on f UNIV"
  by (simp add: is_antitone_def)

lemma is_proj_simp:
  "is_proj f \<longleftrightarrow>  is_proj_on f UNIV"
  by (simp add: is_proj_def)

lemma is_isotone_imp1:
  "is_isotone_on f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> f x1 \<le> f x2"
  by(simp add:is_isotone_on_def)

lemma is_closure_imp_iso_imp1:
  "is_closure_on f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> f x1 \<le> f x2"
  apply(simp add:is_closure_on_def is_proj_on_def) using is_isotone_imp1
  by blast

lemma is_ext_imp1:
  "is_extensive_on f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> f x1 \<le> f x2 \<Longrightarrow> x1 \<le> f x2"
  apply(simp add:is_extensive_on_def)
  using order.trans by blast

lemma is_iso_ext_imp1:
  "is_isotone_on f X \<Longrightarrow> is_extensive_on f X \<Longrightarrow> x \<in> X \<Longrightarrow> f x \<le> f (f x)"
  by(simp add:is_isotone_on_def is_extensive_on_def image_subset_iff is_map_def)

lemma is_iso_idem_imp1:
  "is_isotone_on f X \<Longrightarrow> is_idempotent_on f X \<Longrightarrow> x \<in> X \<Longrightarrow> f x \<le> f (f x)"
  by(simp add:is_isotone_on_def is_idempotent_on_def image_subset_iff is_map_def)

lemma is_iso_ext_imp2:
  "is_isotone_on f X \<Longrightarrow> is_extensive_on f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> f x2 \<Longrightarrow> f x1  \<le> f (f x2)"
  by(simp add:is_isotone_on_def is_extensive_on_def image_subset_iff is_map_def)

lemma is_idempotent_imp1:
  "is_idempotent_on f X \<Longrightarrow> x \<in> X \<Longrightarrow> f x = (f (f x))"
  by(simp add:is_idempotent_on_def)

lemma is_idempotent_imp2:
  "is_idempotent_on f X \<Longrightarrow> x \<in> f`X \<Longrightarrow> f x =x"
  by(auto simp add:is_idempotent_on_def)

lemma is_idempotent_imp3:
  "is_idempotent_on f X \<Longrightarrow> is_self_map f X"
  by(simp add:is_idempotent_on_def)

lemma is_closure_simp:
  "is_closure f \<longleftrightarrow>  is_closure_on f UNIV"
  by (simp add: is_closure_def)

lemma antitone_comp:
  "is_map f X Y \<Longrightarrow> is_map g Y X \<Longrightarrow> is_antitone_on f X \<Longrightarrow> is_antitone_on g Y \<Longrightarrow> is_isotone_on (g \<circ> f) X"
  apply(simp add:is_map_def is_antitone_on_def is_isotone_on_def)
  by (simp add: image_subset_iff)

lemma is_proj_on_imp1:
  "is_proj_on f X \<Longrightarrow> is_idempotent_on f X" 
  by(simp add:is_proj_on_def) 

lemma is_proj_on_imp2:
  "is_proj_on f X \<Longrightarrow> is_isotone_on f X" 
  by(simp add:is_proj_on_def) 

lemma is_proj_on_imp3:
  "is_proj_on f X \<Longrightarrow> is_self_map f X" 
  by(simp add:is_idempotent_imp3 is_proj_on_imp1)
 
lemma is_iso_idem_imp2:
  "is_isotone_on f X \<Longrightarrow> is_idempotent_on f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> f x2 \<Longrightarrow> f x1  \<le> f (f x2)"
  by (simp add: is_idempotent_imp3 is_isotone_imp1 is_self_map_imp2)

lemma is_iso_idem_imp3:
  "is_isotone_on f X \<Longrightarrow> is_idempotent_on f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> f x2 \<Longrightarrow> f x1  \<le> (f x2)"
   using is_iso_idem_imp2[of "f" "X" "x1" "x2"] is_idempotent_imp1[of "f" "X" "x2"] by fastforce 

lemma proj_imp_lt_cl_lt:
  "is_proj_on f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> f x2 \<Longrightarrow> f x1 \<le> f x2"
  using is_iso_idem_imp3 is_proj_on_imp1 is_proj_on_imp2 by blast

context fixes f::"'a::order \<Rightarrow> 'a::order" and X::"'a::order set"
    assumes ismap:"is_self_map f X" and cl_eq:"closure_eq f X"
begin
lemma cl_eq_imp_ext1:
  "x \<in> X \<Longrightarrow>  x \<le> f x"
  by (simp add: cl_eq closure_eq_imp2[of "f" "X" "x" "x"])
            

lemma cl_eq_imp_iso1:
  shows "x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> x1 \<le> f x2"
  using cl_eq_imp_ext1[of "x2"]  dual_order.trans by auto

lemma cl_eq_imp_iso2:
  "x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> f x2 \<Longrightarrow> f x1 \<le> f x2"
  using cl_eq closure_eq_imp1 by blast

lemma cl_eq_imp_iso3:
  shows "x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> f x1 \<le> f x2"
  using cl_eq_imp_iso2[of "x1" "x2"] cl_eq_imp_iso1[of "x1" "x2"] by auto

lemma cl_eq_imp_idm1:
  "x \<in> X \<Longrightarrow> (f (f x)) \<le> (f x)"
  using ismap is_self_map_imp2[of "f" "X" "x"] cl_eq closure_eq_imp1[of "f" "X" "f x" "x"] by auto

lemma cl_eq_imp_idm2:
  "x \<in> X \<Longrightarrow> f (f x) = f x"
  using cl_eq_imp_idm1[of "x"] ismap is_iso_idem_imp2[of "f" "X" "x" "f x"]
  by (simp add: cl_eq_imp_ext1 is_self_map_imp2 order_antisym)

lemma cl_eq_imp_ext2:
  "is_extensive_on f X"
  by (simp add: is_extensive_on_def ismap cl_eq_imp_ext1)

lemma cl_eq_imp_iso4:
  "is_isotone_on f X"
  by (simp add:is_isotone_on_def cl_eq_imp_iso3)

lemma cl_eq_imp_idm3:
  "is_idempotent_on f X"
  by (simp add: cl_eq_imp_idm2 is_idempotent_on_def ismap)

end

lemma is_closure_on_imp1:
  "is_closure_on f X \<Longrightarrow> is_extensive_on f X" 
  by (simp add:is_closure_on_def)

lemma is_closure_on_imp2:
  "is_closure_on f X \<Longrightarrow> is_self_map f X" 
  using is_closure_on_imp1[of "f" "X"] is_extensive_on_imp_map[of "f" "X"] by blast

lemma closure_eq_if_closure_l:
  "is_closure_on f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> f x1 \<le> f x2 \<Longrightarrow> x1 \<le> f x2"
  using is_ext_imp1 is_closure_on_def by blast

lemma closure_eq_if_closure_r:
  "is_closure_on f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow>  x1 \<le> f x2 \<Longrightarrow> f x1 \<le> f x2"
  by(simp add:is_closure_on_def is_closure_on_imp2[of "f" "X"] proj_imp_lt_cl_lt[of "f" "X" "x1" "x2"])


lemma closure_eq_if_closure:
  "is_closure_on f X \<Longrightarrow> closure_eq f X"
  by(auto simp add:closure_eq_def closure_eq_if_closure_l closure_eq_if_closure_r)

lemma closure_eq_imp_closure:
  "is_self_map f X \<Longrightarrow> closure_eq f X \<Longrightarrow> is_closure_on f X"
  by (simp add: cl_eq_imp_ext2 cl_eq_imp_idm3 cl_eq_imp_iso4 is_closure_on_def is_proj_on_def)


lemma closure_if_cl_eq:
   "is_closure_on f X \<longleftrightarrow> (is_self_map f X \<and> closure_eq f X)"
  using closure_eq_if_closure closure_eq_imp_closure is_closure_on_imp2 by blast

definition cl_sup_cond1::"('a::order \<Rightarrow> 'a::order) \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "cl_sup_cond1 f X \<equiv> (\<forall>A \<in> Pow X. has_sup A X \<longrightarrow> Sup A X \<le> f(Sup A X) \<and> f(Sup A X) = (Sup (f`A) (f`X)))"

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
  " is_ne A  \<Longrightarrow> (\<forall>a b. a \<in> A \<and>  b \<in> A \<longrightarrow>  (\<exists>c \<in> A. c ub {a, b})) \<Longrightarrow> is_updir A"
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
  apply (simp add: dw_sets_in_def)
  using is_dwclosed_in_imp1 by auto

lemma in_upsets_in_imp_subset:
  "E \<in> up_sets_in X  \<Longrightarrow> E \<subseteq> X"
  apply (simp add: up_sets_in_def)
  using is_upclosed_in_imp1 by auto


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
  have B3:"is_dw_cl B X" (*by (meson A1 B0 B2 in_mono is_downclosed_in_def is_downclosed_in_imp2)*)
    apply(auto simp add:is_dw_cl_def)
    apply (metis B30 dw_cl_if dw_cl_in_carrier1)
    by (meson B0 dw_cl_in_extensive in_mono subset_trans)
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
  have B3:"is_up_cl B X" (*using B0 B1 B2 is_upclosed_in_def by fastforce*)
  apply(auto simp add:is_up_cl_def up_cl_def)
    using B30 apply blast
    using B0 by blast
  have B4:"B \<subseteq> X"
    using B0 by blast
  show ?thesis
    by (simp add: B3 up_sets_in_def)
qed

lemma in_downsets_imp_complement_in_upsets:
  "D \<in> dw_sets_in X  \<Longrightarrow> (X - D) \<in> up_sets_in X "
  apply(auto simp add:up_sets_in_def is_up_cl_def up_cl_def)
  using is_downclosed_in_imp2 is_dw_cl_imp2 by blast

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
proof-
  obtain s where B0:"s = Sup A X"
    by simp
  have B1:"ub_set (dw_cl A X) X = ub_set A X"
    by (simp add: A1 down_closure_has_same_ub)
  show "has_sup (dw_cl A X) X \<and>  Sup A X = Sup (dw_cl A X) X"
    by (metis A0 B1 has_sup_def has_sup_in_imp1 min_unique)
qed


lemma has_inf_in_imp_upclosure_has_inf_in:
  assumes A0:"has_inf A X" and A1:"A \<subseteq> X"
  shows "has_inf (up_cl A X) X \<and> Inf A X = Inf (up_cl A X) X"
proof-
 obtain i where B0:"i = Inf A X" by simp
  have B1:"lb_set (up_cl A X) X = lb_set A X"
    by (simp add: A1 up_closure_has_same_lb)
  show "has_inf (up_cl A X) X \<and> Inf A X = Inf (up_cl A X) X"
    by (metis A0 B1 has_inf_def has_inf_in_imp1 max_unique)
qed


lemma is_up_cl_if2:
  "(A::'a::order set) \<subseteq> X \<Longrightarrow> (\<And>a b. (b \<in> X \<and> a \<le> b \<and> a \<in> A) \<Longrightarrow> b \<in> A) \<Longrightarrow> is_up_cl A X"
  by (meson is_upclosed_in_if0 subsetI subset_antisym up_cl_if up_cl_in_carrier2 up_cl_in_extensive)

lemma is_dw_cl_if2:
  "(A::'a::order set) \<subseteq> X \<Longrightarrow> (\<And>a b. (b \<in> X \<and> a \<ge> b \<and> a \<in> A) \<Longrightarrow> b \<in> A) \<Longrightarrow> is_dw_cl A X"
  by (meson is_dwclosed_in_if0 subsetI subset_antisym dw_cl_if dw_cl_in_carrier2 dw_cl_in_extensive)


  
   

section FilterIdeals
subsection Filters
definition is_filter::"'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "is_filter F X \<equiv> F \<subseteq> X \<and> is_dwdir F \<and> is_up_cl F X"

definition is_principal_filter::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
   "is_principal_filter F X \<equiv> F \<subseteq> X \<and> is_filter F X \<and> has_min F "

lemma is_filter_imp0:
  "is_filter F X \<Longrightarrow> is_dwdir F"
  by (simp add: is_filter_def)

lemma is_filter_imp01:
  "is_filter F X \<Longrightarrow>  (\<And>a b. a \<in> F \<and>  b \<in> F \<Longrightarrow>  (\<exists>c \<in> F. c \<le> a \<and> c \<le> b))"
  by (simp add: is_dwdir_imp3 is_filter_imp0)

lemma is_filter_obtains:
  assumes "is_filter F X" and  "a \<in> F" and  "b \<in> F" 
  obtains c where  "c \<in> F \<and>  c \<le> a \<and> c \<le> b"
  by (meson assms(1) assms(2) assms(3) is_filter_imp01)

lemma is_filter_imp1:
  "is_filter F X \<Longrightarrow> is_up_cl F X"
  by (simp add: is_filter_def)

lemma is_filter_imp20:
  "is_filter F X \<Longrightarrow> F \<subseteq> X"
  by (simp add: is_filter_def)     

lemma is_filter_imp21:
  "is_filter F X \<Longrightarrow> F \<in> Pow X"
  by (simp add: is_filter_def)

lemma is_filter_imp3:
  "is_filter F X \<Longrightarrow> F \<noteq> {}"
  by (simp add: is_filter_def is_dwdir_imp1)

lemma is_filter_imp4:
  "is_filter F X \<Longrightarrow> F \<in> Pow_ne X"
  by (simp add: is_filter_def is_dwdir_imp1)

lemma is_filter_if:
  "F \<subseteq> X \<Longrightarrow> is_dwdir F \<Longrightarrow> is_up_cl F X \<Longrightarrow> is_filter F X"
  by (simp add: is_filter_def)

lemma principal_filter_imp1:
  "is_principal_filter F X \<Longrightarrow> (\<exists>m. is_min m F)"
  using has_min_def is_principal_filter_def by blast

lemma principal_filter_obtains:
  assumes "is_principal_filter F X"
  obtains m where "m = min F"
  by simp

lemma principal_filter_imp2:
  "is_principal_filter F X \<Longrightarrow> x \<in> X \<Longrightarrow> x \<ge> min F \<Longrightarrow> x \<in> F"
  by (metis is_filter_imp1 is_min_imp is_principal_filter_def is_up_cl_imp2 min_if principal_filter_imp1) 

lemma principal_filter_imp3:
  "is_principal_filter F X \<Longrightarrow> x \<in> F \<Longrightarrow> x \<ge> min F"
  using is_min_imp lb_set_imp min_if principal_filter_imp1 by blast

lemma principal_filter_imp4:
  "is_principal_filter F X \<Longrightarrow> F \<subseteq> X"
  by (simp add: is_principal_filter_def)

lemma principal_filter_imp5:
  assumes "is_principal_filter F X"
  shows "\<forall>x. x \<in> F \<longleftrightarrow> (x \<in> X \<and> x \<ge> min F)"
  using assms principal_filter_imp2 principal_filter_imp3 principal_filter_imp4 by blast

lemma principal_filter_imp6:
  "is_principal_filter F X \<Longrightarrow> F = {x \<in> X. x \<ge> min F}"
  by (simp add: Orderings.order_eq_iff principal_filter_imp5 subset_iff)

lemma principal_filter_imp7:
  "is_principal_filter F X \<Longrightarrow> is_filter F X"
  by (simp add: is_principal_filter_def)

lemma principal_filter_imply70:
  "is_principal_filter F X \<Longrightarrow> is_dwdir F"
  using is_filter_imp0 principal_filter_imp7 by blast

lemma ub_set_min0:
  "a \<in> X \<Longrightarrow> is_min a(ub_set {a} X)"
  by (simp add: is_sup_in_imp1 is_sup_singleton2)

lemma ub_set_min1:
  "a \<in> X \<Longrightarrow> is_min a {x \<in> X. x \<ge> a}"
  by (metis is_sup_def is_sup_singleton2 ub_set_in_singleton)

lemma principal_filter_if1:
  "a \<in> X \<Longrightarrow> is_principal_filter (ub_set {a} X) X"
  apply(auto simp add:is_principal_filter_def is_filter_def is_dwdir_def is_up_cl_def)
  using ub_set_imp2 apply blast
  using is_sup_def is_sup_singleton2 min_imp_ne apply blast
  apply (metis empty_subsetI has_lb_def has_lb_iff has_sup_def has_sup_singleton2 insert_subset is_inf_def is_sup_lb_imp_is_inf max_imp_ne sup_is_sup ub_set_in_degenerate)
  apply (simp add: is_upcl_in_imp0 ub_is_upset)
  apply (simp add: is_upcl_in_imp0 ub_is_upset)
  by (simp add: has_sup_has_lub has_sup_singleton2)
  
lemma principal_filter_if2:
  "a \<in> X \<Longrightarrow> is_principal_filter {x \<in> X. x \<ge> a} X"
  by (metis principal_filter_if1 ub_set_in_singleton)

definition is_ideal::"'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "is_ideal I X \<equiv> is_updir I \<and> is_dw_cl I X"

definition is_pfilter::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
   "is_pfilter F X \<equiv> is_filter F X \<and> F \<noteq> X " 

definition is_pideal::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
   "is_pideal I X \<equiv> is_ideal I X \<and> I \<noteq> X " 

definition is_principal_ideal::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
   "is_principal_ideal I X \<equiv> is_ideal I X \<and> has_max I "

subsection ProperFilters
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

lemma is_principal_filter_imp1:
  "is_principal_filter F X \<Longrightarrow> \<exists>m. is_min m F"
  by (simp add: has_min_iff2 is_principal_filter_def)

lemma is_principal_filter_obtains:
  assumes "is_principal_filter F X"  obtains m where  "is_min m F"
  using assms is_principal_filter_imp1 by auto

lemma up_cl_ub:
  "up_cl {x} X = ub_set {x} X"
  by(simp add:up_cl_def ub_set_def ub_def)
  

lemma is_principal_filter_equiv:
  assumes A0:"F \<subseteq> X"
  shows "is_principal_filter F X \<longleftrightarrow> (\<exists>x \<in> X. F = up_cl {x} X)" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L 
  obtain m where B0:"is_min m F"
    using L is_principal_filter_imp1 by auto
  have B1:"\<forall>x \<in> F. m \<le> x"
    by (meson B0 is_min_iff)
  have B2:"\<forall>x \<in> X. m \<le> x \<longrightarrow> x \<in> F"
    using B0 L min_if principal_filter_imp2 by blast
  have B3:"F \<subseteq> up_cl {m} X"
    by (meson B1 assms singletonI subset_eq up_closure_in_imp)
  have B4:"up_cl {m} X \<subseteq> F"
    by (metis B0 Diff_eq_empty_iff Diff_subset L is_filter_def assms insert_subset is_min_imp is_principal_filter_def is_upcl_in_imp0 up_cl_in_isotone)
  show ?R
    using B0 B3 B4 assms is_min_imp by blast
 next
  assume R:?R 
  obtain x where B5:"x \<in> X \<and> F = up_cl {x} X"
    using R by blast
  have B6:"is_min x ( up_cl {x} X)"
    by (metis B5 dual_order.refl is_min_iff singletonD singletonI up_cl_in_obtai1 up_closure_in_imp)
  have B7:"is_min x (ub_set {x} X)"
    using B6 up_cl_ub[of "x" "X"] by force
  have B8:"F = ub_set {x} X"
    using B5 up_cl_ub[of "x" "X"]
    by meson
  show ?L
    by (metis B5 B8 principal_filter_if1)
qed

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
  by (simp add: has_min_imp_has_inf is_clr_imp2 ub_set_subset)

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
      by (metis assms has_min_iff2 is_clr_def is_min_iff min_if subsetD ub_set_imp2 ub_set_min0)
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


context fixes A::"'a::order set set" and
              X::"'a::order set"
        assumes ex:"\<forall>Ai \<in> A. has_inf  Ai X"
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
proof-
  have B0:"lb_set (\<Union>A) X  \<subseteq> lb_set {s \<in> X. \<exists>Ai \<in> A. s = Inf Ai X } X "
    using lb_un_lb_infs by blast
  have B1:"lb_set (\<Union>A) X  \<supseteq> lb_set {s \<in> X. \<exists>Ai \<in> A. s = Inf Ai X } X "
    using lb_infs_lb_un by blast
  show ?thesis
    using B0 B1 by blast
qed

lemma has_inf_imp_eq_inf_inf:
  assumes "has_inf (\<Union>A) X"
  shows "has_inf {s \<in> X. \<exists>Ai \<in> A. s = Inf Ai X } X \<and> Inf {s \<in> X. \<exists>Ai \<in> A. s = Inf Ai X } X = Inf (\<Union>A) X"
  using assms lb_un_eq_lb_fp same_lower_bounds_imp_sup_eq by blast

lemma inf_inf_imp_has_inf_eq:
  assumes "has_inf {s \<in> X. \<exists>Ai \<in> A. s = Inf Ai X } X"
  shows "has_inf  (\<Union>A) X \<and> Inf  {s \<in> X. \<exists>Ai \<in> A. s = Inf Ai X } X = Inf  (\<Union>A) X"
  using assms lb_un_eq_lb_fp same_lower_bounds_imp_sup_eq by blast

end


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
      by (meson B2 UnionI assms ub_set_mem)
    show "s \<le> u"
      using B0 B2 B3 ex sup_is_sup is_sup_in_imp3 by blast
  qed
  show ?thesis
    using B0 B1 ub_set_elm by blast
qed

lemma ub_un_eq_ub_fp:
  "ub_set (\<Union>A) X = ub_set {s \<in> X. \<exists>Ai \<in> A. s = Sup Ai X } X"
proof-
  have B0:"ub_set (\<Union>A) X  \<subseteq> ub_set {s \<in> X. \<exists>Ai \<in> A. s = Sup Ai X } X "
    using ub_un_ub_sup by blast
  have B1:"ub_set (\<Union>A) X  \<supseteq> ub_set {s \<in> X. \<exists>Ai \<in> A. s = Sup Ai X } X "
    using ub_sup_ub_un by blast
  show ?thesis
    using B0 B1 by blast
qed

lemma has_sup_imp_eq_sup_sup:
  assumes "has_sup (\<Union>A) X"
  shows "has_sup {s \<in> X. \<exists>Ai \<in> A. s = Sup Ai X } X \<and> Sup {s \<in> X. \<exists>Ai \<in> A. s = Sup Ai X } X = Sup (\<Union>A) X"
  using assms ub_un_eq_ub_fp same_upper_bounds_imp_sup_eq by blast

lemma sup_sup_imp_has_sup_eq:
  assumes "has_sup {s \<in> X. \<exists>Ai \<in> A. s = Sup Ai X } X"
  shows "has_sup  (\<Union>A) X \<and> Sup  {s \<in> X. \<exists>Ai \<in> A. s = Sup Ai X } X = Sup  (\<Union>A) X"
  using assms ub_un_eq_ub_fp same_upper_bounds_imp_sup_eq by blast


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
        using P1 sup_cl_obtains by (metis DiffE PowD insert_absorb insert_subset)
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




lemma top_is_closed1:
  assumes "is_closure_on f X" and "is_max m X"
  shows "f m = m"
  by (meson assms(1) assms(2) cl_eq_imp_ext1 closure_eq_if_closure is_closure_on_imp2 is_max_iff is_self_map_imp2 order_antisym)

lemma top_is_closed2:
  assumes "is_clr C X" and "is_max m X"
  shows "m \<in> C"
proof-
  have B0:"m \<in> X"
    using assms(2) is_max_imp by blast
  have B1:"ub_set {m} C = {m}"
    by (metis B0 assms(1) assms(2) is_clr_imp1 is_clr_imp3 subset_singletonD ub_set_in_isotone2 ub_set_max)
  show ?thesis
    using B1 ub_set_mem_iff by auto
qed

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
  by (simp add: Pow_not_empty image_subset_iff is_map_def lb_set_subset)

lemma u_is_map:
  "is_map (\<lambda>A. ub_set A X) (Pow X) (Pow X)"
  by (simp add: Pow_not_empty image_subset_iff is_map_def ub_set_subset)

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
  using has_inf_def is_inf_in_imp1 is_max_imp_has_max sets_have_inf4 by blast

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
  by (simp add: Posets8.sets_have_inf2 inf_ub_imp_has_sup)

lemma sets_have_sup3:
  "Sup A UNIV  =  (\<Union>A) "
  using is_sup_sup_eq sets_have_sup1 by blast

end



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
    by (meson Pow_iff assms is_inter_system_def ub_set_subset)
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
  assumes A0:"is_inf_complete X \<and> has_max X" and A1:" A \<in> Pow_ne X" 
  shows "has_sup A X"
   by (meson A0 A1 PowI inf_ub_imp_has_sup is_inf_complete_def max_imp_ub_set_ne pow_ne_if pow_ne_imp2 ub_set_subset)

lemma sup_complete_min_exists_inf:
  assumes A0:"is_sup_complete X \<and> has_min X" and A1:" A \<in> Pow_ne X" 
  shows "has_inf A X"
  by (meson A0 A1 PowI sup_lb_imp_has_inf is_sup_complete_def min_imp_lb_set_ne pow_ne_if pow_ne_imp2 lb_set_subset)


lemma inf_comp_max_imp_sup_comp_min:
  assumes A0:"(is_inf_complete X \<and> has_max X)"
  shows "(is_sup_complete X \<and> has_min X)"
  by (metis assms has_max_iff2 inf_complete_max_exists_sup inf_complete_min2 is_sup_complete_def max_imp_ne)

lemma sup_comp_max_imp_inf_comp_min:
  assumes A0:"(is_sup_complete X \<and> has_min X)"
  shows "(is_inf_complete X \<and> has_max X)"
  by (metis assms has_min_iff2 is_inf_complete_def min_imp_ne sup_complete_max2 sup_complete_min_exists_inf)


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
  by (simp add: A1 clr_inf_complete1 clr_inf_complete2 inf_subset_eq)


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
    have B4:"Inf ?P X = Inf ?P C"
      by (simp add: A3 B0 ub_set_subset)
    have B5:"Inf ?P C \<in> C"
      by (meson A3 B0 PowI has_inf_in_set pow_ne_if ub_set_subset)
    have B6:"Inf ?P C lb ?P"
      by (metis B3 B4 has_inf_in_imp2 lb_def)
    have B7:"x lb ?P"
      by (simp add: is_lb_simp2 ub_set_imp)
    have B8:"x \<le> Inf ?P C"
      by (metis A5 B3 B4 B7 has_inf_imp3 lb_def)
    have B9:"Inf ?P C \<in> ?P"
      by (simp add: B5 B8 ub_set_mem_iff)
    have B10:"is_min (Inf ?P C) ?P"
      by (simp add: B6 B9 is_min_def lb_set_if)
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
    using A3 cl_eq_imp_idm1 closure_if_cl_eq order_trans apply blast
    by (metis A3 cl_eq_imp_idm2 closure_eq_if_closure is_closure_on_imp2)
  have B1:"has_min ?E2"
    using A2 A3 closure_range_is_clr is_clr_imp2 by blast
  have B2:"(min ?E2) lb ?E2"
    using B1 has_min_def is_sup_imp_lt_ub is_sup_in_iff min_if by blast
  have B3:"(min ?E2) \<in> X"
    by (metis A3 B1 has_sup_def has_sup_in_imp1 is_closure_on_imp2 is_self_map_imp min_if subsetD ub_set_subset)
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
        by (metis A0 assms has_inf_def is_clr_imp1 is_complete_imp_max_and_inf lb_set_in_degenerate subset_empty)
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
      by (metis A0 A1 Pow_bottom assms complete_clr1 empty_subsetI has_inf_def inf_subset_eq 
          insert_absorb insert_not_empty insert_subset is_complete_imp_max_and_inf lb_set_in_degenerate)
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
      by (simp add: assms ub_set_subset)
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
    by (meson A0 A1 B0 PowI dual_order.trans is_complete_lattice_def is_inf_complete_def pow_ne_if ub_set_subset)
  have B2:"Inf (ub_set A C) X = Inf (ub_set A C) C "
    by (metis A1 A2 B1 clr_inf_closed inf_subset_eq ub_set_subset)
  have B3:"has_inf (ub_set A C) C"
    by (meson A1 A2 B1 clr_inf_closed inf_subset_eq ub_set_subset)
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
    by (metis A1 A2 B1 True cl_eq_imp_idm2 closure_eq_if_closure closure_of_min has_sup_def has_sup_in_set is_closure_on_imp2 is_complete_imp_min_and_sup sup_in_degenerate ub_set_in_degenerate)
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
  using complete_clr_sup3[of "X" "f" "A"] A0 A1 A2 A3
  by (metis closure_range_is_clr complete_clr_sup2 has_sup_in_set image_mono is_closure_on_def is_closure_on_imp2 is_idempotent_imp2 is_proj_on_def is_self_map_imp)
  

lemma is_moore_family_imp1:
  "is_moore_family C X \<Longrightarrow> a \<in> C \<Longrightarrow> a \<subseteq> X"
  using PowD is_moore_family_def by auto

lemma is_moore_family_imp2:
  "is_moore_family C X \<Longrightarrow> A \<subseteq> C \<Longrightarrow> a \<in> A \<Longrightarrow> a \<subseteq> X"
  by (meson PowD is_moore_family_def subsetD)

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

section Grilling

lemma lattice_inf_is_inf:
  "is_inf (inf (a::'a::lattice) b) {a, b} UNIV"
  by (simp add: is_inf_def is_max_iff lb_set_mem_iff)

lemma lattice_sup_is_sup:
  "is_sup (sup (a::'a::lattice) b) {a, b} UNIV"
  by (simp add: is_sup_def is_min_iff ub_set_mem_iff)


lemma order_bot_is_min:
  "is_min (bot::'a::order_bot) UNIV"
  by (simp add: is_min_bot)


definition meshes::"('a::{lattice,order_bot} set) \<Rightarrow> ('a::{lattice,order_bot} set) \<Rightarrow> bool"  (infixl "#" 50)  where
   "(A # B) \<equiv> (\<forall>a \<in> A. \<forall>b \<in> B.  ((inf a b) \<noteq> bot))"

definition grill::"'a::{lattice,order_bot} set \<Rightarrow> 'a::{lattice,order_bot} set" where
  "grill A = {x::('a::{lattice,order_bot}). {x}#A}"  

lemma meshes_imp1:
  "A#B \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> B\<Longrightarrow> inf a b \<noteq> bot"
  by (simp add: meshes_def)

lemma meshes_if1:
  "(\<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> inf a b \<noteq> bot) \<Longrightarrow> A#B"
  by (simp add: meshes_def)

lemma meshes_imp2:
  "{a}#F \<Longrightarrow> f \<in> F \<Longrightarrow> inf a f \<noteq> bot"
  by (simp add: meshes_imp1)


lemma mesh_prop1:
  assumes A0:"{a}#F" and A1:"a \<le> b"
  shows "{b}#F"
  by (metis (no_types, lifting) A0 A1 bot.extremum_uniqueI inf.orderE inf_assoc inf_le2 meshes_def singletonD singletonI)

lemma mesh_prop2:
  assumes A0:"is_up_cl (F::'X::boolean_algebra set) UNIV" and A1:"a \<in> F"
  shows "\<not>{-a}#F"
proof(rule ccontr)
  assume A2:"\<not>(\<not>({(-a)}#F))"
  have B0:"{(-a)}#F"
    using A2 by blast
  have B1:"inf (-a) a = bot"
    by simp
  show "False"
    by (meson A1 B0 B1 insertCI meshes_def)
qed



definition top_u1::"'a set set \<Rightarrow> bool" where
  "top_u1 T \<equiv> (\<forall>E. E \<subseteq> T \<longrightarrow> \<Union>E \<in> T )"

definition top_i1::"'a set set \<Rightarrow> bool" where
  "top_i1 T \<equiv> (\<forall>E. (finite E \<and> E \<subseteq> T) \<longrightarrow> \<Inter>E \<in> T )"

definition top_i2::"'a set set \<Rightarrow> bool" where
  "top_i2 T \<equiv> (\<forall>E. (finite E \<and> E \<subseteq> T \<and> E \<noteq> {}) \<longrightarrow> \<Inter>E \<in> T )"

definition top_i3::"'a set set \<Rightarrow> bool" where
  "top_i3 T \<equiv> (\<forall>a1 a2. (a1 \<in> T \<and> a2 \<in> T) \<longrightarrow> a1 \<inter> a2 \<in> T)"

definition is_base1_for_topology::"'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "is_base1_for_topology B T \<equiv> B \<subseteq> T \<and> (\<forall>U \<in>T.  (\<exists>E \<in> Pow B. U=\<Union>E))"

definition is_base2_for_topology::"'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "is_base2_for_topology B T \<equiv> (B \<subseteq> T) \<and> (\<forall>U \<in> T. \<forall>x \<in> U. \<exists>B \<in> B. (x \<in> B \<and> B \<subseteq> U))"

definition is_base_3_covering::"'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_base_3_covering B X \<equiv>   (B \<in> Dpow X) \<and> (\<forall>x \<in> X. \<exists>U \<in> B. x \<in> U)"

definition is_base_3_intercont::"'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_base_3_intercont B X \<equiv> (B \<subseteq> Pow X) \<and>(\<forall>U1  U2. U1 \<in> B \<and> U2 \<in> B \<longrightarrow> (\<forall>x \<in> U1 \<inter> U2. \<exists> U3\<in> B. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2))"

definition is_base3_for_topology::"'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_base3_for_topology B X \<equiv> is_base_3_covering B X \<and> is_base_3_intercont B X"


definition basis_element_int_npt::"'a set set \<Rightarrow> 'a set \<Rightarrow> ('a set \<Rightarrow> 'a set \<Rightarrow> 'a  \<Rightarrow> 'a set)" where
  "basis_element_int_npt B X \<equiv>  \<lambda>U1 U2 x. SOME U3. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2 \<and>  U3 \<in> B"

definition basis_element_npt::"'a set set \<Rightarrow>  ('a set \<Rightarrow> 'a  \<Rightarrow> 'a set)" where
  "basis_element_npt B \<equiv>  \<lambda>U x. SOME B3. (x \<in> B3) \<and> (B3 \<subseteq> U) \<and>  (B3 \<in> B)"

definition basis_element_pt::"'a set set \<Rightarrow> 'a set \<Rightarrow> ('a  \<Rightarrow> 'a set)" where
  "basis_element_pt B X \<equiv>  \<lambda>x. SOME B3. x \<in> B3 \<and>  B3 \<in> B"


definition is_nhood_system_in::"('a \<Rightarrow> 'a set set) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_nhood_system_in N X \<equiv> (\<forall>x \<in> X. is_pfilter (N x) (Pow X) \<and>
                             (\<forall>V \<in> N x. x \<in> V \<and> 
                               (\<exists>W \<in> N x. (\<forall>y \<in> W. V \<in> N y))))"

definition is_topology_on::"'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
   "is_topology_on T X \<equiv> (T \<in> Dpow X) \<and> (top_u1 T) \<and> (top_i3 T) \<and> (X \<in> T)"

definition top_from_nhoods::"('a \<Rightarrow> 'a set set) \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "top_from_nhoods N X \<equiv> {V \<in> Pow X. (\<forall>x \<in> V. V \<in> N x)}"

definition nhoods_of_in::"'a \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "nhoods_of_in x T X \<equiv> {V. V \<subseteq> X \<and> (\<exists>U. U \<in> T \<and> x \<in> U \<and> U \<subseteq> V)}"

definition topologies_on::"'a set \<Rightarrow> 'a set set set" where
  "topologies_on X \<equiv> {T. is_topology_on T X}"

definition finer_topologies::"'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set set" where
  "finer_topologies E X \<equiv> {T. is_topology_on T X \<and> E \<subseteq> T}"

definition topology_generated_in::"'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "topology_generated_in E X \<equiv> (Sup {E} (topologies_on X))"

definition topology_generated_by_in::"'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "topology_generated_by_in E X \<equiv> \<Inter>(finer_topologies E X)"

lemma pfilter_in_powerset_simp:
  assumes "is_pfilter F (Pow X)"
  shows "\<forall>f \<in> F. f \<le> X"
  using assms is_pfilter_in_imp2 by auto

definition top_sup1::"'a set set set \<Rightarrow>'a set \<Rightarrow> 'a set set" where
  "top_sup1 ET X \<equiv> topology_generated_in (\<Union>ET) X"

definition top_sup2::"'a set set set \<Rightarrow>'a set \<Rightarrow> 'a set set" where
  "top_sup2 ET X \<equiv> (\<Inter>{T. is_topology_on T X \<and> (\<Union>ET) \<subseteq> T})"


definition nhoods_from_top::"'a set set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a set set)" where
  "nhoods_from_top T X \<equiv> (\<lambda>x. if x \<in> X then {V \<in> Pow X. \<exists>U \<in> T. x \<in> U \<and> U \<subseteq> V} else undefined)"

definition nhood_base_from_base::"'a set set \<Rightarrow> 'a set \<Rightarrow>  ('a \<Rightarrow> 'a set set)" where
  "nhood_base_from_base B X \<equiv> (\<lambda>x. if x \<in> X then {Bx \<in> B. x \<in> Bx} else undefined)"

definition is_nhood_base::"('a \<Rightarrow> 'a set set) \<Rightarrow> ('a \<Rightarrow> 'a set set) \<Rightarrow> 'a set \<Rightarrow> bool" where
    "is_nhood_base B N X \<equiv>  (\<forall>x \<in> X. \<forall>V \<in> N x. \<exists>b\<in> B x.  x \<in> b \<and> b \<subseteq> V)"

definition cofinite_sets_in::"'a set \<Rightarrow> 'a set set" where
  "cofinite_sets_in X \<equiv> {U. U \<in> Pow X \<and>  (finite (X - U) \<or> U={})}"

definition particular_point_top::"'a \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "particular_point_top a X \<equiv> {U. U \<in> Pow X \<and>  ((a \<in> U) \<or> U={})}"

definition excluded_point_top::"'a \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "excluded_point_top a X \<equiv> {U. U \<in> Pow X \<and>  a \<notin>  U \<or> U=X}"

definition is_limit_point::"'a  \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_limit_point x A T X \<equiv> (\<forall>V. V \<in>  nhoods_of_in x T X \<longrightarrow> A \<inter> (V - {x}) \<noteq> {})"

definition limit_points::"'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "limit_points A T X \<equiv> {x \<in> X. is_limit_point x A T X}"

definition is_adherent_point::"'a \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_adherent_point x A T X \<equiv> (\<forall>V. V \<in> nhoods_of_in x T X \<longrightarrow> A \<inter> V \<noteq> {})"

definition adherent_points::"'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "adherent_points A T X \<equiv> {x \<in> X. is_adherent_point x A T X}"

definition is_isolated_point::"'a \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_isolated_point x A T X \<equiv> (\<exists>V. V \<in> nhoods_of_in x T X \<and> V \<inter> A = {x})"

definition is_interior_point::"'a \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_interior_point x A T X \<equiv> (A \<in> nhoods_of_in x T X)"

definition smaller_open_sets::"'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "smaller_open_sets E T X \<equiv> {U \<in> T. U \<subseteq> E}"

definition larger_closed_sets::"'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "larger_closed_sets E T X \<equiv> {F \<in> Pow X. (X - F) \<in> T \<and> E \<subseteq> F}"

definition interior1::"'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "interior1 E T X \<equiv> \<Union>{U \<in> T. U \<subseteq> E}"

definition closure1::"'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "closure1 E T X \<equiv> \<Inter>{F. F \<subseteq> X \<and> (X-F) \<in> T \<and> E \<subseteq> F}"

definition interior2::"'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "interior2 E T X \<equiv> {x \<in> X. is_interior_point x E T X}"

definition closure2::"'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "closure2 E T X \<equiv> {x \<in> X. is_adherent_point x E T X}"

definition continuous_at::"('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'b set set \<Rightarrow> 'b set \<Rightarrow> bool" where
  "continuous_at f x T X S Y \<equiv> (\<forall>V \<in> nhoods_of_in (f x) S Y. \<exists>U \<in> nhoods_of_in x T X. f`U \<le> V)"

lemma top_u1_imp_contains_empty:
  "\<And>T. top_u1 T \<Longrightarrow> {} \<in> T"
  by (metis Sup_empty empty_subsetI top_u1_def)

lemma top_i1_imp_contains_carrier:
  "\<And>T. top_i1 T \<Longrightarrow> UNIV \<in> T"
  using top_i1_def by force

lemma top_i3_induct:
  assumes A0:"top_i3 T" and A1:"finite E" and A2:"E \<noteq> {}" and A3:"E \<subseteq> T"
  shows "(\<Inter>E) \<in> T"
  using A1 A2 A3 
proof (induct E rule: finite_ne_induct)
  case (singleton x)
  then show ?case
    by simp 
next
  case (insert x F)
  then show ?case
    using A0 top_i3_def by auto
qed

lemma top_i3_finite_ne:
  assumes "top_i3 T"
  shows "\<And>E. E \<in> Fpow_ne T \<Longrightarrow> (\<Inter>E) \<in> T"
  by (simp add: Fpow_def assms top_i3_induct)

lemma top_i3_i2:
  "top_i3 T \<Longrightarrow> top_i2 T"
  by (simp add: top_i2_def top_i3_induct)


lemma trivial_in_top:
  "is_topology_on T X \<Longrightarrow> ({} \<in> T) \<and> (X \<in> T)"
  by (simp add: is_topology_on_def top_u1_imp_contains_empty)

lemma carrier_is_top_un:
  "is_topology_on T X \<Longrightarrow> \<Union>T = X"
  by (meson Pow_iff cSup_eq_maximum is_topology_on_def subsetD)

lemma trivial_top:
  fixes X::"'a set"
  shows "is_topology_on {{}, X} X"
proof-
  define T where "T= {{}, X}"
  have T0:"T \<in> Dpow X"
    by (simp add: T_def)
  have T1:"top_u1 T"
    using T_def top_u1_def by fastforce
  have T2:"top_i3 T"
    using T_def top_i3_def by fastforce
  have T3:"X \<in> T"
    by (simp add: T_def)
  show ?thesis
    using T1 T2 T_def is_topology_on_def by auto
qed

lemma discrete_top:
  fixes X::"'a set"
  shows "is_topology_on (Pow X) X"
proof-
  define T where "T=Pow X"
  have T0:"T \<in> Dpow X"
    by (simp add: T_def)
  have T1:"top_u1 T"
    using T_def top_u1_def by fastforce
  have T2:"top_i3 T"
    using T_def top_i3_def by fastforce
  have T3:"X \<in> T"
    by (simp add: T_def)
  show ?thesis
    using T1 T2 T_def is_topology_on_def by auto
qed


lemma trivial_is_top:
  "{{}, X} \<in> (topologies_on X)"
  by (simp add: topologies_on_def trivial_top)

lemma discrete_is_top:
  "Pow X\<in> (topologies_on X)"
  by (simp add: discrete_top topologies_on_def)

lemma discrete_greater:
  "\<And>T. T \<in> topologies_on X \<Longrightarrow> T \<le> (Pow X)"
  by (simp add: is_topology_on_def topologies_on_def)

lemma trivial_least:
  "\<And>T. T \<in> topologies_on X \<Longrightarrow> T \<ge> {{} ,X}"
  by (simp add: topologies_on_def trivial_in_top)

lemma topologies_top:
  "is_min {{}, X} (topologies_on X)"
  by (metis is_min_iff trivial_is_top trivial_least)

lemma topologies_bot:
  "is_max (Pow X) (topologies_on X)"
  by (simp add: discrete_greater discrete_is_top is_max_iff)

lemma topologies_inf_closed:
  assumes A0:"ET \<noteq> {}" and A1:"\<forall>T \<in> ET. T \<in> topologies_on X"
  shows  "(\<Inter>ET) \<in> topologies_on X \<and> is_inf (\<Inter>ET) ET (topologies_on X)"
 proof-
  have B0:"\<forall>T \<in> ET. is_topology_on T X"
    using A1 topologies_on_def by fastforce
  have B1:"\<forall>T \<in> ET. top_u1 T \<and> top_i3 T \<and> X \<in> T"
    using B0 is_topology_on_def by blast
  define I where  "I=(\<Inter>ET)"
  have T0:"I \<in> Dpow X"
    by (simp add: A0 A1 I_def Inf_less_eq discrete_greater)
  have T1:"top_u1 I"
  proof-
    have T13:"\<And>E. E \<subseteq> I \<longrightarrow> \<Union>E \<in> I"
    proof
      fix E assume A2:"E \<subseteq> I"
      have T10:"\<forall>x. x \<in> E \<longrightarrow> (\<forall>T \<in> ET. x \<in> T) "
        using A2 I_def by auto
      have T11:"(\<forall>T \<in> ET. E \<subseteq> T) "
        using T10 by blast
      have T12:"(\<forall>T \<in> ET. (\<Union>E) \<in> T)"
        by (meson B1 T11 top_u1_def)
      show "\<Union>E \<in> I"
        using I_def T12 by fastforce
    qed
    show ?thesis
      by (simp add: T13 top_u1_def)
  qed
  have T2:"top_i3 I"
  proof-
    have T13:"\<And>a1 a2. (a1 \<in> I \<and> a2 \<in> I) \<longrightarrow> a1 \<inter> a2 \<in> I"
    proof
      fix a1 a2  assume T13A0:"(a1 \<in> I \<and> a2 \<in> I) "
      have T13B0:"\<forall>T \<in> ET. a1 \<in> T \<and> a2 \<in> T"
        using I_def T13A0 by blast
      have T13B1:"\<forall>T \<in> ET. a1 \<inter> a2 \<in> T"
        by (meson B1 T13B0 top_i3_def)
      show "a1 \<inter> a2 \<in> I"
        by (simp add: I_def T13B1)
    qed
    show ?thesis
      by (simp add: T13 top_i3_def)
  qed
  have T3:"X \<in> I"
    by (simp add: B1 I_def)
  have B3:"I \<in> topologies_on X"
    by (metis T0 T1 T2 T3 is_topology_on_def mem_Collect_eq topologies_on_def)
  have B4:"\<forall>T. T \<in> ET \<longrightarrow> I \<le> T"
    by (simp add: I_def Inter_lower)
  have B5:"\<And>S. (\<And>T. T \<in> ET \<Longrightarrow> S\<le> T) \<Longrightarrow> S \<le> I"
    by (simp add: I_def Inter_greatest)
  have B6:"is_inf I ET (topologies_on X)"
    by (simp add: B3 B4 B5 is_inf_if3)
  show ?thesis
    using B3 B6 I_def by blast
qed

lemma generated_topology1:
  fixes E::"'a set set" and  X::"'a set"
  defines "T \<equiv> topology_generated_by_in E X"
  shows "X \<in> T"
  apply(simp add:T_def topology_generated_by_in_def finer_topologies_def)
  using is_topology_on_def by blast

lemma in_finer_top_imp:
  "Ea \<subseteq> \<Inter>(finer_topologies E X) \<Longrightarrow> T \<in> finer_topologies E X \<Longrightarrow> Ea \<subseteq> T"
  by (simp add: le_Inf_iff)

lemma in_finer_top_imp1:
  "T \<in> finer_topologies E X \<Longrightarrow> is_topology_on T X \<and> (E \<subseteq> T)"
  by (simp add: finer_topologies_def)

lemma in_finer_top_imp2:
  "T \<in> finer_topologies E X \<Longrightarrow> T \<in> Dpow X"
  by (simp add: finer_topologies_def is_topology_on_def)

lemma in_iner_top_imp3:
  "\<And>x. x \<in> \<Inter>(finer_topologies E X) \<Longrightarrow> (\<And>S. S \<in> (finer_topologies E X) \<Longrightarrow> x \<in> S)"
  using InterE by blast

lemma generated_topology2:
  fixes E::"'a set set" and  X::"'a set"
  defines "T \<equiv> topology_generated_by_in E X"
  shows "top_u1 T"
  apply(auto simp add:T_def topology_generated_by_in_def top_u1_def)
proof-
  let ?F="(finer_topologies E X)"
  fix Ea Xa::"'a set set" assume A0:"Ea \<subseteq> \<Inter>?F" assume A1:"Xa \<in> ?F"
  have B0:"Ea \<subseteq> Xa"
    using A0 A1 by blast
  have B1:"top_u1 Xa"
    using A1 in_finer_top_imp1 is_topology_on_def by blast
  show "\<Union>Ea \<in> Xa"
    using B0 B1 top_u1_def by blast
qed

lemma generated_topology3:
  fixes Xa E::"'a set set" and  a1 a2 X::"'a set"
  defines "T \<equiv> topology_generated_by_in E X"
  assumes A0:"\<And>S. S \<in> (finer_topologies E X) \<Longrightarrow> (a1 \<in> S \<and> a2 \<in> S)" and A1:"Xa \<in> (finer_topologies E X)"
  shows "a1 \<inter> a2 \<in> Xa"
proof-
  have B0:"\<And>S. S \<in> (finer_topologies E X) \<longrightarrow> (a1 \<inter> a2 \<in> S)"
    by (meson assms(2) in_finer_top_imp1 is_topology_on_def top_i3_def)
  show ?thesis
    using A1 B0 by blast
qed


lemma generated_topology4:
  fixes E::"'a set set" and  X::"'a set"
  defines "T \<equiv> topology_generated_by_in E X"
  shows "top_i3 T"
  apply(auto simp add:T_def topology_generated_by_in_def top_i3_def)
  by (meson in_finer_top_imp1 is_topology_on_def top_i3_def)

lemma generated_topology5:
  fixes E::"'a set set" and X::"'a set"
  defines "T \<equiv> topology_generated_by_in E X"
  assumes A1:"(finer_topologies E X) \<noteq> {}"
  shows "T \<in> Dpow X"
  apply(auto simp add:T_def topology_generated_by_in_def)
  by (metis A1 DiffI Diff_eq_empty_iff Union_Pow_eq Union_upper empty_iff equals0I in_finer_top_imp1 is_topology_on_def)


lemma generated_topology6:
  fixes E::"'a set set" and X::"'a set"
  defines "T \<equiv> topology_generated_by_in E X"
  assumes "E \<in> Dpow X"
  shows A1:"(finer_topologies E X) \<noteq> {}"
  using assms(2) discrete_top finer_topologies_def by fastforce

lemma generated_topology_is_topology:
  assumes A0:"E \<in> Dpow X"
  shows "is_topology_on (topology_generated_by_in E X) X"
  apply(simp add:is_topology_on_def)
  by (meson PowD assms generated_topology1 generated_topology2 generated_topology4 generated_topology5 generated_topology6)

lemma generated_topology_upper0:
  assumes A0:"E \<in> Dpow X"
  defines "T \<equiv> (topology_generated_by_in E X) "
  shows "E \<subseteq> T"
  apply(auto simp add: T_def)
  by (metis in_finer_top_imp1 le_Inf_iff subsetD topology_generated_by_in_def)

lemma generated_topology_upper1:
  assumes A0:"E \<in> Dpow X"
  defines "T \<equiv> (topology_generated_by_in E X) "
  shows "\<And>Ei. Ei \<in> {E}  \<Longrightarrow> E \<le> T"
  using A0 T_def generated_topology_upper0 by blast


lemma generated_topology_least1:
  assumes A0:"E \<in> Dpow X"
  defines "T \<equiv> (topology_generated_by_in E X) "
  assumes A0:"is_topology_on S X" and A1:"E \<subseteq> S"
  shows "T \<subseteq> S"
  by (auto simp add: T_def A0 finer_topologies_def local.A1 topology_generated_by_in_def)

lemma generated_topology_least2:
  assumes A0:"E \<in> Dpow X"
  defines "T \<equiv> (topology_generated_by_in E X) "
  shows "\<And>S. S \<in> topologies_on X \<and> E \<le> S \<Longrightarrow> T \<le> S"
  by (metis A0 T_def generated_topology_least1 mem_Collect_eq topologies_on_def)


lemma generated_topology_is_sup_in:
  assumes A0:"E \<in> Dpow X"
  defines "T \<equiv> (topology_generated_by_in E X) "
  shows "has_sup {E} (topologies_on X) \<and> is_sup T {E} (topologies_on X)"
  proof-
    have B0:"T \<in> ub_set {E} (topologies_on X)"
      by (metis A0 T_def generated_topology_is_topology generated_topology_upper0 mem_Collect_eq singletonD topologies_on_def ub_set_elm)
    have B1:"\<And>S. S \<in> ub_set {E} (topologies_on X) \<Longrightarrow> T \<le> S"
      by (metis A0 T_def generated_topology_least2 singletonI ub_set_mem)
    have B2:"is_sup T {E} (topologies_on X)"
      by (simp add: B0 B1 is_min_iff is_sup_def)
    have B3:"is_sup T {E} (topologies_on X)"
      by (simp add: B2)
    show ?thesis
      using B3 has_sup_def is_min_imp_has_min is_sup_def by blast
qed

lemma generated_topology_is_sup_in2:
 assumes A0:"E \<in> Dpow X"
 shows  "(topology_generated_by_in E X) = (topology_generated_in E X)"
  by (metis assms generated_topology_is_sup_in is_sup_sup_eq topology_generated_in_def)


lemma topologies_sup_closed:
  assumes A0:"ET \<noteq> {}" and A1:"\<forall>T \<in> ET. T \<in> topologies_on X"
  shows "(\<Inter>{T. is_topology_on T X \<and> (\<Union>ET) \<subseteq> T}) \<in> topologies_on X \<and>
         (is_sup (\<Inter>{T. is_topology_on T X \<and> (\<Union>ET) \<subseteq> T}) ET (topologies_on X)) "
proof-
  define U where "U=({T. is_topology_on T X \<and> (\<Union>ET) \<subseteq> T})"
  have B0:"(Pow X) \<in> U"
    by (simp add: A1 Sup_le_iff U_def discrete_greater discrete_top)
  have B1:"U \<noteq> {}"
    using B0 by force
  have B2:"(\<Inter>U) \<in> topologies_on X"
    by (metis (no_types, lifting) B1 U_def mem_Collect_eq topologies_inf_closed topologies_on_def)
  have B3:"\<forall>T. is_topology_on T X \<and>  (\<Union>ET) \<subseteq> T \<longrightarrow> (\<Inter>U) \<subseteq> T"
    by (simp add: Inter_lower U_def)
  have B4:"\<forall>T \<in> ET. T \<subseteq> (\<Inter>U)"
    using U_def by blast
  have B5:" (is_sup (\<Inter>U) ET (topologies_on X))"
    by (metis B2 B3 B4 Sup_least is_sup_if3 mem_Collect_eq topologies_on_def)
  show ?thesis
    using B2 B5 U_def by auto
qed
  


lemma topologies_on_mem_iff:
  "\<And>T. T \<in> topologies_on X \<longleftrightarrow> is_topology_on T X"
  by (simp add: topologies_on_def)

lemma nhoods_of_in_mem_iff:
  "\<And>N. N \<in> nhoods_of_in x T X \<longleftrightarrow> (N \<subseteq> X) \<and>(\<exists>U. U \<in> T \<and> x \<in> U \<and> U \<subseteq> N)"
  by (simp add: nhoods_of_in_def)

lemma nhoods_of_in_imp0:
  "\<And>N. N \<in> nhoods_of_in x T X \<Longrightarrow> x \<in> N"
  by (meson nhoods_of_in_mem_iff subsetD)

lemma nhoods_of_in_imp1:
  "\<And>N. N \<in> nhoods_of_in x T X \<Longrightarrow> N \<in> Pow X"
  by (simp add: nhoods_of_in_mem_iff)

lemma nhoods_of_in_imp2:
  "nhoods_of_in x T X \<subseteq> Pow X"
  by (meson nhoods_of_in_imp1 subsetI)

lemma nhoods_of_in_imp3:
  "\<And>N. N \<in> nhoods_of_in x T X \<Longrightarrow>  (\<exists>U. U \<in> T \<and> x \<in> U \<and> U \<subseteq> N)"
  by (simp add: nhoods_of_in_mem_iff)

lemma nhoods_of_obtains:
  assumes "N \<in> nhoods_of_in x T X"
  obtains U where "U \<in> T \<and> x \<in> U \<and> U \<subseteq> N"
  by (meson assms nhoods_of_in_imp3)

lemma top_from_nhoods_mem_imp:
  "\<And>V. V \<in> top_from_nhoods N X \<Longrightarrow>  V \<in> Pow X \<and> (\<forall>x \<in> V. V \<in> N x)"
  by (simp add: top_from_nhoods_def)

lemma nhoods_from_top_mem_imp1:
  "\<And>V x. x \<in> X \<Longrightarrow> V \<in> nhoods_from_top T X x \<Longrightarrow>  (\<exists>U \<in> T. x \<in> U \<and> U \<subseteq> V)"
  by (simp add: nhoods_from_top_def)

lemma nhood_system_imp_pfilters:
  assumes A0:"is_nhood_system_in N X"
  shows "\<And>x. x \<in> X \<Longrightarrow> is_pfilter (N x) (Pow X)"
  using assms is_nhood_system_in_def by fastforce 

lemma nhood_system_imp_subset:
  assumes A0:"is_nhood_system_in N X" 
  shows "\<And>x V. (x \<in> X \<and> V \<in> (N x)) \<Longrightarrow> V \<subseteq> X"
  by (meson assms is_nhood_system_in_def pfilter_in_powerset_simp)

lemma open_is_nhood_in:
  "\<And>V x. x \<in> X \<Longrightarrow> x \<in> V \<Longrightarrow> V \<in> T \<Longrightarrow>  V \<subseteq> X \<Longrightarrow> V \<in> nhoods_of_in x T X"
  using nhoods_of_in_def by fastforce

lemma adherent_to_self:
  assumes "is_topology_on T X" and "A \<subseteq> X" and "x \<in> A"
  shows "is_adherent_point x A T X"
  apply(simp add: is_adherent_point_def)
  by (meson assms(3) disjoint_iff nhoods_of_in_imp0)

lemma nhoods_is_pfilter:
  fixes X::"'a set" and T::"'a set set" and x::"'a"
  assumes A0:"is_topology_on T X" and A1:"x \<in> X"
  shows "is_pfilter (nhoods_of_in x T X) (Pow X)"
proof-
  let ?Nx="(nhoods_of_in x T X)"
  have B0:"?Nx \<noteq> Pow X"
    using nhoods_of_in_imp0 by force
  have B1:"is_dwdir ?Nx"
  proof-
    have B10:"\<And>a b. (a \<in> ?Nx \<and> b \<in> ?Nx) \<longrightarrow> (\<exists>c  \<in> ?Nx. (c \<le> a) \<and>  (c \<le> b))"
    proof
      fix Va Vb assume A2:"(Va \<in> ?Nx \<and> Vb \<in> ?Nx)"
      obtain Ua where A3:"Ua \<in> T \<and> x \<in> Ua \<and> Ua \<subseteq> Va"
        by (meson A2 nhoods_of_in_imp3)
      obtain Ub where A4:"Ub \<in> T \<and> x \<in> Ub \<and> Ub \<subseteq> Vb"
        by (meson A2 nhoods_of_in_imp3)
      have B11:"Ua \<inter> Ub \<in> T"
        by (meson A0 A3 A4 is_topology_on_def top_i3_def)
      have B12:"Ua \<inter> Ub \<in> T \<and> x \<in> Ua \<inter> Ub \<and> Ua \<inter> Ub \<subseteq> Va \<and> Ua \<inter> Ub \<subseteq> Vb"
        by (simp add: A3 A4 B11 inf.coboundedI1 inf.coboundedI2)
      show "(\<exists>c  \<in> ?Nx. (c \<le> Va) \<and>  (c \<le> Vb))"
        by (metis A0 B12 Sup_upper carrier_is_top_un local.A1 open_is_nhood_in)
    qed
    show ?thesis
      by (metis A0 B10 PowD Pow_top bex_empty is_dwdir_if2 local.A1 open_is_nhood_in trivial_in_top)
  qed
  have B2:"is_up_cl ?Nx (Pow X)"
  proof-
    have B20:"\<And>a b. (a \<le> b \<and> b \<in> Pow X \<and>  a \<in> ?Nx) \<longrightarrow>  b \<in> ?Nx"
    proof
      fix Va Vb assume A5:"Va \<le> Vb \<and> Vb \<in> Pow X \<and> Va \<in> ?Nx"
      obtain Ua where A6:"Ua \<in> T \<and> x \<in> Ua \<and> Ua \<subseteq> Va"
        by (meson A5 nhoods_of_in_imp3)
      have B21:"Ua \<subseteq> Vb"
        using A5 A6 by auto
      show "Vb \<in> ?Nx"
        by (meson A5 A6 B21 PowD nhoods_of_in_mem_iff)
    qed
    have B21:"?Nx \<subseteq> (Pow X)"
      by (simp add: nhoods_of_in_imp2)
   show ?thesis
     by (meson B20 B21 is_up_cl_if2)
  qed
  have B3:"?Nx \<noteq> {}"
    by (simp add: B1 is_dwdir_imp1)
  show ?thesis
    by (simp add: B0 B1 B2 is_pfilter_in_if2 nhoods_of_in_imp2)
qed



lemma top_from_nhoods_inv:
  fixes X::"'a set" and T::"'a set set" and x::"'a"
  assumes A0:"is_topology_on T X"
  shows "top_from_nhoods (nhoods_from_top T X) X = T" (is "?L = ?R")
proof-
  define N where "N= (nhoods_from_top T X)"
  have B0:"?L \<subseteq> ?R"
  proof
    fix V assume A1:"V \<in> ?L"
    have B01:"V \<in> Pow X \<and> (\<forall>x \<in> V. V \<in> N x)"
      using A1 N_def top_from_nhoods_mem_imp by blast
    have B02:"\<forall>x \<in> V. \<exists>U \<in> T. x \<in> U \<and> U \<subseteq> V"
      by (metis A1 Pow_iff nhoods_from_top_mem_imp1 subsetD top_from_nhoods_mem_imp)
    define F where "F=(\<lambda>x. (SOME U. U \<in> T \<and> x \<in> U \<and> U \<subseteq> V))"
    have B03:"\<forall>x \<in> V. F x \<in> T \<and> x \<in> (F x) \<and> (F x) \<subseteq> V"
      by (metis (mono_tags, lifting) B02 F_def someI)
    have B04:"\<Union>(F`V) \<subseteq> V"
      using B03 by blast
    have B05:"\<Union>(F`V) \<supseteq> V"
      using B03 by blast
    have B06:"\<Union>(F`V) =V"
      using B04 B05 by blast
    have B07:"\<forall>U \<in> (F`V). U \<in> T"
      using B03 by blast
    have B08:"V \<in> T"
      by (metis A0 B06 B07 is_topology_on_def subsetI top_u1_def)
    show "V \<in> ?R"
      by (simp add: B08)
  qed
  have B1:"?R \<subseteq> ?L"
  proof
    fix V assume A1:"V \<in> ?R"
    have B10:"V \<subseteq> X"
      by (meson A1 PowD assms in_mono is_topology_on_def)
    show "V \<in> ?L"
    proof(cases "V = {}")
      case True
      then show ?thesis
        by (simp add: top_from_nhoods_def)
    next
      case False
      obtain x where A2:"x \<in> V"
        using False by blast
      have B11:"\<exists>U \<in> T. x \<in> U \<and> U \<subseteq> V"
        using A1 A2 by blast
      then show ?thesis
        apply(simp add:top_from_nhoods_def nhoods_from_top_def)
        using B10 local.A1 by blast
    qed
  qed
  show ?thesis
    by (simp add: B0 B1 subset_antisym)
qed

lemma nhoods_from_top_inv:
  fixes X::"'a set" and N::"('a \<Rightarrow> 'a set set)" and x::"'a"
  assumes A0:"is_nhood_system_in N X" and A1:"x \<in> X"
  shows "(nhoods_from_top (top_from_nhoods N X) X)(x) = N(x)"
proof-
  define T where A2:"T=top_from_nhoods N X"
  define L where "L=(nhoods_from_top (top_from_nhoods N X) X)"
  have B0:"\<And>V. V \<in> L x \<longrightarrow> V \<in> N x"
  proof
    fix V assume A3:"V \<in> L x"
    obtain U where B1:"U \<in> T \<and> x \<in> U \<and> U \<subseteq> V"
      by (metis A1 A2 A3 L_def nhoods_from_top_mem_imp1)
    have B2:" (\<forall>y \<in> U. U \<in> N y)"
      using A2 B1 top_from_nhoods_mem_imp by blast
    have B3:"U \<in> N x"
      by (simp add: B1 B2)
    have B4:"U \<subseteq> V \<and> V \<subseteq> X"
      by (metis (no_types, lifting) A1 A3 B1 CollectD L_def PowD nhoods_from_top_def)
    have B5:"is_pfilter (N x) (Pow X)"
      using A2 assms is_nhood_system_in_def by fastforce
    have B6:"is_up_cl (N x) (Pow X)"
      by (simp add: B5 is_filter_imp1 is_pfilter_in_imp)
    show "V \<in> N x"
      by (metis B3 B4 B6 PowI is_up_cl_imp2)
  qed
  have B7:"\<And>V. V \<in> N x \<longrightarrow> V \<in> L x"
  proof
    fix V assume A4:"V \<in> N x"
    have A40:"V \<subseteq> X"
      by (meson A0 A1 A4 nhood_system_imp_subset)
    define U where A5:"U={y \<in> X. V \<in> N y}"
    have B7:"x \<in> U"
      by (simp add: A1 A4 A5)
    have B8:"U \<subseteq> V"
      using A0 A5 is_nhood_system_in_def by fastforce
    have B9:"(\<And>y. y \<in> U \<longrightarrow> U \<in> N y)"
      proof
        fix y assume A6:"y \<in> U"
        have A61:"V \<in> N y"
          using A5 A6 by blast
        obtain W where A7:"(W \<in> N y \<and> (\<forall>z \<in> W. V \<in> N z))"
          by (metis (no_types, lifting) A0 A5 A6 CollectD is_nhood_system_in_def)
        have B10:"W \<subseteq> U"
        proof
          fix z assume A8:"z \<in> W"
          have B101:"V \<in> N z"
            by (simp add: A7 A8)
          show "z \<in> U"
            using A0 A5 A6 A7 A8 nhood_system_imp_subset by fastforce
        qed
        have B110:"W \<in> N y \<and> is_pfilter (N y) (Pow X) \<and> W \<subseteq> U "
          by (meson A0 A40 A6 A7 B10 B8 in_mono nhood_system_imp_pfilters)
        have B11:"U \<in> N y"
          by (meson A40 B110 B8 Pow_iff is_pfilter_in_imp2 is_up_cl_imp2 order.trans)
        show "U \<in> N y"
          using B11 by force
      qed
    have B120:"U \<in> Pow X \<and> (\<forall>u \<in> U.  V \<in> N u)"
      using A5 by blast
    have B121:"U \<in> T"
      using A2 B120 B9 top_from_nhoods_def by force
    have B122:"x \<in> U \<and> U \<subseteq> V"
      by (simp add: B7 B8)
    have B12:"V \<in> Pow X \<and> U \<in> T \<and> x \<in> U \<and> U \<subseteq> V"
      by (simp add: A40 B121 B7 B8)
    show "V \<in> L x"
      by (metis (no_types, lifting) A1 A2 B12 CollectI L_def nhoods_from_top_def)
  qed
  show ?thesis
    using B0 B7 L_def by blast
qed




lemma is_base1_for_topology_imp:
   "is_base1_for_topology B T \<Longrightarrow> U \<in> T \<Longrightarrow> (\<exists>E \<in> Pow B. U=\<Union>E)"
  by (simp add: is_base1_for_topology_def)

lemma is_base2_for_topology_imp0:
  "is_base2_for_topology B T \<Longrightarrow> (B \<subseteq> T) \<and> (\<forall>U \<in> T. \<forall>x \<in> U. \<exists>B \<in> B. (x \<in> B \<and> B \<subseteq> U))"
  by (simp add: is_base2_for_topology_def)

lemma is_base2_for_topology_if0:
  "(B \<subseteq> T) \<Longrightarrow> (\<forall>U \<in> T. \<forall>x \<in> U. \<exists>B \<in> B. (x \<in> B \<and> B \<subseteq> U)) \<Longrightarrow> is_base2_for_topology B T "
  by (simp add: is_base2_for_topology_def)

lemma is_base2_for_topology_imp1:
  "is_base2_for_topology B T \<Longrightarrow>  U \<in> T \<Longrightarrow> x \<in> U \<Longrightarrow>  (\<exists>Bx \<in> B. (x \<in> Bx \<and> Bx \<subseteq> U))"
  by (simp add: is_base2_for_topology_def)

lemma is_base2_for_topology_imp2:
  assumes "is_base2_for_topology B T" "U \<in> T" "x \<in> U"
  obtains Bx where "Bx \<in> B  \<and> x \<in> Bx \<and> Bx \<subseteq> U"
  by (meson assms(1) assms(2) assms(3) is_base2_for_topology_imp1)

lemma is_base_3_covering_imp1:
  "is_base_3_covering B X \<Longrightarrow>  (B \<in> Dpow X)"
  by (simp add: is_base_3_covering_def)

lemma is_base_3_covering_imp2:
  "is_base_3_covering B X  \<Longrightarrow> (\<forall>x \<in> X. \<exists>U \<in> B. x \<in> U)"
  by (simp add: is_base_3_covering_def)

lemma is_base_3_covering_obtains:
  assumes "is_base_3_covering B X"  and "x \<in> X" obtains U where "U \<in> B \<and> x \<in> U"
  using assms(1) assms(2) is_base_3_covering_imp2 by blast


lemma is_base_3_covering_if:
  "(B \<in> Dpow X) \<Longrightarrow>  (\<forall>x \<in> X. \<exists>U \<in> B. x \<in> U) \<Longrightarrow>  is_base_3_covering B X"
  by (simp add: is_base_3_covering_def)


lemma is_base_3_intercont_imp1:
  "is_base_3_intercont B X \<Longrightarrow> (\<forall>U1  U2. U1 \<in> B \<and> U2 \<in> B \<longrightarrow> (\<forall>x \<in> U1 \<inter> U2. \<exists> U3\<in> B. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2))"
  by (simp add: is_base_3_intercont_def)

lemma is_base_3_intercont_if:
  "B \<subseteq> Pow X \<Longrightarrow> (\<forall>U1  U2. U1 \<in> B \<and> U2 \<in> B \<longrightarrow> (\<forall>x \<in> U1 \<inter> U2. \<exists> U3\<in> B. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2)) \<Longrightarrow> is_base_3_intercont B X "
  by (simp add: is_base_3_intercont_def)


lemma is_base_3_intercont_if2:
  "B \<subseteq> Pow X \<Longrightarrow> (\<And>x U1  U2. x \<in> U1 \<inter> U2 \<and> U1 \<in> B \<and> U2 \<in> B \<Longrightarrow> (\<exists> U3\<in> B. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2)) \<Longrightarrow> is_base_3_intercont B X "
  by (simp add: is_base_3_intercont_def)


lemma is_base_3_intercont_obtains1:
  assumes "is_base_3_intercont B X" and "U1 \<in> B \<and> U2 \<in> B" and "x \<in> U1 \<inter> U2"
  obtains U3 where "U3 \<in> B \<and> x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2"
  by (meson assms(1) assms(2) assms(3) is_base_3_intercont_imp1)


lemma is_base3_for_topology_imp0:
  "is_base3_for_topology B X \<Longrightarrow> is_base_3_intercont B X"
  by (simp add: is_base3_for_topology_def)

lemma is_base3_for_topology_imp1:
  "is_base3_for_topology B X \<Longrightarrow> is_base_3_covering B X"
  by (simp add: is_base3_for_topology_def)

lemma is_base3_for_topology_imp2:
   "is_base3_for_topology B X \<Longrightarrow> B \<in> Dpow X"
   by (simp add: is_base3_for_topology_def is_base_3_covering_def)

lemma is_base3_for_topology_imp3:
   "is_base3_for_topology B X \<Longrightarrow> (\<forall>x \<in> X. \<exists>U \<in> B. x \<in> U)"
    by (simp add: is_base3_for_topology_def is_base_3_covering_def)

lemma is_base3_for_topology_imp3b:
  "is_base3_for_topology B X \<Longrightarrow> x \<in> X  \<Longrightarrow>  \<exists>U \<in> B. x \<in> U"
  by (simp add: is_base3_for_topology_imp3)


lemma is_base3_for_topology_imp4:
   "is_base3_for_topology B X \<Longrightarrow> (\<forall>U1  U2. U1 \<in> B \<and> U2 \<in> B \<longrightarrow> (\<forall>x \<in> U1 \<inter> U2. \<exists> U3\<in> B. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2))"
    by (simp add: is_base3_for_topology_def is_base_3_intercont_def)

lemma is_base3_for_topology_imp4b:
   "is_base3_for_topology B X \<Longrightarrow>  U1 \<in> B \<and> U2 \<in> B \<and> x \<in> U1 \<inter> U2 \<Longrightarrow> (\<exists>U3\<in> B. x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2)"
    by (simp add: is_base3_for_topology_def is_base_3_intercont_def)

lemma is_base_3_intercont_imp4c:
  assumes "is_base_3_intercont B X" and "U1 \<in> B \<and> U2 \<in> B \<and> x \<in> U1 \<inter> U2"
  shows "\<exists>U3. U3 \<in> B \<and> x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2"
  by (meson assms(1) assms(2) is_base_3_intercont_imp1)

lemma is_base3_for_topology_imp5:
  "is_base3_for_topology B X \<Longrightarrow> b \<in> B \<Longrightarrow> b \<subseteq> X"
  using is_base3_for_topology_imp2 by fastforce

lemma is_base3_for_topology_imp6:
  "is_base3_for_topology B X \<Longrightarrow> V \<in> Pow B \<Longrightarrow> (\<Union>V) \<in> Pow X"
  using is_base3_for_topology_imp2 by fastforce

lemma is_base3_for_topology_if:
   " is_base_3_covering B X \<Longrightarrow> is_base_3_intercont B X   \<Longrightarrow>is_base3_for_topology B X"
    by (simp add: is_base3_for_topology_def)

lemma nhood_base_imp0:
  "x \<in> X \<Longrightarrow> b \<in> nhood_base_from_base B X x \<Longrightarrow> b \<in> B"
  by (simp add: nhood_base_from_base_def)

lemma nhood_base_imp1:
  "x \<in> X \<Longrightarrow> b \<in> nhood_base_from_base B X x \<Longrightarrow> x \<in> b"
  by (simp add: nhood_base_from_base_def)

lemma in_nhood_base_imp2:
  "x \<in> X \<Longrightarrow> x \<in> b  \<Longrightarrow>b \<in> B \<Longrightarrow>  b \<in> nhood_base_from_base B X x"
  by (simp add: nhood_base_from_base_def)

lemma base_intercont_imp_pset_downdir:
  assumes A0:"is_base_3_intercont B X" and  A1:"x \<in> X" and A2:"(nhood_base_from_base B X x) \<noteq> {}"
  shows "is_dwdir (nhood_base_from_base B X x)"
  proof-
  have B0:"\<And>a b. a \<in> nhood_base_from_base B X x \<and> b \<in> nhood_base_from_base B X x \<longrightarrow> ( \<exists>c::'a set\<in>nhood_base_from_base B X x. c lb {a, b})"
  proof
    fix a b assume A3:"a \<in> nhood_base_from_base B X x \<and> b \<in> nhood_base_from_base B X x"
    have B0:"x \<in> a \<inter> b"
      by (meson A3 IntI local.A1 nhood_base_imp1)
    obtain c where B1:"c \<in> B \<and> x \<in> c \<and> c \<subseteq> a \<inter> b"
      by (metis A0 A3 B0 is_base_3_intercont_def local.A1 nhood_base_imp0)
    have B2:"c \<in> nhood_base_from_base B X x"
      by (simp add: B1 in_nhood_base_imp2 local.A1)
    have B3:"c lb {a, b}"
      by (metis B1 Inf_insert Inter_empty inf_top.right_neutral lb_def le_Inf_iff)
    show "( \<exists>c::'a set\<in>nhood_base_from_base B X x. c lb {a, b})"
      using B2 B3 by auto
    qed
  show ?thesis
    by (simp add: A2 B0 is_dwdir_if1)
qed





lemma basis_element_pt_props:
  assumes A0:"is_base2_for_topology B T"
  defines "f \<equiv> basis_element_npt B"
  shows "\<And>U x. (U \<in> T \<and> x \<in> U) \<longrightarrow> (f U x) \<in> B \<and> x \<in> (f U x) \<and> (f U x) \<subseteq> U"
proof
    fix U x assume A1:"U \<in> T \<and> x \<in> U"
    obtain Bx where B1:"Bx \<in> B \<and> x \<in> Bx \<and> Bx \<subseteq> U"
      by (meson A0 A1 is_base2_for_topology_imp2)
    show "(f U x) \<in> B \<and> x \<in> (f U x) \<and> (f U x) \<subseteq> U"
    apply( simp add:f_def basis_element_npt_def)
      by (metis (mono_tags, lifting) \<open>\<And>thesis::bool. (\<And>Bx::'a::type set. Bx \<in> (B::'a::type set set) \<and> (x::'a::type) \<in> Bx \<and> Bx \<subseteq> (U::'a::type set) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> someI2_ex)
qed


lemma basis_element_pt_props2:
  assumes A0:"is_base2_for_topology B T"
  defines "f \<equiv> basis_element_npt B"
  shows "\<And>U. U \<in> T \<Longrightarrow> (\<forall>x. x \<in> U \<longrightarrow> (f U x) \<in> B \<and> x \<in> (f U x) \<and> (f U x) \<subseteq> U)"
  by (metis A0 basis_element_pt_props f_def)


lemma basis_element_pt_props3:
  assumes A0:"is_base2_for_topology B T" and A1:"U \<in> T"
  defines "f \<equiv> (\<lambda>x. ((basis_element_npt B) U x))"
  shows "(\<Union>(f`U)) =U "
  using A0 A1 basis_element_pt_props f_def by fastforce


lemma basis_element_npt_props:
  assumes "is_base3_for_topology B X"
  defines "f \<equiv> basis_element_pt B X"
  shows "\<And>x. x \<in> X \<longrightarrow> (f x) \<in> B \<and> x \<in> (f x)"
proof
    fix x assume A0:"x \<in> X"
    show "(f x) \<in> B \<and> x \<in> (f x)"
    apply(simp add:f_def basis_element_pt_def)
      by (metis (no_types, lifting) A0 assms(1) is_base3_for_topology_imp3 someI_ex)
qed

lemma basis_element_int_npt_props0:
  assumes "is_base3_for_topology B X"
  defines "f \<equiv> basis_element_int_npt B X"
  shows "\<And>U1 U2 x. U1 \<in> B \<and> U2 \<in> B  \<and> x \<in> U1 \<inter> U2 \<longrightarrow> ((f U1 U2 x) \<in> B \<and> ((f U1 U2 x) \<subseteq> U1 \<inter> U2) \<and> x \<in> (f U1 U2 x))"
proof
    fix U1 U2 x assume A0:"U1 \<in> B \<and> U2 \<in> B  \<and> x \<in> U1 \<inter> U2"
    let ?U3="(f U1 U2 x)"
    have B0:"\<exists>U3. U3 \<in> B \<and> x \<in> U3 \<and> U3 \<subseteq> U1 \<inter> U2"
      by (meson A0 assms(1) is_base3_for_topology_imp4b)
    have B1:"is_base_3_intercont B X"
      by (simp add: assms(1) is_base3_for_topology_imp0)
    show "?U3 \<in> B \<and> (?U3 \<subseteq> U1 \<inter> U2) \<and> x \<in> ?U3"
    apply(simp add:f_def basis_element_int_npt_def)
      by (metis (mono_tags, lifting) B0 Int_subset_iff tfl_some)
qed

lemma un_all_pts:
  assumes "\<And>x. x \<in> U \<longrightarrow> (x \<in> V x) \<and> (V x \<subseteq> U)"
  shows "(\<Union>x \<in> U. V x) = U"
  using assms by fastforce

lemma basis_element_int_npt_props1:
  assumes "is_base3_for_topology B X" "(b1 \<in> B \<and> b2 \<in> B)"
  shows "\<exists>V \<in> Pow B.  b1 \<inter> b2 = (\<Union>V)"
proof-
  define V where A2:"V = (\<lambda>x. (basis_element_int_npt B X) b1 b2 x)"
  have B0:"\<And>x. x \<in> b1 \<inter> b2 \<longrightarrow> (x \<in> V x) \<and> (V x \<subseteq> b1 \<inter> b2)"
    by (metis A2 assms(1) assms(2) basis_element_int_npt_props0)
  have B1:"(\<Union>x \<in> b1 \<inter> b2. V x) = b1 \<inter> b2 "
    using B0 by blast
  have B2:"V`(b1 \<inter> b2) \<in> Pow B \<and>   b1 \<inter> b2 = (\<Union>(V`(b1 \<inter> b2)))"
    by (metis B1 PowI \<open>V::'a::type \<Rightarrow> 'a::type set \<equiv> basis_element_int_npt (B::'a::type set set) (X::'a::type set) (b1::'a::type set) (b2::'a::type set)\<close> assms(1) assms(2) basis_element_int_npt_props0 image_subset_iff)
  show ?thesis
    using B2 by auto
qed  

lemma is_base3_for_topology_imp7:
  assumes A0:"is_base3_for_topology B X"
  shows "X \<in> (sup_cle B (Pow X))"
proof-
  define U where "U=basis_element_pt B X"
  have B0:"\<And>x. x \<in> X \<longrightarrow> x \<in> U x \<and>  U x \<in> B"
    by (simp add: U_def assms basis_element_npt_props)
  have B1:"\<And>x. x \<in> X \<longrightarrow> (U x) \<subseteq> X"
    using B0 assms is_base3_for_topology_imp5 by blast
  have B2:"(\<Union>x \<in> X. U x) = X"
    using B0 B1 by blast
  have B8:"U`X \<subseteq> B"
    using B0 by blast
  have B9:"\<forall>a \<in> U`X. a \<le> \<Union>(U`X)"
    by blast
  have B10:"\<forall>u \<in> ub_set (U`X) (Pow X). \<Union>(U`X) \<le> u "
    by (simp add: Sup_le_iff ub_set_mem_iff)
  have B11:"is_sup (\<Union>(U`X)) (U`X) (Pow X)"
    by (metis B2 B9 Pow_iff Sup_least is_sup_if3)
  have B12:"Sup (U`X) (Pow X)= X"
    by (metis B11 B2 is_sup_sup_eq)
  show ?thesis
    by (metis B12 B2 B8 PowI Pow_top inf_ub_imp_has_sup sets_have_inf5 subset_Pow_Union sup_cle_if1)
qed

lemma is_base3_for_topology_imp8:
  assumes A0:"is_base3_for_topology B X"
  shows "X \<in> (sup_cle B UNIV)"
proof-
  define U where "U=basis_element_pt B X"
  have B0:"\<And>x. x \<in> X \<longrightarrow> x \<in> U x \<and>  U x \<in> B"
    by (simp add: U_def assms basis_element_npt_props)
  have B1:"\<And>x. x \<in> X \<longrightarrow> (U x) \<subseteq> X"
    using B0 assms is_base3_for_topology_imp5 by blast
  have B2:"(\<Union>x \<in> X. U x) = X"
    using B0 B1 by blast
  have B8:"U`X \<subseteq> B"
    using B0 by blast
  have B9:"\<forall>a \<in> U`X. a \<le> \<Union>(U`X)"
    by blast
  have B10:"\<forall>u \<in> ub_set (U`X) (Pow X). \<Union>(U`X) \<le> u "
    by (simp add: Sup_le_iff ub_set_mem_iff)
  have B11:"is_sup (\<Union>(U`X)) (U`X) (Pow X)"
    by (metis B2 B9 Pow_iff Sup_least is_sup_if3)
  have B12:"Sup (U`X) (Pow X)= X"
    by (metis B11 B2 is_sup_sup_eq)
  have B13:"Sup (U`X) (Pow X) = Sup (U`X) UNIV"
    by (simp add: B12 B2 sets_have_sup3)
  show ?thesis
    by (metis B12 B13 B8 Pow_iff iso_tuple_UNIV_I sets_have_sup2 sup_cle_if1)
qed
  


end
