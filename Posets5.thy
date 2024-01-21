theory Posets5
  imports Main
begin


section Prelims
subsection DeclarationsAndNotation
hide_const(open) List.list.Nil
no_notation List.list.Nil ("[]")  
no_notation Cons (infixr "#" 65) 
hide_type list
hide_const rev

declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]


abbreviation Fpow_ne::"'a set \<Rightarrow> 'a set set" where
  "Fpow_ne A \<equiv> (Fpow A)-{{}}"

abbreviation Dpow::"'a set \<Rightarrow> 'a set set set" where
  "Dpow A \<equiv> (Pow (Pow A))"

abbreviation Pow_ne::"'a set \<Rightarrow> 'a set set" where
  "Pow_ne A \<equiv> (Pow A) - {{}}"

abbreviation is_ne::"'a set \<Rightarrow> bool" where
  "is_ne A \<equiv> A  \<noteq> {}"

definition lb::"'a::ord \<Rightarrow> 'a::ord set \<Rightarrow> bool"  (infix "lb" 50) where
  "b lb A \<equiv> (\<forall>a \<in> A. b \<le> a)"

lemma is_lb_simp1:
  "b lb A \<Longrightarrow> a \<in> A \<Longrightarrow> b \<le> a"
  by (simp add: lb_def)

lemma is_lb_simp2:
  "\<And>b. (\<And>a. a \<in> A \<Longrightarrow> b \<le> a) \<Longrightarrow> b lb A"
  by (simp add: lb_def)

definition ub::"'a::ord \<Rightarrow> 'a::ord set \<Rightarrow> bool"  (infix "ub" 50) where
  "b ub A \<equiv> (\<forall>a \<in> A. a \<le> b)"

lemma is_ub_simp1:
  "b ub A \<Longrightarrow> a \<in> A \<Longrightarrow> a \<le> b"
  by (simp add: ub_def)

lemma is_ub_simp2:
  "\<And>b. (\<And>a. a \<in> A \<Longrightarrow> a \<le> b) \<Longrightarrow> b ub A"
  by (simp add: ub_def)

definition has_lb::"'a::ord set \<Rightarrow>  'a::ord set \<Rightarrow> bool" where
  "has_lb A B \<equiv> (\<exists>b \<in> B. b lb A)"

definition has_ub::"'a::ord set \<Rightarrow>  'a::ord set \<Rightarrow> bool" where
  "has_ub A B \<equiv> (\<exists>b \<in> B. b ub A)"

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


lemma ub_set_imp:
  "\<And>(A::'a::order set) X u. (u \<in> ub_set A X) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> x \<le> u)"
  by (simp add: ub_set_def ub_def)

lemma lb_set_imp:
  "\<And>(A::'a::order set) X l. (l \<in> lb_set A X) \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> l \<le> x)"
  by (simp add: lb_set_def lb_def)


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

lemma lb_set_in_singleton:
  "lb_set {a} X  = {x \<in> X. x \<le> a}"
  by (simp add: set_eq_iff lb_set_mem_iff)

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



definition is_max::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_max m A \<equiv> m \<in> ub_set A A"

definition is_min::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_min m A \<equiv> m \<in> lb_set A A"

definition has_max::"'a::order set \<Rightarrow> bool" where
  "has_max A \<equiv> (\<exists>m. is_max m A)"

definition has_min::"'a::order set \<Rightarrow> bool" where
  "has_min A \<equiv> (\<exists>m. is_min m A)"

definition is_sup::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_sup s A X \<equiv>  (is_min s (ub_set A X))"

definition is_inf::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_inf i A X \<equiv>  (is_max i (lb_set A X))"

definition has_sup::" 'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "has_sup A X \<equiv>  (has_min (ub_set A X))"

definition has_inf::" 'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "has_inf A X \<equiv>  (has_max (lb_set A X))"

definition max::"'a::order set \<Rightarrow> 'a::order" where
  "max A \<equiv> (THE m. is_max m A)"

definition min::"'a::order set \<Rightarrow> 'a::order" where
  "min A \<equiv> (THE m. is_min m A)"

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
  "\<And>(A::'a::order set) B. A \<subseteq> B \<and> (has_min A) \<and> ( has_min B) \<longrightarrow>  min B \<le> min B"
  by(auto simp add:if_has_max_max_unique max_isotone1)

lemma max_singleton:
  "max {x::'a::order} = x"
  apply(simp add: max_def is_max_def ub_set_def ub_def)
  by blast

lemma min_singleton:
  "min {x::'a::order} = x"
  apply(simp add: min_def is_min_def lb_set_def lb_def)
  by blast

definition Sup::"'a::order set \<Rightarrow>'a::order set \<Rightarrow> 'a::order" where
  "Sup A X = (THE s. is_sup s A X)"

definition Inf::"'a::order set \<Rightarrow>'a::order set \<Rightarrow> 'a::order" where
  "Inf A X = (THE i. is_inf i A X)"


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

lemma sup_in_degenerate:  
  assumes A0:"has_min (X::'a::order set)"
  shows "Sup {} X = min X"
  by (simp add: min_def Sup_def is_sup_in_iff ub_set_in_degenerate)

lemma inf_in_degenerate:  
  assumes A0:"has_min (X::'a::order set)"
  shows "Inf {} X = max X"
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

lemma sup_singleton:
  "Sup {x::'a::order} UNIV = x"
  apply(simp add: Sup_def)
  using is_sup_singleton sup_unique by blast

lemma inf_singleton:
  "Inf {x::'a::order} UNIV = x"
  apply(simp add: Inf_def)
  using is_inf_singleton inf_unique by blast

lemma sup_singleton2:
  "(x::'a::order) \<in> X \<Longrightarrow> Sup {x} X = x"
  by (meson has_sup_singleton2 sup_unique sup_is_sup is_sup_singleton2)

lemma inf_singleton2:
  "(x::'a::order) \<in> X \<Longrightarrow> Inf {x} X = x"
  by (meson has_inf_singleton2 inf_unique inf_is_inf is_inf_singleton2)

lemma sup_in_max:
  fixes X::"'a::order set"
  assumes "has_sup X X"
  shows "is_max (Sup X X) X"
  by (simp add: assms has_sup_in_imp2 has_sup_in_set is_max_if2)

lemma inf_in_min:
  fixes X::"'a::order set"
  assumes "has_inf X X"
  shows "is_min (Inf X X) X"
  by (simp add: assms has_inf_in_imp2 has_inf_in_set is_min_if2)

lemma sup_isotone1:
  "\<And>(A::'a::order set) B X. has_sup A X \<Longrightarrow> has_sup B X \<Longrightarrow> A \<subseteq> B \<Longrightarrow> Sup A X \<le> Sup B X"
  by (meson sup_is_sup is_sup_in_imp1 is_min_iff ub_set_antitone1 subsetD)

lemma inf__antitone1:
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

context   
fixes A B C::"'a::order set"
  assumes A0:"A \<noteq> {} \<and> A \<subseteq> B \<and> B \<subseteq> C" and
          A1:"has_sup A C" and
          A2:"has_sup A B"
begin

lemma sup_geq_rsup:
  "Sup A C \<le> Sup A B"
  by (simp add: A0 A1 A2 sup_antitone2)

lemma sup_leq_rsup_if:
  "Sup A B \<le> Sup A C \<longleftrightarrow> (Sup A C \<in> B)" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L show ?R
    by (metis A0 A1 A2 L dual_order.antisym has_sup_in_set sup_antitone2)
  next
  assume R:?R show ?L
    by (simp add: A1 A2 R has_sup_in_imp2 has_sup_imp3)
qed

end

lemma inf_subset_eq:
  fixes A B C::"'a::order set"
  assumes A0:"A \<subseteq> B" and A1:"B \<subseteq> C" and A2:"has_inf A C" and A3:"Inf A C \<in> B"
  shows "has_inf A B \<and> Inf A B = Inf A C"
proof-
  let ?ic="Inf A C"
  have B0:"is_inf ?ic A C"
    by (simp add: A2 inf_is_inf)
  have B1:"?ic \<in> lb_set A B"
    by (simp add: A2 A3 has_inf_in_imp2 lb_set_elm)
  have B2:"lb_set A B \<subseteq> lb_set A C"
    by (simp add: A1 lb_set_in_isotone2)
  have B3:"is_max ?ic (lb_set A B)"
    by (meson B0 B1 B2 is_max_iff is_inf_def subset_eq)
  have B4:"is_inf ?ic A B"
    by (simp add: B3 is_inf_def)
  have B5:"Inf A B = ?ic"
    using B4 is_inf_inf_eq by fastforce
  show ?thesis
    using B3 B4 B5 has_inf_def is_max_imp_has_max by blast
qed


lemma sup_subset_eq:
  fixes A B C::"'a::order set"
  assumes A0:"A \<subseteq> B" and A1:"B \<subseteq> C" and A2:"has_sup A C" and A3:"Sup A C \<in> B"
  shows "has_sup A B \<and> Sup A B = Sup A C"
proof-
  let ?sc="Sup A C"
  have B0:"is_sup ?sc A C"
    by (simp add: A2 sup_is_sup)
  have B1:"?sc \<in> ub_set A B"
    by (simp add: A2 A3 has_sup_in_imp2 ub_set_elm)
  have B2:"ub_set A B \<subseteq> ub_set A C"
    by (simp add: A1 ub_set_in_isotone2)
  have B3:"is_min ?sc (ub_set A B)"
    by (meson B0 B1 B2 is_min_iff is_sup_def subset_eq)
  have B4:"is_sup ?sc A B"
    by (simp add: B3 is_sup_def)
  have B5:"Sup A B = ?sc"
    using B4 is_sup_sup_eq by fastforce
  show ?thesis
    using B3 B4 B5 has_sup_def is_min_imp_has_min by force
qed

lemma inf_in_expression:
  "is_inf m A X \<longleftrightarrow> m \<in> (ub_set (lb_set A X) X) \<inter> (lb_set A X)" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:"?L" show "?R"
    by (metis L inf_commute is_inf_def is_max_def lb_set_subset ub_set_restrict1)
  next
  assume R:"?R" show "?L"
    by (metis R inf_commute is_inf_def is_max_def lb_set_subset ub_set_restrict1)
qed

lemma sup_in_expression:
  "is_sup m A X \<longleftrightarrow> m \<in> (lb_set (ub_set A X) X) \<inter> (ub_set A X)" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:"?L" show "?R"
    by (metis L inf_commute is_min_def is_sup_def lb_set_restrict1 ub_set_subset)
  next
  assume R:"?R" show "?L"
    by (metis R inf_commute is_min_def is_sup_def lb_set_restrict1 ub_set_subset)
qed

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

context fixes A X::"'a::order set"
  assumes A0:"A \<subseteq> X" 
begin

lemma sup_in_eq_inf_in_ub:
  assumes  A1:"has_inf (ub_set A X) X"
  shows "has_sup A X \<and> Sup A X = Inf(ub_set A X) X"
proof-
  let ?U="ub_set A X" let ?i="Inf ?U X"
  have B0:"A \<subseteq> lb_set ?U X"
    by (simp add: A0 lu_extensive)
  have B1:"\<forall>a. a \<in> A \<longrightarrow> a \<le> ?i"
    by (meson A0 A1 has_inf_imp3 subsetD ub_set_imp)
  have B2:"?i \<in> ?U"
    by (simp add: A1 B1 has_inf_in_set ub_set_elm)
  have B3:"is_min ?i ?U"
    by (simp add: A1 B2 has_inf_in_imp2 is_min_if2)
  show ?thesis
    using B3 has_sup_def has_sup_in_imp1 is_min_imp_has_min min_unique by blast
qed

lemma inf_in_eq_sup_in_lb:
  assumes A1:"has_sup (lb_set A X) X"
  shows "has_inf A X \<and> Inf A X = Sup(lb_set A X) X"
proof-
  let ?L="lb_set A X"
  let ?s="Sup ?L X"
  have B0:"A \<subseteq> ub_set ?L X"
    by (meson A0 lb_set_imp subset_eq ub_set_elm)
  have B1:"?s \<in> lb_set A X"
    by (meson A1 B0 has_sup_in_imp1 has_sup_in_set is_min_iff lb_set_elm subset_eq)
  have B2:"is_max ?s ?L"
    by (simp add: A1 B1 has_sup_in_imp2 is_max_if2)
  show ?thesis
    by (metis B2 has_inf_def has_max_iff2 is_inf_in_iff is_inf_inf_eq)
qed


lemma inf_complete_bounded_sup_eq1:
  assumes A1:"(ub_set A X \<noteq> {})" and
          A2:"has_inf (ub_set A X) X"
  shows "Sup A X = Inf (ub_set A X) X"
proof(cases "A = {}")
  case True
  then show ?thesis
    using A2 sup_in_eq_inf_in_ub by blast
next
  case False
  then show ?thesis
    by (simp add: A2 sup_in_eq_inf_in_ub)
qed

lemma sup_complete_bounded_inf_eq1:
  assumes A1:"lb_set A X \<noteq> {}" and
          A2:"has_sup (lb_set A X) X"
  shows "Inf A X = Sup (lb_set A X) X"
proof(cases "A = {}")
  case True
  then show ?thesis
    using A2 inf_in_eq_sup_in_lb by fastforce
next
  case False
  then show ?thesis
    by (simp add: A2 inf_in_eq_sup_in_lb)
qed

end

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


definition up_cl::"'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> 'a::ord set" where
  "up_cl A X \<equiv> {x \<in> X. \<exists>a \<in> A. a \<le> x}"

definition dw_cl::"'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> 'a::ord set" where
  "dw_cl A X \<equiv> {x \<in> X. \<exists>a \<in> A. x \<le> a}"


definition is_up_cl::"'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "is_up_cl A X \<equiv> (up_cl A X = A)"

definition is_dw_cl::"'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "is_dw_cl A X \<equiv> (dw_cl A X = A)"


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


definition is_filter::"'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "is_filter F X \<equiv> is_dwdir F \<and> is_up_cl F X"

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

lemma is_filter_if:
  "is_dwdir F \<Longrightarrow> is_up_cl F X \<Longrightarrow> is_filter F X"
  by (simp add: is_filter_def)



definition is_ideal::"'a::ord set \<Rightarrow> 'a::ord set \<Rightarrow> bool" where
  "is_ideal I X \<equiv> is_updir I \<and> is_dw_cl I X"


definition is_pfilter::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
   "is_pfilter F X \<equiv> is_filter F X \<and> F \<noteq> X " 

definition is_pideal::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
   "is_pideal I X \<equiv> is_ideal I X \<and> I \<noteq> X " 

definition is_principal_filter::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
   "is_principal_filter F X \<equiv> is_filter F X \<and> has_min F "

definition is_principal_ideal::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
   "is_principal_ideal I X \<equiv> is_ideal I X \<and> has_max I "


lemma is_pfilter_in_imp:
  "\<And>F X. is_pfilter F X \<Longrightarrow>  (is_filter F X) \<and> (F \<noteq>  X)"
  by (simp add:is_pfilter_def)

lemma is_pfilter_if:
  "\<And>F X.  (is_filter F X) \<and> ( F \<noteq>  X) \<Longrightarrow> is_pfilter F X "
  by (simp add:is_pfilter_def)

lemma is_pfilter_in_imp2:
  "\<And>F X. is_pfilter F X \<Longrightarrow>  (F \<noteq> X \<and> F \<subseteq> X \<and> is_dwdir F \<and> is_up_cl F X)"
  apply(auto simp add: is_pfilter_def is_filter_def)
  using is_upclosed_in_imp1 apply fastforce
  using is_upclosed_in_imp1 by auto

lemma is_pfilter_in_if2:
  "\<And>F X.  (F \<noteq> X \<and>  F \<subseteq> X \<and> is_dwdir F \<and> is_up_cl F X) \<Longrightarrow> is_pfilter F X "
  by (simp add: is_pfilter_def is_filter_def)

lemma is_principal_filter_imp1:
  "is_principal_filter F X \<Longrightarrow> \<exists>m. is_min m F"
  by (simp add: has_min_iff2 is_principal_filter_def)

lemma is_principal_filter_obtains:
  assumes "is_principal_filter F X"  obtains m where  "is_min m F"
  using assms is_principal_filter_imp1 by auto


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
    using B0 L is_filter_def is_min_imp is_principal_filter_def is_up_cl_imp2 by blast
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
  show ?L
    by (metis B5 B6 is_filter_def empty_iff empty_subsetI insert_subsetI is_dwdir_if2 is_min_imp is_min_imp_has_min is_principal_filter_def is_up_cl_def lb_set_mem up_cl_idempotent)
qed


definition sup_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "sup_cl A X \<equiv> {x \<in> X. \<exists>E \<in> Pow_ne A. has_sup E X \<and> x = Sup E X}"

definition inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "inf_cl A X \<equiv> {x \<in> X. \<exists>E \<in> Pow_ne A. has_inf E X \<and> x = Inf E X}"


definition is_sup_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_sup_cl A X \<equiv> (\<forall>E \<in> Pow_ne A. has_sup E X \<longrightarrow> Sup E X \<in> A)"

definition is_inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_inf_cl A X \<equiv> (\<forall>E \<in> Pow_ne A. has_inf E X \<longrightarrow> Inf E X \<in> A)"

lemma up_closed_supin_closed:
  assumes A0:"is_up_cl A X"
  shows "is_sup_cl A X"
  unfolding is_sup_cl_def
proof
  fix E assume A1:"E \<in> Pow_ne A"
  show "has_sup E X \<longrightarrow> Sup E X \<in> A"
  proof
    assume A2:"has_sup E X"
    have B0:"\<exists>x \<in> E. x \<in> A \<and> x \<le> Sup E X"
      using A1 A2 has_sup_in_imp2 by fastforce
   show "Sup E X \<in> A"
     using A2 B0 assms has_sup_in_set is_up_cl_imp2 by blast
  qed
qed

lemma down_closed_infin_closed:
  assumes "is_dw_cl A X"
  shows "is_inf_cl A X"
  unfolding is_inf_cl_def
proof
  fix E assume "E \<in> Pow_ne A"
  show "has_inf E X \<longrightarrow> Inf E X \<in> A"
  proof
    assume "has_inf E X"
    have "\<exists>x \<in> E. x \<in> A \<and> Inf E X \<le> x"
      using `E \<in> Pow_ne A` `has_inf E X` has_inf_in_imp2 by fastforce
    show "Inf E X \<in> A"
      using `has_inf E X` `\<exists>x \<in> E. x \<in> A \<and> Inf E X \<le> x` assms has_inf_in_set is_dw_cl_imp2 by blast
  qed
qed



context fixes A::"'a::order set set" and
              X::"'a::order set"
        assumes ne:"A \<noteq> {} \<and> (\<forall>Ai \<in> A. Ai \<noteq> {})" and
                ex:"\<forall>Ai \<in> A. has_inf  Ai X"
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
  have B2:"\<forall>x \<in> ?B. u \<le> x"
  proof
    fix x assume A1:"x \<in> ?B"
    obtain Ai where B10:"Ai \<in> A  \<and> x \<in> Ai"
      using A1 by blast
    have B11:"u \<le>  Inf Ai X \<and>  Inf Ai X \<le> x"
      by (simp add: B1 B10 ex has_inf_in_imp2)
    show "u \<le> x"
      using B11 order.trans by blast
  qed
  show ?thesis
    by (meson B0 B2 lb_set_elm)
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

lemma has_inf_imp_eq_inf_inf:
  assumes "has_inf (\<Union>A) X"
  shows "has_inf {s \<in> X. \<exists>Ai \<in> A. s = Inf Ai X } X \<and> Inf {s \<in> X. \<exists>Ai \<in> A. s = Inf Ai X } X = Inf (\<Union>A) X"
proof-
  let ?B= "(\<Union>A)" let ?S="{s \<in> X. \<exists>Ai \<in> A. s = Inf Ai X }"
  let ?i="Inf ?B X"
  have B0:"\<forall>s \<in> ?S. ?i \<le> s"
    using assms has_inf_in_imp1 lb_set_imp lb_un_lb_infs by blast
  have B1:"?i \<in> lb_set ?S X"
    using assms has_inf_in_imp1 lb_un_lb_infs by blast
  have B2:"\<forall>u \<in> lb_set ?S X. u \<in> lb_set ?B X"
    using lb_infs_lb_un by blast
  have B3:"\<forall>u \<in> lb_set ?S X. u \<le> ?i"
    using B2 assms has_inf_in_imp1 is_max_iff by blast
  have B4:"is_inf ?i ?S X"
    by (simp add: B1 B3 assms has_inf_in_set is_inf_if1 is_max_if2)
  have B5:"has_inf ?S X  \<and> ?i = Inf ?S X"
    using B4 has_inf_def has_max_def is_inf_in_imp1 is_inf_inf_eq by blast
  show ?thesis
    using B5 by presburger
qed


lemma inf_inf_imp_has_inf_eq:
  assumes "has_inf (\<Union>A) X"
  shows "has_inf  (\<Union>A) X \<and> Inf  {s \<in> X. \<exists>Ai \<in> A. s = Inf Ai X } X = Inf  (\<Union>A) X"
proof-
  let ?B= "(\<Union>A)" let ?S="{s \<in> X. \<exists>Ai \<in> A. s = Inf Ai X }"
  let ?i="Inf ?S X"
 have B0:"\<forall>x \<in> ?B. \<exists>Ai \<in> A. x \<in>Ai"
   by blast
  have B1:"\<forall>x \<in> ?B. ?i \<le> x"
    by (simp add: assms has_inf_imp_eq_inf_inf has_inf_in_imp2)
  have B2:"?i \<in> lb_set ?B X"
    by (simp add: assms has_inf_imp_eq_inf_inf has_inf_in_imp1)
  have B3:"\<forall>l \<in> lb_set ?B X. l \<in> lb_set ?S X"
    using lb_un_lb_infs by blast
  have B4:"\<forall>l \<in> lb_set ?B X. l \<le> ?i"
    by (metis (no_types, lifting) assms has_inf_imp_eq_inf_inf inf_is_inf is_inf_in_imp1 is_max_iff)
  have B5:"is_inf ?i ?B X"
    using assms has_inf_imp_eq_inf_inf inf_is_inf by auto
   have B6:"has_inf ?B X \<and> ?i = Inf ?B X"
    using B5 has_inf_def has_inf_imp_eq_inf_inf has_max_def is_inf_in_imp1 by blast
  show ?thesis
  using B6 by blast
qed

end



context fixes f::"'b \<Rightarrow> 'a::order set" and
              I::"'b set" and 
              X::"'a::order set"
        assumes ne:"\<forall>i \<in> I. f i \<noteq> {}" and
                ex:"\<forall>i \<in> I. has_inf (f i) X"
begin

lemma lb_infs_lb_un_indexed:
  assumes A0:"u \<in> lb_set {s \<in> X. \<exists>i \<in> I. s = Inf (f i) X } X"
  shows "u \<in> lb_set (\<Union>(f`I)) X"
proof-
  have B0:"u \<in> X"
    using assms lb_set_mem_iff by blast
  have B1:"\<forall>i \<in> I. u \<le> Inf (f i) X "
     using assms ex has_inf_in_set lb_set_imp by blast
  have B2:"\<forall>x \<in>  (\<Union>(f`I)). u \<le> x"
  proof
    fix x assume A1:"x \<in>  (\<Union>(f`I))"
    obtain i where B10:"i \<in> I \<and> x \<in> (f i)"
      using A1 by blast
    have B11:"u \<le>  Inf (f i) X \<and>  Inf (f i) X \<le> x"
      by (simp add: B1 B10 ex has_inf_in_imp2)
    show "u \<le> x"
      using B11 order.trans by blast
  qed
  show ?thesis
    by (meson B0 B2 lb_set_elm)
qed

lemma lb_un_lb_infs_indexed:
  assumes A0:"u \<in> lb_set  (\<Union>(f`I)) X"
  shows "u \<in> lb_set {s \<in> X. \<exists>i \<in> I. s = Inf (f i) X } X"
proof-
  have B0:"u \<in> X"
    using assms lb_set_mem_iff by blast
  have B1:"\<forall>s \<in> {s \<in> X. \<exists>i \<in> I. s = Inf (f i) X }. u \<le> s"
  proof 
    fix s assume A1:"s \<in> {s \<in> X. \<exists>i \<in> I. s = Inf (f i) X }"
    obtain i where B2:"i \<in> I \<and> s = Inf (f i) X"
      using A1 by blast
    have B3:"\<forall>x \<in> (f i). u \<le> x"
      by (meson B2 UN_I assms lb_set_mem)
    show"u \<le> s"
      using B0 B2 B3 ex inf_is_inf is_inf_in_imp3 by blast
  qed
  show ?thesis
    using B0 B1 lb_set_elm by blast
qed

lemma has_inf_imp_eq_inf_inf_indexed:
  assumes "has_inf  (\<Union>(f`I)) X"
  shows "has_inf {s \<in> X. \<exists>i \<in> I. s = Inf (f i) X } X \<and> Inf {s \<in> X. \<exists>i \<in> I. s = Inf (f i) X } X = Inf  (\<Union>(f`I)) X"
proof-
  let ?S="{s \<in> X. \<exists>i \<in> I. s = Inf (f i) X }"
  let ?i="Inf  (\<Union>(f`I)) X"
  have B0:"\<forall>s \<in> ?S. ?i \<le> s"
    using assms has_inf_in_imp1 lb_set_imp lb_un_lb_infs_indexed by blast
  have B1:"?i \<in> lb_set ?S X"
    using assms has_inf_in_imp1 lb_un_lb_infs_indexed by blast
  have B2:"\<forall>u \<in> lb_set ?S X. u \<in> lb_set  (\<Union>(f`I)) X"
    using lb_infs_lb_un_indexed by blast
  have B3:"\<forall>u \<in> lb_set ?S X. u \<le> ?i"
    using B2 assms has_inf_in_imp1 is_max_iff by blast
  have B4:"is_inf ?i ?S X"
    by (simp add: B1 B3 assms has_inf_in_set is_inf_if1 is_max_if2)
  have B5:"has_inf ?S X  \<and> ?i = Inf ?S X"
    using B4 has_inf_def has_max_def is_inf_in_imp1 is_inf_inf_eq by blast
  show ?thesis
    using B5 by presburger
qed


lemma inf_inf_imp_has_inf_eq_indexed:
  assumes "has_inf {s \<in> X. \<exists>i \<in> I. s = Inf (f i) X } X"
  shows "has_inf  (\<Union>(f`I)) X \<and> Inf {s \<in> X. \<exists>i \<in> I. s = Inf (f i) X } X = Inf  (\<Union>(f`I)) X"
proof-
  let ?S="{s \<in> X. \<exists>i \<in> I. s = Inf (f i) X }"
  let ?i="Inf ?S X"
 have B0:"\<forall>x \<in>  (\<Union>(f`I)). \<exists>i \<in> I. x \<in> (f i)"
   by blast
  have B1:"\<forall>x \<in>  (\<Union>(f`I)). ?i \<le> x"
    using assms has_inf_in_imp1 lb_infs_lb_un_indexed lb_set_imp by blast
  have B2:"?i \<in> lb_set  (\<Union>(f`I)) X"
    using assms has_inf_in_imp1 lb_infs_lb_un_indexed by blast
  have B3:"\<forall>l \<in> lb_set  (\<Union>(f`I)) X. l \<in> lb_set ?S X"
    using lb_un_lb_infs_indexed by blast
  have B4:"\<forall>l \<in> lb_set  (\<Union>(f`I)) X. l \<le> ?i"
    using B3 assms has_inf_in_imp1 is_max_iff by blast
  have B5:"is_inf ?i  (\<Union>(f`I)) X"
    by (simp add: B2 B4 assms has_inf_in_set is_inf_if1 is_max_if2)
   have B6:"has_inf  (\<Union>(f`I)) X \<and> ?i = Inf  (\<Union>(f`I)) X"
    using B5 has_inf_def has_inf_imp_eq_inf_inf_indexed has_max_def is_inf_in_imp1 by blast
  show ?thesis
  using B6 by blast
qed

end



(*
definition fin_inf_cl_in::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow>  'a::order set" where
  "fin_inf_cl_in A X \<equiv> {x \<in> X. \<exists>F \<in> Fpow A. has_inf F X \<and> x = Inf F X}"

definition arb_sup_cl::"'a::order set \<Rightarrow> 'a::order set" where
  "arb_sup_cl A \<equiv> {x. \<exists>F \<in> Pow A. has_sup F \<and> x = SupUn F}"

definition arb_sup_cl_in::"'a::order set \<Rightarrow>'a::order set \<Rightarrow> 'a::order set" where
  "arb_sup_cl_in A X \<equiv> {x \<in> X. \<exists>F \<in> Pow A. has_sup_in F X \<and> x = SupIn F X}"

definition is_supin_closed::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow>  bool" where
  "is_supin_closed A X \<equiv> (\<forall>B \<in> Pow_ne A. has_sup_in B X \<longrightarrow> SupIn B X \<in> A)"

definition is_infin_closed::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow>  bool" where
  "is_infin_closed A X \<equiv> (\<forall>B \<in> Pow_ne A. has_inf_in B X \<longrightarrow> InfIn B X \<in> A)"

lemma up_closed_supin_closed:
  assumes A0:"is_upclosed_in A X"
  shows "is_supin_closed A X"
  unfolding is_supin_closed_def
proof
  fix B assume A1:"B \<in> Pow_ne A"
  show "has_sup_in B X \<longrightarrow> SupIn B X \<in> A"
  proof
    assume A2:"has_sup_in B X"
    have B0:"\<exists>x \<in> B. x \<in> A \<and> x \<le> SupIn B X"
      using A1 A2 has_sup_in_imp2 by fastforce
   show "SupIn B X \<in> A"
     using A2 B0 assms has_sup_in_in_set is_upclosed_in_def by blast
  qed
qed


lemma down_closed_infin_closed:
  assumes A0:"is_downclosed_in A X"
  shows "is_infin_closed A X"
  unfolding is_infin_closed_def
proof
  fix B assume A1: "B \<in> Pow_ne A"
  show "has_inf_in B X \<longrightarrow> InfIn B X \<in> A"
  proof
    assume A2: "has_inf_in B X"
    have B0: "\<exists>x \<in> B. x \<in> A \<and> InfIn B X \<le> x"
      using A1 A2 has_inf_in_imp2 by fastforce
    show "InfIn B X \<in> A"
      using A2 B0 assms has_inf_in_in_set is_downclosed_in_def by blast
  qed
qed

lemma sup_un_sets:
  "SupUn (A::'a set set) = \<Union>A"
  by (simp add: complete_lattice_sup_exists)

lemma has_sup_un_sets:
  "has_sup (A::'a set set)"
  by (metis UNIV_I bot.extremum complete_lattice_sup_is_sup has_min_iff has_sup_def is_min_imp_has_min is_sup_def ub_set_degenerate)

lemma arb_sup_cl_sets:
  "arb_sup_cl (A::'a set set) = {x. \<exists>F \<in> Pow A. x=\<Union> F }"
  apply(simp add:arb_sup_cl_def)
  by (simp add: has_sup_un_sets sup_un_sets)
  

lemma fin_inf_cl_imp0:
  "\<And>A x. x \<in>  fin_inf_cl A \<Longrightarrow> (\<exists>F \<in>  Fpow_ne A. has_inf F \<and> x = InfUn F)"
  using fin_inf_cl_def by blast

lemma fin_inf_cl_in_imp0:
  "\<And>A X x. x \<in>  fin_inf_cl_in A X \<Longrightarrow> (\<exists>F \<in>  Fpow A. has_inf_in F X \<and> x = InfIn F X)"
  using fin_inf_cl_in_def by blast

lemma arb_sup_cl_imp0:
  "\<And>A x. x \<in>  arb_sup_cl A \<Longrightarrow> (\<exists>F \<in>  Pow A. has_sup F \<and> x = SupUn F)"
  using arb_sup_cl_def by blast

lemma arb_sup_cl_in_imp0:
  "\<And>A X x. x \<in>  arb_sup_cl_in A X \<Longrightarrow> (\<exists>F \<in>  Pow A. has_sup_in F X \<and> x = SupIn F X)"
  using arb_sup_cl_in_def by blast

lemma fin_inf_cl_imp1:
  "\<And>A x. x \<in>  fin_inf_cl A \<Longrightarrow> (\<exists>F. F \<subseteq> A \<and> finite F \<and> F \<noteq> {} \<and> has_inf F \<and>  x = InfUn F)"
  by (metis fin_inf_cl_imp0 fpow_ne_imp)

lemma fin_inf_cl_in_imp1:
  "\<And>A X x. x \<in>  fin_inf_cl_in A X \<Longrightarrow> (\<exists>F. F \<subseteq> A \<and> finite F \<and> has_inf_in F X \<and>  x = InfIn F X)"
   by (metis DiffI fin_inf_cl_in_imp0 finite.emptyI fpow_ne_imp order_bot_class.bot_least singletonD)

lemma arb_sup_cl_imp1:
  "\<And>A x. x \<in>  arb_sup_cl A \<Longrightarrow> (\<exists>F. F \<subseteq> A  \<and> has_sup F \<and> x = SupUn F)"
  using arb_sup_cl_imp0 by auto

lemma arb_sup_cl_in_imp1:
  "\<And>A X x. x \<in>  arb_sup_cl_in A X \<Longrightarrow> (\<exists>F. F \<subseteq> A \<and> has_sup_in F X \<and>  x = SupIn F X)"
  by (meson PowD arb_sup_cl_in_imp0)

lemma arb_sup_cl_in_imp2:
  "\<And>A X x. x \<in>  arb_sup_cl_in A X \<Longrightarrow> x \<in> X"
  using arb_sup_cl_in_def by blast

lemma fin_inf_cl_if1:
  "\<And>A x.  (\<exists>F \<in>  Fpow_ne A. has_inf F \<and> x = InfUn F) \<Longrightarrow> x \<in> fin_inf_cl A"
  by (simp add: fin_inf_cl_def)

lemma fin_inf_cl_in_if1:
  "\<And>A X x.  (\<exists>F \<in>  Fpow A. has_inf_in F X \<and> x = InfIn F X) \<Longrightarrow> x \<in> fin_inf_cl_in A X"
  using fin_inf_cl_in_def has_inf_in_in_set by blast

lemma arb_sup_cl_if1:
  "\<And>A x.  (\<exists>F \<in>  Pow A. has_sup F \<and> x = SupUn F) \<Longrightarrow> x \<in> arb_sup_cl A"
  by (simp add: arb_sup_cl_def)

lemma arb_sup_cl_in_if1:
  "\<And>A X x.  (\<exists>F \<in> Pow A. has_sup_in F X \<and> x = SupIn F X) \<Longrightarrow> x \<in> arb_sup_cl_in A X"
  using arb_sup_cl_in_def has_sup_in_in_set by blast


lemma fin_inf_cl_mem_iff:
  "x \<in> fin_inf_cl A \<longleftrightarrow> (\<exists>F \<in>  Fpow_ne A. has_inf F \<and> x = InfUn F)"
  by (simp add: fin_inf_cl_def)

lemma fin_inf_cl_in_mem_iff:
  "x \<in> fin_inf_cl_in A X \<longleftrightarrow> (\<exists>F \<in>  Fpow A. has_inf_in F X \<and> x = InfIn F X)"
  using fin_inf_cl_in_if1 fin_inf_cl_in_imp0 by blast

lemma  arb_sup_cl_mem_iff:
  "x \<in> arb_sup_cl A \<longleftrightarrow> (\<exists>F \<in>  Pow A. has_sup F \<and> x = SupUn F)"
  by (simp add: arb_sup_cl_def)

lemma arb_sup_cl_in_mem_iff:
  "x \<in> arb_sup_cl_in A X \<longleftrightarrow> (\<exists>F \<in>  Pow A. has_sup_in F X \<and> x = SupIn F X)"
  using arb_sup_cl_in_if1 arb_sup_cl_in_imp0
  by metis


lemma fpow_ne_iso:
  "A \<subseteq> B \<Longrightarrow> Fpow_ne A \<subseteq> Fpow_ne B"
  by (simp add: Diff_mono Fpow_mono)

lemma fpow_iso:
  "A \<subseteq> B \<Longrightarrow> Fpow A \<subseteq> Fpow B"
  by (simp add: Diff_mono Fpow_mono)

lemma fpow_ne_finite_union:
  assumes A0:"EF \<in> Fpow_ne (Fpow_ne A)"
  shows "(\<Union>EF) \<in> Fpow_ne A"
  by (metis DiffD2 Pow_empty Pow_iff assms fpow_ne_equiv fpow_ne_union subset_eq)

lemma fpow_finite_union:
  assumes A0:"EF \<in> Fpow (Fpow A)"
  shows "(\<Union>EF) \<in> Fpow A"
  by (smt (verit, ccfv_threshold) Fpow_def Sup_least assms finite_Union mem_Collect_eq subset_eq)


lemma arb_sup_cl_extensive:
  "A \<subseteq> arb_sup_cl A"
proof
  fix a assume A0:"a \<in> A"
  have B0:"{a} \<in> Pow A \<and> has_sup {a} \<and> a = SupUn {a}"
    by (simp add: A0 has_sup_singleton sup_singleton)
  show "a \<in> arb_sup_cl A"
    using B0 arb_sup_cl_def by blast
qed

lemma fin_inf_cl_extensive:
  "A \<subseteq> fin_inf_cl A"
proof
  fix a assume A0:"a \<in> A"
  have B0:"{a} \<in> Fpow_ne A \<and> has_inf {a} \<and> a = InfUn {a}"
    by (metis A0 fpow_ne_singleton has_inf_singleton inf_singleton)
  show "a \<in> fin_inf_cl A"
    using B0 fin_inf_cl_def by blast
qed


lemma fin_inf_cl_in_range:
  "fin_inf_cl_in A X \<subseteq> X"
  by (simp add: fin_inf_cl_in_def)

lemma arb_sup_cl_in_range:
  "arb_sup_cl_in A X \<subseteq> X"
  by (simp add: arb_sup_cl_in_def)

lemma fin_inf_cl_in_extensive:
  "A \<inter> X \<subseteq> fin_inf_cl_in A X"
proof
  fix a assume A0:"a \<in> A \<inter> X"
  have B0:"{a} \<in> Fpow A \<and> has_inf_in {a} X \<and> a = InfIn {a} X"
    by (metis A0 IntD2 Int_commute fpow_singleton has_infin_singleton2 infin_singleton2)
  show "a \<in> fin_inf_cl_in A X"
    using B0 fin_inf_cl_in_if1 by blast
qed

lemma arb_sup_cl_in_extensive:
  "A \<inter> X \<subseteq> arb_sup_cl_in A X"
proof
  fix a assume A0:"a \<in> A \<inter> X"
  have B0:"{a} \<in> Pow A \<and> has_sup_in {a} X \<and> a = SupIn {a} X"
    by (metis A0 IntD1 IntD2 fpow_ne_equiv fpow_ne_singleton has_supin_singleton2 supin_singleton2)
  show "a \<in> arb_sup_cl_in A X"
    using B0 arb_sup_cl_in_if1 by blast
qed


lemma arb_sup_cl_iso:
  assumes "A \<subseteq> B"
  shows "arb_sup_cl A  \<subseteq> arb_sup_cl B"
proof
  fix a assume A0:"a \<in> arb_sup_cl A"
  obtain F where A1:"F \<in> Pow A \<and> has_sup F \<and> a = SupUn F"
    using A0 arb_sup_cl_imp0 by auto
  have B0:"F \<in> Pow B \<and> has_sup F \<and>  a = SupUn F"
    using A1 assms fpow_ne_iso by blast
  show "a \<in> arb_sup_cl B"
    using B0 arb_sup_cl_def by blast
qed

lemma fin_inf_cl_iso:
  assumes "A \<subseteq> B"
  shows "fin_inf_cl A  \<subseteq> fin_inf_cl B"
proof
  fix a assume A0:"a \<in> fin_inf_cl A"
  obtain F where A1:"F \<in> Fpow_ne A \<and> has_inf F \<and> a = InfUn F"
    using A0 fin_inf_cl_def by auto
  have B0:"F \<in> Fpow_ne B \<and> has_inf F \<and>  a = InfUn F"
    using A1 assms fpow_ne_iso by blast
  show "a \<in> fin_inf_cl B"
    using B0 fin_inf_cl_def by blast
qed

lemma fin_inf_in_cl_iso:
  assumes "A \<subseteq> B"
  shows "fin_inf_cl_in A X  \<subseteq> fin_inf_cl_in B X"
proof
  fix a assume A0:"a \<in> fin_inf_cl_in A X"
  obtain F where A1:"F \<in> Fpow A \<and> has_inf_in F X \<and> a = InfIn F X"
    using A0 fin_inf_cl_in_imp0 by blast
  have B0:"F \<in> Fpow B \<and> has_inf_in F X \<and>  a = InfIn F X"
    using A1 assms fpow_iso by blast
  show "a \<in> fin_inf_cl_in B X"
    using B0 fin_inf_cl_in_if1 by blast
qed

lemma arb_sup_cl_in_iso:
  assumes "A \<subseteq> B"
  shows "arb_sup_cl_in A X  \<subseteq> arb_sup_cl_in B X"
proof
  fix a assume A0:"a \<in> arb_sup_cl_in A X"
  obtain F where A1:"F \<in> Pow A \<and> has_sup_in F X \<and> a = SupIn F X"
    using A0 arb_sup_cl_in_imp0 by blast
  have B0:"F \<in> Pow B \<and> has_sup_in F X \<and>  a = SupIn F X"
    using A1 assms by blast
  show "a \<in> arb_sup_cl_in B X"
    using B0 arb_sup_cl_in_if1 has_sup_in_in_set by blast
qed





(*these got out of hand and are just FUBAR*)
lemma fin_inf_cl_idemp:
    "fin_inf_cl A = fin_inf_cl (fin_inf_cl A)"
proof-
  define C where "C=(fin_inf_cl A)"
  have L:"C \<subseteq> fin_inf_cl C"
    by (simp add: fin_inf_cl_extensive)
  have R:"fin_inf_cl C \<subseteq> C"
  proof
    fix x assume A0:"x \<in> fin_inf_cl C"
    obtain Fx where A1:"Fx \<in> Fpow_ne C \<and> has_inf Fx \<and> x = InfUn Fx"
      using A0 C_def fin_inf_cl_def by blast
    have B0:"\<forall>y. y \<in> Fx \<longrightarrow> (\<exists>Fy \<in> Fpow_ne A. has_inf Fy \<and>  y = InfUn Fy)"
      using A1 C_def fin_inf_cl_def fpow_ne_imp by blast
    (*define Fxy where "Fxy={Fy \<in> Fpow_ne A. has_inf Fy \<and> (\<exists>y \<in> Fx. y = InfUn Fy)}" something something injection*)
    define F where "F=(\<lambda>y. SOME Fy. Fy \<in> Fpow_ne A \<and> has_inf Fy \<and>  y= InfUn Fy)"
    define FFx where "FFx=F`Fx"
    have B1:"\<And>y. y \<in> Fx  \<longrightarrow>  has_inf (F y)" 
    proof
      fix y assume A2:"y \<in> Fx"
      obtain Fy where A3:"Fy \<in> Fpow_ne A \<and> has_inf Fy \<and>  y= InfUn Fy"
        by (meson A2 B0)
      show "has_inf (F y)"
        by (metis (mono_tags, lifting) A3 F_def someI_ex)
     qed
    have B2:"Fx = (InfUn`FFx)"
    proof-
      have B3:"Fx \<subseteq> InfUn`FFx"
      proof
        fix y assume A4:"y \<in> Fx"
        have B4:"(InfUn (F y) = y)"
          by (metis (mono_tags, lifting) A4 B0 F_def someI_ex)
        show "y \<in> (InfUn`FFx)"
          by (metis A4 B4 FFx_def imageI)
      qed
      have B4:"InfUn`FFx \<subseteq> Fx"
        by (metis A1 B3 FFx_def card_seteq dual_order.eq_iff finite_imageI fpow_ne_imp surj_card_le)
      show ?thesis
        using B3 B4 by blast
    qed
   define G where "G=\<Union>FFx"
    have B6:"has_inf (InfUn`FFx)"
      using A1 B2 by blast
    have B7:"InfUn Fx = InfUn(InfUn`FFx)"
      using B2 by blast
    have B8:"... = InfUn(G)"
      by (metis A1 B1 B6 FFx_def fpow_ne_equiv inf_comp_un_ind G_def)
    have B9:"\<And>y. y \<in> Fx  \<longrightarrow> (F y) \<in> Fpow_ne A"
      by (metis (mono_tags, lifting) B0 F_def someI)
    have B10:"\<forall>Fy \<in> FFx. Fy \<in> Fpow_ne A"
      using B9 FFx_def by auto
    have B11:"FFx \<in> Fpow_ne (Fpow_ne A)"
      by (metis A1 B10 FFx_def finite_imageI fpow_ne_equiv fpow_ne_if image_is_empty subsetI)
    define G where "G=\<Union>FFx"
    have B12:"G \<in> Fpow_ne A"
      using B11 G_def fpow_ne_finite_union by auto
    have B13:"has_inf G \<and> x = InfUn G"
      by (metis A1 B1 B6 B7 FFx_def G_def fpow_ne_equiv inf_comp_un_ind)
    show "x \<in> C"
      using B12 B13 C_def fin_inf_cl_if1 by blast
    qed
  show ?thesis
    using C_def L R by force
qed

lemma fin_inf_cl_in_idemp:
    "fin_inf_cl_in A X = fin_inf_cl_in (fin_inf_cl_in A X) X"
proof-
  define C where "C=(fin_inf_cl_in A X)"
  have L:"C \<subseteq> fin_inf_cl_in C X"
    by (metis C_def fin_inf_cl_in_extensive fin_inf_cl_in_range inf.orderE)
  have R:"fin_inf_cl_in C X \<subseteq> C"
  proof
    fix x assume A0:"x \<in> fin_inf_cl_in C X"
    obtain Fx where A1:"Fx \<in> Fpow C \<and> has_inf_in Fx X \<and> x = InfIn Fx X"
      using A0 fin_inf_cl_in_imp0 by blast
    have B0:"\<forall>y. y \<in> Fx \<longrightarrow> (\<exists>Fy \<in> Fpow A. has_inf_in Fy X \<and>  y = InfIn Fy X)"
      using A1 C_def fin_inf_cl_in_imp0 fpow_ne_imp by blast
    define F where "F=(\<lambda>y. SOME Fy. Fy \<in> Fpow A \<and> has_inf_in Fy X \<and>  y= InfIn Fy X)"
    define FFx where "FFx=F`Fx"
    have B1:"\<And>y. y \<in> Fx  \<longrightarrow>  has_inf_in (F y) X" 
    proof
      fix y assume A2:"y \<in> Fx"
      obtain Fy where A3:"Fy \<in> Fpow A \<and> has_inf_in Fy X \<and>  y= InfIn Fy X"
        by (meson A2 B0)
      show "has_inf_in (F y) X"
        by (metis (mono_tags, lifting) A3 F_def someI_ex)
     qed
    define InfX where "InfX \<equiv> (\<lambda>A. InfIn A X)"
    have B2:"Fx = (InfX`FFx)"
    proof-
      have B3:"Fx \<subseteq> InfX`FFx"
      proof
        fix y assume A4:"y \<in> Fx"
        have B4:"(InfIn (F y) X = y)"
        apply(simp add:F_def)
          by (smt (verit, best) A4 B0 someI_ex)
        show "y \<in> (InfX`FFx)"
          by (metis A4 B4 FFx_def InfX_def image_eqI)
      qed
      have B4:"InfX`FFx \<subseteq> Fx"
        by (smt (verit, del_insts) A1 B3 CollectD FFx_def Fpow_def card_image_le card_seteq finite_imageI order.trans)
      show ?thesis
        using B3 B4 by blast
    qed
   define G where "G=\<Union>FFx"
    have B6:"has_inf_in (InfX`FFx) X"
      using A1 B2 by blast
    have B7:"InfIn Fx X  = InfX(InfX`FFx)"
      using B2 InfX_def by blast
    have B8:"... = InfX G"
      apply(simp add:InfX_def)
      by (metis B1 B6 FFx_def G_def InfX_def Union_empty image_cong image_empty inf_in_comp_un_ind)
    have B9:"\<And>y. y \<in> Fx  \<longrightarrow> (F y) \<in> Fpow A"
      by (smt (verit, ccfv_threshold) B0 F_def someI_ex)
    have B10:"\<forall>Fy \<in> FFx. Fy \<in> Fpow A"
      using B9 FFx_def by auto
    have B11:"FFx \<in> Fpow (Fpow A)"
      by (metis (no_types, lifting) A1 B10 FFx_def Fpow_def finite_imageI mem_Collect_eq subsetI)
    have B12:"G \<in> Fpow A"
      by (simp add: B11 G_def fpow_finite_union)
    have B13:"has_inf_in G X \<and> x = InfIn G X"
      by (metis A1 B1 B2 FFx_def G_def InfX_def Union_empty image_cong image_empty inf_in_comp_un_ind)
    show "x \<in> C"
      using B12 B13 C_def fin_inf_cl_in_if1 by blast
    qed
  show ?thesis
    using C_def L R by force
qed




lemma arb_sup_cl_idemp:
    "arb_sup_cl A = arb_sup_cl (arb_sup_cl A)"
proof-
  define C where "C=(arb_sup_cl A)"
  have L:"C \<subseteq> arb_sup_cl C"
    by (simp add: arb_sup_cl_extensive)
  have R:"arb_sup_cl C \<subseteq> C"
  proof
    fix x assume A0:"x \<in> arb_sup_cl C"
    obtain Fx where A1:"Fx \<in> Pow C \<and> has_sup Fx \<and> x = SupUn Fx"
      using A0 arb_sup_cl_imp0 by auto
    have B0:"\<forall>y. y \<in> Fx \<longrightarrow> (\<exists>Fy \<in> Pow A. has_sup Fy \<and>  y = SupUn Fy)"
      using A1 C_def arb_sup_cl_def by blast
    define F where "F=(\<lambda>y. SOME Fy. Fy \<in> Pow A \<and> has_sup Fy \<and>  y= SupUn Fy)"
    have B00:"\<And>x1 x2. x1 \<in> Fx \<and> x2 \<in> Fx  \<and> (SupUn \<circ> F) x1 = (SupUn \<circ> F) x2 \<longrightarrow> x1 =x2"
    proof
      fix x1 x2 assume B00A0:"x1 \<in> Fx \<and> x2 \<in> Fx  \<and> (SupUn \<circ> F) x1 = (SupUn \<circ> F) x2" 
      have B00B0:"(F x1) \<in> Pow A \<and> has_sup (F x1) \<and>  x1 = SupUn (F x1)"
        by (metis (mono_tags, lifting) B0 B00A0 F_def someI)
      have B00B1:"(F x2) \<in> Pow A \<and> has_sup (F x2) \<and>  x2 = SupUn (F x2)"
        by (metis (mono_tags, lifting) B0 B00A0 F_def someI)
      have B00B2:"SupUn (F x1) = SupUn (F x2)"
        using B00A0 by fastforce
      show "x1 = x2"
        using B00B0 B00B1 B00B2 by presburger
    qed
    define FFx where "FFx=F`Fx"
    have B1:"\<And>y. y \<in> Fx  \<longrightarrow>  has_sup (F y)" 
    proof
      fix y assume A2:"y \<in> Fx"
      obtain Fy where A3:"Fy \<in> Pow A \<and> has_sup Fy \<and>  y= SupUn Fy"
        by (meson A2 B0)
      show "has_sup (F y)"
        by (metis (mono_tags, lifting) A3 F_def someI_ex)
     qed
    have B2:"Fx = (SupUn`FFx)"
    proof-
      have B3:"Fx \<subseteq> SupUn`FFx"
      proof
        fix y assume A4:"y \<in> Fx"
        have B4:"(SupUn (F y) = y)"
          by (metis (mono_tags, lifting) A4 B0 F_def someI_ex)
        show "y \<in> (SupUn`FFx)"
          by (metis A4 B4 FFx_def imageI)
      qed
      have B4:"SupUn`FFx \<subseteq> Fx"
      proof
        fix z assume B4A0:"z \<in> SupUn`FFx"
        obtain w where B4A1:"w \<in> Fx \<and> z = (SupUn \<circ> F) w "
          using B4A0 FFx_def by auto
        obtain Fw where B4A2:"Fw = (F w) \<and> w = SupUn Fw \<and> Fw \<in> Pow A \<and> has_sup Fw"
          by (metis (mono_tags, lifting) B0 B4A1 F_def someI_ex)
        have B4B0:"SupUn Fw = SupUn (F w)"
          using B4A2 by force
        have B4B1:"... =  (SupUn \<circ> F) w "
          by simp
        have B4B2:"... = z"
          using B4A1 by force
        show "z \<in> Fx"
          using B4A1 B4A2 by fastforce
      qed
      show ?thesis
        using B3 B4 by blast
    qed
   define G where "G=\<Union>FFx"
    have B6:"has_sup (SupUn`FFx)"
      using A1 B2 by blast
    have B7:"SupUn Fx = SupUn(SupUn`FFx)"
      using B2 by blast
    have B8:"... = SupUn(G)"
      by (metis B1 B6 FFx_def G_def Union_empty image_empty sup_comp_un_ind)
    have B9:"\<And>y. y \<in> Fx  \<longrightarrow> (F y) \<in> Pow A"
      by (metis (mono_tags, lifting) B0 F_def someI)
    have B10:"\<forall>Fy \<in> FFx. Fy \<in> Pow A"
      using B9 FFx_def by auto
    have B11:"FFx \<in> Pow (Pow A)"
      using B10 by blast
    have B12:"G \<in> Pow A"
      using B11 G_def fpow_ne_finite_union by auto
    have B13:"has_sup G \<and> x = SupUn G"
      by (metis A1 B1 B2 FFx_def G_def Sup_empty image_empty sup_comp_un_ind)
    show "x \<in> C"
      using B12 B13 C_def arb_sup_cl_def by blast
    qed
  show ?thesis
    using C_def L R by force
qed

lemma f_inf_cl_idemp2:
  "\<forall>A. fin_inf_cl A = fin_inf_cl (fin_inf_cl A)"
  using fin_inf_cl_idemp by blast

lemma f_inf_cl_in_idemp2:
  "\<forall>A. fin_inf_cl_in A X = fin_inf_cl_in (fin_inf_cl_in A X) X"
  using fin_inf_cl_in_idemp by blast

lemma arb_sup_cl_idemp2:
  "\<forall>A. arb_sup_cl A = arb_sup_cl (arb_sup_cl A)"
  using arb_sup_cl_idemp by blast


lemma arb_sup_cl_idemp3:
  "\<And>E. E \<subseteq> arb_sup_cl (A::'a set set) \<longrightarrow> \<Union>E \<in>  arb_sup_cl A "
proof
   fix E assume A0:"E \<subseteq> arb_sup_cl (A::'a set set)" 
   show" \<Union>E \<in>  arb_sup_cl A"
   by (metis A0 PowI arb_sup_cl_idemp arb_sup_cl_if1 complete_lattice_sup_exists has_sup_un_sets)
qed



lemma fin_inf_cl_is_cl:
  "is_closure fin_inf_cl"
  unfolding is_closure_def
  apply(simp add: is_extensive_def fin_inf_cl_extensive is_isotone_def fin_inf_cl_iso)
  apply(simp add:is_idempotent_def)
  using f_inf_cl_idemp2 by blast


lemma arb_sup_cl_is_cl:
  "is_closure arb_sup_cl"
  unfolding is_closure_def
  apply(simp add: is_extensive_def arb_sup_cl_extensive is_isotone_def arb_sup_cl_iso)
  apply(simp add:is_idempotent_def)
  using arb_sup_cl_idemp2 by blast

lemma fin_inf_cl_in_top:
  "X \<in> fin_inf_cl_in A (Pow X)"
proof-
  have B0:"{} \<in> Fpow A"
    by (simp add: empty_in_Fpow)
  have B1:"(InfIn {} (Pow X)) = X"
    by (simp add: empty_inter_is_carrier)
   have B2:"has_inf_in {} (Pow X)"
     by (metis Pow_top Sup_upper Union_Pow_eq has_inf_in_def has_max_iff lb_set_in_degenerate)
    show ?thesis
      using B0 B1 B2 fin_inf_cl_in_if1 by blast
qed

lemma comp_extensive:
  fixes f1 f2::"'a::order \<Rightarrow> 'a::order" 
  assumes "is_extensive f1 \<and> is_extensive f2"
  shows " is_extensive (f1 \<circ> f2)"
  by (metis assms comp_apply is_extensive_def order_trans)

lemma comp_isotone:
  fixes f1 f2::"'a::order \<Rightarrow> 'a::order" 
  assumes "is_isotone f1 \<and> is_isotone f2"
  shows " is_isotone (f1 \<circ> f2)"
  by (metis assms comp_apply is_isotone_def)

*)

end