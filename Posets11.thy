theory Posets11
  imports Main
begin
hide_const(open) List.list.Nil
no_notation List.list.Nil ("[]")  
no_notation Cons (infixr "#" 65) 
hide_type list
hide_const rev
hide_const top
declare [[show_consts,show_sorts,show_types, show_results]]

section Bounds
subsection Upper
subsubsection UbPredicate

definition ub::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> bool" (infix "ub" 50) where 
   "x ub  A \<equiv> (\<forall>a. a \<in> A \<longrightarrow> a \<le> x)"

lemma ubI: 
  "(\<And>a. a \<in> A \<Longrightarrow> a \<le> x) \<Longrightarrow> x ub A" 
  by (simp add:ub_def)

lemma ubD:
   "\<lbrakk>x ub A;  a \<in> A\<rbrakk>  \<Longrightarrow> a \<le> x "
    by (simp add:ub_def)

lemma ub_ant2:
  "\<lbrakk>A \<subseteq> B; x ub B\<rbrakk> \<Longrightarrow> x ub A"
   by (simp add:ub_def subsetD)

lemma ub_iso1:
  "\<lbrakk>x \<le> y; x ub A\<rbrakk> \<Longrightarrow> y ub A" 
   apply(intro ubI; drule ubD) 
   by(simp)+

lemma ub_empty:
  "x ub {}"
  by (simp add: ub_def)

lemma ub_singleton:
  "x ub {x}"
  by (simp add: ub_def)

lemma ub_insert:
  "\<lbrakk>c ub F; c \<ge> x\<rbrakk> \<Longrightarrow> c ub (insert x F)"
  by (simp add: ub_def)

lemma ub_binary:
  "a \<le> b \<longleftrightarrow> b ub {a, b}"
  by (simp add: ub_def)

lemma ub_double:
  "c ub {a, b} \<longleftrightarrow> c \<ge> a \<and> c \<ge> b"
  by (metis insert_iff ubD ubI ub_singleton)

lemma ub_union:
  "\<lbrakk>x ub A; x ub B\<rbrakk> \<Longrightarrow> x ub A \<union> B"
  by (simp add: ub_def)


subsubsection UpperBoundsSet

definition Upper_Bounds::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "Upper_Bounds X A \<equiv> {b \<in> X. b ub A}"

lemma Upper_Bounds_mem_iff:
  "b \<in> Upper_Bounds X A \<longleftrightarrow> (b \<in> X \<and> b ub A)" 
   by(simp add: Upper_Bounds_def)

lemma Upper_Bounds_mem_iff2:
  "b \<in> Upper_Bounds X A \<longleftrightarrow> (b \<in> X \<and> (\<forall>a. a \<in> A \<longrightarrow>  a \<le> b))"
  by (simp add: Upper_Bounds_mem_iff ub_def)

lemma Upper_BoundsI:
  "\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> a \<le> b); b \<in> X\<rbrakk> \<Longrightarrow> b \<in> Upper_Bounds X A"
   by(simp add: Upper_Bounds_def ubI)

lemma Upper_BoundsD1:
  "\<lbrakk>b \<in> Upper_Bounds X A; x \<in> A\<rbrakk> \<Longrightarrow> x \<le> b"
  by (simp add: Upper_Bounds_mem_iff ub_def)  

lemma Upper_BoundsD2:
  "\<lbrakk>b \<in> Upper_Bounds X A\<rbrakk> \<Longrightarrow> b \<in> X"
   by(simp add: Upper_Bounds_def)

lemma Upper_BoundsD3:
  "b \<in> Upper_Bounds X A \<Longrightarrow> b ub A"
  by (simp add: Upper_Bounds_mem_iff)

lemma Upper_BoundsD4:
  "\<lbrakk>b \<in> Upper_Bounds X A; x \<in> X; b \<le> x \<rbrakk> \<Longrightarrow> x \<in> Upper_Bounds X A"
  by (simp add: Upper_Bounds_mem_iff ub_iso1)

lemma Upper_Bounds_sub:
  "Upper_Bounds X A \<subseteq> X"
   by(simp add: Upper_Bounds_def)

lemma Upper_Bounds_ant1:
  "A \<subseteq> B \<Longrightarrow> Upper_Bounds X B \<subseteq> Upper_Bounds X A"
  by (simp add: Upper_Bounds_mem_iff subset_iff ub_ant2) 

lemma Upper_Bounds_iso2:
  "Y \<subseteq> X \<Longrightarrow> Upper_Bounds Y A \<subseteq> Upper_Bounds X A" 
  by (simp add:subset_iff Upper_Bounds_def)

lemma Upper_Bounds_iso2b:
  "\<lbrakk>Y \<subseteq> X; x \<in> Upper_Bounds Y A \<rbrakk> \<Longrightarrow> x \<in> Upper_Bounds X A"
  by (simp add: Upper_Bounds_mem_iff in_mono)

lemma Upper_Bounds_empty:
  "Upper_Bounds X {} = X"
   by(simp add: set_eq_iff Upper_Bounds_mem_iff ub_def)

lemma Upper_Bounds_singleton:
  "x \<in> X \<Longrightarrow> x \<in> Upper_Bounds X {x}"
  by (simp add: Upper_Bounds_def ub_singleton)

lemma Upper_Bounds_singleton2:
  "\<lbrakk>x \<in> X; a \<le> x \<rbrakk> \<Longrightarrow>  x \<in> Upper_Bounds X {a}"
  by (simp add: Upper_Bounds_mem_iff ub_iso1 ub_singleton)

lemma ub_single_D2:
  "x \<in> Upper_Bounds X {a}\<Longrightarrow> a \<le> x"
  by (simp add: Upper_BoundsD1)

lemma ubd_mem1:
  "\<lbrakk>A \<subseteq> B; x \<in> Upper_Bounds X B\<rbrakk> \<Longrightarrow> x \<in>  Upper_Bounds X A"
  by (simp add: Upper_Bounds_mem_iff ub_ant2)

lemma ubd_mem2:
  "x \<in> X \<Longrightarrow> x \<in> Upper_Bounds X {}"
  by (simp add: Upper_Bounds_empty)

lemma ubd_mem_insert:
  "\<lbrakk>c \<in> Upper_Bounds X F; c \<ge> x\<rbrakk> \<Longrightarrow> c \<in> Upper_Bounds X (insert x F)"
  by (simp add: Upper_Bounds_mem_iff ub_insert)

lemma ubd_mem_binary:
  "\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> a \<le> b \<longleftrightarrow> b \<in> Upper_Bounds X {a, b}"
  by (simp add: Upper_Bounds_mem_iff ub_binary)

lemma ubd_mem_double:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> c \<in> Upper_Bounds X {a, b} \<longleftrightarrow> c \<ge> a \<and> c \<ge> b"
  by (simp add: Upper_Bounds_mem_iff ub_double)

lemma ubd_mem_union:
  "\<lbrakk>x \<in> Upper_Bounds X A; x \<in> Upper_Bounds X B\<rbrakk> \<Longrightarrow> x \<in> Upper_Bounds X (A \<union> B)"
  by (simp add: Upper_Bounds_mem_iff ub_union)

lemma ne_subset_ne:
  "A \<subseteq> B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> B \<noteq> {}"
  by blast

lemma upbd_neD1:
  "Upper_Bounds X A \<noteq> {} \<Longrightarrow> X \<noteq> {}"
  using Upper_Bounds_sub by blast

lemma upbd_neE1:
  "Upper_Bounds X A \<noteq> {} \<Longrightarrow> a \<in> A \<Longrightarrow> (\<exists>x. x \<in> X \<and> a \<le> x)"
  using Upper_BoundsD1 Upper_Bounds_sub by blast

lemma upbd_neE2:
  "Upper_Bounds X A \<noteq> {} \<Longrightarrow> (\<exists>x \<in> X. x ub A)"
  using Upper_Bounds_def by blast

lemma upbd_neE3:
  "Upper_Bounds X {a} \<noteq> {} \<Longrightarrow> (\<exists>x \<in> X. a \<le> x)"
  using upbd_neE1 by auto


definition lb::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> bool" (infix "lb" 50) where 
   "x lb  A \<equiv> (\<forall>a. a \<in> A \<longrightarrow> a \<ge> x)"

subsection Lower
subsubsection LbPredicate

lemma lbI:
  "(\<And>a. a \<in> A \<Longrightarrow> a \<ge> x) \<Longrightarrow> x lb A" 
  by (simp add: lb_def)

lemma lbD:
  "\<lbrakk>x lb A; a \<in> A\<rbrakk> \<Longrightarrow> a \<ge> x"
  by (simp add: lb_def)

lemma lb_ant2:
  "\<lbrakk>A \<subseteq> B; x lb B\<rbrakk> \<Longrightarrow> x lb A"
   by (simp add:lb_def subsetD)

lemma lb_iso1:
  "\<lbrakk>y \<le> x; x lb A\<rbrakk> \<Longrightarrow> y lb A" 
   apply(intro lbI; drule lbD) 
   by(simp)+

lemma lb_empty:
  "x lb {}"
  by (simp add: lb_def)

lemma lb_singleton:
  "x lb {x}"
  by (simp add: lb_def)

lemma lb_insert:
  "\<lbrakk>c lb F; c \<le> x\<rbrakk> \<Longrightarrow> c lb (insert x F)"
  by (simp add: lb_def)

lemma lb_binary:
  "a \<le> b \<longleftrightarrow> a lb {a, b}"
  by (simp add: lb_def)

lemma lb_double:
  "c lb {a, b} \<longleftrightarrow> c \<le> a \<and> c \<le> b"
  by (metis insert_iff lbD lbI lb_singleton)

lemma lb_union:
  "\<lbrakk>x lb A; x lb B\<rbrakk> \<Longrightarrow> x lb A \<union> B"
  by (simp add: lb_def)

subsubsection LowerBounds

definition Lower_Bounds::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "Lower_Bounds X A \<equiv> {b \<in> X. b lb A}"

lemma Lower_Bounds_mem_iff:
  "b \<in> Lower_Bounds X A \<longleftrightarrow> (b \<in> X \<and> b lb A)" 
   by(simp add: Lower_Bounds_def)

lemma Lower_Bounds_mem_iff2:
  "b \<in> Lower_Bounds X A \<longleftrightarrow> (b \<in> X \<and> (\<forall>a. a \<in> A \<longrightarrow>  b \<le> a))"
  by (simp add: Lower_Bounds_mem_iff lb_def)

lemma Lower_BoundsI:
  "\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> b \<le> a); b \<in> X\<rbrakk> \<Longrightarrow> b \<in> Lower_Bounds X A"
   by(simp add: Lower_Bounds_def lbI)

lemma Lower_BoundsD1:
  "\<lbrakk>b \<in> Lower_Bounds X A; x \<in> A\<rbrakk> \<Longrightarrow> b \<le> x"
  by (simp add: Lower_Bounds_mem_iff lb_def)  

lemma Lower_BoundsD2:
  "\<lbrakk>b \<in> Lower_Bounds X A\<rbrakk> \<Longrightarrow> b \<in> X"
   by(simp add: Lower_Bounds_def)

lemma Lower_BoundsD3:
  "b \<in> Lower_Bounds X A \<Longrightarrow> b lb A"
  by (simp add: Lower_Bounds_mem_iff)

lemma Lower_BoundsD4:
  "\<lbrakk>b \<in> Lower_Bounds X A; x \<in> X; x \<le> b\<rbrakk> \<Longrightarrow> x \<in> Lower_Bounds X A"
  by (simp add: Lower_Bounds_mem_iff lb_iso1)

lemma Lower_Bounds_sub:
  "Lower_Bounds X A \<subseteq> X"
   by(simp add: Lower_Bounds_def)

lemma Lower_Bounds_ant1:
  "A \<subseteq> B \<Longrightarrow> Lower_Bounds X B \<subseteq> Lower_Bounds X A"
  by (simp add: Lower_Bounds_mem_iff lb_ant2 subset_iff) 

lemma Lower_Bounds_iso2:
  "Y \<subseteq> X \<Longrightarrow> Lower_Bounds Y A \<subseteq> Lower_Bounds X A" 
  by (simp add:subset_iff Lower_Bounds_def)

lemma Lower_Bounds_iso2b:
  "\<lbrakk>Y \<subseteq> X; x \<in> Lower_Bounds Y A \<rbrakk> \<Longrightarrow> x \<in> Lower_Bounds X A"
  by (simp add: Lower_Bounds_mem_iff in_mono)

lemma Lower_Bounds_empty:
  "Lower_Bounds X {} = X"
   by(simp add: set_eq_iff Lower_Bounds_mem_iff lb_def)

lemma Lower_Bounds_singleton:
  "x \<in> X \<Longrightarrow> x \<in> Lower_Bounds X {x}"
  by (simp add: Lower_Bounds_def lb_singleton)


lemma lbd_mem1:
  "\<lbrakk>A \<subseteq> B; x \<in> Lower_Bounds X B\<rbrakk> \<Longrightarrow> x \<in>  Lower_Bounds X A"
  by (simp add: Lower_Bounds_mem_iff lb_ant2)

lemma lbd_mem2:
  "x \<in> X \<Longrightarrow> x \<in> Lower_Bounds X {}"
  by (simp add: Lower_Bounds_empty)

lemma lbd_mem_insert:
  "\<lbrakk>c \<in> Lower_Bounds X F; c \<le> x\<rbrakk> \<Longrightarrow> c \<in> Lower_Bounds X (insert x F)"
  by (simp add: Lower_Bounds_mem_iff lb_insert)

lemma lbd_mem_binary:
  "\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> a \<le> b \<longleftrightarrow> a \<in> Lower_Bounds X {a, b}"
  by (simp add: Lower_Bounds_mem_iff lb_binary)

lemma lbd_mem_double:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> c \<in> Lower_Bounds X {a, b} \<longleftrightarrow> c \<le> a \<and> c \<le> b"
  by (simp add: Lower_Bounds_mem_iff lb_double)

lemma lbd_mem_union:
  "\<lbrakk>x \<in> Lower_Bounds X A; x \<in> Lower_Bounds X B\<rbrakk> \<Longrightarrow> x \<in> Lower_Bounds X (A \<union> B)"
  by (simp add: Lower_Bounds_mem_iff lb_union)


subsection LowerUpper

lemma Lower_Upper_comp1:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> Lower_Bounds X (Upper_Bounds X A)"
  by (simp add: Lower_BoundsI Upper_BoundsD1 subset_iff) 

lemma Upper_Lower_comp1:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> Upper_Bounds X (Lower_Bounds X A)"
  by (simp add: Lower_BoundsD1 Upper_BoundsI subset_iff)

lemma Lower_Upper_comp2:
  "A \<subseteq> B \<Longrightarrow> Lower_Bounds X (Upper_Bounds X A) \<subseteq> Lower_Bounds X (Upper_Bounds X B)"
  by (simp add: Lower_Bounds_ant1 Upper_Bounds_ant1)

lemma Upper_Lower_comp2:
  "A \<subseteq> B  \<Longrightarrow> Upper_Bounds X (Lower_Bounds X A) \<subseteq> Upper_Bounds X (Lower_Bounds X B)"
  by (simp add: Lower_Bounds_ant1 Upper_Bounds_ant1)

lemma Lower_Upper_comp3:
  "Lower_Bounds X (Upper_Bounds X A) = Lower_Bounds X (Upper_Bounds X (Lower_Bounds X (Upper_Bounds X A)))"
  by (simp add: Lower_Upper_comp1 Lower_Bounds_ant1 Lower_Bounds_sub Upper_Lower_comp1 Upper_Bounds_sub order_antisym)

lemma Upper_Lower_comp3:
  "Upper_Bounds X (Lower_Bounds X A) = Upper_Bounds X (Lower_Bounds X (Upper_Bounds X (Lower_Bounds X A)))"
  by (simp add: Lower_Upper_comp1 Lower_Bounds_sub Upper_Lower_comp1 Upper_Bounds_ant1 Upper_Bounds_sub order_antisym)

section GreatestLeast
subsection Greatest
subsubsection Predicate

definition is_greatest::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "is_greatest A m \<equiv> m \<in> Upper_Bounds A A"

lemma greatestI1:
  "m \<in> Upper_Bounds A A \<Longrightarrow> is_greatest A m" 
  by (simp add: is_greatest_def)

lemma greatestI2:
  "\<lbrakk>m ub A; m \<in> A\<rbrakk> \<Longrightarrow> is_greatest A m"
  by (simp add: Upper_Bounds_mem_iff is_greatest_def)

lemma greatestI3:
  "\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> a \<le> m); m \<in> A\<rbrakk> \<Longrightarrow> is_greatest A m"
  by (simp add: ubI greatestI2)

lemma greatestI4:
  "\<lbrakk>m \<in> Upper_Bounds X A; A \<subseteq> X; m \<in> A\<rbrakk> \<Longrightarrow> is_greatest A m"
  by (simp add: Upper_BoundsD3 greatestI2)

lemma greatestI5:
  "(\<And>X. A \<subseteq> X \<Longrightarrow> m \<in> Upper_Bounds X A) \<Longrightarrow> is_greatest A m"
  by (simp add: is_greatest_def)

lemma greatestD0:
  "is_greatest A m \<Longrightarrow>m \<in> Upper_Bounds A A"
  by (simp add: is_greatest_def)

lemma greatestD1:
  "is_greatest A m \<Longrightarrow> (m \<in> A \<and> m ub A)"
  by (simp add: Upper_Bounds_mem_iff is_greatest_def)

lemma greatestD11:
  "is_greatest A m \<Longrightarrow> m \<in> A"
  by (simp add: greatestD1)

lemma greatestD12:
  "is_greatest A m \<Longrightarrow> m ub A"
  by (simp add: greatestD1)

lemma greatestD2:
  "\<lbrakk>is_greatest A m; a \<in> A\<rbrakk> \<Longrightarrow> a \<le> m " 
  by (simp add: ubD[of "m" "A" "a"] greatestD1[of "A" "m"])

lemma greatestD3:
  "\<lbrakk>A \<subseteq> X; is_greatest A m\<rbrakk>  \<Longrightarrow> m \<in> Upper_Bounds X A"
  by (simp add: Upper_Bounds_iso2b is_greatest_def)

lemma greatest_iff:
  "is_greatest A m \<longleftrightarrow> (m \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> a \<le> m))"
  by (simp add: Upper_Bounds_mem_iff is_greatest_def ub_def)

lemma greatest_unique:
  "is_greatest A m1 \<Longrightarrow> is_greatest A m2 \<Longrightarrow> m1 =m2"
  by (simp add: greatest_iff order_antisym)

lemma is_greatest_iso2:
  "A \<subseteq> B \<Longrightarrow> is_greatest A ma \<Longrightarrow> is_greatest B mb \<Longrightarrow> ma \<le> mb"
  using greatestD11 greatestD2 by blast


lemma greatest_ne:
  "is_greatest A m \<Longrightarrow> A \<noteq> {}"
  using greatestD11 by auto

lemma greatest_ne2:
  "(\<exists>m. is_greatest A m) \<Longrightarrow> A \<noteq> {}"
  using greatestD11 by blast

lemma greatest_singleton:
  "is_greatest {x} x"
  by (simp add: greatestI2 ub_singleton)

lemma singleton_ex_greatest:
  "\<exists>m. is_greatest {x} m"
  using greatest_singleton by blast

lemma greatest_pair:
  "is_greatest {a, b} a \<longleftrightarrow> b \<le> a"
  by (simp add: greatest_iff)

lemma greatest_double1:
  "is_greatest {a, b} c \<Longrightarrow> c = a \<or> c = b"
  by (simp add: greatest_iff)

lemma greatest_insert1:
  "x ub A \<Longrightarrow> is_greatest (insert x A) x"
  by (simp add: greatestI2 ub_insert)

lemma greatest_insert2:
  "is_greatest A m \<Longrightarrow> x \<le> m \<Longrightarrow> is_greatest (insert x A) m"
  by (simp add: greatestD11 greatestI2 greatestD12 ub_insert)

lemma greatest_insert3:
  "is_greatest A m \<Longrightarrow> m \<le> x \<Longrightarrow> is_greatest (insert x A) x"
  by (simp add: greatest_insert1 greatestD12 ub_iso1)

lemma greatest_insert4:
  "is_greatest A m \<Longrightarrow> x < m \<Longrightarrow> is_greatest (insert x A) m"
  by (simp add: greatest_insert2)

lemma greatest_insert5:
  "is_greatest A m \<Longrightarrow> m < x \<Longrightarrow> is_greatest (insert x A) x"
  by (simp add: greatest_insert3)

lemma greatest_finite_linear:
  assumes A0:"finite A" and A1:"A \<noteq> {}" and A3:"(\<And>a b. \<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> (a \<le> b) \<or> (b \<le> a))"
  shows "\<exists>m. is_greatest A m"
  unfolding atomize_conj
  using assms
proof(induction A rule:finite_ne_induct)
  case (singleton x)
  then show ?case
    by (simp add: singleton_ex_greatest)
next
  case (insert x F)
  obtain m where B0:"is_greatest F m"
    using insert.IH insert.prems by blast
  then show ?case 
  proof(cases "x \<le> m")
    case True
    then show ?thesis
      using B0 greatest_insert2 by blast
  next
    case False
    have B1:"x > m"
      by (meson B0 False greatestD11 insert.prems insert_iff less_le_not_le)
    then show ?thesis
      using B0 greatest_insert5 by auto
  qed
qed

subsubsection Operator

definition Greatest::"'a::order set \<Rightarrow> 'a::order" where
  "Greatest A \<equiv> (THE m. is_greatest A m)"

lemma greatest_equality:
  "\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> a \<le> m); m \<in> A\<rbrakk> \<Longrightarrow> Greatest A = m" 
  apply(simp add: Greatest_def) 
    apply(rule the_equality)
  by (simp add: greatest_iff order_antisym)+

lemma greatest_equality2:
  "is_greatest A m \<Longrightarrow> Greatest A = m"
  by (simp add: greatest_equality greatest_iff)

lemma greatest_equality3:
  "m \<in> Upper_Bounds A A \<Longrightarrow> Greatest A = m"
  by (simp add: greatest_equality2 is_greatest_def)

lemma lb_single_least1:
  "x \<in> X \<Longrightarrow> is_greatest (Lower_Bounds X {x}) x"
  by (simp add: Lower_BoundsD1 Lower_Bounds_singleton greatestI3)

lemma lb_single_least2:
  "x \<in> X \<Longrightarrow> Greatest (Lower_Bounds X {x}) = x"
  by (simp add: greatest_equality2 lb_single_least1)

lemma greatest_exD0:
  "(\<exists>m. is_greatest A m) \<Longrightarrow> A \<noteq> {}"
  using greatest_ne by blast 

lemma greatest_exD1:
  "(\<exists>m. is_greatest A m) \<Longrightarrow> Greatest A \<in> A"
  using greatestD11 greatest_equality2 by auto

lemma greatest_exD2:
  "(\<exists>m. is_greatest A m) \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> (Greatest A))"
  using greatestD2 greatest_equality2 by blast

lemma greatest_exD3:
  "(\<exists>m. is_greatest A m) \<Longrightarrow> (Greatest A) \<in> Upper_Bounds A A"
  using greatest_equality2 is_greatest_def by blast

lemma greatest_exD4:
  "(\<exists>m. is_greatest A m) \<Longrightarrow>  Greatest A ub A"
  using greatestD1 greatest_equality2 by blast

lemma greatest_exD5:
  "\<lbrakk>A \<subseteq> B; (\<exists>m. is_greatest A m); (\<exists>m. is_greatest B m)\<rbrakk> \<Longrightarrow> Greatest A \<le> Greatest B"
  using greatest_equality2 is_greatest_iso2 by blast

lemma greatest_singleton2:
  "Greatest {x} = x"
  by (simp add: greatest_equality2 greatest_singleton)

lemma greatest_insert1b:
  "x ub A \<Longrightarrow> Greatest (insert x A) = x"
  by (simp add: greatest_equality2 greatest_insert1)

lemma greatest_insert2b:
  "is_greatest A m \<Longrightarrow> x \<le> m \<Longrightarrow> Greatest (insert x A) = m"
  by (simp add: greatest_equality2 greatest_insert2)

lemma greatest_insert3b:
  "is_greatest A m \<Longrightarrow> m \<le> x \<Longrightarrow> Greatest (insert x A) =  x"
  by (simp add: greatest_equality2 greatest_insert3)

lemma greatest_insert4b:
  "is_greatest A m \<Longrightarrow> x < m \<Longrightarrow> Greatest (insert x A) = m"
  by (simp add: greatest_insert2b)

lemma greatest_insert5b:
  "is_greatest A m \<Longrightarrow> m < x \<Longrightarrow> Greatest (insert x A) = x"
  by (simp add: greatest_insert3b)

subsection Least
subsubsection Predicate

definition is_least::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "is_least A m \<equiv> m \<in> Lower_Bounds A A"

lemma leastI1:
  "m \<in> Lower_Bounds A A \<Longrightarrow> is_least A m" 
  by (simp add: is_least_def)

lemma leastI2:
  "\<lbrakk>m lb A; m \<in> A\<rbrakk> \<Longrightarrow> is_least A m"
  by (simp add: Lower_Bounds_mem_iff is_least_def)

lemma leastI3:
  "\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> m \<le> a); m \<in> A\<rbrakk> \<Longrightarrow> is_least A m"
  by (simp add: lbI leastI2)

lemma leastI4:
  "\<lbrakk>m \<in> Lower_Bounds X A; A \<subseteq> X; m \<in> A\<rbrakk> \<Longrightarrow> is_least A m"
  by (simp add: Lower_BoundsD3 leastI2)

lemma leastI5:
  "(\<And>X. A \<subseteq> X \<Longrightarrow> m \<in> Lower_Bounds X A) \<Longrightarrow> is_least A m"
  by (simp add: is_least_def)

lemma leastD0:
  "is_least A m \<Longrightarrow>m \<in> Lower_Bounds A A"
  by (simp add: is_least_def)

lemma leastD1:
  "is_least A m \<Longrightarrow> (m \<in> A \<and> m lb A)"
  by (simp add: Lower_Bounds_mem_iff is_least_def)

lemma leastD11:
  "is_least A m \<Longrightarrow> m \<in> A"
  by (simp add: leastD1)

lemma leastD12:
  "is_least A m \<Longrightarrow> m lb A"
  by (simp add: leastD1)

lemma leastD2:
  "\<lbrakk>is_least A m; a \<in> A\<rbrakk> \<Longrightarrow> a \<ge> m " 
  by (simp add: lbD[of "m" "A" "a"] leastD1[of "A" "m"])

lemma leastD3:
  "\<lbrakk>A \<subseteq> X; is_least A m\<rbrakk>  \<Longrightarrow> m \<in> Lower_Bounds X A"
  by (simp add: Lower_Bounds_iso2b is_least_def)

lemma least_iff:
  "is_least A m \<longleftrightarrow> (m \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> a \<ge>  m))"
  by (simp add: Lower_Bounds_mem_iff is_least_def lb_def)

lemma least_unique:
  "is_least A m1 \<Longrightarrow> is_least A m2 \<Longrightarrow> m1 =m2"
  by (simp add: least_iff order_antisym)

lemma is_least_iso2:
  "A \<subseteq> B \<Longrightarrow> is_least A ma \<Longrightarrow> is_least B mb \<Longrightarrow> ma \<ge> mb"
  using leastD11 leastD2 by blast

lemma least_ne:
  "is_least A m \<Longrightarrow> A \<noteq> {}"
  using leastD11 by auto

lemma least_ne2:
  "(\<exists>m. is_least A m) \<Longrightarrow> A \<noteq> {}"
  using leastD11 by blast

lemma least_singleton:
  "is_least {x} x"
  by (simp add: lb_singleton leastI2)

lemma singleton_ex_least:
  "\<exists>m. is_least {x} m"
  using least_singleton by blast

lemma least_pair:
  "is_least {a, b} a \<longleftrightarrow> a \<le> b"
  by (simp add: least_iff)

lemma least_double1:
  "is_least {a, b} c \<Longrightarrow> c = a \<or> c = b"
  by (simp add: least_iff)

lemma least_insert1:
  "x lb A \<Longrightarrow> is_least (insert x A) x"
  by (simp add: leastI2 lb_insert)

lemma least_insert2:
  "is_least A m \<Longrightarrow> m \<le> x \<Longrightarrow> is_least (insert x A) m"
  by (simp add: leastD11 leastI2 leastD12 lb_insert)

lemma least_insert3:
  "is_least A m \<Longrightarrow> x \<le> m \<Longrightarrow> is_least (insert x A) x"
  by (simp add: lb_iso1 leastD1 least_insert1)

lemma least_insert4:
  "is_least A m \<Longrightarrow> m < x \<Longrightarrow> is_least (insert x A) m"
  by (simp add: least_insert2)

lemma least_insert5:
  "is_least A m \<Longrightarrow> x < m \<Longrightarrow> is_least (insert x A) x"
  by (simp add: least_insert3)

lemma least_finite_linear:
  assumes A0:"finite A" and A1:"A \<noteq> {}" and A3:"(\<And>a b. \<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> (a \<le> b) \<or> (b \<le> a))"
  shows "\<exists>m. is_least A m"
  unfolding atomize_conj
  using assms
proof(induction A rule:finite_ne_induct)
  case (singleton x)
  then show ?case
    by (simp add: singleton_ex_least)
next
  case (insert x F)
  obtain m where B0:"is_least F m"
    using insert.IH insert.prems by blast
  then show ?case 
  proof(cases "x \<le> m")
    case True
    then show ?thesis
      using B0 least_insert3 by blast
  next
    case False
    have B1:"x > m"
      by (meson B0 False insert.prems insert_iff leastD11 less_le_not_le)
    then show ?thesis
      using B0 least_insert4 by auto
  qed
qed


subsubsection Operator

definition Least::"'a::order set \<Rightarrow> 'a::order" where
  "Least A \<equiv> (THE m. is_least A m)"

lemma least_equality1:
  "\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> a \<ge> m); m \<in> A\<rbrakk> \<Longrightarrow> Least A = m" 
  apply(simp add: Least_def) 
    apply(rule the_equality)
  by (simp add: least_iff order_antisym)+

lemma least_equality2:
  "is_least A m \<Longrightarrow> Least A = m"
  by (simp add: Least_def least_unique the_equality) 

lemma least_equality3:
  "m \<in> Lower_Bounds A A \<Longrightarrow> Least A = m"
  by (simp add: least_equality2 is_least_def)

lemma ub_single_least1:
  "x \<in> X \<Longrightarrow> is_least (Upper_Bounds X {x}) x"
  by (simp add: Upper_BoundsD1 Upper_Bounds_singleton least_iff)

lemma ub_single_least2:
  "x \<in> X \<Longrightarrow> Least (Upper_Bounds X {x}) = x"
  by (simp add: least_equality2 ub_single_least1)

lemma least_exD0:
  "(\<exists>m. is_least A m) \<Longrightarrow> A \<noteq> {}"
  using leastD1 least_equality2 by blast

lemma least_exD1:
  "(\<exists>m. is_least A m) \<Longrightarrow> Least A \<in> A"
  using leastD1 least_equality2 by blast

lemma least_exD2:
  "(\<exists>m. is_least A m) \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (Least A) \<le> a)"
  using leastD2 least_equality2 by blast

lemma least_exD3:
  "(\<exists>m. is_least A m) \<Longrightarrow> (Least A) \<in> Lower_Bounds A A"
  using is_least_def least_equality2 by auto

lemma least_exD4:
  "(\<exists>m. is_least A m) \<Longrightarrow>  Least A lb A"
  using leastD1 least_equality2 by blast

lemma least_exD5:
  "\<lbrakk>A \<subseteq> B; (\<exists>m. is_least A m); (\<exists>m. is_least B m)\<rbrakk> \<Longrightarrow> Least B \<le> Least A"
  using is_least_iso2 least_equality2 by blast

lemma least_singleton2:
  "Least {x} = x"
  by (simp add: least_equality2 least_singleton)

lemma least_insert1b:
  "x lb A \<Longrightarrow> Least (insert x A) =  x"
  by (simp add: least_equality2 least_insert1)

lemma least_insert2b:
  "is_least A m \<Longrightarrow> m \<le> x \<Longrightarrow> Least (insert x A) = m"
  by (simp add: least_equality2 least_insert2)

lemma least_insert3b:
  "is_least A m \<Longrightarrow> x \<le> m \<Longrightarrow> Least (insert x A) = x"
  by (simp add: least_equality2 least_insert3)

lemma least_insert4b:
  "is_least A m \<Longrightarrow> m < x \<Longrightarrow> Least (insert x A) =  m"
  by (simp add: least_insert2b)

lemma least_insert5b:
  "is_least A m \<Longrightarrow> x < m \<Longrightarrow> Least (insert x A) = x"
  by (simp add: least_insert3b)


section SupInf
subsection Sup
subsubsection Predicate

definition is_sup::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "is_sup X A x \<equiv> (is_least (Upper_Bounds X A) x)"

lemma is_supD1:
  "is_sup X A x \<Longrightarrow> (is_least (Upper_Bounds X A) x)"
  by (simp add: is_sup_def)

lemma is_supD11:
  "is_sup X A x \<Longrightarrow> (x \<in> (Upper_Bounds X A))"
  by (simp add: is_supD1 leastD1)

lemma is_supD111:
  "is_sup X A x \<Longrightarrow> x \<in> X" 
  by (simp add:is_supD11[of "X" "A" "x"] Upper_BoundsD2[of "x" "X" "A"])

lemma is_supD12:
  "is_sup X A x \<Longrightarrow> x lb (Upper_Bounds X A)"
  by (simp add: is_supD1 leastD1)

lemma is_supD112:
  "is_sup X A x \<Longrightarrow> x ub A" 
  by(simp add: Upper_BoundsD3[of "x" "X" "A"] is_supD11[of "X" "A" "x"])            

lemma is_supD121:
  "\<lbrakk> is_sup X A x; y \<in> Upper_Bounds X A\<rbrakk> \<Longrightarrow> x \<le> y "
  by (simp add: is_sup_def leastD2)
                     
lemma is_supD122:
  "\<lbrakk>is_sup X A x; y \<in> X; y ub A\<rbrakk> \<Longrightarrow> x \<le> y "
  by (simp add: Upper_Bounds_mem_iff is_supD121)
        
lemma is_supD3:
  "\<lbrakk>is_sup X A x; z \<in> X;  x \<le> z\<rbrakk> \<Longrightarrow> z \<in> Upper_Bounds X A"
  by (simp add: Upper_Bounds_mem_iff is_supD112 ub_iso1)

lemma is_supD1121:
  "\<lbrakk>is_sup X A x; a \<in> A \<rbrakk> \<Longrightarrow> a \<le> x"
  by(simp add: ubD[of "x" "A" "a"] is_supD112[of "X" "A" "x"])

lemma is_supD1122:
  "\<lbrakk>is_sup X A x; a \<in> A; b \<in> X; b \<le> a\<rbrakk> \<Longrightarrow> b \<le> x"
  using is_supD1121[of X A x a] by simp
                
lemma is_supI1:
  "is_least (Upper_Bounds X A) x \<Longrightarrow> is_sup X A x"
  by (simp add: is_sup_def) 

lemma is_supI11:
  "x \<in> Lower_Bounds (Upper_Bounds X A) (Upper_Bounds X A)  \<Longrightarrow> is_sup X A x"
  by (simp add: is_supI1 leastI1)

lemma is_supI111:
  "\<lbrakk>x lb (Upper_Bounds X A); x \<in> (Upper_Bounds X A)\<rbrakk> \<Longrightarrow> is_sup X A x"
  by (simp add: is_supI1 leastI2)

lemma is_supI112:
  "\<lbrakk>x lb (Upper_Bounds X A); x \<in> X; x ub A\<rbrakk> \<Longrightarrow> is_sup X A x"
  by (simp add: Upper_Bounds_mem_iff leastI2 is_supI1)

lemma is_supI113:
  "\<lbrakk>(\<And>a. a \<in> (Upper_Bounds X A) \<Longrightarrow> x \<le> a); x \<in> (Upper_Bounds X A)\<rbrakk> \<Longrightarrow> is_sup X A x"
  by (simp add: is_supI111 lbI)

lemma is_supI114:
  "\<lbrakk>x \<in> X; x ub A; (\<And>a. a \<in> (Upper_Bounds X A) \<Longrightarrow> x \<le> a)\<rbrakk> \<Longrightarrow> is_sup X A x"
  by (simp add: is_supI112 lb_def)

lemma is_supI115:
  "\<lbrakk>x \<in> X; x ub A; (\<And>a. a \<in> X \<Longrightarrow> a ub A \<Longrightarrow>  x \<le> a)\<rbrakk> \<Longrightarrow> is_sup X A x"
  using is_supI114[of "x" "X" "A"]  by (simp add: Upper_Bounds_mem_iff)

lemma is_supI2:
  "\<lbrakk>x \<in> X; (\<And>z. z \<in> X \<Longrightarrow> x \<le> z \<Longrightarrow> z ub A); (\<And>z. z \<in> X \<Longrightarrow> z ub A \<Longrightarrow> x \<le> z) \<rbrakk> \<Longrightarrow> is_sup X A x"
  by (simp add: Upper_Bounds_mem_iff is_supI112 lb_def)

lemma is_supD31:
  "\<lbrakk>is_sup X A x;  x \<le> z\<rbrakk> \<Longrightarrow> z ub A"
  by (simp add: is_supD112 ub_iso1)

lemma is_supD32:
  "\<lbrakk>is_sup X A x;  x \<le> z; a \<in> A\<rbrakk> \<Longrightarrow> a \<le> z"
  by (simp add: is_supD31[of "X" "A" "x" "z"] ubD[of "z" "A" "a"])

lemma is_supD41:
  "is_sup X A x \<Longrightarrow> (\<And>z. z \<in> X \<Longrightarrow> z \<ge> x \<Longrightarrow> z ub A)"
  by (simp add: is_supD31)

lemma is_supD42:
  "is_sup X A x \<Longrightarrow> (\<And>z. z \<in> X \<Longrightarrow>  z ub A \<Longrightarrow> z \<ge> x)"
  by (simp add: is_supD122)

lemma is_supD5:
  "is_sup X A x \<Longrightarrow> (\<forall>z \<in> X. (z \<ge> x) \<longleftrightarrow> (z ub A))"
  by(auto simp add:is_supD41[of "X" "A" "x"]  is_supD42[of "X" "A" "x"]) 
   
lemma is_supI3:
  "\<lbrakk>x \<in> A; A \<subseteq> X; (\<forall>z \<in> X. (z \<ge> x) \<longleftrightarrow> (z ub A))\<rbrakk> \<Longrightarrow> is_sup X A x"
  by (meson in_mono is_supI115 order_refl)

lemma is_sup_iff1:
  "\<lbrakk>x \<in> A; A \<subseteq> X\<rbrakk> \<Longrightarrow> ((\<forall>z \<in> X. (z \<ge> x) \<longleftrightarrow> (z ub A)) \<longleftrightarrow> is_sup X A x)"
  by (meson is_supD5 is_supI3)
   
lemma ge_sup_iff:
  "\<lbrakk>z \<in> X; is_sup X A x\<rbrakk> \<Longrightarrow> (z \<ge> x \<longleftrightarrow> z ub A)"
  by (simp add: is_supD5)

lemma sup_iff2:
  "is_sup X A s \<longleftrightarrow>  s \<in> X \<and> (\<forall>z \<in> X.  s \<le> z \<longleftrightarrow> z \<in> Upper_Bounds X A)"
  by (meson Upper_BoundsD2 is_supD3 is_sup_def least_iff order_refl)

lemma is_sup_unique:
  "is_sup X A m1 \<Longrightarrow> is_sup X A m2 \<Longrightarrow> m1 = m2"
  by (simp add: is_supD11 is_supD121 order_antisym)

lemma is_sup_iso1:
  "A \<subseteq> B \<Longrightarrow> is_sup X A ma \<Longrightarrow> is_sup X B mb \<Longrightarrow> ma \<le> mb "
  by (simp add: is_supD111 is_supD112 is_supD122 ub_ant2)

lemma is_sup_iso2:
  "A \<subseteq> Y \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> is_sup Y A my \<Longrightarrow> is_sup X A mx \<Longrightarrow> mx \<le> my"
  by (simp add: in_mono is_supD111 is_supD112 is_supD122)

lemma sup_max_eq:
  "A \<subseteq> X \<Longrightarrow> (is_sup X A x \<and> x \<in> A) \<longleftrightarrow> (is_greatest A x)"
  by (meson Upper_BoundsD1 greatestD11 greatestI4 greatestD12 is_supD11 is_supI114 subsetD)

lemma sup_max_eq2:
  "(is_sup A A x) \<longleftrightarrow> (is_greatest A x)"
  using is_supD111 sup_max_eq by blast

lemma sup_in_subset:
  "A \<subseteq> B \<Longrightarrow>  B \<subseteq> X \<Longrightarrow> is_sup X A s \<Longrightarrow> s \<in> B \<Longrightarrow> is_sup B A s"
  by(simp add:in_mono sup_iff2 Upper_Bounds_mem_iff)

lemma sup_iff3:
  "is_sup X A x \<longleftrightarrow> x \<in> Lower_Bounds (Upper_Bounds X A) (Upper_Bounds X A)"
  by (simp add: is_least_def is_sup_def)

lemma sup_singleton:
  "s \<in> X \<Longrightarrow> is_sup X {s} s"
  by (simp add: is_supI1 ub_single_least1)

lemma sup_empty:
  "is_sup X {} i \<longleftrightarrow> (is_least X i)"
  by (simp add: Upper_Bounds_empty is_sup_def)

lemma binary_supI1:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; x1 \<le> x2\<rbrakk> \<Longrightarrow> is_sup X {x1, x2} x2"
  by(simp add:is_sup_def is_least_def Lower_Bounds_def Upper_Bounds_def lb_def ub_def) 

lemma binary_supD1:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; is_sup X {x1, x2} x2\<rbrakk> \<Longrightarrow> x1 \<le> x2"
  by (simp add: is_supD1121)

lemma binary_supI2:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; x3 \<in> X; x3 \<ge> x1; x3 \<ge> x2; (\<And>z. \<lbrakk>z \<in> X; z \<ge> x1; z \<ge> x2\<rbrakk> \<Longrightarrow> x3 \<le> z)\<rbrakk> \<Longrightarrow> is_sup X {x1, x2} x3"
  apply(erule is_supI115) by (simp add: ub_double)+

lemma binary_supD21:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; x3 \<in> X;s \<in> X;is_sup X {x1, x2} s; x3 \<le> x1\<rbrakk> \<Longrightarrow>  x3 \<le> s"
  by (metis dual_order.trans is_supD112 ub_double)

lemma binary_supD22:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; x3 \<in> X;s \<in> X;is_sup X {x1, x2} s; x3 \<le> x2\<rbrakk> \<Longrightarrow>  x3 \<le> s"
  by (metis dual_order.trans is_supD112 ub_double)

lemma binary_supD31:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; s \<in> X; is_sup X {x1, x2} s\<rbrakk>  \<Longrightarrow>  x1 \<le> s"
  by (simp add: is_supD1121)

lemma binary_supD32:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; s \<in> X; is_sup X {x1, x2} s\<rbrakk>  \<Longrightarrow>  x2 \<le> s"
  by (simp add: is_supD1121)

lemma binary_supD4:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; x3 \<in> X; s \<in> X; is_sup X {x1, x2} s\<rbrakk>  \<Longrightarrow> (s \<le> x3 \<longleftrightarrow> x1 \<le> x3 \<and> x2 \<le> x3)"
  by (simp add: sup_iff2 ubd_mem_double)

lemma binary_sup_iff:
  "\<lbrakk>x1 \<in> X; x2 \<in> X\<rbrakk> \<Longrightarrow> (x1 \<le> x2 \<longleftrightarrow> is_sup X {x1, x2} x2)"
  by(auto simp add:binary_supI1 binary_supD1)

lemma sup_insert1:
  "\<lbrakk>x ub A; x \<in> X\<rbrakk> \<Longrightarrow> is_sup X (insert x A) x"
  by (metis greatest_exD4 greatest_insert1 greatest_insert1b insertI1 is_supI115 ubD)

lemma sup_insert2:
  "\<lbrakk>is_sup X A m;  x \<le> m\<rbrakk> \<Longrightarrow> is_sup X (insert x A) m"
  by (meson Upper_Bounds_ant1 is_supD111 is_supD112 is_supD12 is_supI112 lb_ant2 subset_insertI ub_insert)

lemma sup_insert3:
  "\<lbrakk>is_sup X A m; m \<le> x; x \<in> X\<rbrakk> \<Longrightarrow> is_sup X (insert x A) x"
  by (simp add: is_supD41 sup_insert1)

lemma sup_insert4:
  "\<lbrakk>is_sup X A m;  x < m\<rbrakk> \<Longrightarrow> is_sup X (insert x A) m"
  by (simp add: sup_insert2)

lemma sup_insert5:
  "\<lbrakk>is_sup X A m;  m < x; x \<in> X\<rbrakk> \<Longrightarrow> is_sup X (insert x A) x"
  by (simp add: sup_insert3)

lemma sup_insert61:
  "\<lbrakk>is_sup X A s1; is_sup X {s1, x} s2\<rbrakk> \<Longrightarrow> s2 ub A"
  by (simp add: is_supD1121 is_supD31)  

lemma sup_insert62:
  "\<lbrakk>is_sup X A s1; is_sup X {s1, x} s2\<rbrakk> \<Longrightarrow> s2 \<in> Upper_Bounds X A"
  by (simp add: Upper_Bounds_mem_iff sup_insert61 is_supD111)

lemma sup_insert7:
  "\<lbrakk>is_sup X A s1; is_sup X {s1, x} s2; u \<in> Upper_Bounds X (insert x A)\<rbrakk> \<Longrightarrow>  s2 \<le> u"
  by (simp add: Upper_Bounds_mem_iff2 is_supD121)

subsubsection Operator

definition Sup::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order" where
  "Sup X A \<equiv> (THE m. is_sup X A m)"

lemma sup_equality:
  "is_sup X A m \<Longrightarrow> Sup X A = m"
  by (simp add: Sup_def is_sup_unique the_equality) 

lemma sup_singleton3:
  "x \<in> X \<Longrightarrow> Sup X {x} = x"
  by (simp add: sup_equality sup_singleton)

lemma sup_singleton4:
  "x \<in> X \<Longrightarrow> Sup X {x, x} = x"
  by (simp add: sup_equality sup_singleton)

subsection Inf
subsubsection Predicate

definition is_inf::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "is_inf X A x \<equiv> (is_greatest (Lower_Bounds X A) x)"

lemma is_infD1:
  "is_inf X A x \<Longrightarrow> (is_greatest (Lower_Bounds X A) x)"
  by (simp add: is_inf_def)

lemma is_infD11:
  "is_inf X A x \<Longrightarrow> (x \<in> (Lower_Bounds X A))"
  by (simp add: is_infD1 greatestD1)

lemma is_infD111:
  "is_inf X A x \<Longrightarrow> x \<in> X" 
  by (simp add:is_infD11[of "X" "A" "x"] Lower_BoundsD2[of "x" "X" "A"])

lemma is_infD12:
  "is_inf X A x \<Longrightarrow> x ub (Lower_Bounds X A)"
  by (simp add: is_infD1 greatestD1)

lemma is_infD112:
  "is_inf X A x \<Longrightarrow> x lb A" 
  by(simp add: Lower_BoundsD3[of "x" "X" "A"] is_infD11[of "X" "A" "x"])            

lemma is_infD121:
  "\<lbrakk>is_inf X A x; y \<in> Lower_Bounds X A\<rbrakk> \<Longrightarrow> y \<le> x "
  by (simp add: is_inf_def greatestD2)

lemma is_infD122:
  "\<lbrakk>is_inf X A x; y \<in> X; y lb A\<rbrakk> \<Longrightarrow> y \<le> x "
  by (simp add: Lower_Bounds_mem_iff is_infD121)
        
lemma is_infD1121:
  "\<lbrakk>is_inf X A x; a \<in> A \<rbrakk> \<Longrightarrow> x \<le> a"
  by(simp add: lbD[of "x" "A" "a"] is_infD112[of "X" "A" "x"])
                
lemma is_infI1:
  "is_greatest (Lower_Bounds X A) x \<Longrightarrow> is_inf X A x"
  by (simp add: is_inf_def) 
             
lemma is_infI11:
  "x \<in> Upper_Bounds (Lower_Bounds X A) (Lower_Bounds X A)  \<Longrightarrow> is_inf X A x"
  by (simp add: is_infI1 greatestI1)

lemma is_infI111:
  "\<lbrakk>x ub (Lower_Bounds X A); x \<in> (Lower_Bounds X A)\<rbrakk> \<Longrightarrow> is_inf X A x"
  by (simp add: is_infI1 greatestI2)

lemma is_infI112:
  "\<lbrakk>x ub (Lower_Bounds X A); x \<in> X; x lb A\<rbrakk> \<Longrightarrow> is_inf X A x"
  by (simp add: Lower_Bounds_mem_iff greatestI2 is_infI1)

lemma is_infI113:
  "\<lbrakk>(\<And>a. a \<in> (Lower_Bounds X A) \<Longrightarrow> a \<le> x); x \<in>  (Lower_Bounds X A)\<rbrakk> \<Longrightarrow> is_inf X A x"
  by (simp add: is_infI111 ubI)

lemma is_infI114:
  "\<lbrakk>x \<in> X; x lb A; (\<And>a. a \<in> (Lower_Bounds X A) \<Longrightarrow> a \<le> x)\<rbrakk> \<Longrightarrow> is_inf X A x"
  by (simp add: is_infI112 ub_def)

lemma is_infI115:
  "\<lbrakk>x \<in> X; x lb A; (\<And>a. a \<in> X \<Longrightarrow> a lb A \<Longrightarrow>  a \<le> x)\<rbrakk> \<Longrightarrow> is_inf X A x"
  using is_infI114[of "x" "X" "A"] by (auto simp add: Lower_Bounds_mem_iff)

lemma is_infI2:
  "\<lbrakk>x \<in> X; (\<And>z. z \<in> X \<Longrightarrow> z \<le> x \<Longrightarrow> z lb A); (\<And>z. z \<in> X \<Longrightarrow> z lb A \<Longrightarrow> z \<le> x) \<rbrakk> \<Longrightarrow> is_inf X A x"
  by (simp add: Lower_Bounds_mem_iff is_infI112 ub_def)

lemma is_infD3:
  "\<lbrakk>is_inf X A x; z \<in> X;  z \<le> x\<rbrakk> \<Longrightarrow> z \<in> Lower_Bounds X A"
  by (simp add: Lower_Bounds_mem_iff is_infD112 lb_iso1)

lemma is_infD31:
  "\<lbrakk>is_inf X A x;  z \<le> x\<rbrakk> \<Longrightarrow> z lb A"
  by (simp add: is_infD112 lb_iso1)

lemma is_infD32:
  "\<lbrakk>is_inf X A x;  z \<le> x; a \<in> A\<rbrakk> \<Longrightarrow> z \<le> a"
  by (simp add: is_infD31[of "X" "A" "x" "z"] lbD[of "z" "A" "a"])

lemma is_infD33:
  "\<lbrakk>is_inf X A x;  z \<le> x; z \<in> X\<rbrakk> \<Longrightarrow> z \<in> Lower_Bounds X A"
  by (simp add: is_infD3)

lemma is_infD41:
  "is_inf X A x \<Longrightarrow> (\<And>z. z \<in> X \<Longrightarrow> z \<le> x \<Longrightarrow> z lb A)"
  by (simp add: is_infD31)

lemma is_infD42:
  "is_inf X A x \<Longrightarrow> (\<And>z. z \<in> X \<Longrightarrow>  z lb A \<Longrightarrow> z \<le> x)"
  by (simp add: is_infD122)

lemma is_infD5:
  "is_inf X A x \<Longrightarrow> (\<forall>z \<in> X. (z \<le> x) \<longleftrightarrow> (z lb A))"
  by(auto simp add:is_infD41[of "X" "A" "x"]  is_infD42[of "X" "A" "x"]) 
 
lemma is_infI3:
  "\<lbrakk>x \<in> A; A \<subseteq> X; (\<forall>z \<in> X. (z \<le> x) \<longleftrightarrow> (z lb A))\<rbrakk> \<Longrightarrow> is_inf X A x"
  by (meson in_mono is_infI115 order_refl)

lemma is_inf_iff1:
  "\<lbrakk>x \<in> A; A \<subseteq> X\<rbrakk> \<Longrightarrow> ((\<forall>z \<in> X. (z \<le> x) \<longleftrightarrow> (z lb A)) \<longleftrightarrow> is_inf X A x)"
  by (meson is_infD31 is_infI3 lbD)

lemma lt_inf_iff:
  "\<lbrakk>z \<in> X; is_inf X A x\<rbrakk> \<Longrightarrow> (z \<le> x \<longleftrightarrow> z lb A)"
  by (simp add: is_infD5)

lemma inf_iff2:
  "is_inf X A s \<longleftrightarrow>  s \<in> X \<and> (\<forall>z \<in> X.  s \<ge> z \<longleftrightarrow> z \<in> Lower_Bounds X A)"
  by (meson Lower_BoundsD2 greatest_iff is_infD3 is_inf_def order_refl)

lemma is_inf_unique:
  "is_inf X A m1 \<Longrightarrow> is_inf X A m2 \<Longrightarrow> m1 = m2"
  by (simp add: is_infD11 is_infD121 order_antisym)

lemma is_inf_ant1:
  "A \<subseteq> B \<Longrightarrow> is_inf X A ma \<Longrightarrow> is_inf X B mb \<Longrightarrow> mb \<le> ma"
  by (simp add: is_infD111 is_infD112 is_infD122 lb_ant2)
       
lemma is_inf_ant2:
  "A \<subseteq> Y \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> is_inf Y A my \<Longrightarrow> is_inf X A mx \<Longrightarrow> my \<le> mx"
  by (simp add: in_mono is_infD111 is_infD112 is_infD122)

lemma inf_min_eq:
  "A \<subseteq> X \<Longrightarrow> (is_inf X A x \<and> x \<in> A) \<longleftrightarrow> (is_least A x)"
  by (meson Lower_BoundsD1 is_infD11 is_infI114 leastD11 leastD12 leastI4 subsetD)

lemma inf_min_eq2:
  "(is_inf A A x) \<longleftrightarrow> (is_least A x)"
  using is_infD111 inf_min_eq by blast

lemma inf_in_subset:
  "A \<subseteq> B \<Longrightarrow>  B \<subseteq> X \<Longrightarrow> is_inf X A s \<Longrightarrow> s \<in> B \<Longrightarrow> is_inf B A s"
  by(simp add:in_mono inf_iff2 Lower_Bounds_mem_iff)

lemma inf_iff3:
  "is_inf X A x \<longleftrightarrow> x \<in> Upper_Bounds (Lower_Bounds X A) (Lower_Bounds X A)"
  by (simp add: is_greatest_def is_inf_def)

lemma inf_singleton:
  "s \<in> X \<Longrightarrow> is_inf X {s} s"
  by (simp add: is_infI115 lbD lb_singleton)

lemma inf_empty:
  "is_inf X {} i \<longleftrightarrow> (is_greatest X i)"
  by (simp add: Lower_Bounds_empty is_inf_def)

lemma binary_infI1:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; x1 \<le> x2\<rbrakk> \<Longrightarrow> is_inf X {x1, x2} x1"
  by(simp add:is_inf_def is_greatest_def Upper_Bounds_def Lower_Bounds_def lb_def ub_def) 

lemma binary_infI2:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; x3 \<in> X; x3 \<le> x1; x3 \<le> x2; (\<And>z. \<lbrakk>z \<in> X; z \<le> x1; z \<le> x2\<rbrakk> \<Longrightarrow> x3 \<ge> z)\<rbrakk> \<Longrightarrow> is_inf X {x1, x2} x3"
  apply(erule is_infI115) by (simp add: lb_double)+

lemma binary_infD1:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; is_inf X {x1, x2} x1\<rbrakk> \<Longrightarrow> x1 \<le> x2"
  by (simp add: is_infD1121)

lemma binary_infD21:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; x3 \<in> X;s \<in> X;is_inf X {x1, x2} s; x3 \<ge> x1\<rbrakk> \<Longrightarrow>  x3 \<ge> s"
  by (meson dual_order.trans is_infD112 lb_double)

lemma binary_infD22:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; x3 \<in> X;s \<in> X;is_inf X {x1, x2} s; x3 \<ge> x2\<rbrakk> \<Longrightarrow>  x3 \<ge> s"
  by (metis dual_order.trans is_infD112 lb_double)

lemma binary_infD31:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; s \<in> X; is_inf X {x1, x2} s\<rbrakk>  \<Longrightarrow>  x1 \<ge> s"
  by (simp add: is_infD1121)

lemma binary_infD32:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; s \<in> X; is_inf X {x1, x2} s\<rbrakk>  \<Longrightarrow>  x2 \<ge> s"
  by (simp add: is_infD1121)

lemma binary_infD4:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; x3 \<in> X; s \<in> X; is_inf X {x1, x2} s\<rbrakk>  \<Longrightarrow> (s \<ge> x3 \<longleftrightarrow> x1 \<ge> x3 \<and> x2 \<ge> x3)"
  by (simp add: inf_iff2 lbd_mem_double)

lemma binary_inf_iff:
  "\<lbrakk>x1 \<in> X; x2 \<in> X\<rbrakk> \<Longrightarrow> (x1 \<le> x2 \<longleftrightarrow> is_inf X {x1, x2} x1)"
  by(auto simp add:binary_infI1 binary_infD1)


lemma inf_insert1:
  "\<lbrakk>x lb A; x \<in> X\<rbrakk> \<Longrightarrow> is_inf X (insert x A) x"
  by (simp add: is_infI115 lbD leastD1 least_insert1)

lemma inf_insert2:
  "\<lbrakk>is_inf X A m;  m \<le> x\<rbrakk> \<Longrightarrow> is_inf X (insert x A) m"
  by (metis insert_iff is_infD111 is_infD112 is_infD122 is_infI115 lb_def)

lemma inf_insert3:
  "\<lbrakk>is_inf X A m; x \<le> m; x \<in> X\<rbrakk> \<Longrightarrow> is_inf X (insert x A) x"
  by (simp add: is_infD41 inf_insert1)

lemma inf_insert4:
  "\<lbrakk>is_inf X A m;  m < x\<rbrakk> \<Longrightarrow> is_inf X (insert x A) m"
  by (simp add: inf_insert2)

lemma inf_insert5:
  "\<lbrakk>is_inf X A m;  x < m; x \<in> X\<rbrakk> \<Longrightarrow> is_inf X (insert x A) x"
  by (simp add: inf_insert3)

lemma inf_insert61:
  "\<lbrakk>is_inf X A i1; is_inf X {i1, x} i2\<rbrakk> \<Longrightarrow> i2 lb A"
  by (simp add: is_infD1121 is_infD31)  

lemma inf_insert62:
  "\<lbrakk>is_inf X A i1; is_inf X {i1, x} i2\<rbrakk> \<Longrightarrow> i2 \<in> Lower_Bounds X A"
  by (simp add: Lower_Bounds_mem_iff inf_insert61 is_infD111)

lemma inf_insert7:
  "\<lbrakk>is_inf X A i1; is_inf X {i1, x} i2; l \<in> Lower_Bounds X (insert x A)\<rbrakk> \<Longrightarrow>  l \<le> i2"
  by (simp add: Lower_Bounds_mem_iff2 is_infD121)

subsubsection Operator

definition Inf::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order" where
  "Inf X A \<equiv> (THE m. is_inf X A m)"

lemma inf_equality:
  "is_inf X A m \<Longrightarrow> Inf X A = m"
  by (simp add: Inf_def is_inf_unique the_equality) 

lemma inf_singleton3:
  "x \<in> X \<Longrightarrow> Inf X {x} = x"
  by (simp add: inf_equality inf_singleton)

lemma inf_singleton4:
  "x \<in> X \<Longrightarrow> Inf X {x, x} = x"
  by (simp add: inf_singleton3)

lemma sup_imp_inf_ub:
  "A \<subseteq> X \<Longrightarrow> is_sup X A s \<Longrightarrow>  is_inf X (Upper_Bounds X A) s"
  by(simp add:is_sup_def is_inf_def is_least_def is_greatest_def Upper_Bounds_def Lower_Bounds_def lb_def ub_def)
  
lemma sup_if_inf_ub:
  "A \<subseteq> X \<Longrightarrow> is_inf X (Upper_Bounds X A) s \<Longrightarrow>  is_sup X A s"
  by(auto simp add:is_sup_def is_inf_def is_least_def is_greatest_def Upper_Bounds_def Lower_Bounds_def lb_def ub_def)
  
lemma inf_imp_sup_lb:
  "A \<subseteq> X \<Longrightarrow> is_inf X A s \<Longrightarrow>  is_sup X (Lower_Bounds X A) s"
  by(simp add:is_sup_def is_inf_def is_least_def is_greatest_def Upper_Bounds_def Lower_Bounds_def lb_def ub_def)
  
lemma inf_if_sup_lb:
  "A \<subseteq> X \<Longrightarrow> is_sup X (Lower_Bounds X A) s \<Longrightarrow>  is_inf X A s"
  by(auto simp add:is_sup_def is_inf_def is_least_def is_greatest_def Upper_Bounds_def Lower_Bounds_def lb_def ub_def)
  
lemma Upper_eq_sup_eq:
  "Upper_Bounds X A = Upper_Bounds X B \<Longrightarrow> (is_sup X A s \<longleftrightarrow> is_sup X B s)"
  by (simp add: is_sup_def)

lemma ub_eq_sup_eq:
  "(\<And>x. x ub A \<longleftrightarrow> x ub B) \<Longrightarrow> (is_sup X A s \<longleftrightarrow> is_sup X B s)"
  by (simp add: Upper_Bounds_mem_iff sup_iff2)

lemma Lower_eq_inf_eq:
  "Lower_Bounds X A = Lower_Bounds X B \<Longrightarrow> (is_inf X A i \<longleftrightarrow> is_inf X B i)"
  by (simp add: is_inf_def)

lemma lb_eq_inf_eq:
  "(\<And>x. x lb A \<longleftrightarrow> x lb B) \<Longrightarrow> (is_inf X A i \<longleftrightarrow> is_inf X B i)"
  by (simp add: Lower_Bounds_mem_iff inf_iff2)

lemma inf_exI:
  "\<exists>t. is_inf X A t \<Longrightarrow> (\<And>t. is_inf X A t \<Longrightarrow> P t) \<Longrightarrow> P (Inf X A)"
  using inf_equality by auto

lemma sup_exI:
  "\<exists>s. is_sup X A s \<Longrightarrow> (\<And>s. is_sup X A s \<Longrightarrow> P s) \<Longrightarrow> P (Sup X A)"
  using sup_equality by auto

lemma lbd_eqI1:
  "(\<And>x. x \<in> X \<Longrightarrow> x lb A \<Longrightarrow> x lb B) \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x lb B \<Longrightarrow> x lb A) \<Longrightarrow> Lower_Bounds X A = Lower_Bounds X B"
  by(auto simp add:set_eq_iff Lower_Bounds_mem_iff)

lemma ubd_eqI1:
  "(\<And>x. x \<in> X \<Longrightarrow> x ub A \<Longrightarrow> x ub B) \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x ub B \<Longrightarrow> x ub A) \<Longrightarrow> Upper_Bounds X A = Upper_Bounds X B"
  by(auto simp add:set_eq_iff Upper_Bounds_mem_iff)

lemma image_p:
  "(\<And>a. a \<in> A \<Longrightarrow> P (f a)) \<Longrightarrow> (\<forall>y \<in> f ` A.  P(y))"
  by blast

lemma lb_imageI:
  "(\<And>a. a \<in> A \<Longrightarrow> x \<le> f a) \<Longrightarrow> x lb (f`A)"
  by(simp add:lb_def image_p[of "A" "\<lambda>a. x \<le> a" "f"])

lemma ub_imageI:
  "(\<And>a. a \<in> A \<Longrightarrow> x \<ge> f a) \<Longrightarrow> x ub (f`A)"
  by(simp add:ub_def image_p[of "A" "\<lambda>a. x \<ge> a" "f"])

lemma inf_families1:
  "A \<noteq> {} \<Longrightarrow> (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>ti. is_inf X Ai ti) \<Longrightarrow> x \<in> X \<Longrightarrow> x lb Inf X ` A \<Longrightarrow> x lb \<Union> A"
  by (metis Union_iff imageI inf_equality is_infD32 lb_def)

lemma inf_families2:
  "A \<noteq> {} \<Longrightarrow> (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>ti. is_inf X Ai ti) \<Longrightarrow> x \<in> X \<Longrightarrow> x lb \<Union> A \<Longrightarrow>  x lb Inf X ` A"
   by (metis lb_imageI  Union_upper inf_equality is_infD5 lb_ant2)

lemma sup_families1:
  "A \<noteq> {} \<Longrightarrow> (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_sup X Ai si) \<Longrightarrow> x \<in> X \<Longrightarrow> x ub Sup X ` A \<Longrightarrow> x ub \<Union> A"
  by (metis Union_iff imageI sup_equality is_supD32 ub_def)

lemma sup_families2:
  "A \<noteq> {} \<Longrightarrow> (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_sup X Ai si) \<Longrightarrow> x \<in> X \<Longrightarrow> x ub \<Union> A \<Longrightarrow>  x ub Sup X ` A"
   by (metis ub_imageI Union_upper sup_equality is_supD5 ub_ant2)

lemma inf_families:
  "A \<noteq> {} \<Longrightarrow>(\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>ti. is_inf X Ai ti) \<Longrightarrow>(is_inf X ((\<lambda>Ai. Inf X Ai)`A) t) \<longleftrightarrow> (is_inf X (\<Union>A) t)"
  apply(rule Lower_eq_inf_eq, rule lbd_eqI1) using inf_families1 apply blast using inf_families2 by blast

lemma sup_families:
  "A \<noteq> {} \<Longrightarrow>(\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_sup X Ai si) \<Longrightarrow>(is_sup X ((\<lambda>Ai. Sup X Ai)`A) s) \<longleftrightarrow> (is_sup X (\<Union>A) s)"
  apply(rule Upper_eq_sup_eq, rule ubd_eqI1) using sup_families1 apply blast using sup_families2 by blast



subsection Completeness

definition is_inf_semilattice::"'a::order set \<Rightarrow> bool" where
  "is_inf_semilattice X \<equiv> (X \<noteq> {}) \<and> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>x. is_inf X {a, b} x))"

definition is_finf_closed::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_finf_closed X A \<equiv> (\<forall>a1 a2. a1 \<in> A \<and>  a2 \<in> A \<longrightarrow> Inf X {a1, a2} \<in> A)"

lemma sinfI1:
  "\<lbrakk>(X \<noteq> {});  (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>x. is_inf X {a, b} x))\<rbrakk> \<Longrightarrow> is_inf_semilattice X"
  by (simp add:is_inf_semilattice_def)

lemma sinfD1:
  " is_inf_semilattice X \<Longrightarrow> X \<noteq> {}"
  by (simp add: is_inf_semilattice_def)

lemma sinfD2:
  "\<lbrakk>is_inf_semilattice X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>x. is_inf X {a, b} x) "
  by (simp add: is_inf_semilattice_def)

lemma sinfD3:
  "\<lbrakk>is_inf_semilattice X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> is_inf X {a, b} (Inf X {a, b}) "
  using inf_equality sinfD2 by blast

lemma sinfD4:
  "\<lbrakk>is_inf_semilattice X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> (Inf X {a, b}) \<in> X"
  using is_infD111 sinfD3 by blast

lemma binfI:
  "\<lbrakk>is_inf_semilattice X; (\<And>s. is_inf X {a, b} s \<Longrightarrow> P s); a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> P (Inf X {a, b})"
  by (simp add: sinfD3)

lemma binf_commute:
  "is_inf X {a, b} c \<longleftrightarrow> is_inf X {b, a } c "
  by (simp add: insert_commute)

lemma binf_leI1:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X; a \<le> c\<rbrakk>  \<Longrightarrow> Inf X {a, b} \<le> c"
  by (simp add: binary_infD21 sinfD3 sinfD4)

lemma binf_leI2:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X; b \<le> c\<rbrakk>  \<Longrightarrow> Inf X {a, b} \<le> c"
  by (simp add: binary_infD22 sinfD3 sinfD4)

lemma binf_leI3:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X; c \<le>a; c \<le> b\<rbrakk>  \<Longrightarrow>c \<le> Inf X {a, b}"
  by (simp add: binary_infD4 sinfD3 sinfD4)

lemma binf_iff:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X\<rbrakk>  \<Longrightarrow> (c \<le> Inf X {a, b} \<longleftrightarrow> c \<le> a \<and> c \<le> b)"
  by (simp add: binary_infD4 sinfD3 sinfD4)

lemma binf_assoc1:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow>  (\<lambda>x y. Inf X {x, y}) ((\<lambda>x y. Inf X {x, y}) a b) c =  (\<lambda>x y. Inf X {x, y}) a ( (\<lambda>x y. Inf X {x, y}) b c)"
  apply(rule order.antisym) by (metis sinfD3 binf_iff is_infD111 order_refl)+

lemma binf_assoc2:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow>   (\<lambda>x y. Inf X {x, y}) a ( (\<lambda>x y. Inf X {x, y}) b c) =  (\<lambda>x y. Inf X {x, y}) b ( (\<lambda>x y. Inf X {x, y}) a c)"
  apply(rule order.antisym) by (simp add: binf_leI1 binf_leI2 binf_leI3 sinfD4)+

lemma binf_commute2:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> Inf X {a, b}  =  Inf X {b,a}"
  by (simp add: insert_commute)

lemma binf_idem1:
  "a\<in> X \<Longrightarrow> (\<lambda>x y. Inf X {x, y}) a a = a"
  by (simp add:  inf_equality inf_singleton)

lemma binf_idem2:
  "is_inf_semilattice X \<Longrightarrow>a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow>  (\<lambda>x y. Inf X {x, y}) a ( (\<lambda>x y. Inf X {x, y}) a b) =  (\<lambda>x y. Inf X {x, y}) a b"
  by (metis binf_assoc1 binf_idem1)

lemma binf_idem3:
  "is_inf_semilattice X \<Longrightarrow> a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow>  (\<lambda>x y. Inf X {x, y}) ( (\<lambda>x y. Inf X {x, y}) a b) b =  (\<lambda>x y. Inf X {x, y}) a b"
  by (metis binf_assoc1 binf_idem1)

lemma binf_lt1:
  "is_inf_semilattice X\<Longrightarrow>a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> a \<le> b \<Longrightarrow>  Inf X {a, b} = a"
  by (simp add: dual_order.eq_iff binf_iff binf_leI1)

lemma binf_lt2:
  "is_inf_semilattice X \<Longrightarrow>a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> b \<le> a \<Longrightarrow> Inf X {a, b} = b"
  by (simp add: dual_order.eq_iff binf_iff binf_leI2)

lemma binf_finite:
  assumes A0: "\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> is_inf X {a1, a2} (Inf X {a1, a2})" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X"
  shows "is_inf X A (Inf X A)"
  using A1 A2 A3 
proof (induct A rule: finite_ne_induct)
  case (singleton x)
  then show ?case using A0 by force
next
  case (insert x F)
  obtain i1 where B0:"is_inf X F i1"
    using insert.hyps(4) insert.prems by blast
  have B1:"i1 \<in> X"
    using B0 is_infD111 by auto
  obtain i2 where B2:"is_inf X {i1, x} i2"
    using A0 B1 insert.prems by auto
  have B3:"i2 \<in> Lower_Bounds X (insert x F)"
    by (meson B0 B2 inf_insert62 insertI2 is_infD1121 lbd_mem_insert singleton_iff)
  have B4:"\<And>l. l \<in> Lower_Bounds X (insert x F) \<longrightarrow> l \<le> i2"
    using B0 B2 inf_insert7 by blast
  have B3:"is_inf X (insert x F) i2"
    by (simp add: B3 B4 is_infI113)
  then show ?case
    by (simp add: inf_equality)
qed


lemma binf_finite2:
  "\<lbrakk>is_inf_semilattice X;  A \<subseteq> X;A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow>  is_inf X A (Inf X A)"
  by (meson binf_finite sinfD3)

lemma finf_closedD1:
  "is_finf_closed X A \<Longrightarrow> (\<And>a1 a2. a1 \<in> A\<Longrightarrow> a2 \<in> A \<Longrightarrow> Inf X {a1, a2} \<in> A)"
  by (simp add: is_finf_closed_def)

lemma finite_inf_closed2:
  assumes A0: "\<And>a1 a2. a1 \<in> A \<Longrightarrow> a2 \<in> A \<Longrightarrow>  Inf X {a1, a2} \<in> A" and 
          A1:"finite E" and
          A2:"E \<noteq> {}" and
          A3:"E \<subseteq> A" and
          A4:"A \<subseteq> X" and
          A5:"is_inf_semilattice X"
  shows "Inf X E \<in> A"
  using A1 A2 A3 A4 A5
proof (induct E rule: finite_ne_induct)
  case (singleton x)
  then show ?case
    using A0 by fastforce
next
  case (insert x F)
  obtain i where A6:"is_inf X F i"
    by (meson A4 A5 binf_finite2 insert.hyps(1) insert.hyps(2) insert.prems(1) insert_subset order_trans)
  have B0:"i \<in> A"
    using A4 A5 A6 inf_equality insert.hyps(4) insert.prems(1) by blast
  have B1:"x \<in> A"
    using insert.prems(1) by auto
  obtain t where A7:"is_inf X {x, i} t"
    by (meson A4 A5 A6 B1 is_infD111 is_inf_semilattice_def subset_eq)
  have B2:"t \<in> A"
    using A0 A7 B0 B1 inf_equality by blast
  have B3:"t \<in> (Lower_Bounds X (insert x F))"
    by (metis A6 A7 Lower_Bounds_mem_iff is_infD111 is_infD112 is_infD5 lb_double lb_insert)
  have B4:"\<And>y. y \<in> (Lower_Bounds X (insert x F)) \<longrightarrow> y \<le>t "
    by (metis A6 A7 Lower_BoundsD3 Lower_Bounds_mem_iff2 insertCI is_infD42 lb_double)
  have B5:"is_inf X (insert x F) t"
    by (simp add: B3 B4 is_infI113)
  then show ?case
    by (simp add: B2 inf_equality)
qed

lemma inf_semilattice_finf_closed:
  "\<lbrakk>is_finf_closed X A; A \<subseteq> X; E \<subseteq> A; finite E; E \<noteq> {}; is_inf_semilattice X\<rbrakk> \<Longrightarrow> Inf X E \<in> A "
  by (metis finite_inf_closed2 is_finf_closed_def)


context fixes X::"'a::order set" and
              x x1 y y1 z::"'a::order" 
        assumes elem:"x \<in> X  \<and> x1 \<in> X \<and> y \<in> X \<and> y1 \<in> X \<and> z \<in> X" and
                inf_latt:"is_inf_semilattice X"
begin

context assumes 
  le:"x \<le> y"
begin

lemma sinfs_leD1:
"Inf X {z, x} \<le> Inf X {z, y}"
 by (simp add: binf_leI1 binf_leI2 binf_leI3 le local.elem sinfD4 inf_latt)

lemma sinfs_leD2:
"Inf X {z, x} \<le> Inf X {y, z}"
 by (simp add: binf_leI1 binf_leI2 binf_leI3 le local.elem sinfD4 inf_latt)

lemma sinfs_leD3:
"Inf X {x, z} \<le> Inf X {z, y}"
 by (simp add: binf_leI1 binf_leI2 binf_leI3 le local.elem sinfD4 inf_latt)

lemma sinfs_leD4:
"Inf X {x, z} \<le> Inf X {y, z}"
 by (simp add: binf_leI1 binf_leI2 binf_leI3 le local.elem sinfD4 inf_latt)

end

context assumes 
  le:"x \<le> z"
begin

lemma sinf_leD5:
  "Inf X {x, y} \<le>z"
  by (simp add: binf_leI1 le local.elem inf_latt)

lemma sinf_leD6:
  "Inf X {y, x} \<le> z"
  by (simp add: binf_leI2 le local.elem inf_latt)

end

context assumes 
  le:"x \<le> x1 \<and> y \<le> y1"
begin
lemma sinf_leD7:
  "Inf X {x, y} \<le> Inf X {x1, y1}"
  by (simp add: binf_leI1 binf_leI2 binf_leI3 le local.elem sinfD4 inf_latt)

lemma sinf_leD8:
  "Inf X {x, y} \<le> Inf X {y1, x1}"
  by (simp add: insert_commute sinf_leD7)

end


context assumes 
  le:"x \<ge> z\<and> y \<ge> z"
begin
lemma sinf_leD9:
  "Inf X {x, y} \<ge> z"
  by (simp add: binf_leI3 le local.elem inf_latt)
end


end



definition is_sup_semilattice::"'a::order set \<Rightarrow> bool" where
  "is_sup_semilattice X \<equiv> (X \<noteq> {}) \<and> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>x. is_sup X {a, b} x))"

definition is_fsup_closed::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_fsup_closed X A \<equiv> (\<forall>a1 a2. a1 \<in> A \<and>  a2 \<in> A \<longrightarrow> Sup X {a1, a2} \<in> A)"

lemma ssupI1:
  "\<lbrakk>(X \<noteq> {});  (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>x. is_sup X {a, b} x))\<rbrakk> \<Longrightarrow> is_sup_semilattice X"
  by (simp add:is_sup_semilattice_def)

lemma ssupD1:
  " is_sup_semilattice X \<Longrightarrow> X \<noteq> {}"
  by (simp add: is_sup_semilattice_def)

lemma ssupD2:
  "\<lbrakk>is_sup_semilattice X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup X {a, b} x) "
  by (simp add: is_sup_semilattice_def)

lemma ssupD3:
  "\<lbrakk>is_sup_semilattice X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> is_sup X {a, b} (Sup X {a, b}) "
  using ssupD2 sup_equality by blast

lemma ssupD4:
  "\<lbrakk>is_sup_semilattice X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow>  (Sup X {a, b}) \<in> X"
  using is_supD111 ssupD3 by blast

lemma bsupI:
  "\<lbrakk>is_sup_semilattice X; (\<And>s. is_sup X {a, b} s \<Longrightarrow> P s); a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> P (Sup X {a, b})"
  by (metis is_sup_semilattice_def sup_equality)

lemma bsup_commute:
  "is_sup X {a, b} c \<longleftrightarrow> is_sup X {b, a } c "
  by (simp add: insert_commute)

lemma bsup_geI1:
  "\<lbrakk>is_sup_semilattice X;a \<in> X; b \<in> X; c \<in> X; a \<ge> c\<rbrakk>  \<Longrightarrow> Sup X {a, b} \<ge> c"
  by (simp add: binary_supD21 ssupD3 ssupD4)

lemma bsup_geI2:
  "\<lbrakk>is_sup_semilattice X;a \<in> X; b \<in> X; c \<in> X; b \<ge> c\<rbrakk>  \<Longrightarrow> Sup X {a, b} \<ge> c"
  by (simp add: binary_supD22 ssupD3 ssupD4)

lemma bsup_geI3:
  "\<lbrakk>is_sup_semilattice X;a \<in> X; b \<in> X; c \<in> X; c \<ge>a; c \<ge> b\<rbrakk> \<Longrightarrow> c \<ge> Sup X {a, b}"
  by (simp add: binary_supD4 ssupD3 ssupD4)

lemma bsup_iff:
  "\<lbrakk>is_sup_semilattice X; a \<in> X; b \<in> X; c \<in> X\<rbrakk>  \<Longrightarrow> (c \<ge> Sup X {a, b} \<longleftrightarrow> c \<ge> a \<and> c \<ge> b)"
  by (simp add: binary_supD4 ssupD3 ssupD4)

lemma bsup_assoc1:
  "\<lbrakk>is_sup_semilattice X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow>  (\<lambda>x y. Sup X {x, y}) ((\<lambda>x y. Sup X {x, y}) a b) c =  (\<lambda>x y. Sup X {x, y}) a ( (\<lambda>x y. Sup X {x, y}) b c)"
  apply(rule order.antisym) by (metis ssupD3 bsup_iff is_supD111 order_refl)+

lemma bsup_assoc2:
  "\<lbrakk>is_sup_semilattice X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow>   (\<lambda>x y. Sup X {x, y}) a ( (\<lambda>x y. Sup X {x, y}) b c) = (\<lambda>x y. Sup X {x, y}) b ( (\<lambda>x y. Sup X {x, y}) a c)"
  apply(rule order.antisym) by (metis ssupD3 bsup_iff is_supD111 order_refl)+

lemma bsup_commute2:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow>  (\<lambda>x y. Sup X {x, y}) a b =  (\<lambda>x y. Sup X {x, y}) b a"
  by (simp add: insert_commute)

lemma bsup_idem1:
  "a\<in> X \<Longrightarrow> (\<lambda>x y. Sup X {x, y}) a a = a"
  by (simp add: sup_equality sup_singleton)

lemma bsup_idem2:
  "is_sup_semilattice X \<Longrightarrow>a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow>  (\<lambda>x y. Sup X {x, y}) a ( (\<lambda>x y. Sup X {x, y}) a b) =  (\<lambda>x y. Sup X {x, y}) a b"
  by (metis bsup_assoc1 bsup_idem1)

lemma bsup_idem3:
  "is_sup_semilattice X \<Longrightarrow> a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow>  (\<lambda>x y. Sup X {x, y}) ( (\<lambda>x y. Sup X {x, y}) a b) b =  (\<lambda>x y. Sup X {x, y}) a b"
  by (metis bsup_assoc1 bsup_idem1)

lemma bsup_ge1:
  "is_sup_semilattice X\<Longrightarrow>a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> a \<le> b \<Longrightarrow>  Sup X {a, b} = b"
  by (simp add: Orderings.order_eq_iff bsup_geI2 bsup_geI3)

lemma bsup_ge2:
  "is_sup_semilattice X \<Longrightarrow>a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> b \<le> a \<Longrightarrow> Sup X {a, b} = a"
  by (simp add: dual_order.eq_iff bsup_iff bsup_geI1)

lemma bsup_finite:
  assumes A0: "\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> is_sup X {a1, a2} (Sup X {a1, a2})" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X"
  shows "is_sup X A (Sup X A)"
  using A1 A2 A3 
proof (induct A rule: finite_ne_induct)
  case (singleton x)
  then show ?case using A0 by force
next
  case (insert x F)
  obtain s1 where B0:"is_sup X F s1"
    using insert.hyps(4) insert.prems by blast
  have B1:"s1 \<in> X"
    using B0 is_supD111 by auto
  obtain s2 where B2:"is_sup X {s1, x} s2"
    using A0 B1 insert.prems by auto
  have B3:"s2 \<in> Upper_Bounds X (insert x F)"
    by (meson B0 B2 insertI2 is_supD1121 singleton_iff sup_insert62 ubd_mem_insert)
  have B4:"\<And>u. u \<in> Upper_Bounds X (insert x F) \<longrightarrow> s2 \<le> u"
    using B0 B2 sup_insert7 by blast
  have B3:"is_sup X (insert x F) s2"
    by (simp add: B3 B4 is_supI113)
  then show ?case
    by (simp add: sup_equality)
qed

lemma bsup_finite2:
  "\<lbrakk>is_sup_semilattice X;  A \<subseteq> X;A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow>  is_sup X A (Sup X A)"
  by (simp add: bsup_finite ssupD3)

lemma fsup_closedD1:
  "is_fsup_closed X A \<Longrightarrow> (\<And>a1 a2. a1 \<in> A\<Longrightarrow> a2 \<in> A \<Longrightarrow> Sup X {a1, a2} \<in> A)"
  by (simp add: is_fsup_closed_def)

lemma finite_sup_closed2:
  assumes A0: "\<And>a1 a2. a1 \<in> A \<Longrightarrow> a2 \<in> A \<Longrightarrow> Sup X {a1, a2} \<in> A" and 
          A1: "finite E" and
          A2: "E \<noteq> {}" and
          A3: "E \<subseteq> A" and
          A4: "A \<subseteq> X" and
          A5: "is_sup_semilattice X"
  shows "Sup X E \<in> A"
  using A1 A2 A3 A4 A5
proof (induct E rule: finite_ne_induct)
  case (singleton x)
  then show ?case
    using A0 by fastforce
next
  case (insert x F)
  obtain s where A6: "is_sup X F s"
    by (meson A4 A5 bsup_finite2 insert.hyps(1) insert.hyps(2) insert.prems(1) insert_subset order_trans)
  have B0: "s \<in> A"
    using A4 A5 A6 sup_equality insert.hyps(4) insert.prems(1) by blast
  have B1: "x \<in> A"
    using insert.prems(1) by auto
  obtain t where A7: "is_sup X {x, s} t"
    by (meson A4 A5 A6 B1 is_supD111 is_sup_semilattice_def subset_eq)
  have B2: "t \<in> A"
    using A0 A7 B0 B1 sup_equality by blast
  have B3: "t \<in> Upper_Bounds X (insert x F)"
    by (metis A6 A7 Upper_Bounds_mem_iff is_supD111 is_supD112 is_supD5 ub_double ub_insert)
  have B4: "\<And>y. y \<in> Upper_Bounds X (insert x F) \<longrightarrow> t \<le> y"
    by (metis A6 A7 Upper_BoundsD3 Upper_Bounds_mem_iff2 insertCI is_supD42 ub_double)
  have B5: "is_sup X (insert x F) t"
    by (simp add: B3 B4 is_supI113)
  then show ?case
    by (simp add: B2 sup_equality)
qed


lemma sup_semilattice_fsup_closed:
  "\<lbrakk>is_fsup_closed X A; A \<subseteq> X; E \<subseteq> A; finite E; E \<noteq> {}; is_sup_semilattice X\<rbrakk> \<Longrightarrow> Sup X E \<in> A "
  by (metis finite_sup_closed2 is_fsup_closed_def)


context fixes X::"'a::order set" and
              x x1 y y1 z::"'a::order" 
        assumes elem:"x \<in> X  \<and> x1 \<in> X \<and> y \<in> X \<and> y1 \<in> X \<and> z \<in> X" and
                sup_latt:"is_sup_semilattice X"
begin

context assumes 
  le:"x \<le> y"
begin
lemma ssup_leD1:
  "Sup X {z, x} \<le> Sup X {z, y}"
  by (simp add: bsup_geI1 bsup_geI2 bsup_iff le local.elem ssupD4 sup_latt)

lemma ssup_leD2:
  "Sup X {x, z} \<le> Sup X {y, z}"
  by (simp add: bsup_geI1 bsup_geI2 bsup_geI3 le local.elem ssupD4 sup_latt)

lemma ssup_leD3:
  "Sup X {x, z} \<le> Sup X {z, x}"
  by (simp add: bsup_geI1 bsup_geI2 bsup_iff le local.elem ssupD4 sup_latt)

lemma ssup_leD4:
  "Sup X {z, x} \<le> Sup X {y, z}"
  by (simp add: bsup_geI1 bsup_geI2 bsup_iff le local.elem ssupD4 sup_latt)

end

context assumes 
  le:"x\<le> z"
begin
lemma ssup_leD5:
  "x \<le> Sup X {y, z}"
  by (simp add: bsup_geI2 le local.elem sup_latt)

lemma ssup_leD6:
  "x \<le> Sup X {z, y}"
  by (simp add: bsup_geI1 le local.elem sup_latt)
end


context assumes 
  le:"x\<le>x1 \<and> y\<le>y1"
begin

lemma ssup_leD7:
  "Sup X {x, y} \<le> Sup X {x1, y1}"
  by (simp add: bsup_geI1 bsup_geI2 bsup_geI3 le local.elem ssupD4 sup_latt)

lemma ssup_leD8:
  "Sup X {x, y} \<le> Sup X {y1, x1}"
  by (simp add: bsup_geI1 bsup_geI2 bsup_geI3 le local.elem ssupD4 sup_latt)

end

context assumes 
  le:"x\<le>z \<and> y\<le>z"
begin
lemma ssup_leD9:
  "Sup X {x, y} \<le> z"
  by (simp add: bsup_geI3 le local.elem sup_latt)
end

end



definition is_lattice::"'a::order set \<Rightarrow> bool" where
  "is_lattice X \<equiv> ((X \<noteq> {}) \<and> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>x. is_inf X {a, b} x) \<and>  (\<exists>x. is_sup X {a, b} x)))"


lemma lattI1:
  "\<lbrakk>X \<noteq> {}; (\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  (\<exists>x. is_inf X {a, b} x) \<and>  (\<exists>x. is_sup X {a, b} x))\<rbrakk> \<Longrightarrow> is_lattice X"
  by (simp add: is_lattice_def)

lemma lattI2:
  "\<lbrakk>is_inf_semilattice X; is_sup_semilattice X\<rbrakk> \<Longrightarrow> is_lattice X"
  by (simp add: is_inf_semilattice_def is_sup_semilattice_def lattI1)

lemma lattD1:
  "is_lattice X \<Longrightarrow> X \<noteq> {}"
  by (simp add: is_lattice_def)

lemma lattD21:
  "\<lbrakk>is_lattice X;  a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  (\<exists>x. is_inf X {a, b} x) "
  by (simp add: is_lattice_def)

lemma lattD22:
  "\<lbrakk>is_lattice X;  a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  (\<exists>x. is_sup X {a, b} x) "
  by (simp add: is_lattice_def)

lemma lattD31:
  "\<lbrakk>is_lattice X;  a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  is_inf X {a, b} (Inf X {a, b}) "
  using inf_equality lattD21 by blast

lemma lattD32:
  "\<lbrakk>is_lattice X;  a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  is_sup X {a, b} (Sup X {a, b}) "
  using sup_equality lattD22 by blast

lemma lattD41:
  "is_lattice X \<Longrightarrow> is_inf_semilattice X"
  by (simp add: is_inf_semilattice_def is_lattice_def)

lemma lattD42:
  "is_lattice X \<Longrightarrow> is_sup_semilattice X"
  by (simp add: is_sup_semilattice_def is_lattice_def)

lemma latt_iff:
  "is_lattice X \<longleftrightarrow> (is_inf_semilattice X) \<and> (is_sup_semilattice X)"
  using lattD41 lattD42 lattI2 by blast

definition is_cinf_semilattice::"'a::order set \<Rightarrow> bool" where
  "is_cinf_semilattice X \<equiv> (X \<noteq> {}) \<and> (\<forall>A. A \<subseteq> X \<and> A \<noteq> {} \<longrightarrow> (\<exists>x. is_inf X A x))"

definition is_cinf_closed::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_cinf_closed X A \<equiv> (\<forall>E. E \<subseteq> A\<longrightarrow> E \<noteq>{} \<longrightarrow> Inf X E \<in> A)"

lemma cinf_closedI:
  "\<lbrakk> (\<And>E.  \<lbrakk>E \<subseteq> A; E \<noteq> {}\<rbrakk> \<Longrightarrow>  Inf X E \<in> A)\<rbrakk> \<Longrightarrow> is_cinf_closed X A"
  by (simp add: is_cinf_closed_def)

lemma cinf_closedE:
  "\<lbrakk>is_cinf_closed X A; E \<subseteq> A; E \<noteq> {}\<rbrakk> \<Longrightarrow> Inf X E \<in> A"
  by (simp add: is_cinf_closed_def)

definition is_csup_semilattice::"'a::order set \<Rightarrow> bool" where
  "is_csup_semilattice X \<equiv> (X \<noteq> {}) \<and> (\<forall>A. A \<subseteq> X \<and> A \<noteq> {} \<longrightarrow> (\<exists>x. is_sup X A x))"

definition is_csup_closed::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_csup_closed X A \<equiv> (\<forall>E. E \<subseteq> A \<longrightarrow> E \<noteq>{} \<longrightarrow> Inf X E \<in> A)"

definition is_clattice::"'a::order set \<Rightarrow> bool" where
  "is_clattice X \<equiv> (X \<noteq> {}) \<and> (\<forall>A. A \<subseteq> X \<longrightarrow> (\<exists>s. is_sup X A s))"

lemma cinfI1:
  "\<lbrakk>X \<noteq> {}; (\<forall>A. A \<subseteq> X \<and> A \<noteq> {} \<longrightarrow> (\<exists>x. is_inf X A x)) \<rbrakk> \<Longrightarrow> is_cinf_semilattice X"
  by (simp add: is_cinf_semilattice_def)

lemma csupI1:
  "\<lbrakk>X \<noteq> {}; (\<forall>A. A \<subseteq> X \<and> A \<noteq> {} \<longrightarrow> (\<exists>x. is_sup X A x)) \<rbrakk> \<Longrightarrow> is_csup_semilattice X"
  by (simp add: is_csup_semilattice_def)

lemma clatI1:
  "\<lbrakk>X \<noteq> {}; (\<forall>A. A \<subseteq> X \<longrightarrow> (\<exists>x. is_sup X A x)) \<rbrakk> \<Longrightarrow> is_clattice X"
  by (simp add: is_clattice_def)

lemma clatI2:
  "\<lbrakk>X \<noteq> {}; (\<forall>A. A \<subseteq> X \<longrightarrow> (\<exists>x. is_inf X A x))\<rbrakk> \<Longrightarrow> is_clattice X"
  by (meson Upper_Bounds_sub clatI1 sup_if_inf_ub)

lemma cinfD1:
  "is_cinf_semilattice X \<Longrightarrow> X \<noteq> {}"
  by (simp add: is_cinf_semilattice_def)

lemma csupD1:
  "is_csup_semilattice X \<Longrightarrow> X \<noteq> {}"
  by (simp add: is_csup_semilattice_def)

lemma clatD1:
  "is_clattice X \<Longrightarrow> X \<noteq> {}"
  by (simp add: is_clattice_def)

lemma cinfD2:
  "\<lbrakk>is_cinf_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_inf X A x)"
  by (simp add: is_cinf_semilattice_def)

lemma csupD2:
  "\<lbrakk>is_csup_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup X A x)"
  by (simp add: is_csup_semilattice_def)

lemma clatD21:
  "\<lbrakk>is_clattice X; A \<subseteq> X\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup X A x)"
  by (simp add: is_clattice_def)

lemma cinfD3:
  "is_cinf_semilattice X \<Longrightarrow> (\<exists>x. is_least X x)"
  by (metis inf_min_eq2 is_cinf_semilattice_def order_refl)

lemma csupD3:
  "is_csup_semilattice X \<Longrightarrow> (\<exists>x. is_greatest X x)"
  by (metis is_csup_semilattice_def order_refl sup_max_eq2)

lemma cinf_sup:
  "\<lbrakk>is_cinf_semilattice X; A \<subseteq> X; Upper_Bounds X A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup X A x)"
  by (meson Upper_Bounds_sub cinfD2 sup_if_inf_ub)

lemma csup_inf:
  "\<lbrakk>is_csup_semilattice X; A \<subseteq> X; Lower_Bounds X A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_inf X A x)"
  by (meson Lower_Bounds_sub csupD2 inf_if_sup_lb)

lemma clatD22:
  "\<lbrakk>is_clattice X; A \<subseteq> X\<rbrakk> \<Longrightarrow> (\<exists>x. is_inf X A x)"
  by (meson Lower_Bounds_sub clatD21 inf_if_sup_lb)

lemma clatD31:
  "\<lbrakk>is_clattice X\<rbrakk> \<Longrightarrow> is_greatest X (Inf X {})"
  by (metis clatD22 empty_subsetI inf_empty inf_equality)

lemma clatD32:
  "\<lbrakk>is_clattice X\<rbrakk> \<Longrightarrow> is_least X (Sup X {})"
  by (metis clatD21 empty_subsetI sup_empty sup_equality)

lemma clatI31:
  "\<lbrakk>is_cinf_semilattice X; is_greatest X (Inf X {})\<rbrakk> \<Longrightarrow> is_clattice X"
  by (metis cinfD1 cinf_sup clatI1 inf_empty sup_if_inf_ub)

lemma clatI32:
  "\<lbrakk>is_csup_semilattice X; is_least X (Sup X {})\<rbrakk> \<Longrightarrow> is_clattice X"
  by (metis clatI1 is_csup_semilattice_def sup_empty)

lemma cinfD41:
  "\<lbrakk>is_cinf_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Inf X A lb A "
  by (metis cinfD2 inf_equality is_infD112)

lemma cinfD42:
  "\<lbrakk>is_cinf_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Inf X A \<in> X "
  by (metis cinfD2 inf_equality is_infD111)

lemma cinfD43:
  "\<lbrakk>is_cinf_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Inf X A \<in> Lower_Bounds X A "
  by (simp add: Lower_Bounds_mem_iff cinfD41 cinfD42)

lemma cinfD44:
  "\<lbrakk>is_cinf_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_inf X A (Inf X A)"
  by (metis cinfD2 inf_equality)    

lemma csupD41:
  "\<lbrakk>is_csup_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Sup X A ub A "
  by (metis csupD2 is_supD112 sup_equality)

lemma csupD42:
  "\<lbrakk>is_csup_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Sup X A \<in> X "
  by (metis csupD2 sup_equality is_supD111)

lemma csupD43:
  "\<lbrakk>is_csup_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Sup X A \<in> Upper_Bounds X A "
  by (simp add: Upper_Bounds_mem_iff csupD41 csupD42)

lemma csupD44:
  "\<lbrakk>is_csup_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_sup X A (Sup X A)"
  by (metis csupD2 sup_equality)    

lemma cinf_sinf:
  "is_cinf_semilattice X \<Longrightarrow> is_inf_semilattice X"
  by (simp add: is_cinf_semilattice_def is_inf_semilattice_def)

lemma csup_fsup:
  "is_csup_semilattice X \<Longrightarrow> is_sup_semilattice X"
  by (simp add: is_csup_semilattice_def is_sup_semilattice_def)

section Locales
subsection Poset


locale inf_semilattice=
  fixes X
  assumes inf_ex:"is_inf_semilattice X"
begin
definition inf::"'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "inf a b \<equiv> Inf X {a, b}"


lemma binf_assoc1b:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow>  inf (inf a b) c = inf a (inf b c)"
  by (simp add: binf_assoc1 inf_ex inf_def)

lemma binf_assoc2b:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow>  inf a (inf b c) = inf b (inf a c)"
  by (simp add: binf_assoc2 inf_ex inf_def)

lemma binf_leI1b:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X; a \<le> c\<rbrakk>  \<Longrightarrow>inf a b \<le> c"
  by (simp add: binary_infD21 sinfD3 sinfD4 inf_def inf_ex)

lemma binf_leI2b:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X; b \<le> c\<rbrakk> \<Longrightarrow>inf a b \<le> c"
  by (simp add: binary_infD22 sinfD3 sinfD4 inf_def inf_ex)

lemma binf_leI3b:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X; c \<le>a; c \<le> b\<rbrakk>  \<Longrightarrow>c \<le>inf a b"
  by (simp add: binary_infD4 sinfD3 sinfD4 inf_def inf_ex)

lemma binf_iffb:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk>  \<Longrightarrow> (c \<le> inf a b \<longleftrightarrow> c \<le> a \<and> c \<le> b)"
  by (simp add: binary_infD4 sinfD3 sinfD4 inf_def inf_ex)

lemma binf_commute2b:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow>  inf a b =inf b a"
  by (simp add: insert_commute inf_def)

lemma binf_idem1b:
  "a\<in> X \<Longrightarrow>inf a a = a"
  by (simp add:  inf_equality inf_singleton inf_def)

lemma binf_idem2b:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> inf a (inf a b) = inf a b"
  by (simp add: binf_idem2 inf_ex inf_def)

lemma binf_idem3b:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> inf (inf a b) b = inf a b"
  by (simp add: inf_def inf_ex binf_idem3)

lemma binf_lt1b:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> a \<le> b \<Longrightarrow> inf a b = a"
  by (simp add: binf_lt1 inf_def inf_ex)

lemma binf_lt2b:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> b \<le> a \<Longrightarrow> inf a b = b"
  by (simp add: binf_lt2 inf_ex inf_def)

lemma finite_inf1:
  "\<lbrakk>A \<subseteq> X; A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow>  is_inf X A (Inf X A)"
  by (simp add: binf_finite2 inf_ex)

lemma finite_inf2:
  "\<lbrakk>A \<subseteq> X; A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow>  (\<exists>i. is_inf X A i)"
  using finite_inf1 by blast


end

locale sup_semilattice=  
  fixes X
  assumes sup_ex:"is_sup_semilattice X"
begin
definition sup::"'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "sup a b \<equiv> Sup X {a, b}"

lemma bsup_commuteb:
  "\<lbrakk>a \<in> X ; b \<in> X\<rbrakk> \<Longrightarrow>sup a b = sup b a"
   by (simp add: insert_commute sup_def)

lemma bsup_geI1b:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X; a \<ge> c\<rbrakk>  \<Longrightarrow>c \<le> sup a b"
  by (simp add: bsup_geI1 sup_def sup_ex)

lemma bsup_geI2b:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X; b \<ge> c\<rbrakk>  \<Longrightarrow> c \<le> sup a b"
  by (simp add: bsup_geI2 sup_def sup_ex)

lemma bsup_geI3:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X; c \<ge>a; c \<ge> b\<rbrakk> \<Longrightarrow>sup a b \<le> c"
  by (simp add: bsup_geI3 sup_def sup_ex)

lemma bsup_iffb:
  "\<lbrakk> a \<in> X; b \<in> X; c \<in> X\<rbrakk>  \<Longrightarrow> (sup a b \<le> c \<longleftrightarrow> a \<le> c \<and> b \<le> c)"
  by (simp add: bsup_iff sup_def sup_ex)

lemma bsup_assoc1b:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow>  sup (sup a b) c =  sup a (sup b c)"
  by (simp add: bsup_assoc1 sup_def sup_ex)

lemma bsup_assoc2b:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk>  \<Longrightarrow>  sup a (sup b c) = sup b (sup a c)"
  by (simp add: bsup_assoc2 sup_def sup_ex)

lemma bsup_idem1b:
  "a\<in> X \<Longrightarrow> sup a a = a"
  by (simp add: sup_def sup_singleton3)

lemma bsup_idem2b:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow>  sup a (sup a b) =  sup a b"
  by (simp add: bsup_idem2 sup_def sup_ex)

lemma bsup_idem3b:
  " a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> sup (sup a b) b = sup a b"
  by (simp add: bsup_idem3 sup_def sup_ex)

lemma bsup_ge1b:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> a \<le> b \<Longrightarrow>  sup a b = b"
  by (simp add: bsup_ge1 sup_def sup_ex)

lemma bsup_ge2b:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> b \<le> a \<Longrightarrow>  sup a b = a"
  by (simp add: bsup_ge2 sup_def sup_ex)

lemma finite_sup1:
  "\<lbrakk>A \<subseteq> X; A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow>  is_sup X A (Sup X A)"
  by (simp add: bsup_finite2 sup_ex)

lemma finite_sup2:
  "\<lbrakk>A \<subseteq> X; A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow>  (\<exists>s. is_sup X A s)"
  using finite_sup1 by blast

end

locale lattice=inf_semilattice+sup_semilattice
begin

lemma lattice_is_sinfs:
  "is_inf_semilattice X"
  by (simp add: inf_ex)

lemma lattice_is_ssups:
  "is_sup_semilattice X"
  by (simp add: sup_ex)

end

locale cinf_semilattice= fixes X
  assumes cinf_ex:"is_cinf_semilattice X"
begin

lemma cinfD1b:
  "X \<noteq> {}"
  by (simp add: cinf_ex cinfD1)

lemma cinfD2b:
  "\<lbrakk>A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_inf X A x)"
  by (simp add: cinf_ex cinfD2)

lemma cinfD3b:
  "(\<exists>x. is_least X x)"
  by (simp add: cinf_ex cinfD3)


lemma cinf_supb:
  "\<lbrakk>A \<subseteq> X; Upper_Bounds X A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup X A x)"
  by (simp add:cinf_ex cinf_sup)

lemma cinfD41b:
  "\<lbrakk>A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Inf X A lb A "
  by (simp add:cinf_ex cinfD41)

lemma cinfD42b:
  "\<lbrakk> A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Inf X A \<in> X "
  by (simp add:cinf_ex cinfD42)

lemma cinfD43b:
  "\<lbrakk> A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Inf X A \<in> Lower_Bounds X A "
  by (simp add:cinf_ex cinfD43)

lemma cinfD44b:
  "\<lbrakk> A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_inf X A (Inf X A)"
  by (simp add:cinf_ex cinfD44)

end

sublocale cinf_semilattice \<subseteq> inf_semilattice
  by(unfold_locales, simp add:is_inf_semilattice_def cinfD1 cinfD2 cinf_ex)

locale csup_semilattice=fixes X
  assumes csup_ex:"is_csup_semilattice X"
begin
lemma csupD1b:
  "X \<noteq> {}"
  by (simp add: csup_ex csupD1)

lemma csupD2b:
  "\<lbrakk>A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup X A x)"
  by (simp add: csup_ex csupD2)

lemma csupD3b:
  "\<lbrakk>A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_greatest X x)"
  by (simp add: csup_ex csupD3)

lemma csup_infb:
  "\<lbrakk>A \<subseteq> X; Lower_Bounds X A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_inf X A x)"
  by (simp add:csup_ex csup_inf)

lemma csupD41b:
  "\<lbrakk>A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Sup X A ub A "
  by (simp add:csup_ex csupD41)

lemma csupD42b:
  "\<lbrakk> A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Sup X A \<in> X "
  by (simp add:csup_ex csupD42)

lemma csupD43b:
  "\<lbrakk> A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Sup X A \<in> Upper_Bounds X A "
  by (simp add:csup_ex csupD43)

lemma csupD44b:
  "\<lbrakk> A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_sup X A (Sup X A)"
  by (simp add:csup_ex csupD44)

end


sublocale csup_semilattice \<subseteq> sup_semilattice
  by(unfold_locales, simp add:is_sup_semilattice_def csupD1 csupD2 csup_ex)

locale complete_lattice=cinf_semilattice+csup_semilattice
begin

lemma inf_empty_locale:
  "Inf X {} = Greatest X"
  by (simp add: Greatest_def Inf_def Lower_Bounds_empty is_inf_def)           

lemma sup_empty_locale:
  "Sup X {} = Least X"
  by (simp add: Least_def Sup_def Upper_Bounds_empty is_sup_def)

end

sublocale complete_lattice \<subseteq> lattice by(unfold_locales)



locale cinf_semilattice_top=cinf_semilattice+
  assumes ex_top:"\<exists>top. is_greatest X top"

locale csup_semilattice_bot=csup_semilattice+
  assumes ex_bot:"\<exists>bot. is_least X bot"

sublocale cinf_semilattice_top \<subseteq> complete_lattice
  by (unfold_locales, metis cinfD1b cinf_ex clatD21 clatI31 csupI1 inf_empty inf_equality ex_top)

sublocale csup_semilattice_bot \<subseteq> complete_lattice
  by (unfold_locales, metis csupD1b csup_ex clatD22 clatI32 cinfI1 sup_empty sup_equality ex_bot)

locale inf_semilattice_top=inf_semilattice+
  assumes ex_top:"\<exists>top. is_greatest X top"

locale sup_semilattice_bot=sup_semilattice+
  assumes ex_bot:"\<exists>bot. is_least X bot"


locale inf_semilattice_bot=inf_semilattice+
  assumes  ex_bot:"\<exists>bot. is_least X bot"

locale sup_semilattice_top=sup_semilattice+
  assumes ex_top:"\<exists>top. is_greatest X top"


sublocale cinf_semilattice_top \<subseteq> inf_semilattice_top
  by (unfold_locales, simp add: ex_top)

sublocale csup_semilattice_bot \<subseteq> sup_semilattice_bot
  by (unfold_locales, simp add: ex_bot)

section Functions
subsection Isotonicity
definition is_isotone::"  'a::order set\<Rightarrow>('a::order \<Rightarrow> 'b::order)  \<Rightarrow> bool" where
  "is_isotone X f \<equiv> (\<forall>x1 x2. x1 \<in> X \<and> x2 \<in> X \<and> x1 \<le> x2 \<longrightarrow> (f x1) \<le> (f x2))"

lemma isotoneD1:
  "\<lbrakk>is_isotone X f; x1 \<in> X; x2 \<in> X; x1 \<le> x2 \<rbrakk> \<Longrightarrow> f x1 \<le> f x2"
  by (simp add: is_isotone_def)

lemma isotoneD2:
  "A \<subseteq> X \<Longrightarrow> is_isotone X f \<Longrightarrow> is_isotone A f"
  by (simp add: is_isotone_def subset_eq)

lemma isotoneI1:
  "(\<And>x1 x2. \<lbrakk>x1 \<in> X; x2 \<in> X; x1 \<le> x2\<rbrakk> \<Longrightarrow> f x1 \<le> f x2) \<Longrightarrow> is_isotone X f"
  by (simp add: is_isotone_def)

lemma isotoneD31:
  "\<lbrakk>is_isotone X f; b ub A; A \<subseteq> X; b \<in> X \<rbrakk> \<Longrightarrow> (f b) ub (f`A) "
  by(auto simp add:ub_def image_iff is_isotone_def subset_iff)

lemma isotoneD32:
  "\<lbrakk>is_isotone X f; b lb A; A \<subseteq> X; b \<in> X \<rbrakk> \<Longrightarrow> (f b) lb (f`A) "
  by(auto simp add:lb_def image_iff is_isotone_def subset_iff)

lemma isotoneD41:
  "\<lbrakk>is_isotone X f; b \<in> Upper_Bounds X A; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f b) \<in> Upper_Bounds (f`X) (f`A)"
  by (simp add: Upper_Bounds_mem_iff isotoneD31)
             
lemma isotoneD42:
  "\<lbrakk>is_isotone X f; b \<in> Lower_Bounds X A; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f b) \<in> Lower_Bounds (f`X) (f`A)"
  by (simp add: Lower_Bounds_mem_iff isotoneD32)

lemma isotoneD51:
  "\<lbrakk>is_isotone X f; is_least A x; A \<subseteq> X\<rbrakk> \<Longrightarrow> is_least (f`A) (f x)"
  by (simp add: is_least_def isotoneD2 isotoneD42)   

lemma isotoneD52:
  "\<lbrakk>is_isotone X f; is_greatest A x; A \<subseteq> X\<rbrakk> \<Longrightarrow> is_greatest (f`A) (f x)"
  by (simp add: is_greatest_def isotoneD2 isotoneD41)

lemma isotoneD61:
  "\<lbrakk>is_isotone X f; is_sup X A x; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f x) ub f`A"
  by (simp add: is_supD112 isotoneD31 sup_iff2)

lemma isotoneD62:
  "\<lbrakk>is_isotone X f; is_inf X A x; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f x) lb f`A"
  by (simp add: is_infD112 isotoneD32 inf_iff2)



subsection Extensivity
definition is_extensive::" 'a::order set \<Rightarrow>  ('a::order \<Rightarrow> 'a::order) \<Rightarrow> bool" where
  "is_extensive X f \<equiv> (\<forall>x. x \<in> X \<longrightarrow> x \<le> f x)"

lemma extensiveI1:
  "\<lbrakk>(\<And>x. x \<in> X \<Longrightarrow> x \<le> f x)\<rbrakk> \<Longrightarrow> is_extensive X f"
  by (simp add: is_extensive_def)

lemma extensiveD1:
  "\<lbrakk>is_extensive X f; x \<in> X\<rbrakk> \<Longrightarrow> x \<le> f x"
  by (simp add: is_extensive_def)         

lemma extensiveD2:
  "\<lbrakk>is_extensive X f; b ub f`X\<rbrakk> \<Longrightarrow> b ub X"
  by (metis dual_order.trans extensiveD1 imageI ub_def)

lemma extensiveD3:
  "\<lbrakk>is_extensive X f; x \<in> X; y \<in> X; x \<le> y\<rbrakk> \<Longrightarrow> x \<le> f y"
  using extensiveD1 order_trans by blast

lemma extensiveD4:
  "\<lbrakk>is_extensive X f;  x1 \<in> X;x2 \<in> X; (f x2) \<in> X;  f x1 \<le> f x2\<rbrakk> \<Longrightarrow> x1  \<le> (f x2)"
  by (meson dual_order.trans extensiveD1)

lemma extensive_ub_imp:
  "\<lbrakk>is_extensive X f ; (f`X \<subseteq> X); A \<subseteq> X ; b \<in> Upper_Bounds (f`X)  (f`A) \<rbrakk> \<Longrightarrow> b \<in> Upper_Bounds X A"
  by (metis Upper_Bounds_mem_iff extensiveD1 extensiveD2 extensiveI1 in_mono)

lemma extensive_ub_imp2:
  "\<lbrakk>is_extensive X f; (f`X \<subseteq> X); A \<subseteq> X; b \<in> Upper_Bounds X  (f`A)\<rbrakk> \<Longrightarrow> b \<in> Upper_Bounds X A"
  by (metis Upper_Bounds_mem_iff extensiveD2 in_mono is_extensive_def)

lemma is_iso_extD1:
  "\<lbrakk>is_isotone X f;  is_extensive X f;  (f`X \<subseteq> X);  x \<in> X\<rbrakk> \<Longrightarrow> f x \<le> f (f x)"
  by (simp add: extensiveD3 image_subset_iff)

lemma is_iso_extD2:
  "\<lbrakk>is_isotone X f; is_extensive X f;  (f`X \<subseteq> X);  x1 \<in> X;  x2 \<in> X;  x1 \<le> f x2\<rbrakk> \<Longrightarrow> f x1  \<le> f (f x2)"
  by (simp add: image_subset_iff isotoneD1)

lemma is_iso_sup:
  "is_isotone X f \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_sup X A x \<Longrightarrow> is_sup (f`X) (f`A) y  \<Longrightarrow> y \<le> f x"
  by (simp add: Upper_Bounds_mem_iff is_sup_def isotoneD31 least_iff)

lemma is_iso_inf:
  "is_isotone X f \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_inf A X x \<Longrightarrow> is_inf (f`X) (f`A) y  \<Longrightarrow> f x \<le> y"
  by(simp add: is_inf_def Lower_Bounds_mem_iff lb_ant2 subsetD greatest_iff isotoneD32)


subsection Idempotency
definition is_idempotent::"'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_idempotent X f \<equiv> (\<forall>x. x \<in> X \<longrightarrow> f (f x) = f x)"

lemma idempotentI1:
  "(\<And>x. x \<in> X \<Longrightarrow> f (f x) = f x) \<Longrightarrow> is_idempotent X f"
  by (simp add: is_idempotent_def)

lemma idempotentD1:
  "\<lbrakk>is_idempotent X f; x \<in> X \<rbrakk> \<Longrightarrow>  f (f x) = f x"
  by (simp add: is_idempotent_def)

lemma idempotentD2:
  "\<lbrakk>is_idempotent X f; x \<in> X; f x = y\<rbrakk> \<Longrightarrow>  f y = y"
  by (auto simp add: idempotentD1)

lemma idempotentD3:
  "\<lbrakk>is_idempotent X f; y \<in> f`X \<rbrakk> \<Longrightarrow>  f y = y"
  by (auto simp add: is_idempotent_def)
          
lemma idempotentD4:
  "\<lbrakk>is_idempotent X f; P y; y \<in> f`X \<rbrakk> \<Longrightarrow>  P (f y)"
  by (auto simp add: is_idempotent_def)
 
lemma idempotentD5:
  "\<lbrakk>is_idempotent X f; x \<in> X; f x = x \<rbrakk> \<Longrightarrow> x \<in> f`X"
  by (simp add: rev_image_eqI)

lemma iso_idemD1:
  "\<lbrakk>is_isotone X f; is_idempotent X f; x \<in> X\<rbrakk> \<Longrightarrow> f x \<le> f (f x)"
  by (simp add: idempotentD1)

lemma iso_idemD2:
  "\<lbrakk>is_isotone X f; is_idempotent X f;  x1 \<in> X;x2 \<in> X; (f x2) \<in> X;  x1 \<le> f x2\<rbrakk> \<Longrightarrow> f x1  \<le> (f x2)"
   using idempotentD1[of X f x2] isotoneD1[of X f x1 "f x2"] by simp

lemma iso_idemD3:
  "\<lbrakk>is_isotone X f; is_idempotent X f; f`X \<subseteq> X; x1 \<in> X;x2 \<in> X;   x1 \<le> f x2\<rbrakk> \<Longrightarrow> f x1  \<le> (f x2)"
  by (simp add: image_subset_iff iso_idemD2)

lemma idemp_iff:
  "is_idempotent X f \<longleftrightarrow> (\<forall>x \<in> X. (f \<circ> f) x = f x)"
  using is_idempotent_def by auto

lemma idempotentI2:
  "\<lbrakk>is_extensive X f;is_isotone X f;  f`X \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> f (f x) \<le> f x)\<rbrakk> \<Longrightarrow> is_idempotent X f"
  by (simp add: is_idempotent_def is_iso_extD1 order_class.order_eq_iff)

lemma idempotent_isotoneD1:
  "\<lbrakk>is_idempotent X f; is_isotone X f;  f`X \<subseteq> X;  y \<in> f`X;  x \<in> X; x \<le> y\<rbrakk> \<Longrightarrow> f x \<le> y"
   using rev_subsetD[of "y" "f`X" "X"] isotoneD1[of "X" "f" "x" "y"] idempotentD3[of "X" "f" "y"] by simp

subsection Closures
definition is_closure::" 'a::order set \<Rightarrow>('a::order \<Rightarrow> 'a::order) \<Rightarrow>  bool" where
  "is_closure X f \<equiv> is_extensive X f \<and> is_idempotent X f \<and> is_isotone X f \<and> (f`X \<subseteq> X)"

definition closure_cond::"'a::order set \<Rightarrow> ('a::order \<Rightarrow> 'a::order ) \<Rightarrow> bool" where
  "closure_cond X f \<equiv> (\<forall>x1 x2. x1 \<in> X \<longrightarrow> x2 \<in> X \<longrightarrow> x1 \<le> f x2 \<longrightarrow> f x1 \<le> f x2)"

lemma closureI1:
  "\<lbrakk>is_extensive X f; is_idempotent X f; is_isotone X f;  (f`X \<subseteq> X)\<rbrakk> \<Longrightarrow> is_closure X f"
  by (simp add: is_closure_def)

lemma closureI2:
  "\<lbrakk>is_extensive X f; is_isotone X f;  f`X \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> f (f x) \<le> f x)\<rbrakk> \<Longrightarrow> is_closure X f"
  by (simp add: idempotentI2 is_closure_def)

lemma isotoneI2:
  "\<lbrakk>is_extensive X f;  closure_cond X f\<rbrakk> \<Longrightarrow> is_isotone X f"
  by (simp add: closure_cond_def extensiveD3 is_isotone_def)

lemma idempotentI3:
  "\<lbrakk>is_extensive X f;  f`X \<subseteq> X; closure_cond X f\<rbrakk> \<Longrightarrow> is_idempotent X f"
  by (simp add: closure_cond_def idempotentI2 image_subset_iff isotoneI2)

lemma closureI3:
  "\<lbrakk>is_extensive X f; f`X \<subseteq> X;  closure_cond X f\<rbrakk> \<Longrightarrow> is_closure X f"
  by (simp add: is_closure_def idempotentI3 isotoneI2)

lemma closureD1:
  "\<lbrakk>is_closure X f;  x \<in> X\<rbrakk> \<Longrightarrow> f x \<in> X"
  by (simp add: image_subset_iff is_closure_def)

lemma closureD2:
  "\<lbrakk>is_closure X f;  y \<in> f`X\<rbrakk> \<Longrightarrow> y \<in> X"
  by(simp add: is_closure_def[of "X" "f"] subsetD[of "f`X" "X" "y"])

lemma closureD3:
  "is_closure X f \<Longrightarrow> closure_cond X f"
  by(simp add:closure_cond_def[of X f] is_closure_def[of X f] iso_idemD3[of X f])

lemma closureD4:
  "\<lbrakk>is_closure X f; x \<in> X; y \<in> X; x \<le> y\<rbrakk> \<Longrightarrow> f x \<le> f y"
  by(simp add:is_closure_def isotoneD1[of "X" "f" "x" "y"])

lemma closureD5:
  "\<lbrakk>is_closure X f; x \<in> X\<rbrakk> \<Longrightarrow> x \<le> f x"
  by(simp add:is_closure_def is_extensive_def)

lemma closureD6:
  "\<lbrakk>is_closure X f;  x \<in> X\<rbrakk> \<Longrightarrow> f x = f( f x)"
  by(simp add:is_closure_def is_idempotent_def)

lemma closureD7:
  "\<lbrakk>is_closure X f; x \<in> X;  y \<in> (f`X) ;  x \<le> y\<rbrakk> \<Longrightarrow> f x \<le> y"
  by (simp add:is_closure_def[of "X" "f"] idempotent_isotoneD1[of "X" "f" "y" "x"])

lemma closureD8:
  "\<lbrakk>is_closure X f;  x \<in> X;  y \<in> (f`X) ;  f x \<le> y\<rbrakk> \<Longrightarrow>  x \<le> y"
  by (simp add:closureD5[of "X" "f" "x"] order_trans[of "x" "f x" "y"])

lemma cl_le_cl_iff_le:
  "\<lbrakk>is_closure X f; x \<in> X ; y  \<in> f`X\<rbrakk> \<Longrightarrow>  (x \<le> y \<longleftrightarrow> f x \<le> y)"
  by (meson closureD7 closureD8)

lemma closureD9:
  "\<lbrakk>is_closure X f;  y \<in> f`X\<rbrakk>  \<Longrightarrow> f y \<le> y"
  by (metis antisym_conv1 idempotentD3 is_closure_def nless_le)

lemma closureD10:
  "\<lbrakk>is_closure X f;  x \<in> X;  f x \<le> x\<rbrakk> \<Longrightarrow> x = f x"
  by (simp add: closureD5 dual_order.eq_iff)

lemma closureD11:
  "\<lbrakk>is_closure X f;  x \<in> X; f x \<le> x\<rbrakk> \<Longrightarrow> x \<in> f `X"
  using closureD10 by blast

lemma closureD12:
  "\<lbrakk>is_closure X f;  x \<in> X\<rbrakk> \<Longrightarrow> (x \<in> (f`X) \<longleftrightarrow> f x \<le> x )"
  using closureD11 closureD9 by blast

lemma closureD13:
  "\<lbrakk>is_closure X f; x \<in> X; f x \<le> x\<rbrakk> \<Longrightarrow> f x = x"
  by (simp add: closureD5 dual_order.eq_iff)

lemma cl_sup_eq_sup_cl1:
  "\<lbrakk>is_closure X f; is_sup X A s; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f s) \<in> Upper_Bounds (f`X) (f`A)"
  by (simp add: is_closure_def is_supD11 isotoneD41)

lemma cl_inf_eq_inf_cl1:
  "\<lbrakk>is_closure X f;  is_inf X A i;  A \<subseteq> X\<rbrakk> \<Longrightarrow> (f i) \<in> Lower_Bounds (f`X) (f`A)"
  by (simp add: is_closure_def is_infD11 isotoneD42)

lemma cl_sup_eq_sup_cl2:
  "\<lbrakk>is_closure X f;  is_sup X A s; b \<in> Upper_Bounds (f`X) (f`A); A \<subseteq> X\<rbrakk> \<Longrightarrow> s \<le> b"
  by(simp add: is_closure_def[of "X" "f"] Upper_BoundsD2[of "b" "f`X" "f`A"]  closureD2[of "X" "f" "b"] extensive_ub_imp[of "X" "f" "A" "b"]  is_supD121[of "X" "A" "s"] )

lemma cl_sup_eq_sup_cl3:
  "\<lbrakk>is_closure X f;  is_sup X A s; b \<in> Upper_Bounds (f`X) (f`A);A \<subseteq> X\<rbrakk> \<Longrightarrow> f s \<le> b"
  by (meson Upper_BoundsD2 cl_sup_eq_sup_cl2 closureD7 is_supD111)

(*
cl_sup_eq_sup and cl_sup_ge_sup_cl have converses in extensiveI4 idempotentI4 and isotoneI4 

*)

lemma cl_sup_eq_sup:
  "\<lbrakk>is_closure X f;  is_sup X A s;A \<subseteq> X\<rbrakk> \<Longrightarrow> is_sup (f`X) (f`A) (f s)"
  by(simp add:is_sup_def[of "f`X" "f`A" "f s"] cl_sup_eq_sup_cl1 cl_sup_eq_sup_cl3 is_least_def Lower_Bounds_mem_iff2)
         
lemma closure_iff2:
  "is_closure X f \<longleftrightarrow> (f`X \<subseteq> X) \<and> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. x1 \<le> f x2 \<longleftrightarrow> f x1 \<le> f x2)"
  by (meson closureD3 closureI3 closure_cond_def dual_order.trans is_closure_def is_extensive_def order_refl)

lemma cl_sup_ge_sup_cl11:
  "\<lbrakk>is_closure X f; is_sup X A s1; is_sup X (f`A) s2; A \<subseteq> X\<rbrakk> \<Longrightarrow> s1 \<le> s2"
  by (meson extensive_ub_imp2 is_closure_def is_supD11 is_supD121)

lemma cl_sup_ge_sup_cl2:
  "\<lbrakk>is_closure X f;  is_sup X A s1;  is_sup X (f`A) s2; A \<subseteq>  X\<rbrakk> \<Longrightarrow> s2  \<le> f s1"
  by (meson closureD1 is_closure_def is_supD111 is_supD122 isotoneD61)

lemma cl_sup_ge_sup_cl3:
  "\<lbrakk>is_closure X f;  is_sup X A s1;  is_sup X (f`A) s2; A \<subseteq> X\<rbrakk> \<Longrightarrow> f s2  \<le> f s1"
  by (meson cl_sup_ge_sup_cl2 is_closure_def is_supD111 iso_idemD3)

lemma cl_sup_ge_sup_cl4:
  "\<lbrakk>is_closure X f; is_sup X A s1;  is_sup X (f`A) s2; A \<subseteq> X\<rbrakk> \<Longrightarrow> f s1  \<le> f s2"
  by (simp add: cl_sup_ge_sup_cl11 closureD4 is_supD111)

lemma cl_sup_ge_sup_cl:
  "\<lbrakk>is_closure X f; is_sup X A s1;  is_sup X (f`A) s2; A \<subseteq> X\<rbrakk> \<Longrightarrow> f s1  = f s2"
  by (simp add: cl_sup_ge_sup_cl3 cl_sup_ge_sup_cl4 dual_order.eq_iff)

lemma cl_inf_closed1:
  "\<lbrakk>is_closure X f; A \<subseteq> f`X; is_inf X A m\<rbrakk> \<Longrightarrow> f m \<le> m"
  by (simp add: closureD1 closureD7  in_mono is_infD111 is_infD1121 is_infD122 lb_def )
         
lemma cl_inf_closed2:
  "\<lbrakk>is_closure X f; A \<subseteq> f`X; is_inf X A m\<rbrakk> \<Longrightarrow> f m = m"
  by (simp add: cl_inf_closed1 closureD5 dual_order.eq_iff is_infD111)
         


subsection ClosureRanges

definition is_clr::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_clr C X \<equiv> (C \<noteq> {}) \<and> (C \<subseteq> X) \<and> (\<forall>x. x \<in> X \<longrightarrow> (\<exists>c. is_least (Upper_Bounds C {x}) c))"

lemma clrI1:
  "\<lbrakk>C \<noteq> {}; C \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> (\<exists>c. is_least (Upper_Bounds C {x}) c)) \<rbrakk> \<Longrightarrow> is_clr C X"
  by (simp add:is_clr_def)

lemma clrI2:
  "\<lbrakk>C \<noteq> {}; C \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> (\<exists>c. is_sup C {x} c)) \<rbrakk> \<Longrightarrow> is_clr C X"
  by (simp add: is_clr_def is_sup_def)

lemma clrE21:
  "is_clr C X \<Longrightarrow>(\<And>x. x \<in> X \<Longrightarrow> (\<exists>c. is_sup C {x} c))"
  by (simp add: is_clr_def is_sup_def)

lemma clr_iff_sup:
  "(is_clr C X) \<longleftrightarrow> ((C \<noteq> {}) \<and> (C \<subseteq> X) \<and> (\<forall>x. x \<in> X \<longrightarrow> (\<exists>c. is_sup C {x} c)))"
  by(simp add:is_clr_def is_sup_def)

lemma clr_memI1:
  "\<lbrakk>is_clr C X; x \<in> X; is_least (Upper_Bounds C {x}) x\<rbrakk> \<Longrightarrow> x \<in> C"
  by (simp add: is_supD111 is_sup_def)

lemma clr_memI2:
  "\<lbrakk>is_clr C X; x \<in> X;  is_sup C {x} x\<rbrakk> \<Longrightarrow> x \<in> C"
  by (simp add: is_supD111 is_sup_def)

lemma clrD1:
  "is_clr C X \<Longrightarrow> C \<noteq> {}"
  by (simp add:is_clr_def)

lemma clrD2:
  "is_clr C X \<Longrightarrow> C \<subseteq> X"
  by (simp add:is_clr_def)

lemma clrD2b:
  "is_clr C X \<Longrightarrow> x \<in> C \<Longrightarrow>x \<in> X"
  by(drule clrD2,simp add:subsetD)

lemma clrD3:
  "is_clr C X \<Longrightarrow>  (\<And>x. x \<in> X \<Longrightarrow> (\<exists>c. is_least (Upper_Bounds C {x}) c))"
  by (simp add:is_clr_def)

lemma clrD3b:
  "is_clr C X \<Longrightarrow>  (\<And>x. x \<in> X \<Longrightarrow> (\<exists>c. is_sup C {x} c))"
  by (simp add: clrD3 is_sup_def)

lemma clrD4:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> (\<exists>c. is_least (Upper_Bounds C {x}) c)"
  by (simp add:is_clr_def)

lemma clrD5:
  "is_clr C X \<Longrightarrow>  (\<And>x. x \<in> X  \<Longrightarrow> ((Upper_Bounds C {x}) \<noteq> {}))"
  by (simp add: clrD4 least_exD0)

lemma clrD6:
  "is_clr C X \<Longrightarrow>  x \<in> X \<Longrightarrow> (Upper_Bounds C {x}) \<noteq> {}"
  by (simp add: clrD5)

lemma clrD61:
  "is_clr C X \<Longrightarrow>  x \<in> X \<Longrightarrow> (\<exists>b \<in> C. b ub {x})"
  by (simp add: clrD6 upbd_neE2)

lemma clrD7:
  "is_clr C X \<Longrightarrow>  x \<in> X \<Longrightarrow> (\<exists>c \<in> C.  x \<le> c)"
  by (simp add: clrD6 upbd_neE3)

(*
lemma clrD7:
  "is_clr C X \<Longrightarrow>  x \<in> X \<Longrightarrow> (\<exists>c. c \<in> C \<and>  x \<le> c)"
  by(rule_tac ?A="{x}" in upbd_neE1, simp add:clrD5,simp)
*)


lemma is_clr_cofinal1:
  "is_clr C X \<Longrightarrow> is_greatest X m \<Longrightarrow> (\<exists>c \<in> C.  m \<le> c)"
  by (simp add: clrD7 greatestD11)

lemma is_clr_cofinal2:
  "is_clr C X \<Longrightarrow> is_greatest X m \<Longrightarrow> c \<in> C \<Longrightarrow> m \<le> c \<Longrightarrow> m =c"
  by (simp add: clrD2b greatestD2 order_antisym)

lemma is_clr_cofinal:
  "is_clr C X \<Longrightarrow> is_greatest X m \<Longrightarrow> m \<in> C"
  using is_clr_cofinal1 is_clr_cofinal2 by blast

definition cl_from_clr::"'a::order set \<Rightarrow> ('a::order \<Rightarrow> 'a::order)" where
  "cl_from_clr C \<equiv> (\<lambda>x. Least (Upper_Bounds C {x}))"

lemma cl_range1:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> (cl_from_clr C) x \<in> C"
  by(simp add:cl_from_clr_def, auto intro: Upper_BoundsD2 clrD4 least_exD1)

lemma cl_range2:
  "is_clr C X  \<Longrightarrow> (cl_from_clr C)`X \<subseteq> C"
  using cl_range1 by blast

lemma cl_range3:
  "is_clr C X  \<Longrightarrow> x \<in> C \<Longrightarrow> (cl_from_clr C) x = x"
  by (simp add: cl_from_clr_def ub_single_least2)

lemma cl_range3b:
  "is_clr C X  \<Longrightarrow> c \<in> C \<Longrightarrow> (\<exists>x \<in> X.  (cl_from_clr C) x = c)"
  using cl_range3 clrD2b by blast

lemma cl_range4:
  "is_clr C X  \<Longrightarrow> (cl_from_clr C)`C = C"
  by (simp add: cl_range3)

lemma cl_range5:
  "is_clr C X \<Longrightarrow> x \<in> C  \<Longrightarrow> x \<in>  cl_from_clr C ` X"
  using cl_range3b by blast

lemma clr_induced_closure_id:
  "is_clr C X  \<Longrightarrow>  (cl_from_clr C)`X = C"
   by (rule order_antisym, auto simp add: cl_range2 cl_range5)

lemma cl_ext1:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> x \<le> (cl_from_clr C) x"
  by (metis Upper_BoundsD1 cl_from_clr_def clrD3 least_exD1 singletonI)

lemma cl_ext2:
  "is_clr C X \<Longrightarrow> is_extensive X (cl_from_clr C)"
  by (simp add: cl_ext1 is_extensive_def)

lemma cl_lt_ub1:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> c \<in> Upper_Bounds C {x} \<Longrightarrow> (cl_from_clr C) x \<le> c"
  by (simp add: cl_from_clr_def clrD3 least_exD2)

lemma cl_lt_ub2:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> c \<in> C \<Longrightarrow> x \<le> c \<Longrightarrow> (cl_from_clr C) x \<le> c"
  by (simp add: Upper_Bounds_singleton2 cl_lt_ub1)

lemma cl_iso1:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> X  \<Longrightarrow> x \<le> y \<Longrightarrow> (cl_from_clr C) x \<le> (cl_from_clr C) y"
  by (meson cl_ext2 cl_lt_ub2 cl_range1 extensiveD3)

lemma cl_iso2:
  "is_clr C X \<Longrightarrow> is_isotone X (cl_from_clr C)"
  by (simp add: cl_iso1 is_isotone_def)

lemma cl_ide:
  "is_clr C X \<Longrightarrow> is_idempotent X (cl_from_clr C) "
  by (simp add: cl_range1 cl_range3 is_idempotent_def)

lemma cl_is_closure:
  "is_clr C X \<Longrightarrow> is_closure X (cl_from_clr C)"
  by(simp add:is_closure_def cl_ext2 cl_ide cl_iso2 clr_induced_closure_id clrD2)

lemma closure_of_in_ub:
  "is_closure X f \<Longrightarrow>x \<in> X \<Longrightarrow> (f x) \<in> (Upper_Bounds (f`X) {x})"
  by (simp add: Upper_Bounds_singleton2 closureD5)

lemma closure_of_lt_ub:
  "is_closure X f \<Longrightarrow>x \<in> X \<Longrightarrow> y \<in>  (Upper_Bounds (f`X) {x}) \<Longrightarrow> (f x) \<le> y"
  by (meson Upper_BoundsD2 closureD7 ub_single_D2)

lemma closure_of_least_closed1:
  "is_closure X f \<Longrightarrow> x \<in> X \<Longrightarrow> is_least (Upper_Bounds (f`X) {x}) (f x)"
  by (simp add: closure_of_in_ub closure_of_lt_ub leastI3)

lemma closure_of_least_closed2:
  "is_closure X f \<Longrightarrow> x \<in> X \<Longrightarrow> Least (Upper_Bounds (f`X) {x}) =  (f x)"
  by (simp add: closure_of_in_ub closure_of_lt_ub least_equality2 least_iff)

lemma closure_induced_clr:
  "is_closure X f \<Longrightarrow> X \<noteq> {} \<Longrightarrow> is_clr (f`X) X"
  by (metis closure_iff2 closure_of_least_closed1 clrI1 empty_is_image)

lemma closure_induced_clr_id:
  "is_closure X f \<Longrightarrow> X \<noteq> {} \<Longrightarrow> x  \<in> X \<Longrightarrow> (cl_from_clr (f`X)) x = f x"
  by (simp add: cl_from_clr_def closure_of_least_closed2)

(*
  clr_induced_closure_id 
    is_clr C X  \<Longrightarrow>  (cl_from_clr C)`X = C
  
  and closure_induced_clr_id
    is_closure X f \<Longrightarrow> X \<noteq> {} \<Longrightarrow> x  \<in> X \<Longrightarrow> (cl_from_clr (f`X)) x = f x

  define 
    F=(\<lambda>C. cl_from_clr C)
  and 
    G=(\<lambda>f. f`X)
  
  Then
     F \<circ> G (f) = f 
  where equality is defined on X and
    G \<circ> F (C) = C

*)

lemma closure_induced_clr_dual:
  "is_closure X f1 \<Longrightarrow> is_closure X f2 \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> f1 x \<le> f2 x) \<Longrightarrow> (f2`X) \<subseteq> (f1`X)"
  by (metis closureD11 closureD2 idempotentD3 is_closure_def subsetI)
                    
lemma clr_induced_closure_dual:
  "is_clr C1 X \<Longrightarrow> is_clr C2 X \<Longrightarrow> C2 \<subseteq> C1 \<Longrightarrow>  x \<in> X \<Longrightarrow> ((cl_from_clr C1) x) \<le> ((cl_from_clr C2) x)"
  by (simp add: cl_ext1 cl_lt_ub2 cl_range1 subsetD)


(*
  Clunky converses to cl_sup_eq_sup
    \<lbrakk>is_closure X f;  is_sup X A s; A \<subseteq> X\<rbrakk> \<Longrightarrow> is_sup (f`X) (f`A) (f s)
  and to cl_sup_ge_sup_cl. 
    \<lbrakk>is_closure X f; is_sup X A s1;  is_sup X (f`A) s2; A \<subseteq> X\<rbrakk> \<Longrightarrow> f s1  = f s2
  Combined they read that f:X\<longrightarrow>X  is a closure 
  iff A \<subseteq> X has a sup then \<Or>A \<le> f (\<Or>A)              (extensiveI4; trivial)
                                = \<Or>\<^sub>(\<^sub>f\<^sub>X\<^sub>)f(A)            (isotoneI4; cl_sup_eq_sup) 
   and if f(A) has a sup in X then f(\<Or>A) = f(\<Or>(fA))  (idempotentI4; cl_sup_ge_sup_cl) 
*)

lemma extensiveI4:
  "(\<And>A s. A \<subseteq> X \<Longrightarrow> is_sup X A s \<Longrightarrow> s \<le> f s) \<Longrightarrow>  f`X \<subseteq> X \<Longrightarrow> is_extensive X f"
  by (metis empty_subsetI extensiveI1 insert_absorb insert_mono is_supI1 ub_single_least1)

lemma idempotentI4:
  "(\<And>A s1 s2. A \<subseteq> X \<Longrightarrow> is_sup X A s1 \<Longrightarrow> is_sup X (f`A) s2 \<Longrightarrow> f s1 = f s2) \<Longrightarrow>  f`X \<subseteq> X \<Longrightarrow> is_idempotent X f"
  apply(auto simp add:is_idempotent_def)
  by (metis empty_subsetI image_empty image_insert image_subset_iff insert_subset sup_singleton)

lemma isotoneI4:
  assumes "(\<And>A s. \<lbrakk>A \<subseteq> X; is_sup X A s\<rbrakk> \<Longrightarrow> is_sup (f`X) (f`A) (f s))" and "f`X \<subseteq>X "
  shows "is_isotone X f"
proof- 
  have P:"\<And>x1 x2. x1 \<in> X \<and> x2 \<in> X \<and> x1 \<le> x2 \<longrightarrow> f x1 \<le> f x2"
    proof
      fix x1 x2 assume A2:"x1 \<in> X \<and> x2 \<in> X \<and> x1 \<le> x2"
      have B01:"is_sup X {x1, x2} x2"
        by (simp add: A2 binary_supI1)
      have B02:"is_sup (f`X) (f`{x1, x2}) (f x2)"
        by (meson A2 B01 assms(1) empty_subsetI insert_subset)
      show "f x1 \<le> f x2"
        using B02 is_supD1121 by fastforce
    qed
  show ?thesis
    by (simp add: P isotoneI1)
qed

(*so closure ranges are infimum closed and moreover if the poset is topped then this element is closed*)

lemma clrD8:
  "is_clr C X \<Longrightarrow> A \<subseteq> C  \<Longrightarrow> is_inf X A i \<Longrightarrow> (cl_from_clr C) i \<in> Lower_Bounds X A"
  by (simp add: Lower_BoundsI cl_is_closure cl_lt_ub2 closureD1 in_mono is_infD111 is_infD32)

lemma clrD9:
  "is_clr C X \<Longrightarrow> A \<subseteq> C \<Longrightarrow> is_inf X A i \<Longrightarrow> (cl_from_clr C) i \<le> i"
  by (simp add: clrD8 is_infD121)

lemma clrD10:
  "is_clr C X \<Longrightarrow> A \<subseteq> C  \<Longrightarrow> is_inf X A i \<Longrightarrow>  (cl_from_clr C) i = i"
  by (simp add: cl_ext1 clrD9 is_infD111 order_antisym)

lemma clrD11:
  "is_clr C X \<Longrightarrow> A \<subseteq> C  \<Longrightarrow> is_inf X A i \<Longrightarrow>  i \<in> C"
  by (metis cl_range1 clrD10 is_infD111)

lemma clrD12:
  "\<lbrakk>is_clr C X; top \<in> X; (\<And>x. x \<in> X \<Longrightarrow> x \<le> top)\<rbrakk> \<Longrightarrow> top \<in> C"
  by (simp add: greatestI3 is_clr_cofinal)

lemma moore_clI1:
  "C \<subseteq> Pow X \<Longrightarrow> (\<And>E. E \<subseteq> C \<Longrightarrow> (X \<inter> (\<Inter>E)) \<in> C) \<Longrightarrow> x \<in> Pow X \<Longrightarrow> is_least (Upper_Bounds C {x})  (X \<inter> (\<Inter>(Upper_Bounds C {x}))) "
  by(auto simp add:is_clr_def is_least_def Upper_Bounds_def Lower_Bounds_def ub_def lb_def)

(*
two ways to introduce a moore system; either by demonstrating it is inf closed where the infimum
is taken in the powerset i.e. Inf E=X \<inter> (\<Inter>E) which when {} \<noteq> E \<subseteq> Pow X is simply \<Inter>E but to handle
the case of {} cannot be simplified; or by demonstrating separately that X \<in> C and showing
 nonempty infima closure
*)

lemma moore_clI2:
  "C \<subseteq> Pow X \<Longrightarrow> (\<And>E. E \<subseteq> C \<Longrightarrow> (X \<inter> (\<Inter>E)) \<in> C) \<Longrightarrow> is_clr C (Pow X)"
  by (metis empty_iff empty_subsetI is_clr_def moore_clI1)

lemma moore_clI3:
  "C \<subseteq> Pow X \<Longrightarrow> X \<in> C \<Longrightarrow> (\<And>E. E \<subseteq> C \<Longrightarrow> E \<noteq> {} \<Longrightarrow> (\<Inter>E) \<in> C) \<Longrightarrow> is_clr C (Pow X)"
  by (metis Inf_insert insert_not_empty insert_subsetI moore_clI2)

lemma clr_cinf_semilattice1:
  assumes A0:"is_clr C X" and A1:"is_cinf_semilattice X"
  shows "\<And>A. A \<subseteq> C \<and> A \<noteq> {} \<longrightarrow> (\<exists>x. is_inf C A x \<and> is_inf X A x)"
  by (meson A0 A1 cinfD2 clrD11 clrD2 dual_order.trans inf_in_subset)

lemma clr_cinf_semilattice2:
  "\<lbrakk>is_clr C X; is_cinf_semilattice X\<rbrakk> \<Longrightarrow> (\<And>A. A \<subseteq> C \<and> A \<noteq> {} \<Longrightarrow> Inf C A = Inf X A)"
  by (metis clr_cinf_semilattice1 inf_equality)

lemma clr_clattice1:
  assumes A0:"is_clr C X" and A1:"is_clattice X"
  shows "\<And>A. A \<subseteq> C \<longrightarrow> (\<exists>x. is_sup C A x \<and> is_inf X (Upper_Bounds C A) x)"
proof
  fix A assume A2:"A \<subseteq> C"
  obtain x where B0:"is_inf X (Upper_Bounds C A) x"
    by (meson A0 A1 Upper_Bounds_sub clatD22 is_clr_def order_trans)
  have B1:"is_sup C A x"
    by (meson A0 A2 B0 Upper_Bounds_sub clrD11 clrD2 inf_in_subset sup_if_inf_ub)
  show "(\<exists>x. is_sup C A x \<and> is_inf X (Upper_Bounds C A) x)"
    using B0 B1 by blast
qed

lemma clr_clattice2:
  "\<lbrakk>is_clr C X; is_clattice X\<rbrakk> \<Longrightarrow> (\<And>A. A \<subseteq> C \<Longrightarrow> Sup C A = Inf  X (Upper_Bounds C A))"
  by (metis clr_clattice1 inf_equality sup_equality)

lemma clr_is_clattice:
  "\<lbrakk>is_clr C X; is_clattice X\<rbrakk> \<Longrightarrow> is_clattice C"
  by (metis clr_clattice1 is_clattice_def is_clr_def)


lemma closure_range_is_clattice:
  "\<lbrakk>is_closure X f; is_clattice X\<rbrakk> \<Longrightarrow> is_clattice (f`X)"
  using closure_induced_clr clr_is_clattice is_clattice_def by blast


definition ord_embedding::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "ord_embedding f X \<equiv> (\<forall>x1 x2. x1 \<in> X \<and> x2 \<in> X \<longrightarrow> (x1 \<le> x2  \<longleftrightarrow> f x1 \<le> f x2))"

definition ord_isomorphism::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a::order set  \<Rightarrow>  'b::order set  \<Rightarrow> bool" where
  "ord_isomorphism f X Y \<equiv> ord_embedding f X \<and> f`X=Y"

lemma ord_emb_is_inj:
  "ord_embedding f X \<Longrightarrow> inj_on f X"
  by (simp add: inj_on_def ord_embedding_def order_antisym)  

lemma ord_emb_imp1:
  "ord_embedding f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> f x1 \<le> f x2"
  by(simp add:ord_embedding_def)

lemma ord_emb_imp2:
  "ord_embedding f X \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> f x1 \<le> f x2 \<Longrightarrow>  x1 \<le> x2"
  by(simp add:ord_embedding_def)


subsection ClosureLocales

locale closure=
  fixes X::"'a::order set" and
        f::"'a::order \<Rightarrow> 'a::order"
  assumes is_cl:"is_closure X f" and
          is_ne:"X \<noteq> {}"

locale closure_range=
  fixes X::"'a::order set" and
        C::"'a::order set" 
  assumes is_cl_range:"is_clr C X"

locale clr_closure=closure_range

sublocale closure \<subseteq> cr:closure_range "X" "f`X"
  by (unfold_locales,simp add: closure_induced_clr is_cl is_ne)

sublocale clr_closure \<subseteq> cl:closure "X" "cl_from_clr X"
  apply (unfold_locales,simp add: cl_from_clr_def is_closure_def is_extensive_def is_idempotent_def is_isotone_def ub_single_least2)
  using clrD1 clr_induced_closure_id is_cl_range by blast

section SpecialSubsets

subsection DirectedSets

definition is_dir::"'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "is_dir X ord \<equiv> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>c \<in> X. ord a c \<and> ord b c))"

definition is_ord_cl::"'a set \<Rightarrow> 'a set \<Rightarrow>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "is_ord_cl X A ord \<equiv> (\<forall>a b. a \<in> A \<and> b \<in> X \<and> ord a b \<longrightarrow> b \<in> A )"

lemma is_updirE1:
  "is_dir (X::'a::order set) (\<le>)  \<Longrightarrow> a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> (\<exists>c \<in> X. a \<le> c \<and> b \<le> c) "
  by (simp add: is_dir_def)

lemma is_updirI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. a \<le> c \<and> b \<le> c)) \<Longrightarrow> is_dir (X::'a::order set) (\<le>)"
  by (simp add: is_dir_def)

lemma is_updir_empty:
  "is_dir {} (\<le>)"
  by (simp add: is_dir_def)

lemma is_updir_singleton:
  "is_dir {x::'a::order} (\<le>)"
  by (simp add: is_dir_def)

lemma is_updirD1:
  "\<lbrakk>is_dir (X::'a::order set) (\<le>);a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>c \<in> X. c ub {a, b})"
  by (simp add: is_updirE1 ub_double)

lemma csup_updir:
  "is_csup_semilattice X \<Longrightarrow> is_dir X (\<le>)"
  by (metis csupD3 is_updirI1 greatestD11 greatestD2)

lemma sup_updir:
  "\<lbrakk>is_sup_semilattice X; is_greatest X m\<rbrakk> \<Longrightarrow> is_dir X (\<le>)"
  by (meson greatestD1 greatestD2 is_updirI1)

lemma is_dwdirE1:
  "is_dir (X::'a::order set) (\<ge>)  \<Longrightarrow> a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> (\<exists>c \<in> X. a \<ge> c \<and> b \<ge> c) "
  by (simp add: is_dir_def)

lemma is_dwdirI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. a \<ge> c \<and> b \<ge> c)) \<Longrightarrow> is_dir (X::'a::order set) (\<ge>)"
  by (simp add: is_dir_def)

lemma is_dwdir_empty:
  "is_dir {} (\<ge>)"
  by (simp add: is_dir_def)

lemma is_dwdir_singleton:
  "is_dir {x::'a::order} (\<ge>)"
  by (simp add: is_dir_def)

lemma is_dwdirD1:
  "\<lbrakk>is_dir (X::'a::order set) (\<ge>);a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>c \<in> X. c lb {a, b})"
  by (simp add: is_dwdirE1 lb_double)

lemma dwdir_obtain:
  assumes A0:"is_dir (X::'a::order set) (\<ge>)" and A1:"a \<in> X" and A2:"b \<in> X"
  obtains c where "c \<in> X \<and>  a \<ge> c \<and> b \<ge> c"
  using A0 A1 A2 is_dwdirE1 by blast

lemma cinf_dwdir:
  "is_cinf_semilattice X \<Longrightarrow> is_dir X (\<ge>)"
  by (metis cinfD3 is_dwdirI1 leastD11 leastD2)


lemma sinf_pair_lb:
  "\<lbrakk>is_inf_semilattice X; a \<in> X; b \<in> X\<rbrakk>  \<Longrightarrow>\<exists>c. c \<in> X \<and> c \<le> a \<and>  c \<le> b"
  by(rule_tac ?x="Inf X {a, b}" in exI, simp add:binf_leI1 binf_leI2 sinfD4)

lemma ex_to_space:
  " \<exists>x. x \<in> X \<and> Q x \<Longrightarrow>  \<exists>x \<in> X. Q x"
  by blast

lemma inf_dwdir:
  "\<lbrakk>is_inf_semilattice X\<rbrakk> \<Longrightarrow> is_dir X (\<ge>)"
  by(simp add:is_dir_def ex_to_space sinf_pair_lb)


lemma is_ord_clE1:
  "is_ord_cl (X::'a::order set) A (\<le>)  \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> X \<Longrightarrow> a \<le> b \<Longrightarrow> b \<in> A "
  by (simp add:is_ord_cl_def)

lemma is_ord_clE2:
  "is_ord_cl (X::'a::order set) A (\<ge>)  \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> X \<Longrightarrow> b \<le> a \<Longrightarrow> b \<in> A "
  by (simp add:is_ord_cl_def)

lemma is_ord_clI1:
  "(\<And>a b. \<lbrakk>a \<in> A; b \<in> X; ord a b\<rbrakk> \<Longrightarrow> b \<in> A ) \<Longrightarrow> is_ord_cl  (X::'a::order set) A ord"
  by (auto simp add:is_ord_cl_def)

lemma is_ord_empty:
  "is_ord_cl (X::'a::order set) {} ord "
  by (simp add: is_ord_cl_def)

lemma is_ord_cl_space:
  "is_ord_cl (X::'a::order set) X ord "
  by (simp add: is_ord_cl_def)

lemma is_ord_cl_comp1:
  "is_ord_cl (X::'a::order set) A ord \<Longrightarrow> is_ord_cl (X::'a::order set) (X-A) (\<lambda>a b. ord b a)"
  by(auto simp add:is_ord_cl_def)

lemma is_ord_cl_comp2:
  "A \<subseteq> X \<Longrightarrow> is_ord_cl (X::'a::order set) (X-A) (\<lambda>a b. ord b a) \<Longrightarrow> is_ord_cl (X::'a::order set) A ord"
  by(auto simp add:is_ord_cl_def)

lemma is_ord_cl_iff_comp:
  "A \<subseteq> X \<Longrightarrow> is_ord_cl (X::'a::order set) A ord \<longleftrightarrow> is_ord_cl (X::'a::order set) (X-A) (\<lambda>a b. ord b a) "
  using is_ord_cl_comp1 is_ord_cl_comp2 by blast

lemma is_ord_cl_un:
  "A \<in> (Pow (Pow (X::'a::order set))) \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> is_ord_cl X a ord) \<Longrightarrow>  is_ord_cl X (\<Union>A) ord "
  apply(simp add:is_ord_cl_def) by metis

lemma is_ord_cl_in:
  "A \<in> (Pow (Pow (X::'a::order set))) \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> is_ord_cl X a ord) \<Longrightarrow>  is_ord_cl X (\<Inter>A) ord "
  apply(simp add:is_ord_cl_def) by metis

lemma is_ord_cl_un2:
  "A \<in> (Pow (Pow (X::'a::order set))) \<and> (\<forall>a. a \<in> A \<longrightarrow> is_ord_cl X a ord) \<Longrightarrow>  is_ord_cl X (\<Union>A) ord "
  by (simp add: is_ord_cl_un)

lemma is_ord_cl_in2:
  "A \<in> (Pow (Pow (X::'a::order set))) \<and> (\<forall>a. a \<in> A \<longrightarrow> is_ord_cl X a ord) \<Longrightarrow>  is_ord_cl X (\<Inter>A) ord "
  by (simp add: is_ord_cl_in)

lemma un_to_ind_un:
  "(\<And>(A::'a set set). P A \<Longrightarrow> Q (\<Union>A)) \<Longrightarrow> (\<And>(f::('b \<Rightarrow> 'a set)) (I::'b set). P(f`I) \<Longrightarrow> Q(\<Union>i \<in> I. f i))"
  by simp

lemma int_to_ind_int:
  "(\<And>(A::'a set set). P A \<Longrightarrow> Q (\<Inter>A)) \<Longrightarrow> (\<And>(f::('b \<Rightarrow> 'a set)) (I::'b set). P(f`I) \<Longrightarrow> Q(\<Inter>i \<in> I. f i))"
  by simp

lemma is_ord_cl_un3:
  "(f`I)\<in> (Pow (Pow (X::'a::order set))) \<and> (\<forall>i. i \<in> I \<longrightarrow> is_ord_cl X (f i) ord) \<Longrightarrow>  is_ord_cl X (\<Union>i \<in> I. f i) ord "
  apply (rule un_to_ind_un[of "(\<lambda>A. A \<in> (Pow (Pow (X::'a::order set))) \<and> (\<forall>a. a \<in> A \<longrightarrow> is_ord_cl X a ord))"  "\<lambda>B. is_ord_cl X B ord" "f" "I"])
  apply (simp add: is_ord_cl_un)
  by blast

lemma is_ord_cl_in3:
  "(f`I)\<in> (Pow (Pow (X::'a::order set))) \<and> (\<forall>i. i \<in> I \<longrightarrow> is_ord_cl X (f i) ord) \<Longrightarrow>  is_ord_cl X (\<Inter>i \<in> I. f i) ord "
  apply (rule int_to_ind_int[of "(\<lambda>A. A \<in> (Pow (Pow (X::'a::order set))) \<and> (\<forall>a. a \<in> A \<longrightarrow> is_ord_cl X a ord))"  "\<lambda>B. is_ord_cl X B ord" "f" "I"])
  apply (simp add: is_ord_cl_in)
  by blast


subsection FiltersAndIdeals

definition is_filter::"'a::order set\<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_filter X F \<equiv> F \<noteq> {} \<and> F \<subseteq> X \<and> (is_dir F (\<ge>)) \<and> is_ord_cl X F (\<le>)"

lemma filterI1:
  "\<lbrakk> F \<noteq> {}; F \<subseteq> X; (is_dir F (\<ge>));  (is_ord_cl X F (\<le>))\<rbrakk> \<Longrightarrow> is_filter X F"
  by (simp add: is_filter_def)

lemma filterD1:
  "is_filter X F \<Longrightarrow> F \<noteq> {}"
  by (simp add: is_filter_def)

lemma filterD2:
  "is_filter X F \<Longrightarrow> F \<subseteq> X"
  by (simp add: is_filter_def)

lemma filterD21:
  "is_filter X F \<Longrightarrow> x \<in> F \<Longrightarrow> x \<in> X"
  using filterD2 by blast

lemma filterD3:
  "is_filter X F \<Longrightarrow> (is_dir F (\<ge>))"
  by (simp add: is_filter_def)

lemma filterD4:
  "is_filter X F \<Longrightarrow> (is_ord_cl X F (\<le>))"
  by (simp add: is_filter_def)

lemma greatest_in_filter1:
  "is_greatest X m \<Longrightarrow> is_filter X F \<Longrightarrow>  (\<exists>f. f \<in> F \<and> f \<le> m)"
  by (metis is_filter_def bot.extremum_uniqueI greatestD12 subset_emptyI ubD ub_ant2)

lemma greatest_in_filter2:
  "is_greatest X m \<Longrightarrow> is_filter X F \<Longrightarrow>  m \<in> F"
  using filterD4 greatestD11 greatest_in_filter1 is_ord_clE1 by blast

lemma dwdir_inf:
  assumes A0:"A \<subseteq> X" and A1:"is_dir A (\<ge>)" and A2:"is_ord_cl X A (\<le>)"
  shows "\<And>a b. (a \<in> A \<and> b \<in> A \<and>  is_inf X {a, b} i) \<longrightarrow> (i \<in> A)"
proof
  fix a b assume A3:" (a \<in> A \<and> b \<in> A \<and> is_inf X {a, b} i)"
  obtain c where B0:"c \<in> A \<and> a \<ge> c \<and> b \<ge> c"
    using A1 A3 is_dwdirE1 by blast
  have B1:"c lb {a, b}"
    by (simp add: B0 lb_def)
  have B2:"c \<le> i"
    using A0 A3 B0 B1 lt_inf_iff by blast
  show "i \<in> A"
    using A2 A3 B0 B2 is_infD111 is_ord_clE1 by blast
qed


lemma dwdir_inf2:
  assumes A0:"is_inf_semilattice X"
  shows " is_dir X (\<ge>)"
proof-
  have B0:"\<And>a b. a \<in> X \<and>  b \<in> X \<longrightarrow> (\<exists>c \<in> X.  a \<ge> c \<and>  b \<ge> c)"
  proof
    fix a b assume A1:"a \<in> X \<and> b \<in> X"
    obtain i where B1:"is_inf X {a, b} i"
      by (meson A1 assms is_inf_semilattice_def)
    show "\<exists>c \<in> X.  a \<ge> c \<and>  b \<ge> c"
      using B1 is_infD111 is_infD112 lb_double by blast
  qed
  show ?thesis
    by (simp add: B0 is_dwdirI1)
qed
  
lemma filter_inf_closed:
  "\<lbrakk>is_filter X F; a \<in> F;  b \<in> F;  is_inf X {a, b} i\<rbrakk>\<Longrightarrow> i \<in> F"
  by (meson is_filter_def dwdir_inf)

lemma filter_inf_closed1:
  "\<lbrakk>is_inf_semilattice X; is_filter X F; a \<in> F; b \<in> F\<rbrakk> \<Longrightarrow> Inf X {a, b} \<in> F"
  by (meson filterD21 filter_inf_closed sinfD3)

lemma filter_inf_closed3:
  "\<lbrakk>is_inf_semilattice X; is_filter X F; A \<subseteq> F; A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow> Inf X A \<in> F"
  by (simp add: is_filter_def filter_inf_closed1 finite_inf_closed2)

lemma min_filter1:
  "is_greatest X top \<Longrightarrow> is_filter X {top}"
  by (simp add: is_filter_def greatest_iff is_dwdir_singleton is_ord_cl_def order_antisym) 

lemma min_filter2:
  "\<lbrakk>is_greatest X top; is_filter X F\<rbrakk> \<Longrightarrow>{top} \<subseteq> F"
  by (simp add: greatest_in_filter2)

lemma filters_max0:
  "is_inf_semilattice X \<Longrightarrow> is_filter X X"
  by (simp add: is_filter_def dwdir_inf2 is_inf_semilattice_def is_ord_cl_space)

lemma filters_max1:
  "is_cinf_semilattice X \<Longrightarrow>is_filter X X"
  by (simp add: is_filter_def cinf_dwdir is_cinf_semilattice_def is_ord_cl_space)

definition filters_on::"'a::order set \<Rightarrow> 'a::order set set" where
  "filters_on X \<equiv> {F. is_filter X F}"

lemma filters_on_iff:
  "F \<in> filters_on X \<longleftrightarrow> is_filter X F"
  by (simp add: filters_on_def)

lemma filters_is_clr1:
  "(filters_on X) \<subseteq> Pow X"
  using filterD2 filters_on_iff by fastforce

lemma filters_is_clr1b:
  "is_inf_semilattice X \<Longrightarrow> X \<in> filters_on X"
  by (simp add: filters_max0 filters_on_iff)

lemma filter_inter_upcl:
  "(\<forall>F. F \<in> EF \<longrightarrow> is_filter X F) \<Longrightarrow> is_ord_cl X (\<Inter>EF) (\<le>)"
  by (simp add: filterD2 filterD4 is_ord_cl_in2 subsetI)

lemma filter_inter_ne:
  "\<lbrakk>(\<forall>F. F \<in> EF \<longrightarrow> is_filter X F);is_greatest X top\<rbrakk> \<Longrightarrow> (\<Inter>EF) \<noteq> {}"
  by (metis InterI empty_iff greatest_in_filter2)

lemma filter_inter_dir:
  assumes A0:"is_inf_semilattice X" and
          A1:"(\<forall>F. F \<in> EF \<longrightarrow> is_filter X F)" and
          A2:"EF \<noteq> {}" 
  shows "is_dir (\<Inter>EF) (\<ge>)"
proof-
  let ?I="\<Inter>EF"
  have P: "\<And>a b. a \<in> ?I \<and> b \<in> ?I\<longrightarrow> (\<exists>c\<in>?I. c \<le> a \<and> c \<le> b)"
  proof
    fix a b assume A5:"a \<in> ?I \<and> b \<in> ?I"
    have B0:"a \<in>X \<and> b \<in> X"
      by (metis A1 A2 A5 Inter_iff all_not_in_conv filterD2 subset_iff)
    obtain i where B1:"is_inf X {a, b} i"
      by (meson A0 B0 is_inf_semilattice_def)
    have B2:"\<forall>F \<in> EF. i \<in> F"
      by (meson A1 A5 B1 InterE filter_inf_closed)
    show "(\<exists>c\<in>?I. c \<le> a \<and> c \<le> b)"
      by (meson B1 B2 InterI dual_order.refl insert_iff is_infD32)
  qed
  show ?thesis
    by (metis P is_dwdirI1)
qed

lemma filter_inter_dir2:
  "\<lbrakk>is_inf_semilattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> is_dir (\<Inter>{F1, F2}) (\<ge>)"
  apply(rule_tac ?X="X" in filter_inter_dir) by simp+

lemma filter_inter_dir3:
  assumes "is_inf_semilattice X" "is_filter X F1" "is_filter X F2"
  shows "is_dir (F1 \<inter> F2) (\<ge>)"
proof-
  have B0:"F1 \<inter> F2 = \<Inter>{F1, F2}"
    by simp
  have B1:"is_dir (\<Inter>{F1, F2}) (\<ge>)"
    using assms(1) assms(2) assms(3) filter_inter_dir2 by blast
  show ?thesis
    using B1 by fastforce
qed

lemma filter_inter_closed1:
  "\<lbrakk>is_inf_semilattice X;(\<forall>F. F \<in> EF \<longrightarrow> is_filter X F); EF \<noteq> {};is_greatest X top\<rbrakk> \<Longrightarrow>  is_filter X (\<Inter>EF)"
  by (meson Inter_subset is_filter_def cinf_sinf filter_inter_dir filter_inter_ne filter_inter_upcl)

lemma filter_inter_closed2:
  "\<lbrakk>is_inf_semilattice X;is_greatest X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> (\<And>E. \<lbrakk>E \<subseteq> (filters_on X); E \<noteq> {}\<rbrakk> \<Longrightarrow> (\<Inter>E) \<in> (filters_on X))"
  by (simp add: filter_inter_closed1 filters_on_iff subset_iff)

lemma filter_is_clr:
  "\<lbrakk>is_inf_semilattice X;is_greatest X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> is_clr (filters_on X) (Pow X)"
  by (simp add: cinf_sinf filter_inter_closed2 filters_is_clr1 filters_is_clr1b moore_clI3)

lemma filter_closure_of_empty1:
  "\<lbrakk>is_inf_semilattice X;is_greatest X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> is_least (Upper_Bounds (filters_on X) {{}}) {top}"
  by (simp add: Upper_Bounds_mem_iff2 filters_on_def greatest_in_filter2 least_iff min_filter1)

lemma filter_closure_of_empty2:
  "\<lbrakk>is_inf_semilattice X;is_greatest X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> (cl_from_clr (filters_on X)) {} = {top}"
  by (simp add: cl_from_clr_def filter_closure_of_empty1 least_equality2)



context inf_semilattice
begin 

lemma filter_inter_dirb:
  "(\<And>F. F \<in> EF \<Longrightarrow> is_filter X F) \<Longrightarrow> EF \<noteq> {} \<Longrightarrow> is_dir (\<Inter>EF) (\<ge>)"
  by (simp add:filter_inter_dir[of "X" "EF"] inf_ex)

lemma filter_inter_dir2b:
  "\<lbrakk>is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> is_dir (\<Inter>{F1, F2}) (\<ge>)"
  by(rule filter_inter_dir2[of "X" "F1" "F2"], rule inf_ex, simp+)

lemma filter_inter_dir3b:
  "\<lbrakk>is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> is_dir (F1 \<inter> F2) (\<ge>)"
  using filter_inter_dir2b by simp

end


definition filter_closure::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "filter_closure X A \<equiv> if A={} then {Greatest X} else {x \<in> X. \<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and> Inf X F \<le> x}"

lemma filter_closure_iff:
  "A \<noteq> {} \<Longrightarrow> x \<in> filter_closure X A  \<longleftrightarrow> (x \<in> X \<and> ( \<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and> Inf X F \<le> x))"
  by (simp add: filter_closure_def)

lemma filter_closure_memI1:
  "(x \<in> X \<and> ( \<exists>F. F \<subseteq> A \<and> finite F \<and> F \<noteq> {} \<and> Inf X F \<le> x)) \<Longrightarrow> x \<in> filter_closure X A"
  using filter_closure_iff by blast

lemma filter_closure_memI2:
  "(x \<in> X \<and>  F \<subseteq> A \<and> finite F \<and> F \<noteq> {} \<and> Inf X F \<le> x) \<Longrightarrow> x \<in> filter_closure X A"
  using filter_closure_iff by blast

lemma filter_closure_ne_simp:
  "A \<noteq> {} \<Longrightarrow> filter_closure X A = {x \<in> X. \<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and> Inf X F \<le> x}"
  by (simp add: filter_closure_def)

lemma filter_closure_singleton:
  "\<lbrakk>A \<subseteq> X; a \<in> A\<rbrakk> \<Longrightarrow> a \<in> filter_closure X A"
  apply(rule_tac ?F="{a}"  in filter_closure_memI2, simp)
  by (metis in_mono inf_equality inf_singleton order_refl)

lemma filter_closure_obtains:
  assumes "A \<noteq> {}" and "x \<in> filter_closure X A"
  obtains Fx where "Fx \<subseteq> A \<and> finite Fx \<and> Fx \<noteq> {}  \<and> Inf X Fx \<le> x"
  by (meson assms filter_closure_iff)

lemma filter_closure_empty:
  "is_greatest X top \<Longrightarrow> filter_closure X {} = {top}"
  by (simp add: filter_closure_def greatest_equality2)

lemma filter_closure_ne:
  "\<lbrakk>X \<noteq> {}; A \<subseteq> X\<rbrakk> \<Longrightarrow> filter_closure X A \<noteq> {}"
  by (metis empty_iff filter_closure_def filter_closure_singleton insert_subset subset_empty subset_emptyI)

lemma filter_closure_superset:
  "\<lbrakk>X \<noteq> {}; A \<subseteq> X\<rbrakk> \<Longrightarrow> A \<subseteq> filter_closure X A"
  using filter_closure_singleton by auto

context
  fixes A X::"'a::order set" 
  assumes subs_ne:"A \<subseteq> X" "A \<noteq> {}" and
          csinf:"is_inf_semilattice X" 
begin
lemma ne_filter_cl0:
  "A \<subseteq> (filter_closure X A)"
  by (metis empty_subsetI filter_closure_superset order.trans subs_ne(1))

lemma ne_filter_cl1:
  "is_ord_cl X (filter_closure X A) (\<le>)"
  apply(simp add:subs_ne filter_closure_ne_simp is_ord_cl_def) by (meson order.trans)

end

context inf_semilattice
begin
lemma ne_filter_cl0b:
  "\<lbrakk>A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> A \<subseteq> (filter_closure X A)"
  by (simp add: inf_ex ne_filter_cl0)

lemma ne_filter_cl1b:
  "\<lbrakk>A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_ord_cl X (filter_closure X A) (\<le>)"
  by (simp add: inf_ex ne_filter_cl1)

end

context
  fixes X::"'a::order set"
  assumes toped:"is_greatest X top" and
          csinf:"is_inf_semilattice X"
begin

lemma filter_cl0:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> filter_closure X A"
  by (simp add: filter_closure_singleton subsetI)

lemma filter_cl1:
  "A \<subseteq> X \<Longrightarrow> is_ord_cl X (filter_closure X A) (\<le>)"
  by (metis csinf filterD4 filter_closure_empty min_filter1 ne_filter_cl1 toped)

lemma filter_cl2:
  "A \<subseteq> X \<Longrightarrow> is_dir (filter_closure X A) (\<ge>)"
  by (metis greatestD11 greatestD2 is_dwdirI1 toped)

lemma filter_cl3:
  "A \<subseteq> X \<Longrightarrow> is_filter X (filter_closure X A)"
  by (metis is_filter_def csinf filter_cl1 filter_cl2 filter_closure_ne filters_max0 greatestD11 subsetI toped)

lemma filter_cl_least:
  "\<lbrakk>is_filter X F; A \<subseteq> F\<rbrakk> \<Longrightarrow> (filter_closure X A) \<subseteq> F"
  by (meson greatest_in_filter2 subsetI toped)

lemma filter_cl_is_ub:
  "A \<subseteq> X \<Longrightarrow> (filter_closure X A) \<in>  (Upper_Bounds (filters_on X) {A})"
  by (simp add: Upper_Bounds_singleton2 filter_cl0 filter_cl3 filters_on_def)

lemma filter_cl_lt_ub:
  "A \<subseteq> X  \<Longrightarrow> F \<in>  (Upper_Bounds (filters_on X) {A}) \<Longrightarrow> (filter_closure X A) \<le> F"
  by (meson Upper_BoundsD1 Upper_Bounds_mem_iff filter_cl_least filters_on_iff insertI1)

lemma filter_cl_is_lub:
  "A \<subseteq> X \<Longrightarrow>  is_inf (Pow X) (Upper_Bounds (filters_on X) {A}) (filter_closure X A) "
  by (meson Upper_BoundsD2 filter_cl_is_ub filter_cl_lt_ub filters_is_clr1 is_infI115 lb_def subset_iff)

lemma filter_cl_is_lcl:
  "A \<subseteq> X \<Longrightarrow>  is_least (Upper_Bounds (filters_on X) {A}) (filter_closure X A) "
  by (simp add: filter_cl_is_ub filter_cl_lt_ub leastI3)

lemma filter_closure_eq_closure:                                      
  "A \<subseteq> X  \<Longrightarrow> filter_closure X A = (cl_from_clr (filters_on X)) A "
  by (metis cl_from_clr_def filter_cl_is_lcl least_equality2)

end

context lattice
begin
context fixes F::"'a::order set" 
        assumes in_sp:"F \<subseteq> X" and 
                is_ne:"F \<noteq> {}"
begin
lemma lattice_filD1:
  "is_filter X F \<Longrightarrow> \<lbrakk>x1 \<in> F; x2 \<in> F\<rbrakk> \<Longrightarrow> Inf X {x1, x2} \<in> F"
  by (simp add: filter_inf_closed1 inf_ex)

lemma lattice_filD2:
  "is_filter X F \<Longrightarrow> \<lbrakk>x1 \<in> F; x2 \<in> X; x1 \<le> x2\<rbrakk> \<Longrightarrow> x2 \<in> F"
  using filterD4 is_ord_clE1 by blast

lemma lattice_dwdir:
  "(\<And>x1 x2.  \<lbrakk>x1 \<in> F; x2 \<in> F\<rbrakk> \<Longrightarrow> Inf X {x1, x2} \<in> F) \<Longrightarrow> is_dir F (\<ge>)"
  by (metis binf_iffb in_mono in_sp inf_def is_dwdirI1 order_refl)

lemma lattice_filI1:
  "(\<And>x1 x2.  \<lbrakk>x1 \<in> F; x2 \<in> F\<rbrakk> \<Longrightarrow> Inf X {x1, x2} \<in> F) \<Longrightarrow>
   (\<And>x1 x2. \<lbrakk>x1 \<in> F; x2 \<in> X; x1 \<le> x2\<rbrakk> \<Longrightarrow> x2 \<in> F) \<Longrightarrow> is_filter X F"
  by(simp add: is_filter_def is_ne in_sp,drule lattice_dwdir, simp,erule is_ord_clI1)


end
end


lemma filters_on_lattice_inf01:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> z \<in> F1 \<inter> F2 \<Longrightarrow> \<exists>f1 f2. f1 \<in> F1 \<and> f2 \<in> F2 \<and> z = Sup X {f1, f2}"
  by (metis Int_iff filterD21 insert_absorb2 sup_singleton3)


lemma filters_on_lattice_inf02:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> f1 \<in> F1 \<and> f2 \<in> F2 \<and> z = Sup X {f1, f2} \<Longrightarrow> z \<in> F1 \<inter> F2 "
  using filterD4[of "X" "F1"] is_ord_clE1[of "X" "F1" "f1" "z"] filterD4[of "X" "F2"] is_ord_clE1[of "X" "F2" "f2" "z"]
  by (meson IntI dual_order.eq_iff filterD21 latt_iff ssupD4 ssup_leD5 ssup_leD6) 

lemma filters_on_lattice_inf03:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> f1 \<in> F1 \<Longrightarrow> f2 \<in> F2  \<Longrightarrow> Sup X {f1, f2} \<in> F1 \<inter> F2 "
  using filters_on_lattice_inf02 by blast


lemma filter_on_lattice_sup01:
  "\<lbrakk>is_lattice X; is_filter X F; x \<in> X; y \<in> F\<rbrakk> \<Longrightarrow> Sup X {x, y} \<in> F "
  by (meson binary_supD32 filterD21 filterD4 is_ord_clE1 lattD32 lattD42 ssupD4)

lemma filter_on_lattice_top0:
  "is_lattice X \<Longrightarrow> Posets11.is_filter X {x} \<Longrightarrow> a \<in> X \<Longrightarrow> a \<le> x"
  by (meson Posets11.is_filter_def bsup_iff filter_on_lattice_sup01 insertI1 latt_iff subsetD ubD ub_singleton)

lemma filter_on_lattice_top:
  "\<lbrakk>is_lattice X;  is_filter X {x}\<rbrakk> \<Longrightarrow>  is_greatest X x"
  by(rule greatestI1, rule Upper_BoundsI, simp add: filter_on_lattice_top0, simp add:filterD21)

lemma filter_on_lattice_eq:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> (F1 \<inter> F2) = {y. (\<exists>f1 \<in> F1. \<exists>f2 \<in> F2. y = Sup X {f1, f2})}"
  apply(auto simp add:set_eq_iff)  apply (metis bsup_idem1 filterD21) 
  using filters_on_lattice_inf03[of "X" "F1" "F2"]  by blast+

lemma filters_on_lattice_inf2b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> is_dir (F1 \<inter> F2) (\<ge>)"
  using filter_inter_dir3 lattD41 by blast

lemma filters_upcl:
  "\<lbrakk>is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> is_ord_cl X (F1 \<inter> F2) (\<le>)"
  apply(auto simp add:is_ord_cl_def) using filterD4 is_ord_clE1 by blast+

lemma filter_on_lattice_inf4b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<noteq> {}"
  by (metis empty_iff equals0I filterD1 filters_on_lattice_inf02)

lemma filters_on_lattice_inf5b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> is_filter X (F1 \<inter> F2)"
  by (meson filterD2 filterI1 filter_on_lattice_inf4b filters_on_lattice_inf2b filters_upcl inf.coboundedI2) 

lemma filters_on_lattice_inf6b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<in> (Lower_Bounds (filters_on X) {F1, F2})"
  by (simp add: Lower_Bounds_mem_iff filters_on_iff filters_on_lattice_inf5b lb_double)

lemma filters_on_lattice_inf7b:
  "\<lbrakk>is_filter X F1; is_filter X F2; G \<in> (Lower_Bounds (filters_on X) {F1, F2})\<rbrakk>  \<Longrightarrow>  G \<subseteq>  (F1 \<inter> F2)"
  by (simp add: Lower_Bounds_mem_iff lb_double)

lemma filters_on_lattice_inf8b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk>\<Longrightarrow> is_inf (filters_on X) {F1, F2} (F1 \<inter> F2)"
  by (meson filters_on_lattice_inf6b filters_on_lattice_inf7b is_infI113)

lemma filters_on_lattice_inf_semilattice1:
  "is_lattice X \<Longrightarrow> is_inf_semilattice (filters_on X)"
  by (metis empty_iff filters_is_clr1b filters_on_iff filters_on_lattice_inf8b lattD41 sinfI1)

lemma filters_on_lattice_sup1b:
  "\<lbrakk>is_lattice X; (\<forall>F. F \<in> EF \<longrightarrow> is_filter X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> is_ord_cl X (filter_closure X (\<Union>EF)) (\<le>)"
  by (metis Sup_least all_not_in_conv empty_Union_conv filterD1 filterD2 lattD41 ne_filter_cl1)

lemma filters_on_lattice_sup2a:
  assumes A0:"is_lattice X" and A1:"(\<forall>F. F \<in> EF \<longrightarrow> is_filter X F)" and A2:"EF \<noteq> {}" and
          A3: "a \<in> (filter_closure X (\<Union>EF))" and  A4:"b \<in> (filter_closure X (\<Union>EF))"
  shows "(\<exists>c \<in> (filter_closure X (\<Union>EF)).  a \<ge> c \<and>  b \<ge> c)"
proof-
  obtain Fa Fb where B1:"Fa \<subseteq> (\<Union>EF)" "finite Fa" "Fa \<noteq> {}" "Inf X Fa \<le> a" and 
                     B2:"Fb \<subseteq> (\<Union>EF)" "finite Fb" "Fb \<noteq> {}" "Inf X Fb \<le> b"
   by (metis A3 A4 Pow_empty A1 A2  filterD1 filter_closure_obtains insertI1 subset_Pow_Union subset_singletonD)
  have B3:"Fa \<union> Fb \<subseteq> \<Union>EF \<and> finite (Fa \<union> Fb) \<and> (Fa \<union> Fb) \<noteq> {}"
    by (simp add: B1(1) B1(2) B2(1) B2(2) B2(3))
  have B4:"Fa \<union> Fb \<subseteq> X"
    by (meson A1 B3 Sup_le_iff filterD2 subsetD subsetI)
  have B5:"Inf X (Fa \<union> Fb) \<in>  (filter_closure X (\<Union>EF))"
    by (meson A0 B3 B4 binf_finite2 dual_order.refl filter_closure_memI1 is_infD111 lattD41)
  have B6:"Inf X (Fa \<union> Fb) \<le> a \<and> Inf X (Fa \<union> Fb) \<le> b"
    by (meson A0 B1 B2 B3 B4 Un_upper1 binf_finite2 dual_order.trans is_inf_ant1 lattD41 sup.cobounded2)
  show ?thesis
    using B5 B6 by blast
qed

lemma filters_on_lattice_sup2b:
  "\<lbrakk>is_lattice X;(\<forall>F. F \<in> EF \<longrightarrow> is_filter X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir (filter_closure X (\<Union>EF)) (\<ge>)"
  by (simp add: filters_on_lattice_sup2a is_dwdirI1)

lemma filters_on_lattice_sup3b:
  "\<lbrakk>is_lattice X; (\<forall>F. F \<in> EF \<longrightarrow> is_filter X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> filter_closure X (\<Union>EF) \<noteq> {}"
  by (simp add: Union_least filterD2 filter_closure_ne lattD1)
  
lemma filters_on_lattice_sup4b:
  "\<lbrakk>is_lattice X; (\<forall>F. F \<in> EF \<longrightarrow> is_filter X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> is_filter X (filter_closure X (\<Union>EF))"
  by (simp add: is_filter_def filter_closure_iff filters_on_lattice_sup1b filters_on_lattice_sup2b filters_on_lattice_sup3b subset_iff)

lemma filters_on_lattice_sup5b:
  "\<lbrakk>(\<forall>F. F \<in> EF \<longrightarrow> is_filter X F); EF \<noteq> {}; F \<in> EF\<rbrakk> \<Longrightarrow>  F \<subseteq> (filter_closure X (\<Union>EF))"
  by (meson UnionI Union_least filterD2 filter_closure_singleton subsetI)

lemma filters_on_lattice_sup6b:
  assumes A0:"is_lattice X" and A1:"(\<forall>F. F \<in> EF \<longrightarrow> is_filter X F)" and A2:"EF \<noteq> {}" and
          A3:"is_filter X G"  and A4:"(\<And>F. F \<in> EF \<Longrightarrow> F \<subseteq> G)"
  shows "filter_closure X (\<Union>EF) \<subseteq> G"
proof
  fix x assume A5:"x \<in> filter_closure X (\<Union>EF)"
  obtain Fx where  B1:"Fx \<subseteq>  (\<Union>EF) \<and> finite Fx \<and> Fx \<noteq> {} \<and> Inf X Fx \<le>x"
    by (metis A5 Pow_empty A1 A2 filterD1 filter_closure_obtains insertI1 subset_Pow_Union subset_singletonD)
  have B2:"Fx \<subseteq> G"
    using B1(1) A4  by blast
  have B3:"Fx \<subseteq> X"
    using B2 is_filter_def A3 by auto
  show "x \<in> G"
    by (metis A0 A3 A5 B1 B2 bot.extremum_uniqueI filterD4 filter_closure_iff filter_inf_closed3 is_ord_clE1 lattD41)
qed

lemma filters_on_lattice_sup7b:
  "\<lbrakk>is_lattice X; (\<forall>F. F \<in> EF \<longrightarrow> is_filter X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> is_sup (filters_on X) EF (filter_closure X (\<Union>EF))"
  by(simp add:is_sup_def filters_on_lattice_sup4b filters_on_iff  Upper_Bounds_mem_iff2  filters_on_lattice_sup5b filters_on_lattice_sup6b least_iff)

lemma filters_on_lattice_sup_semilattice1b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> is_sup (filters_on X) {F1, F2} (filter_closure X (F1 \<union> F2))"
  by (metis Union_insert ccpo_Sup_singleton empty_not_insert filters_on_lattice_sup7b insertE singleton_iff)

lemma filters_on_lattice_sup_semilattice2b:
  "is_lattice X \<Longrightarrow> is_sup_semilattice (filters_on X)"
  by (metis filters_on_iff filters_on_lattice_inf_semilattice1 filters_on_lattice_sup_semilattice1b is_inf_semilattice_def is_sup_semilattice_def)

lemma filters_on_lattice_sup_semilattice3b:
  "is_lattice X \<Longrightarrow> EF \<subseteq> (filters_on X) \<Longrightarrow> finite EF \<Longrightarrow> EF \<noteq> {} \<Longrightarrow> (Sup (filters_on X) EF) \<in> filters_on X"
  by (meson bsup_finite2 filters_on_lattice_sup_semilattice2b is_supD111)


definition lorc::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" ("(2[_')\<^sub>_)") where
  "[a)\<^sub>X \<equiv> {y \<in> X. a \<le> y} "

lemma lorcI1:"y \<in> X \<Longrightarrow> a \<le> y \<Longrightarrow> y \<in> [a)\<^sub>X" by (simp add:lorc_def)
lemma lorcD1:"y \<in> [a)\<^sub>X \<Longrightarrow> y \<in> X \<and> a \<le> y" by (simp add:lorc_def)
lemma lorcD11:"y \<in> [a)\<^sub>X \<Longrightarrow> y \<in> X " by (simp add:lorc_def)
lemma lorcD12:"y \<in> [a)\<^sub>X \<Longrightarrow> a \<le> y" by (simp add:lorc_def)

lemma lorcD2:"x \<in> X \<Longrightarrow> y \<in> [a)\<^sub>X \<Longrightarrow>  y \<le> x \<Longrightarrow> x \<in> [a)\<^sub>X"
  by(drule lorcD12, erule lorcI1, simp)

lemma lorcD3:
  "(\<exists>b. b \<le> x \<and> b \<in> [a)\<^sub>X) \<Longrightarrow> x \<in> X \<Longrightarrow>  x \<in> [a)\<^sub>X"
  using lorcD2 by blast

lemma lorc_mem_iff1:
  "y \<in> ([a)\<^sub>X) \<longleftrightarrow> (y \<in> X \<and> a \<le> y)" by (simp add:lorc_def)

lemma lorc_mem_iff2:
  "y \<in> ([a)\<^sub>X) \<longleftrightarrow> (y \<in> X \<and> y ub {a})" by (simp add:lorc_def ub_def)

lemma lorc_eq_upbd:
  "([a)\<^sub>X) = (Upper_Bounds X {a})"
  by(simp add: set_eq_iff Upper_Bounds_mem_iff lorc_mem_iff2)

lemma lorc_memI1:
  "a \<in> X \<Longrightarrow> a \<in> [a)\<^sub>X "
  by (simp add: lorcI1)

lemma lorc_mem_point1:
  "a \<in> X \<longleftrightarrow> a \<in> ([a)\<^sub>X)"
  by (simp add: lorc_def)

lemma lorc_subset1:
  "([a)\<^sub>X) \<subseteq> X"
  by (simp add: Upper_Bounds_sub lorc_eq_upbd)

lemma lorc_top:
  "is_greatest X m \<Longrightarrow> a \<in> X \<Longrightarrow> m \<in> [a)\<^sub>X"
  by (simp add: greatestD11 greatestD2 lorcI1)

lemma lorc_sup_latticeD1:
  "\<lbrakk>is_sup_semilattice X; x \<in> X; y \<in> X\<rbrakk>\<Longrightarrow> Sup X {x, y} \<in> ([x)\<^sub>X)"
  by (simp add: bsup_geI1 lorcI1 ssupD4)

lemma lorc_inf_latticeD1:
  "\<lbrakk>is_least X bot\<rbrakk> \<Longrightarrow> ([bot)\<^sub>X) = X"
  by(auto simp add: lorc_mem_iff1 least_iff)

lemma lorc_dual_iso:
  "\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> ([a)\<^sub>X) \<subseteq> ([b)\<^sub>X)  \<longleftrightarrow> b \<le> a"
  by(auto simp add:lorc_mem_iff1) 

lemma lorc_upclI:
  "a \<in> X \<Longrightarrow> is_ord_cl X ([a)\<^sub>X) (\<le>)"
  by (simp add: is_ord_clI1 lorcD2)

lemma lorc_upclD:
  "U \<subseteq> X \<Longrightarrow> is_ord_cl X U (\<le>) \<Longrightarrow> is_least U x \<Longrightarrow> U = [x)\<^sub>X"
  apply (auto simp add: in_mono leastD2 lorcI1)
  by (meson is_ord_clE1 leastD11 lorcD1)

lemma lorc_upcl1:
  "\<lbrakk>is_greatest X m; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> m \<in> (\<Inter>a \<in> A. [a)\<^sub>X)"
  by (simp add: greatestD11 greatestD2 in_mono lorcI1)

lemma lorc_upcl3:
  "\<lbrakk>is_greatest X m; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow>  is_ord_cl X (\<Inter>a \<in> A. [a)\<^sub>X) (\<le>)"
  by(rule is_ord_cl_in2, auto simp add: lorc_mem_iff1, simp add: in_mono lorc_upclI)
  

definition ord_cl_sets::"'a::order set \<Rightarrow> ('a::order \<Rightarrow> 'a::order \<Rightarrow> bool) \<Rightarrow> 'a::order set set" where
  "ord_cl_sets X ord \<equiv> {A. A \<subseteq> X \<and> is_ord_cl X A (ord)}"

lemma lorc_upcl4:
  "\<lbrakk>is_greatest X m; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> {m} \<in> ord_cl_sets X (\<le>)"
  by (simp add: filterD4 greatestD11 min_filter1 ord_cl_sets_def)

lemma lorc_moore:
  "\<lbrakk>is_greatest X m\<rbrakk> \<Longrightarrow> is_clr (ord_cl_sets X (\<le>)) (Pow X)"  
  apply(rule moore_clI3, auto simp add:ord_cl_sets_def is_ord_cl_space is_ord_cl_def) by blast


definition galois_conn::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a::order set \<Rightarrow> ('b::order \<Rightarrow> 'a::order) \<Rightarrow> 'b::order set \<Rightarrow> bool" where
  "galois_conn f X g Y \<equiv> (f`X \<subseteq> Y) \<and> (g`Y \<subseteq> X) \<and> (\<forall>x \<in> X. \<forall>y \<in> Y.  (x \<le> g y \<longleftrightarrow> y \<le> f x))"

lemma galois_connD11:
  "galois_conn f X g Y \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> x \<le>  g y \<Longrightarrow> y \<le> f x" by (simp add:galois_conn_def)

lemma galois_connD21:
  "galois_conn f X g Y \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> y \<le> f x \<Longrightarrow> x \<le> g y" by (simp add:galois_conn_def)

lemma galois_connD12:
  "galois_conn f X g Y \<Longrightarrow> y \<in> Y \<Longrightarrow> g y \<in> X" by (simp add:galois_conn_def image_subset_iff)

lemma galois_connD22:
  "galois_conn f X g Y \<Longrightarrow> x \<in> X  \<Longrightarrow> f x \<in> Y" by (simp add:galois_conn_def image_subset_iff)


lemma gc_cext1:
  "\<lbrakk>galois_conn f X g Y; x \<in> X\<rbrakk> \<Longrightarrow> x \<le> g (f x) "
  by(simp add: galois_connD22[of f X g Y x] galois_connD21[of f X g Y x "f x"])

lemma gc_cext2:
  "\<lbrakk>galois_conn f X g Y; y \<in> Y\<rbrakk> \<Longrightarrow> y \<le> f (g y) "
  by(simp add: galois_connD12[of f X g Y "y"] galois_connD11[of f X g Y "g y" y])
 

lemma gc_anti1:
  "\<lbrakk>galois_conn f X g Y; x1 \<in> X; x2 \<in> X; x1 \<le> x2\<rbrakk> \<Longrightarrow> f x2 \<le> f x1 "
  by(simp add:gc_cext1[of f X g Y x2]  galois_connD11[of f X g Y x1 "f x2"] galois_connD22[of f X g Y x2] order.trans)

lemma gc_anti2:
  "\<lbrakk>galois_conn f X g Y; y1 \<in> Y; y2 \<in> Y; y1 \<le> y2\<rbrakk> \<Longrightarrow> g y2 \<le> g y1 "
  by(simp add:gc_cext2[of f X g Y y2]  galois_connD21[of f X g Y "g y2" y1]  galois_connD12[of f X g Y y2] order.trans)


end



