theory Posets15
  imports Main
begin

section Settings
hide_const top
hide_const(open) List.list.Nil
no_notation List.list.Nil ("[]")  
no_notation Cons (infixr "#" 65) 
hide_type list
hide_const rev
declare [[show_consts,show_sorts,show_types, show_results]]


section Misc

lemma image_p:
  "(\<And>a. a \<in> A \<Longrightarrow> P (f a)) \<Longrightarrow> (\<forall>y \<in> f ` A.  P(y))"
  by blast

lemma un_to_ind_un:
  "(\<And>(A::'a set set). P A \<Longrightarrow> Q (\<Union>A)) \<Longrightarrow> (\<And>(f::('b \<Rightarrow> 'a set)) (I::'b set). P(f`I) \<Longrightarrow> Q(\<Union>i \<in> I. f i))"
  by simp

lemma int_to_ind_int:
  "(\<And>(A::'a set set). P A \<Longrightarrow> Q (\<Inter>A)) \<Longrightarrow> (\<And>(f::('b \<Rightarrow> 'a set)) (I::'b set). P(f`I) \<Longrightarrow> Q(\<Inter>i \<in> I. f i))"
  by simp

definition Pow_ne::"'a set \<Rightarrow> 'a set set" where
  "Pow_ne X = Pow X - {{}}"

lemma pow_ne_iff1:
  "A \<in> Pow_ne X \<longleftrightarrow> A \<in> Pow X \<and> A \<noteq> {}"
  by (simp add: Pow_ne_def)

lemma pow_ne_iff2:
  "A \<in> Pow_ne X \<longleftrightarrow> A \<subseteq> X \<and> A \<noteq> {}"
  by (simp add: Pow_ne_def)

lemma pow_neI:
  "A \<subseteq> X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> A \<in> Pow_ne X"
  by(simp add:Pow_ne_def)

lemma pow_neD1:
  "A \<in> Pow_ne X \<Longrightarrow> A \<subseteq> X "
  by(simp add:Pow_ne_def)

lemma pow_neD2:
  " A \<in> Pow_ne X \<Longrightarrow> A \<noteq> {} "
  by(simp add:Pow_ne_def)

lemma pow_ne_bot:
  "{} \<notin> Pow_ne X"
  by(simp add:Pow_ne_def)
               
lemma pow_ne_top:
  "X \<noteq> {} \<Longrightarrow> X \<in> Pow_ne X"
  by(simp add:Pow_ne_def)


definition Fpow_ne::"'a set \<Rightarrow> 'a set set" where
  "Fpow_ne X = Fpow X - {{}}"

lemma fpow_ne_iff1:
  "A \<in> Fpow_ne X \<longleftrightarrow> A \<in> Fpow X \<and> A \<noteq> {}"
  by (simp add: Fpow_ne_def)

lemma fpow_ne_iff2:
  "A \<in> Fpow_ne X \<longleftrightarrow> A \<subseteq> X \<and> finite A \<and> A \<noteq> {}"
  by (simp add: Fpow_Pow_finite fpow_ne_iff1)

lemma fpow_neI:
  "A \<subseteq> X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> A \<in> Fpow_ne X"
  by (simp add: Fpow_def fpow_ne_iff1)

lemma fpow_neD0:
  "A \<in> Fpow_ne X \<Longrightarrow> A \<in> Pow X "
  by (simp add: fpow_ne_iff2)

lemma fpow_neD1:
  "A \<in> Fpow_ne X \<Longrightarrow> A \<subseteq> X "
  by (simp add: fpow_ne_iff2)

lemma fpow_neD2:
  " A \<in> Fpow_ne X \<Longrightarrow> A \<noteq> {} "
  by (simp add: fpow_ne_iff2)

lemma fpow_ne_bot:
  "{} \<notin> Fpow_ne X"
  by (simp add: fpow_ne_iff1)


section Bounds
subsection UpperBoundsPredicate

definition ub::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> bool" (infix "ub" 50) where 
   "x ub  A \<equiv> (\<forall>a. a \<in> A \<longrightarrow> a \<le> x)"

lemma ubI: 
  "(\<And>a. a \<in> A \<Longrightarrow> a \<le> x) \<Longrightarrow> x ub A" 
  by (simp add:ub_def)
print_facts!

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

lemma ub_imageI:
  "(\<And>a. a \<in> A \<Longrightarrow> x \<ge> f a) \<Longrightarrow> x ub (f`A)"
  by(simp add:ub_def image_p[of "A" "\<lambda>a. x \<ge> a" "f"])


subsection UpperBoundsSet

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

lemma ubd_mem_insert:
  "\<lbrakk>c \<in> Upper_Bounds X F; c \<ge> x\<rbrakk> \<Longrightarrow> c \<in> Upper_Bounds X (insert x F)"
  by (simp add: Upper_Bounds_mem_iff ub_insert)

lemma ubd_mem_binary:
  "\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> a \<le> b \<longleftrightarrow> b \<in> Upper_Bounds X {a, b}"
  by (simp add: Upper_Bounds_mem_iff ub_binary)

lemma ubd_mem_double:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> c \<in> Upper_Bounds X {a, b} \<longleftrightarrow> c \<ge> a \<and> c \<ge> b"
  by (simp add: Upper_Bounds_mem_iff ub_double)

lemma ne_subset_ne:
  "A \<subseteq> B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> B \<noteq> {}"
  by blast

lemma upbd_neE1:
  "Upper_Bounds X A \<noteq> {} \<Longrightarrow> a \<in> A \<Longrightarrow> (\<exists>x. x \<in> X \<and> a \<le> x)"
  using Upper_BoundsD1 Upper_Bounds_sub by blast

lemma upbd_neE3:
  "Upper_Bounds X {a} \<noteq> {} \<Longrightarrow> (\<exists>x \<in> X. a \<le> x)"
  using upbd_neE1 by auto

lemma ubd_eqI1:
  "(\<And>x. x \<in> X \<Longrightarrow> x ub A \<Longrightarrow> x ub B) \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x ub B \<Longrightarrow> x ub A) \<Longrightarrow> Upper_Bounds X A = Upper_Bounds X B"
  by(auto simp add:set_eq_iff Upper_Bounds_mem_iff)


subsection LowerBoundsPredicate

definition lb::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> bool" (infix "lb" 50) where 
   "x lb  A \<equiv> (\<forall>a. a \<in> A \<longrightarrow> a \<ge> x)"

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

lemma lb_imageI:
  "(\<And>a. a \<in> A \<Longrightarrow> x \<le> f a) \<Longrightarrow> x lb (f`A)"
  by(simp add:lb_def image_p[of "A" "\<lambda>a. x \<le> a" "f"])


subsection LowerBoundsSet
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

lemma lbd_eqI1:
  "(\<And>x. x \<in> X \<Longrightarrow> x lb A \<Longrightarrow> x lb B) \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x lb B \<Longrightarrow> x lb A) \<Longrightarrow> Lower_Bounds X A = Lower_Bounds X B"
  by(auto simp add:set_eq_iff Lower_Bounds_mem_iff)

subsection Composition

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


section AbsoluteExtrema
subsection GreatestPredicate
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

lemma greatest_iff:
  "is_greatest A m \<longleftrightarrow> (m \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> a \<le> m))"
  by (simp add: Upper_Bounds_mem_iff is_greatest_def ub_def)

lemma greatest_unique:
  "is_greatest A m1 \<Longrightarrow> is_greatest A m2 \<Longrightarrow> m1 =m2"
  by (simp add: greatest_iff order_antisym)

lemma is_greatest_iso2:
  "A \<subseteq> B \<Longrightarrow> is_greatest A ma \<Longrightarrow> is_greatest B mb \<Longrightarrow> ma \<le> mb"
  using greatestD11 greatestD2 by blast



lemma greatest_singleton:
  "is_greatest {x} x"
  by (simp add: greatestI2 ub_singleton)

lemma singleton_ex_greatest:
  "\<exists>m. is_greatest {x} m"
  using greatest_singleton by blast


lemma greatest_insert1:
  "x ub A \<Longrightarrow> is_greatest (insert x A) x"
  by (simp add: greatestI2 ub_insert)

lemma greatest_insert2:
  "is_greatest A m \<Longrightarrow> x \<le> m \<Longrightarrow> is_greatest (insert x A) m"
  by (simp add: greatestD11 greatestI2 greatestD12 ub_insert)

lemma greatest_insert3:
  "is_greatest A m \<Longrightarrow> m \<le> x \<Longrightarrow> is_greatest (insert x A) x"
  by (simp add: greatest_insert1 greatestD12 ub_iso1)

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

subsection GreatestOperator

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

lemma lb_single_least1:
  "x \<in> X \<Longrightarrow> is_greatest (Lower_Bounds X {x}) x"
  by (simp add: Lower_BoundsD1 Lower_Bounds_singleton greatestI3)

lemma lb_single_least2:
  "x \<in> X \<Longrightarrow> Greatest (Lower_Bounds X {x}) = x"
  by (simp add: greatest_equality2 lb_single_least1)

lemma greatest_exD4:
  "(\<exists>m. is_greatest A m) \<Longrightarrow>  Greatest A ub A"
  using greatestD1 greatest_equality2 by blast

lemma greatest_insert1b:
  "x ub A \<Longrightarrow> Greatest (insert x A) = x"
  by (simp add: greatest_equality2 greatest_insert1)

subsection LeastPredicate

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

lemma least_singleton:
  "is_least {x} x"
  by (simp add: lb_singleton leastI2)

lemma singleton_ex_least:
  "\<exists>m. is_least {x} m"
  using least_singleton by blast

lemma least_pair:
  "is_least {a, b} a \<longleftrightarrow> a \<le> b"
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

subsection LeastOperator

definition Least::"'a::order set \<Rightarrow> 'a::order" where
  "Least A \<equiv> (THE m. is_least A m)"

lemma least_equality2:
  "is_least A m \<Longrightarrow> Least A = m"
  by (simp add: Least_def least_unique the_equality) 

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

section Extrema
subsection Suprema

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
   
lemma is_supI1:
  "is_least (Upper_Bounds X A) x \<Longrightarrow> is_sup X A x"
  by (simp add: is_sup_def) 

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

lemma sup_singleton:
  "s \<in> X \<Longrightarrow> is_sup X {s} s"
  by (simp add: is_supI1 ub_single_least1)

lemma sup_empty:
  "is_sup X {} i \<longleftrightarrow> (is_least X i)"
  by (simp add: Upper_Bounds_empty is_sup_def)

lemma binary_supI1:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; x1 \<le> x2\<rbrakk> \<Longrightarrow> is_sup X {x1, x2} x2"
  by(simp add:is_sup_def is_least_def Lower_Bounds_def Upper_Bounds_def lb_def ub_def) 

lemma binary_supD21:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; x3 \<in> X;s \<in> X;is_sup X {x1, x2} s; x3 \<le> x1\<rbrakk> \<Longrightarrow>  x3 \<le> s"
  by (metis dual_order.trans is_supD112 ub_double)

lemma binary_supD22:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; x3 \<in> X;s \<in> X;is_sup X {x1, x2} s; x3 \<le> x2\<rbrakk> \<Longrightarrow>  x3 \<le> s"
  by (metis dual_order.trans is_supD112 ub_double)

lemma binary_supD32:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; s \<in> X; is_sup X {x1, x2} s\<rbrakk>  \<Longrightarrow>  x2 \<le> s"
  by (simp add: is_supD1121)

lemma binary_supD4:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; x3 \<in> X; s \<in> X; is_sup X {x1, x2} s\<rbrakk>  \<Longrightarrow> (s \<le> x3 \<longleftrightarrow> x1 \<le> x3 \<and> x2 \<le> x3)"
  by (simp add: sup_iff2 ubd_mem_double)

lemma sup_insert1:
  "\<lbrakk>x ub A; x \<in> X\<rbrakk> \<Longrightarrow> is_sup X (insert x A) x"
  by (metis greatest_exD4 greatest_insert1 greatest_insert1b insertI1 is_supI115 ubD)

lemma sup_insert2:
  "\<lbrakk>is_sup X A m;  x \<le> m\<rbrakk> \<Longrightarrow> is_sup X (insert x A) m"
  by (meson Upper_Bounds_ant1 is_supD111 is_supD112 is_supD12 is_supI112 lb_ant2 subset_insertI ub_insert)

lemma sup_insert3:
  "\<lbrakk>is_sup X A m; m \<le> x; x \<in> X\<rbrakk> \<Longrightarrow> is_sup X (insert x A) x"
  by (simp add: is_supD41 sup_insert1)

lemma sup_insert61:
  "\<lbrakk>is_sup X A s1; is_sup X {s1, x} s2\<rbrakk> \<Longrightarrow> s2 ub A"
  by (simp add: is_supD1121 is_supD31)  

lemma sup_insert62:
  "\<lbrakk>is_sup X A s1; is_sup X {s1, x} s2\<rbrakk> \<Longrightarrow> s2 \<in> Upper_Bounds X A"
  by (simp add: Upper_Bounds_mem_iff sup_insert61 is_supD111)

lemma sup_insert7:
  "\<lbrakk>is_sup X A s1; is_sup X {s1, x} s2; u \<in> Upper_Bounds X (insert x A)\<rbrakk> \<Longrightarrow>  s2 \<le> u"
  by (simp add: Upper_Bounds_mem_iff2 is_supD121)

lemma ub_eq_sup_eq:
  "(\<And>x. x ub A \<longleftrightarrow> x ub B) \<Longrightarrow> (is_sup X A s \<longleftrightarrow> is_sup X B s)"
  by (simp add: Upper_Bounds_mem_iff sup_iff2)

lemma Upper_eq_sup_eq:
  "Upper_Bounds X A = Upper_Bounds X B \<Longrightarrow> (is_sup X A s \<longleftrightarrow> is_sup X B s)"
  by (simp add: is_sup_def)

definition Sup::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order" where
  "Sup X A \<equiv> (THE m. is_sup X A m)"

lemma sup_equality:
  "is_sup X A m \<Longrightarrow> Sup X A = m"
  by (simp add: Sup_def is_sup_unique the_equality) 

lemma sup_exI:
  "\<exists>s. is_sup X A s \<Longrightarrow> (\<And>s. is_sup X A s \<Longrightarrow> P s) \<Longrightarrow> P (Sup X A)"
  using sup_equality by auto

lemma sup_families1:
  "A \<noteq> {} \<Longrightarrow> (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_sup X Ai si) \<Longrightarrow> x \<in> X \<Longrightarrow> x ub Sup X ` A \<Longrightarrow> x ub \<Union> A"
  by (metis Union_iff imageI sup_equality is_supD32 ub_def)

lemma sup_families2:
  "A \<noteq> {} \<Longrightarrow> (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_sup X Ai si) \<Longrightarrow> x \<in> X \<Longrightarrow> x ub \<Union> A \<Longrightarrow>  x ub Sup X ` A"
   by (metis ub_imageI Union_upper sup_equality is_supD5 ub_ant2)

lemma sup_families:
  "A \<noteq> {} \<Longrightarrow>(\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_sup X Ai si) \<Longrightarrow>(is_sup X ((\<lambda>Ai. Sup X Ai)`A) s) \<longleftrightarrow> (is_sup X (\<Union>A) s)"
  apply(rule Upper_eq_sup_eq, rule ubd_eqI1) using sup_families1 apply blast using sup_families2 by blast

subsection Infima

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

lemma is_infD3:
  "\<lbrakk>is_inf X A x; z \<in> X;  z \<le> x\<rbrakk> \<Longrightarrow> z \<in> Lower_Bounds X A"
  by (simp add: Lower_Bounds_mem_iff is_infD112 lb_iso1)

lemma is_infD31:
  "\<lbrakk>is_inf X A x;  z \<le> x\<rbrakk> \<Longrightarrow> z lb A"
  by (simp add: is_infD112 lb_iso1)

lemma is_infD32:
  "\<lbrakk>is_inf X A x;  z \<le> x; a \<in> A\<rbrakk> \<Longrightarrow> z \<le> a"
  by (simp add: is_infD31[of "X" "A" "x" "z"] lbD[of "z" "A" "a"])


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

lemma inf_singleton:
  "s \<in> X \<Longrightarrow> is_inf X {s} s"
  by (simp add: is_infI115 lbD lb_singleton)

lemma inf_empty:
  "is_inf X {} i \<longleftrightarrow> (is_greatest X i)"
  by (simp add: Lower_Bounds_empty is_inf_def)

lemma binary_infD21:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; x3 \<in> X;s \<in> X;is_inf X {x1, x2} s; x3 \<ge> x1\<rbrakk> \<Longrightarrow>  x3 \<ge> s"
  by (meson dual_order.trans is_infD112 lb_double)

lemma binary_infD22:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; x3 \<in> X;s \<in> X;is_inf X {x1, x2} s; x3 \<ge> x2\<rbrakk> \<Longrightarrow>  x3 \<ge> s"
  by (metis dual_order.trans is_infD112 lb_double)

lemma binary_infD4:
  "\<lbrakk>x1 \<in> X; x2 \<in> X; x3 \<in> X; s \<in> X; is_inf X {x1, x2} s\<rbrakk>  \<Longrightarrow> (s \<ge> x3 \<longleftrightarrow> x1 \<ge> x3 \<and> x2 \<ge> x3)"
  by (simp add: inf_iff2 lbd_mem_double)

lemma inf_insert1:
  "\<lbrakk>x lb A; x \<in> X\<rbrakk> \<Longrightarrow> is_inf X (insert x A) x"
  by (simp add: is_infI115 lbD leastD1 least_insert1)

lemma inf_insert2:
  "\<lbrakk>is_inf X A m;  m \<le> x\<rbrakk> \<Longrightarrow> is_inf X (insert x A) m"
  by (metis insert_iff is_infD111 is_infD112 is_infD122 is_infI115 lb_def)

lemma inf_insert3:
  "\<lbrakk>is_inf X A m; x \<le> m; x \<in> X\<rbrakk> \<Longrightarrow> is_inf X (insert x A) x"
  by (simp add: is_infD41 inf_insert1)

lemma inf_insert61:
  "\<lbrakk>is_inf X A i1; is_inf X {i1, x} i2\<rbrakk> \<Longrightarrow> i2 lb A"
  by (simp add: is_infD1121 is_infD31)  

lemma inf_insert62:
  "\<lbrakk>is_inf X A i1; is_inf X {i1, x} i2\<rbrakk> \<Longrightarrow> i2 \<in> Lower_Bounds X A"
  by (simp add: Lower_Bounds_mem_iff inf_insert61 is_infD111)

lemma inf_insert7:
  "\<lbrakk>is_inf X A i1; is_inf X {i1, x} i2; l \<in> Lower_Bounds X (insert x A)\<rbrakk> \<Longrightarrow>  l \<le> i2"
  by (simp add: Lower_Bounds_mem_iff2 is_infD121)

lemma Lower_eq_inf_eq:
  "Lower_Bounds X A = Lower_Bounds X B \<Longrightarrow> (is_inf X A i \<longleftrightarrow> is_inf X B i)"
  by (simp add: is_inf_def)

lemma lb_eq_inf_eq:
  "(\<And>x. x lb A \<longleftrightarrow> x lb B) \<Longrightarrow> (is_inf X A i \<longleftrightarrow> is_inf X B i)"
  by (simp add: Lower_Bounds_mem_iff inf_iff2)


definition Inf::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order" where
  "Inf X A \<equiv> (THE m. is_inf X A m)"

lemma inf_equality:
  "is_inf X A m \<Longrightarrow> Inf X A = m"
  by (simp add: Inf_def is_inf_unique the_equality) 

lemma inf_exI:
  "\<exists>t. is_inf X A t \<Longrightarrow> (\<And>t. is_inf X A t \<Longrightarrow> P t) \<Longrightarrow> P (Inf X A)"
  using inf_equality by auto

lemma inf_families1:
  "A \<noteq> {} \<Longrightarrow> (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>ti. is_inf X Ai ti) \<Longrightarrow> x \<in> X \<Longrightarrow> x lb Inf X ` A \<Longrightarrow> x lb \<Union> A"
  by (metis Union_iff imageI inf_equality is_infD32 lb_def)

lemma inf_families2:
  "A \<noteq> {} \<Longrightarrow> (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>ti. is_inf X Ai ti) \<Longrightarrow> x \<in> X \<Longrightarrow> x lb \<Union> A \<Longrightarrow>  x lb Inf X ` A"
   by (metis lb_imageI  Union_upper inf_equality is_infD5 lb_ant2)

lemma inf_families:
  "A \<noteq> {} \<Longrightarrow>(\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>ti. is_inf X Ai ti) \<Longrightarrow>(is_inf X ((\<lambda>Ai. Inf X Ai)`A) t) \<longleftrightarrow> (is_inf X (\<Union>A) t)"
  apply(rule Lower_eq_inf_eq, rule lbd_eqI1) using inf_families1 apply blast using inf_families2 by blast

subsection Duality

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
 
subsection InfSemilattices

definition is_inf_semilattice::"'a::order set \<Rightarrow> bool" where
  "is_inf_semilattice X \<equiv> (X \<noteq> {}) \<and> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>x. is_inf X {a, b} x))"

definition is_finf_closed::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_finf_closed X A \<equiv> (\<forall>a1 a2. a1 \<in> A \<and>  a2 \<in> A \<longrightarrow> Inf X {a1, a2} \<in> A)"

lemma sinfI1:
  "\<lbrakk>(X \<noteq> {});  (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>x. is_inf X {a, b} x))\<rbrakk> \<Longrightarrow> is_inf_semilattice X"
  by (simp add:is_inf_semilattice_def)

lemma sinfD2:
  "\<lbrakk>is_inf_semilattice X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>x. is_inf X {a, b} x) "
  by (simp add: is_inf_semilattice_def)

lemma sinfD3:
  "\<lbrakk>is_inf_semilattice X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> is_inf X {a, b} (Inf X {a, b}) "
  using inf_equality sinfD2 by blast

lemma sinfD4:
  "\<lbrakk>is_inf_semilattice X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> (Inf X {a, b}) \<in> X"
  using is_infD111 sinfD3 by blast


lemma binf_leI1:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X; a \<le> c\<rbrakk>  \<Longrightarrow> Inf X {a, b} \<le> c"
  by (simp add: binary_infD21 sinfD3 sinfD4)

lemma binf_leI2:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X; b \<le> c\<rbrakk>  \<Longrightarrow> Inf X {a, b} \<le> c"
  by (simp add: binary_infD22 sinfD3 sinfD4)

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


lemma binfI:
  "\<lbrakk>is_inf_semilattice X; (\<And>s. is_inf X {a, b} s \<Longrightarrow> P s); a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> P (Inf X {a, b})"
  by (simp add: sinfD3)

lemma binf_commute:
  "is_inf X {a, b} c \<longleftrightarrow> is_inf X {b, a } c "
  by (simp add: insert_commute)

lemma binf_leI3:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X; c \<le>a; c \<le> b\<rbrakk>  \<Longrightarrow>c \<le> Inf X {a, b}"
  by (simp add: binary_infD4 sinfD3 sinfD4)

lemma binf_iff:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X\<rbrakk>  \<Longrightarrow> (c \<le> Inf X {a, b} \<longleftrightarrow> c \<le> a \<and> c \<le> b)"
  by (simp add: binary_infD4 sinfD3 sinfD4)

lemma binf_assoc1:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow>  Inf X {Inf X {a, b}, c} = Inf X {a,  Inf X {b, c}}"
  apply(rule order.antisym) by (metis sinfD3 binf_iff is_infD111 order_refl)+

lemma binf_assoc2:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf X {a, Inf X {b, c}} = Inf X {b, Inf X {a, c}}"
  apply(rule order.antisym) by (simp add: binf_leI1 binf_leI2 binf_leI3 sinfD4)+

lemma binf_commute2:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> Inf X {a, b}  =  Inf X {b,a}"
  by (simp add: insert_commute)

lemma binf_idem1:
  "a\<in> X \<Longrightarrow> (\<lambda>x y. Inf X {x, y}) a a = a"
  by (simp add:  inf_equality inf_singleton)

lemma binf_idem2:
  "is_inf_semilattice X \<Longrightarrow>a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> Inf X {a, Inf X {a, b}} = Inf X {a, b}"
  by (metis binf_assoc1 binf_idem1)

lemma binf_idem3:
  "is_inf_semilattice X \<Longrightarrow> a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow>  Inf X {Inf X {a, b}, b} = Inf X {a, b}"
  by (metis binf_assoc1 binf_idem1)

lemma binf_lt1:
  "is_inf_semilattice X\<Longrightarrow>a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> a \<le> b \<Longrightarrow>  Inf X {a, b} = a"
  by (simp add: dual_order.eq_iff binf_iff binf_leI1)

lemma binf_lt2:
  "is_inf_semilattice X \<Longrightarrow>a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> b \<le> a \<Longrightarrow> Inf X {a, b} = b"
  by (simp add: dual_order.eq_iff binf_iff binf_leI2)


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

subsection SupSemilattices

definition is_sup_semilattice::"'a::order set \<Rightarrow> bool" where
  "is_sup_semilattice X \<equiv> (X \<noteq> {}) \<and> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>x. is_sup X {a, b} x))"

definition is_fsup_closed::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_fsup_closed X A \<equiv> (\<forall>a1 a2. a1 \<in> A \<and>  a2 \<in> A \<longrightarrow> Sup X {a1, a2} \<in> A)"

lemma ssupD2:
  "\<lbrakk>is_sup_semilattice X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup X {a, b} x) "
  by (simp add: is_sup_semilattice_def)

lemma ssupD3:
  "\<lbrakk>is_sup_semilattice X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> is_sup X {a, b} (Sup X {a, b}) "
  using ssupD2 sup_equality by blast

lemma ssupD4:
  "\<lbrakk>is_sup_semilattice X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow>  (Sup X {a, b}) \<in> X"
  using is_supD111 ssupD3 by blast

lemma bsup_geI1:
  "\<lbrakk>is_sup_semilattice X;a \<in> X; b \<in> X; c \<in> X; a \<ge> c\<rbrakk>  \<Longrightarrow> Sup X {a, b} \<ge> c"
  by (simp add: binary_supD21 ssupD3 ssupD4)

lemma bsup_geI2:
  "\<lbrakk>is_sup_semilattice X;a \<in> X; b \<in> X; c \<in> X; b \<ge> c\<rbrakk>  \<Longrightarrow> Sup X {a, b} \<ge> c"
  by (simp add: binary_supD22 ssupD3 ssupD4)

lemma bsup_iff:
  "\<lbrakk>is_sup_semilattice X; a \<in> X; b \<in> X; c \<in> X\<rbrakk>  \<Longrightarrow> (c \<ge> Sup X {a, b} \<longleftrightarrow> c \<ge> a \<and> c \<ge> b)"
  by (simp add: binary_supD4 ssupD3 ssupD4)


lemma bsup_idem1:
  "a\<in> X \<Longrightarrow> (\<lambda>x y. Sup X {x, y}) a a = a"
  by (simp add: sup_equality sup_singleton)


lemma bsupI:
  "\<lbrakk>is_sup_semilattice X; (\<And>s. is_sup X {a, b} s \<Longrightarrow> P s); a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> P (Sup X {a, b})"
  by (metis is_sup_semilattice_def sup_equality)

lemma bsup_commute:
  "is_sup X {a, b} c \<longleftrightarrow> is_sup X {b, a } c "
  by (simp add: insert_commute)

lemma bsup_geI3:
  "\<lbrakk>is_sup_semilattice X;a \<in> X; b \<in> X; c \<in> X; c \<ge>a; c \<ge> b\<rbrakk> \<Longrightarrow> c \<ge> Sup X {a, b}"
  by (simp add: binary_supD4 ssupD3 ssupD4)

lemma bsup_assoc1:
  "\<lbrakk>is_sup_semilattice X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup X {Sup X {a, b}, c} =Sup X {a, Sup X {b, c}}"
  apply(rule order.antisym) by (metis ssupD3 bsup_iff is_supD111 order_refl)+

lemma bsup_assoc2:
  "\<lbrakk>is_sup_semilattice X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup X {a, Sup X {b, c}} = Sup X {b, Sup X {a, c}}"
  apply(rule order.antisym) by (metis ssupD3 bsup_iff is_supD111 order_refl)+

lemma bsup_commute2:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> Sup X {a, b} =  Sup X  {b, a}"
  by (simp add: insert_commute)

lemma bsup_idem2:
  "is_sup_semilattice X \<Longrightarrow>a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow>  Sup X{ a, Sup X {a, b}} =  Sup X {a, b}"
  by (metis bsup_assoc1 bsup_idem1)

lemma bsup_idem3:
  "is_sup_semilattice X \<Longrightarrow> a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> Sup X {Sup X {a, b}, b} =  Sup X {a, b}"
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

subsection Lattices

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

subsection CompleteLattices

definition is_cinf_semilattice::"'a::order set \<Rightarrow> bool" where
  "is_cinf_semilattice X \<equiv> (X \<noteq> {}) \<and> (\<forall>A. A \<subseteq> X \<and> A \<noteq> {} \<longrightarrow> (\<exists>x. is_inf X A x))"

definition is_cinf_closed::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_cinf_closed X A \<equiv> (\<forall>E. E \<subseteq> A\<longrightarrow> E \<noteq>{} \<longrightarrow> Inf X E \<in> A)"

definition is_csup_semilattice::"'a::order set \<Rightarrow> bool" where
  "is_csup_semilattice X \<equiv> (X \<noteq> {}) \<and> (\<forall>A. A \<subseteq> X \<and> A \<noteq> {} \<longrightarrow> (\<exists>x. is_sup X A x))"

definition is_csup_closed::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_csup_closed X A \<equiv> (\<forall>E. E \<subseteq> A \<longrightarrow> E \<noteq>{} \<longrightarrow> Inf X E \<in> A)"

definition is_clattice::"'a::order set \<Rightarrow> bool" where
  "is_clattice X \<equiv> (X \<noteq> {}) \<and> (\<forall>A. A \<subseteq> X \<longrightarrow> (\<exists>s. is_sup X A s))"

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


lemma csup_fsup:
  "is_csup_semilattice X \<Longrightarrow> is_sup_semilattice X"
  by (simp add: is_csup_semilattice_def is_sup_semilattice_def)

lemma cinf_sinf:
  "is_cinf_semilattice X \<Longrightarrow> is_inf_semilattice X"
  by (simp add: is_cinf_semilattice_def is_inf_semilattice_def)

lemma pow_is_clattice1:
  "A \<subseteq> Pow X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> is_inf (Pow X) A  (\<Inter>A)"
  by(auto simp add:is_inf_def is_greatest_def Upper_Bounds_def Lower_Bounds_def ub_def lb_def)

lemma pow_is_clattice2:
  "is_inf (Pow X) {} X"
  by(auto simp add:is_inf_def is_greatest_def Upper_Bounds_def Lower_Bounds_def ub_def lb_def)

lemma pow_is_clattice3:
  "A \<subseteq> Pow X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> is_sup (Pow X) A  ( \<Union>A)"
  by(auto simp add:is_sup_def is_least_def Upper_Bounds_def Lower_Bounds_def ub_def lb_def)

lemma pow_is_clattice:
  "is_clattice (Pow X)"
   using  pow_is_clattice3 apply(auto simp add:is_clattice_def)
   by (metis Pow_not_empty Upper_Bounds_empty pow_is_clattice1 subset_refl sup_if_inf_ub)

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


lemma is_iso_sup:
  "is_isotone X f \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_sup X A x \<Longrightarrow> is_sup (f`X) (f`A) y  \<Longrightarrow> y \<le> f x"
  by (simp add: Upper_Bounds_mem_iff is_sup_def isotoneD31 least_iff)

lemma is_iso_inf:
  "is_isotone X f \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_inf A X x \<Longrightarrow> is_inf (f`X) (f`A) y  \<Longrightarrow> f x \<le> y"
  by(simp add: is_inf_def Lower_Bounds_mem_iff lb_ant2 subsetD greatest_iff isotoneD32)

subsection Idempotency

definition is_idempotent::"'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_idempotent X f \<equiv> (\<forall>x. x \<in> X \<longrightarrow> f (f x) = f x)"

lemma idempotentD1:
  "\<lbrakk>is_idempotent X f; x \<in> X \<rbrakk> \<Longrightarrow>  f (f x) = f x"
  by (simp add: is_idempotent_def)

lemma idempotentD3:
  "\<lbrakk>is_idempotent X f; y \<in> f`X \<rbrakk> \<Longrightarrow>  f y = y"
  by (auto simp add: is_idempotent_def)
          
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

lemma closureD7:
  "\<lbrakk>is_closure X f; x \<in> X;  y \<in> (f`X) ;  x \<le> y\<rbrakk> \<Longrightarrow> f x \<le> y"
  by (simp add:is_closure_def[of "X" "f"] idempotent_isotoneD1[of "X" "f" "y" "x"])

lemma closureD8:
  "\<lbrakk>is_closure X f;  x \<in> X;  y \<in> (f`X) ;  f x \<le> y\<rbrakk> \<Longrightarrow>  x \<le> y"
  by (simp add:closureD5[of "X" "f" "x"] order_trans[of "x" "f x" "y"])

lemma closureD9:
  "\<lbrakk>is_closure X f;  y \<in> f`X\<rbrakk>  \<Longrightarrow> f y \<le> y"
  by (metis antisym_conv1 idempotentD3 is_closure_def nless_le)

lemma closureD10:
  "\<lbrakk>is_closure X f;  x \<in> X;  f x \<le> x\<rbrakk> \<Longrightarrow> x = f x"
  by (simp add: closureD5 dual_order.eq_iff)

lemma closureD11:
  "\<lbrakk>is_closure X f;  x \<in> X; f x \<le> x\<rbrakk> \<Longrightarrow> x \<in> f `X"
  using closureD10 by blast

lemma cl_sup_eq_sup_cl1:
  "\<lbrakk>is_closure X f; is_sup X A s; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f s) \<in> Upper_Bounds (f`X) (f`A)"
  by (simp add: is_closure_def is_supD11 isotoneD41)

lemma cl_le_cl_iff_le:
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

subsection ClosureRanges

definition is_clr::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_clr C X \<equiv> (C \<noteq> {}) \<and> (C \<subseteq> X) \<and> (\<forall>x. x \<in> X \<longrightarrow> (\<exists>c. is_least (Upper_Bounds C {x}) c))"

lemma clrI1:
  "\<lbrakk>C \<noteq> {}; C \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> (\<exists>c. is_least (Upper_Bounds C {x}) c)) \<rbrakk> \<Longrightarrow> is_clr C X"
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

lemma clrD4:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> (\<exists>c. is_least (Upper_Bounds C {x}) c)"
  by (simp add:is_clr_def)

lemma clrD5:
  "is_clr C X \<Longrightarrow>  (\<And>x. x \<in> X  \<Longrightarrow> ((Upper_Bounds C {x}) \<noteq> {}))"
  by (simp add: clrD4 least_exD0)

lemma clrD6:
  "is_clr C X \<Longrightarrow>  x \<in> X \<Longrightarrow> (Upper_Bounds C {x}) \<noteq> {}"
  by (simp add: clrD5)


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

section Subsets
subsection Directedness
definition is_dir::"'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "is_dir X ord \<equiv> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>c \<in> X. ord a c \<and> ord b c))"

lemma is_updirE1:
  "is_dir (X::'a::order set) (\<le>)  \<Longrightarrow> a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> (\<exists>c \<in> X. a \<le> c \<and> b \<le> c) "
  by (simp add: is_dir_def)

lemma is_updirI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. a \<le> c \<and> b \<le> c)) \<Longrightarrow> is_dir (X::'a::order set) (\<le>)"
  by (simp add: is_dir_def)

lemma is_updirD1:
  "\<lbrakk>is_dir (X::'a::order set) (\<le>);a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>c \<in> X. c ub {a, b})"
  by (simp add: is_updirE1 ub_double)

lemma is_updir_empty:
  "is_dir {} (\<le>)"
  by (simp add: is_dir_def)

lemma is_updir_singleton:
  "is_dir {x::'a::order} (\<le>)"
  by (simp add: is_dir_def)


lemma updir_finite1:
  assumes A0: "\<And>a1 a2. a1 \<in> (X::'a::order set) \<Longrightarrow> a2 \<in> X \<Longrightarrow>  (\<exists>c \<in> X. a1 \<le> c \<and> a2 \<le> c)" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X"
  shows " (\<exists>c \<in> X. \<forall>a. a \<in> A \<longrightarrow> a \<le> c)"
  using A1 A2 A3 
proof (induct A rule: finite_ne_induct)
  case (singleton x)
  then show ?case by blast
next
  case (insert x F)
  then show ?case
    by (metis A0 dual_order.trans insert_iff insert_subset)
qed

lemma updir_finite2:
  "\<lbrakk>is_dir (X::'a::order set) (\<le>); A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. c ub A)"
  by (metis is_dir_def ubI updir_finite1)

lemma updir_finite3:
  "(\<And>A. \<lbrakk>A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. c ub A)) \<Longrightarrow> is_dir (X::'a::order set) (\<le>)"
  apply(auto simp add:ub_def is_dir_def) 
   by (metis bot_least finite.simps insert_iff insert_not_empty insert_subset)

lemma updir_finite:
  "is_dir (X::'a::order set) (\<le>) \<longleftrightarrow> (\<forall>A. A \<subseteq> X \<and> finite A \<and> A \<noteq> {} \<longrightarrow>  (\<exists>c \<in> X. c ub A))"
  by (meson updir_finite2 updir_finite3)

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

lemma dwdir_finite1:
  assumes A0: "\<And>a1 a2. a1 \<in> (X::'a::order set) \<Longrightarrow> a2 \<in> X \<Longrightarrow>  (\<exists>c \<in> X. a1 \<ge> c \<and> a2 \<ge> c)" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X"
  shows " (\<exists>c \<in> X. \<forall>a. a \<in> A \<longrightarrow> a \<ge> c)"
  using A1 A2 A3 
proof (induct A rule: finite_ne_induct)
  case (singleton x)
  then show ?case by blast
next
  case (insert x F)
  then show ?case
    by (metis A0 dual_order.trans insert_iff insert_subset)
qed

lemma dwdir_finite2:
  "\<lbrakk>is_dir (X::'a::order set) (\<ge>); A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. c lb A)"
  by (metis is_dir_def lbI dwdir_finite1)

lemma dwdir_finite3:
  "(\<And>A. \<lbrakk>A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. c lb A)) \<Longrightarrow> is_dir (X::'a::order set) (\<ge>)"
  apply(auto simp add:lb_def is_dir_def) 
  by (metis bot_least finite.simps insert_iff insert_not_empty insert_subset)

lemma dwdir_finite:
  "is_dir (X::'a::order set) (\<ge>) \<longleftrightarrow> (\<forall>A. A \<subseteq> X \<and> finite A \<and> A \<noteq> {} \<longrightarrow>  (\<exists>c \<in> X. c lb A))"
  by (metis dwdir_finite2 dwdir_finite3)


lemma csup_updir:
  "is_csup_semilattice X \<Longrightarrow> is_dir X (\<le>)"
  by (metis csupD3 is_updirI1 greatestD11 greatestD2)

lemma sup_updir:
  "\<lbrakk>is_sup_semilattice X; is_greatest X m\<rbrakk> \<Longrightarrow> is_dir X (\<le>)"
  by (meson greatestD1 greatestD2 is_updirI1)


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


subsection OrderClosure

definition is_ord_cl::"'a set \<Rightarrow> 'a set \<Rightarrow>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "is_ord_cl X A ord \<equiv> (\<forall>a b. a \<in> A \<and> b \<in> X \<and> ord a b \<longrightarrow> b \<in> A )"

lemma is_ord_clE1:
  "is_ord_cl (X::'a::order set) A (\<le>)  \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> X \<Longrightarrow> a \<le> b \<Longrightarrow> b \<in> A "
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

lemma ord_cl_memI1:
  "is_ord_cl (X::'a::order set) A ord \<Longrightarrow> x \<in> X \<Longrightarrow> (\<exists>a. a \<in> A \<and> ord a x) \<Longrightarrow> x \<in> A"
  by(auto simp add:is_ord_cl_def)

lemma ord_cl_dwdir_inf:
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

subsection Filters
subsection DefinitionAndBasicProps
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

subsection TopElements

lemma filter_greatestD1:
  "is_greatest X m \<Longrightarrow> is_filter X F \<Longrightarrow>  (\<exists>f. f \<in> F \<and> f \<le> m)"
  by (metis is_filter_def ex_in_conv filterD21 greatestD2)

lemma filter_greatestD2:
  "is_greatest X m \<Longrightarrow> is_filter X F \<Longrightarrow>  m \<in> F"
  using filterD4 greatestD11 filter_greatestD1 is_ord_clE1 by blast

subsection FiniteInfClosure

lemma filter_finf_closed:
  "\<lbrakk>is_filter X F; a \<in> F;  b \<in> F;  is_inf X {a, b} i\<rbrakk>\<Longrightarrow> i \<in> F"
  by (meson is_filter_def ord_cl_dwdir_inf)

lemma filter_finf_closed1:
  "\<lbrakk>is_inf_semilattice X; is_filter X F; a \<in> F; b \<in> F\<rbrakk> \<Longrightarrow> Inf X {a, b} \<in> F"
  by (meson filterD21 filter_finf_closed sinfD3)

lemma filter_finf_closed3:
  "\<lbrakk>is_inf_semilattice X; is_filter X F; A \<subseteq> F; A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow> Inf X A \<in> F"
  by (simp add: is_filter_def filter_finf_closed1 finite_inf_closed2)

lemma min_filter1:
  "is_greatest X top \<Longrightarrow> is_filter X {top}"
  by (simp add: is_filter_def greatest_iff is_dwdir_singleton is_ord_cl_def order_antisym) 

lemma min_filter2:
  "\<lbrakk>is_greatest X top; is_filter X F\<rbrakk> \<Longrightarrow>{top} \<subseteq> F"
  by (simp add: filter_greatestD2)

lemma filters_max0:
  "is_inf_semilattice X \<Longrightarrow> is_filter X X"
  by (simp add: is_filter_def inf_dwdir is_inf_semilattice_def is_ord_cl_space)

lemma filters_max1:
  "is_cinf_semilattice X \<Longrightarrow>is_filter X X"
  by (simp add: is_filter_def cinf_dwdir is_cinf_semilattice_def is_ord_cl_space)

subsection SetOfFilters

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
  by (metis InterI empty_iff filter_greatestD2)

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
      by (meson A1 A5 B1 InterE filter_finf_closed)
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
  by (meson Inf_less_eq is_filter_def filter_inter_dir filter_inter_ne filter_inter_upcl)

lemma filter_inter_closed2:
  "\<lbrakk>is_inf_semilattice X;is_greatest X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> (\<And>E. \<lbrakk>E \<subseteq> (filters_on X); E \<noteq> {}\<rbrakk> \<Longrightarrow> (\<Inter>E) \<in> (filters_on X))"
  by (simp add: filter_inter_closed1 filters_on_iff subset_iff)


subsection FilterClosure

lemma filter_is_clr:
  "\<lbrakk>is_inf_semilattice X;is_greatest X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> is_clr (filters_on X) (Pow X)"
  by (simp add: cinf_sinf filter_inter_closed2 filters_is_clr1 filters_is_clr1b moore_clI3)

lemma filter_closure_of_empty1:
  "\<lbrakk>is_inf_semilattice X;is_greatest X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> is_least (Upper_Bounds (filters_on X) {{}}) {top}"
  by (simp add: Upper_Bounds_mem_iff2 filters_on_def filter_greatestD2 least_iff min_filter1)

lemma filter_closure_of_empty2:
  "\<lbrakk>is_inf_semilattice X;is_greatest X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> (cl_from_clr (filters_on X)) {} = {top}"
  by (simp add: cl_from_clr_def filter_closure_of_empty1 least_equality2)


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

lemma ne_filter_cl1:
  "\<lbrakk>A \<subseteq> X; A \<noteq> {};is_inf_semilattice X\<rbrakk> \<Longrightarrow> is_ord_cl X (filter_closure X A) (\<le>)"
  apply(simp add:filter_closure_ne_simp is_ord_cl_def order.trans) by (meson order.trans)

lemma filter_cl0:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> filter_closure X A"
  by (simp add: filter_closure_singleton subsetI)

lemma filter_cl1:
  "\<lbrakk>is_inf_semilattice X; is_greatest X top;A \<subseteq> X\<rbrakk> \<Longrightarrow> is_ord_cl X (filter_closure X A) (\<le>)"
  by (metis filterD4 filter_closure_empty min_filter1 ne_filter_cl1)

lemma filter_cl_empty:
  "is_dir (filter_closure X {}) (\<ge>)"
  by (simp add: filter_closure_def is_dwdir_singleton)

context
  fixes X::"'a::order set"
  assumes toped:"is_greatest X top" and
          csinf:"is_inf_semilattice X"
begin

lemma filter_cl2:
  "A \<subseteq> X \<Longrightarrow> is_dir (filter_closure X A) (\<ge>)"
  by (metis greatest_iff is_dwdirI1 toped)

lemma filter_cl3:
  "A \<subseteq> X \<Longrightarrow> is_filter X (filter_closure X A)"
  by (metis is_filter_def csinf filter_cl1 filter_cl2 filter_closure_ne filters_max0 greatestD11 subsetI toped)

lemma filter_cl_least:
  "\<lbrakk>is_filter X F; A \<subseteq> F\<rbrakk> \<Longrightarrow> (filter_closure X A) \<subseteq> F"
  by (meson filter_greatestD2 subsetI toped)

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

lemma filters_on_lattice_inf01:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> z \<in> F1 \<inter> F2 \<Longrightarrow> \<exists>f1 f2. f1 \<in> F1 \<and> f2 \<in> F2 \<and> z = Sup X {f1, f2}"
  by (metis IntE bsup_idem1 filterD21)

lemma filters_on_lattice_inf02:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> f1 \<in> F1 \<and> f2 \<in> F2 \<and> z = Sup X {f1, f2} \<Longrightarrow> z \<in> F1 \<inter> F2 "
  using filterD4[of "X" "F1"] is_ord_clE1[of "X" "F1" "f1" "z"] filterD4[of "X" "F2"] is_ord_clE1[of "X" "F2" "f2" "z"]
  by (metis Int_iff bsup_geI1 bsup_geI2 dual_order.refl filterD21 lattD42 ssupD4)

lemma filters_on_lattice_inf03:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> f1 \<in> F1 \<Longrightarrow> f2 \<in> F2  \<Longrightarrow> Sup X {f1, f2} \<in> F1 \<inter> F2 "
  using filters_on_lattice_inf02 by blast


lemma filter_on_lattice_sup01:
  "\<lbrakk>is_lattice X; is_filter X F; x \<in> X; y \<in> F\<rbrakk> \<Longrightarrow> Sup X {x, y} \<in> F "
  by (meson binary_supD32 filterD21 filterD4 is_ord_clE1 lattD32 lattD42 ssupD4)

lemma filter_on_lattice_top0:
  "is_lattice X \<Longrightarrow> is_filter X {x} \<Longrightarrow> a \<in> X \<Longrightarrow> a \<le> x"
  by (meson is_filter_def bsup_iff filter_on_lattice_sup01 insertI1 latt_iff subsetD ubD ub_singleton)

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

(*
  On a lattice filters form an inf semilattice
*)

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
    by (metis A0 A3 A5 B1 B2 bot.extremum_uniqueI filterD4 filter_closure_iff filter_finf_closed3 is_ord_clE1 lattD41)
qed

lemma filters_on_lattice_sup7b:
  "\<lbrakk>is_lattice X; (\<forall>F. F \<in> EF \<longrightarrow> is_filter X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> is_sup (filters_on X) EF (filter_closure X (\<Union>EF))"
  by(simp add:is_sup_def filters_on_lattice_sup4b filters_on_iff  Upper_Bounds_mem_iff2  filters_on_lattice_sup5b filters_on_lattice_sup6b least_iff)

(*On a lattice filters form a complete sup semilattice*)

lemma filters_on_lattice_csup:
  "is_lattice X \<Longrightarrow> is_csup_semilattice (filters_on X)"
  by (metis empty_not_insert filters_is_clr1b filters_on_iff filters_on_lattice_sup7b insert_absorb insert_subset is_csup_semilattice_def lattD41)

lemma filters_on_lattice_sup_semilattice1b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> is_sup (filters_on X) {F1, F2} (filter_closure X (F1 \<union> F2))"
  by (metis Union_insert ccpo_Sup_singleton empty_not_insert filters_on_lattice_sup7b insertE singleton_iff)

lemma filters_on_lattice_sup_semilattice2b:
  "is_lattice X \<Longrightarrow> is_sup_semilattice (filters_on X)"
  by (metis filters_on_iff filters_on_lattice_inf_semilattice1 filters_on_lattice_sup_semilattice1b is_inf_semilattice_def is_sup_semilattice_def)

lemma filters_on_lattice_sup_semilattice3b:
  "is_lattice X \<Longrightarrow> EF \<subseteq> (filters_on X) \<Longrightarrow> finite EF \<Longrightarrow> EF \<noteq> {} \<Longrightarrow> (Sup (filters_on X) EF) \<in> filters_on X"
  by (meson bsup_finite2 filters_on_lattice_sup_semilattice2b is_supD111)

(*On a topped inf semilattice filters form a complete inf semilattice*)

lemma filters_on_top_inf_semilattice_is_cinf:
  "\<lbrakk>is_greatest X top; is_inf_semilattice X\<rbrakk> \<Longrightarrow> is_cinf_semilattice (filters_on X)"
  apply(auto simp add:is_cinf_semilattice_def)
  using filters_is_clr1b apply auto[1]
  by (metis clatD22 clr_is_clattice filterD1 filter_is_clr filters_max0 pow_is_clattice)

(*On a topped inf semlattice filters form a complete complete lattice*)

lemma filters_on_top_inf_lattice_clattice:
  "\<lbrakk>is_greatest X top; is_inf_semilattice X\<rbrakk> \<Longrightarrow> is_clattice (filters_on X)"
  by (metis clr_is_clattice empty_iff filter_is_clr greatestD11 pow_is_clattice)


(*
  "\<lbrakk>is_inf_semilattice X; is_greatest X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> is_clr (filters_on X) (Pow X)"
  "\<lbrakk>is_inf_semilattice X; is_greatest X top\<rbrakk> \<Longrightarrow> is_cinf_semilattice (filters_on X)
  "\<lbrakk>is_lattice X\<rbrakk> \<Longrightarrow> is_csup_semilattice (filters_on X)"
  "\<lbrakk>is_greatest X top; is_inf_semilattice X\<rbrakk> \<Longrightarrow> is_clattice (filters_on X)"

*)

definition lorc::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" ("(2[_')\<^sub>_)") where
  "[a)\<^sub>X \<equiv> {y \<in> X. a \<le> y} "

lemma lorcI1:
  "y \<in> X \<Longrightarrow> a \<le> y \<Longrightarrow> y \<in> [a)\<^sub>X" 
  by (simp add:lorc_def)
lemma lorcD1:
  "y \<in> [a)\<^sub>X \<Longrightarrow> y \<in> X \<and> a \<le> y"
   by (simp add:lorc_def)
lemma lorcD11:
  "y \<in> [a)\<^sub>X \<Longrightarrow> y \<in> X "
   by (simp add:lorc_def)
lemma lorcD12:
  "y \<in> [a)\<^sub>X \<Longrightarrow> a \<le> y" 
  by (simp add:lorc_def)

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
  apply(rule moore_clI3, auto simp add:ord_cl_sets_def is_ord_cl_space is_ord_cl_def)
   by blast

lemma lorc_is_clattice:
  "is_greatest X m \<Longrightarrow> is_clattice (ord_cl_sets X (\<le>))"
  using clr_is_clattice lorc_moore pow_is_clattice by blast

lemma lorc_filter:
  "x \<in> X \<Longrightarrow> is_filter X [x)\<^sub>X"
  apply(auto simp add:is_filter_def) using lorc_memI1 apply auto[1] 
  apply (simp add: lorc_mem_iff1) apply (metis is_dwdirI1 lorcD12 lorc_memI1)
  by (simp add: lorc_upclI)


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

definition is_antitone::"'a::order set \<Rightarrow> ('a::order \<Rightarrow> 'b::order) \<Rightarrow> bool" where
  "is_antitone X f \<equiv> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. x1 \<le> x2 \<longrightarrow> f x2 \<le> f x1)"

lemma antitoneD:
  "\<lbrakk>is_antitone X f; x1 \<in> X; x2 \<in> X; x1 \<le> x2\<rbrakk> \<Longrightarrow> f x2 \<le> f x1"
  by (simp add:is_antitone_def)

lemma anti_ext_gc:
  "\<lbrakk>is_antitone Y g; is_extensive X (g \<circ> f); f x \<in> Y; g`Y \<subseteq> X; x \<in> X; y \<in> Y; y \<le> f x \<rbrakk> \<Longrightarrow> x \<le> g y"
  using antitoneD[of Y g y "f x"] extensiveD1[of X "(g \<circ> f)" x] order.trans by simp

lemma gcI:
  "\<lbrakk>is_antitone X f; is_extensive X (g \<circ> f);
      is_antitone Y g;  is_extensive Y (f \<circ> g); 
        f`X \<subseteq> Y; g`Y \<subseteq> X \<rbrakk> \<Longrightarrow>  galois_conn f X g Y"
  by(auto simp add:galois_conn_def anti_ext_gc)

lemma gcD:
  "galois_conn f X g Y \<Longrightarrow>is_antitone X f \<and> is_extensive X (g \<circ> f) \<and>
                           is_antitone Y g \<and>  is_extensive Y (f \<circ> g) \<and> f`X \<subseteq> Y \<and> g`Y \<subseteq> X"
  by (simp add: galois_conn_def gc_anti1 gc_anti2 gc_cext1 gc_cext2 is_antitone_def is_extensive_def)

lemma gc_triple1:
  "galois_conn f X g Y \<Longrightarrow> x \<in> X \<Longrightarrow> f (g (f x)) = f x"
  by (simp add: dual_order.eq_iff galois_connD12 galois_connD22 gc_anti1 gc_cext1 gc_cext2)

lemma gc_triple2:
  "galois_conn f X g Y \<Longrightarrow> y \<in> Y \<Longrightarrow> g (f (g y)) =g y"
  by (simp add: antisym galois_connD12 galois_connD22 gc_anti2 gc_cext1 gc_cext2)

lemma gc_idem1a:
  "galois_conn f X g Y \<Longrightarrow> x \<in> X \<Longrightarrow> g (f ( g (f x) ) ) = g (f x)"
  by (simp add: gc_triple1)

lemma gc_idem1b:
  "galois_conn f X g Y \<Longrightarrow> is_idempotent X (g \<circ> f)"
  by (simp add: gc_idem1a is_idempotent_def)


lemma gc_idem2a:
  "galois_conn f X g Y \<Longrightarrow> y \<in> Y \<Longrightarrow> f (g ( f (g y) ) ) = f (g y)"
  by (simp add: gc_triple2)


lemma gc_idem2b:
  "galois_conn f X g Y \<Longrightarrow> is_idempotent Y (f \<circ> g)"
  by (simp add: gc_idem2a is_idempotent_def)

lemma gc_iso1a:
  "galois_conn f X g Y \<Longrightarrow> x1 \<in> X \<Longrightarrow>x2 \<in> X \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> g (f x1 ) \<le> g (f x2)"
  by (simp add: galois_connD22 gc_anti1 gc_anti2)

lemma gc_iso1b:
  "galois_conn f X g Y \<Longrightarrow> is_isotone X (g \<circ> f)"
  by (simp add: gc_iso1a  is_isotone_def)

lemma gc_iso2a:
  "galois_conn f X g Y \<Longrightarrow> y1 \<in> Y \<Longrightarrow>y2 \<in> Y \<Longrightarrow>y1 \<le> y2 \<Longrightarrow> f (g y1 ) \<le> f (g y2)"
  by (simp add: galois_connD12 gc_anti1 gc_anti2)

lemma gc_iso2b:
  "galois_conn f X g Y \<Longrightarrow> is_isotone Y (f \<circ> g)"
  by (simp add: gc_iso2a  is_isotone_def)
   
lemma gc_ext1:
  "galois_conn f X g Y \<Longrightarrow> is_extensive X (g \<circ> f)"
  by (simp add: gcD)

lemma gc_ext2:
  "galois_conn f X g Y \<Longrightarrow> is_extensive Y (f \<circ> g)"
  by (simp add: gcD)
     
    
lemma gc_sub1:
  "galois_conn f X g Y \<Longrightarrow>(\<lambda>x.  g (f x)) ` X \<subseteq> X"
  by (simp add: galois_connD12 galois_connD22 image_subset_iff)       
    
lemma gc_sub2:
  "galois_conn f X g Y \<Longrightarrow>(\<lambda>y. f (g y)) ` Y \<subseteq> Y"
  by (simp add: galois_connD12 galois_connD22 image_subset_iff)       


lemma gc_closure1:
  "galois_conn f X g Y \<Longrightarrow> is_closure X (g \<circ> f)"
  by (simp add: is_closure_def gc_sub1 gc_ext1 gc_iso1b gc_idem1b)

lemma gc_closure2:
  "galois_conn f X g Y \<Longrightarrow> is_closure Y (f \<circ> g)"
  by (simp add: is_closure_def gc_sub2 gc_ext2 gc_iso2b gc_idem2b)

lemma ul_galois:
  "galois_conn (\<lambda>A. Upper_Bounds X A) (Pow X) (\<lambda>A. Lower_Bounds X A) (Pow X)"
  apply(rule gcI) 
  apply(simp add: Upper_Bounds_ant1 is_antitone_def)
  apply(simp add: Lower_Upper_comp1 is_extensive_def)
  apply(simp add: Lower_Bounds_ant1 is_antitone_def)
  apply(simp add: Upper_Lower_comp1 is_extensive_def)
  apply (simp add: Upper_Bounds_sub image_subset_iff)
  by (simp add: Lower_Bounds_sub image_subset_iff)

lemma ul_closure:
  "is_closure (Pow X) ((\<lambda>A. Upper_Bounds X A) \<circ> (\<lambda>A. Lower_Bounds X A))"
  using gc_closure2 ul_galois by blast

lemma lu_closure:
  "is_closure (Pow X) ((\<lambda>A. Lower_Bounds X A) \<circ> (\<lambda>A. Upper_Bounds X A))"
  using gc_closure1 ul_galois by blast

subsection PolarPairs

definition lgc_from_rel::"('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a set \<Rightarrow> 'b set)" where
  "lgc_from_rel R X Y \<equiv> (\<lambda>A. {y. y \<in> Y \<and> (\<forall>x. x \<in> A \<longrightarrow> (x, y) \<in> R)})"

definition rgc_from_rel::"('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('b set \<Rightarrow> 'a set)" where
  "rgc_from_rel R X Y \<equiv> (\<lambda>B. {x. x \<in> X \<and> (\<forall>y. y \<in> B \<longrightarrow> (x, y) \<in> R)})"

lemma lcgD1:
  "\<lbrakk>A \<subseteq> X; y \<in> (lgc_from_rel R X Y) A\<rbrakk> \<Longrightarrow> (\<forall>x \<in> A.  (x, y) \<in> R)"
  by (simp add: lgc_from_rel_def)

lemma rcgD1:
  "\<lbrakk>B \<subseteq> Y; x \<in> (rgc_from_rel R X Y) B\<rbrakk> \<Longrightarrow> (\<forall>y \<in> B.  (x, y) \<in> R)"
  by (simp add: rgc_from_rel_def)

lemma lcg_iff:
  "\<lbrakk>A \<subseteq> X\<rbrakk> \<Longrightarrow> y \<in> (lgc_from_rel R X Y) A \<longleftrightarrow> (y \<in> Y \<and> (\<forall>x \<in> A.  (x, y) \<in> R))"
   by (auto simp add: lgc_from_rel_def)

lemma rcg_iff:
  "\<lbrakk>B \<subseteq> Y\<rbrakk> \<Longrightarrow> x \<in> (rgc_from_rel R X Y) B \<longleftrightarrow> (x \<in> X \<and> (\<forall>y \<in> B.  (x, y) \<in> R))"
   by (auto simp add: rgc_from_rel_def)

lemma lcg_iff2:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> Y; y \<in> B\<rbrakk> \<Longrightarrow> y \<in> (lgc_from_rel R X Y) A \<longleftrightarrow> (\<forall>x \<in> A.  (x, y) \<in> R)"
   by (auto simp add: lgc_from_rel_def)

lemma rcg_iff2:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> Y; x \<in> A\<rbrakk> \<Longrightarrow> x \<in> (rgc_from_rel R X Y) B \<longleftrightarrow> (\<forall>y \<in> B.  (x, y) \<in> R)"
  by (simp add: in_mono rcg_iff)

lemma lcg_iff3:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> Y\<rbrakk>  \<Longrightarrow> (\<forall>b \<in> B. b \<in> lgc_from_rel R X Y A) \<longleftrightarrow> (\<forall>a \<in> A. \<forall>b \<in> B.(a, b) \<in> R)"
  by (meson lcg_iff2)
  
lemma rcg_iff3:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> Y\<rbrakk>  \<Longrightarrow> (\<forall>a \<in> A. a \<in> rgc_from_rel R X Y B) \<longleftrightarrow> (\<forall>a \<in> A. \<forall>b \<in> B.(a, b) \<in> R)"
  by (meson rcg_iff2)

lemma rcg_range1:
  "B \<subseteq> Y \<Longrightarrow>  rgc_from_rel R X Y B \<subseteq> X"
  by (meson rcg_iff subset_eq)
  
lemma rcg_range2:
  "(rgc_from_rel R X Y)`(Pow Y) \<subseteq> Pow X"
  by (simp add: image_subset_iff rcg_range1)
  
lemma lcg_range1:
  "A \<subseteq> X \<Longrightarrow>  lgc_from_rel R X Y A \<subseteq> Y"
  by (meson lcg_iff subset_eq)
  
lemma lcg_range2:
  "(lgc_from_rel R X Y)`(Pow X) \<subseteq> Pow Y"
  by (simp add: image_subset_iff lcg_range1)
  
subsection PolarPairToGalois


lemma gc1_to_gc2:
  assumes A0:"B \<subseteq> Y" and A1:"A \<subseteq> X" 
  shows "B \<subseteq> (lgc_from_rel R X Y) A  \<longleftrightarrow> A \<subseteq> (rgc_from_rel R X Y) B" (is "?L \<longleftrightarrow> ?R")
proof-
  let ?f="(lgc_from_rel R X Y)" and ?g="(rgc_from_rel R X Y)"
  have B0:"?L  \<longleftrightarrow> (\<forall>b. b \<in> B \<longrightarrow> b \<in> ?f A)" by auto
  have B1:"... \<longleftrightarrow> (\<forall>a \<in> A. \<forall>b \<in> B.(a, b) \<in> R)" by (meson A0 A1 in_mono lcg_iff)
  have B2:"... \<longleftrightarrow> (\<forall>a. a \<in> A \<longrightarrow> a \<in> ?g B)" by (meson A0 A1 in_mono rcg_iff) 
  have B3:"... \<longleftrightarrow> ?R" by (simp add: subset_iff)
  show "?L \<longleftrightarrow> ?R"
    using B0 B1 B2 B3 by presburger
qed

lemma polar_pair_gc:
  "galois_conn (lgc_from_rel R X Y) (Pow X) (rgc_from_rel R X Y) (Pow Y)"
  by (simp add: galois_conn_def gc1_to_gc2 lcg_range2 rcg_range2)
  

subsubsection RecoveryOfOriginalRelation

definition rel_from_pair::"('a set \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> ('b set \<Rightarrow> 'a set) \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set" where
  "rel_from_pair f X g Y \<equiv> {(x, y). (x, y) \<in> (X \<times> Y) \<and> y \<in> f {x}}"

lemma gc_polar_pair:
  assumes A0:"(x, y) \<in> (X \<times> Y)"
  shows "(x, y) \<in> rel_from_pair (lgc_from_rel R X Y) X  (rgc_from_rel R X Y) Y \<longleftrightarrow>  (x, y) \<in> R" (is "?L \<longleftrightarrow> ?R")
proof-
  let ?f="(lgc_from_rel R X Y)" and ?g="(rgc_from_rel R X Y)" let ?GFR=" rel_from_pair ?f X  ?g Y"
  have B0:"?L \<longleftrightarrow> y \<in> ?f {x}"  using A0 by(auto simp add:lgc_from_rel_def rel_from_pair_def rgc_from_rel_def)
  have B1:"... \<longleftrightarrow> ?R"  using A0 by(auto simp add:lgc_from_rel_def)
  show ?thesis
    by (simp add: B0 B1)
qed
  
subsubsection GaloisToPolar

lemma gc_to_polar0:
  "galois_conn f (Pow X) g (Pow Y) \<Longrightarrow> a \<in> X \<Longrightarrow> y \<in> Y  \<Longrightarrow>  {y} \<subseteq> f {a} \<longleftrightarrow> {a} \<subseteq> g {y}"
  by (meson Pow_bottom Pow_iff galois_connD11 galois_connD21 insert_subsetI)

lemma gc_to_polar1:
  assumes A0:"galois_conn f (Pow X) g (Pow Y)" and A1:"A \<subseteq> X" and A2:"y \<in> Y"
  shows "y \<in> (lgc_from_rel (rel_from_pair f X g Y) X Y) A \<longleftrightarrow> y \<in> f A" (is "?LHS \<longleftrightarrow> ?RHS")
proof-
  have B0:"\<forall>a \<in> A.  {y} \<subseteq> f {a} \<longleftrightarrow> {a} \<subseteq> g {y}"
    by (meson A0 A1 A2 gc_to_polar0 in_mono)  
  let ?R="rel_from_pair f X g Y" let ?f="lgc_from_rel ?R X Y" let ?g="rgc_from_rel ?R X Y"
  have B0:"?LHS \<longleftrightarrow> (\<forall>a \<in> A. (a, y) \<in> ?R)" by (simp add: A1 A2 lcg_iff)
  have B1:"...  \<longleftrightarrow> (\<forall>a \<in> A.  y \<in> f {a})" using A1 A2 by(auto simp add:rel_from_pair_def)
  have B2:"...  \<longleftrightarrow> (\<forall>a \<in> A.  {y} \<subseteq> f {a})" by simp
  have B3:"...  \<longleftrightarrow> (\<forall>a \<in> A. {a} \<subseteq> g {y})" by (meson A0 A1 A2 gc_to_polar0 subsetD)
  have B4:"...  \<longleftrightarrow> (A \<subseteq> g {y})" by blast
  have B5:"...  \<longleftrightarrow> y \<in>  f A" by (meson A0 A1 A2 PowD PowI Pow_bottom galois_connD11 galois_connD21 insert_subset)
  show "?LHS \<longleftrightarrow> ?RHS"
    using B0 B1 B2 B3 B4 B5 by presburger
qed

subsection SomeClosures

definition sup_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
 "sup_cl X A \<equiv> {x \<in> X. \<exists>E \<in> Pow A. E \<noteq> {} \<and> is_sup X E x}"

definition inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "inf_cl X A \<equiv> {x \<in> X. \<exists>E \<in> Pow A. E \<noteq> {} \<and> is_inf X E x}"

definition fne_inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow>  'a::order set" where
  "fne_inf_cl X A\<equiv> {x \<in> X. \<exists>F \<in> Fpow A. F \<noteq> {} \<and> is_inf X F x}"

definition fne_sup_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow>  'a::order set" where
  "fne_sup_cl X A\<equiv> {x \<in> X. \<exists>F \<in> Fpow A. F \<noteq> {} \<and> is_sup X F x}"

definition fin_inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow>  'a::order set" where
  "fin_inf_cl X A \<equiv> {x \<in> X. \<exists>F \<in> Fpow A. is_inf X F x}"

lemma sup_cl_imp0:
  "x \<in> sup_cl X A  \<Longrightarrow> x \<in> X "
  by (simp add: sup_cl_def)

lemma inf_cl_imp0:
  "x \<in> inf_cl X A \<Longrightarrow> x \<in> X "
  by (simp add: inf_cl_def)

lemma fin_inf_cl_imp0:
  "x \<in> fin_inf_cl X A \<Longrightarrow> x \<in> X"
  by (simp add: fin_inf_cl_def)

lemma fne_sup_cl_imp0:
  "x \<in> fne_sup_cl X A \<Longrightarrow> x \<in> X"
  by (simp add: fne_sup_cl_def)

lemma fne_inf_cl_imp0:
  "x \<in> fne_inf_cl X A\<Longrightarrow> x \<in> X"
  by (simp add: fne_inf_cl_def)

lemma sup_cl_imp1:
  "x \<in> sup_cl X A \<Longrightarrow>  (\<exists>E \<in> Pow A. E \<noteq> {} \<and> is_sup X E x)"
   by (simp add: sup_cl_def) 

lemma inf_cl_imp1:
  "x \<in> inf_cl X A \<Longrightarrow>  (\<exists>E \<in> Pow A. E \<noteq> {} \<and>  is_inf X E x)"
   by (simp add: inf_cl_def) 

lemma fin_inf_cl_imp1:
  "x \<in> fin_inf_cl X A \<Longrightarrow> ( \<exists>F \<in> Fpow A.  is_inf X F x)"
  by (simp add: fin_inf_cl_def)

lemma fne_inf_cl_imp1:
  "x \<in> fne_inf_cl X A \<Longrightarrow> (\<exists>F \<in> Fpow A. F \<noteq> {} \<and> is_inf X F x)"
  by (simp add: fne_inf_cl_def)

lemma fne_sup_cl_imp1:
  "x \<in> fne_sup_cl X A \<Longrightarrow> (\<exists>F \<in> Fpow A. F \<noteq> {} \<and> is_sup X F x)"
  by (simp add: fne_sup_cl_def)

lemma sup_cl_if1:
  " x \<in> X \<Longrightarrow>  (\<exists>E \<in> Pow A. E \<noteq> {} \<and> is_sup X E x) \<Longrightarrow> x \<in> sup_cl X A"
   by (simp add: sup_cl_def) 

lemma inf_cl_if1:
  " x \<in> X \<Longrightarrow>  (\<exists>E \<in> Pow A. E \<noteq> {} \<and>  is_inf X E x) \<Longrightarrow> x \<in> inf_cl X A"
   by (simp add: inf_cl_def) 

lemma fin_inf_cl_if1:
  "x \<in> X \<Longrightarrow> (\<exists>F \<in> Fpow A. is_inf X F x) \<Longrightarrow> x \<in> fin_inf_cl X A"
  by (simp add: fin_inf_cl_def)

lemma fne_inf_cl_if1:
  "x \<in> X \<Longrightarrow> (\<exists>F \<in> Fpow A. F \<noteq> {} \<and>  is_inf X F x) \<Longrightarrow> x \<in> fne_inf_cl X A"
  by (simp add: fne_inf_cl_def)

lemma fne_sup_cl_if1:
  "x \<in> X \<Longrightarrow> (\<exists>F \<in> Fpow A. F \<noteq> {} \<and>  is_sup X F x) \<Longrightarrow> x \<in> fne_sup_cl X A"
  by (simp add: fne_sup_cl_def)

lemma sup_cl_obtains:
  assumes "x \<in> sup_cl X A"
  obtains Ex where "Ex \<in> Pow A \<and> Ex \<noteq> {}  \<and>is_sup X Ex x"
  by (meson assms sup_cl_imp1)

lemma inf_cl_obtains:
  assumes "x \<in> inf_cl X A"
  obtains Ex where "Ex \<in> Pow A \<and> Ex \<noteq> {} \<and> is_inf X Ex x"
  by (meson assms inf_cl_imp1)

lemma fin_inf_cl_obtains:
  assumes "x \<in> fin_inf_cl X A"
  obtains F where "F \<in> Fpow A \<and> is_inf X F x"
  by (meson assms fin_inf_cl_imp1)

lemma fne_inf_cl_obtains:
  assumes "x \<in> fne_inf_cl X A"
  obtains F where "F \<in> Fpow A \<and> F \<noteq> {} \<and> is_inf X F x"
  by (meson assms fne_inf_cl_imp1)

lemma fne_sup_cl_obtains:
  assumes "x \<in> fne_sup_cl X A"
  obtains F where "F \<in> Fpow A \<and> F \<noteq> {} \<and> is_sup X F x"
  by (meson assms fne_sup_cl_imp1)


definition is_sup_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_sup_cl X A\<equiv> (\<forall>E x. E \<in> Pow A \<and> E \<noteq> {} \<and> is_sup X E x \<longrightarrow> x \<in> A)"

definition is_inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_inf_cl X A \<equiv>  (\<forall>E x. E \<in> Pow A \<and> E \<noteq> {} \<and> is_inf X E x \<longrightarrow> x \<in> A)"

definition is_fin_inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_fin_inf_cl X A \<equiv>  (\<forall>E x. E \<in> Pow A \<and>  is_inf X E x \<longrightarrow> x \<in> A)"

definition is_fne_inf_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_fne_inf_cl X A \<equiv>  (\<forall>E x. E \<in> Fpow A \<and> E \<noteq> {} \<and> is_inf X E x \<longrightarrow> x \<in> A)"

lemma up_closed_supin_closed0:
  "is_ord_cl X A (\<le>) \<Longrightarrow> E \<in> Pow A \<Longrightarrow> E \<noteq> {} \<Longrightarrow> is_sup X E x  \<Longrightarrow> x \<in> A"
  using is_supD111 is_supD32 ord_cl_memI1 by fastforce

lemma up_closed_supin_closed:
  "is_ord_cl X A (\<le>) \<Longrightarrow> is_sup_cl X A"
  using is_sup_cl_def up_closed_supin_closed0 by blast

lemma dw_closed_infin_closed0:
  "is_ord_cl X A (\<ge>) \<Longrightarrow> E \<in> Pow A \<Longrightarrow> E \<noteq> {} \<Longrightarrow> is_inf X E x  \<Longrightarrow> x \<in> A"
  using is_infD111 is_infD1121 ord_cl_memI1 by fastforce

lemma down_closed_infin_closed:
  "is_ord_cl X A (\<ge>) \<Longrightarrow> is_inf_cl X A"
  by (metis dw_closed_infin_closed0 is_inf_cl_def)

lemma sup_cl_extensive:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> sup_cl X A"
  apply(auto simp add:sup_cl_def) by (metis PowI empty_not_insert empty_subsetI insert_subsetI subsetD sup_singleton)

lemma inf_cl_extensive:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> inf_cl X A"
  apply(auto simp add:inf_cl_def)
  by (metis PowI empty_not_insert empty_subsetI insert_subsetI subsetD inf_singleton)

lemma fin_inf_cl_extensive:
  assumes A0:"A \<subseteq> X"
  shows "A \<subseteq> fin_inf_cl X A"
proof
  fix a assume A1: "a \<in> A"
  have B0: "is_inf X {a} a"
    using A1 assms inf_singleton by blast
  have B2: "{a} \<in> Fpow A"
    by (simp add: A1 Fpow_def)
  show "a \<in> fin_inf_cl X A" apply(simp add:fin_inf_cl_def) using B0 B2 is_infD111 by blast
qed

lemma fne_inf_cl_extensive:
  assumes A0: "A \<subseteq> X"
  shows "A \<subseteq> fne_inf_cl X A"
proof
  fix a assume A1: "a \<in> A"
  have B0: "is_inf X {a} a"
    using A1 assms inf_singleton by blast
  have B2: "{a} \<in> Fpow A"
    by (simp add: A1 Fpow_def)
  show "a \<in> fne_inf_cl X A"
    apply(simp add:fne_inf_cl_def)
    using A1 B0 B2 assms by blast
qed

lemma fne_sup_cl_extensive:
  assumes A0: "A \<subseteq> X"
  shows "A \<subseteq> fne_sup_cl X A"
proof
  fix a assume A1: "a \<in> A"
  have B0: "is_sup X {a} a"
    using A1 assms sup_singleton by blast
  have B2: "{a} \<in> Fpow A"
    by (simp add: A1 Fpow_def)
  show "a \<in> fne_sup_cl X A"
    apply(simp add:fne_sup_cl_def)
    using A1 B0 B2 assms by blast
qed

lemma sup_cl_ext:
  "is_extensive (Pow X) (\<lambda>A. sup_cl X A)"
  by (meson PowD extensiveI1 sup_cl_extensive)

lemma inf_cl_ext:
  "is_extensive (Pow X) (\<lambda>A. inf_cl X A)"
  by (meson PowD extensiveI1 inf_cl_extensive)

lemma fin_inf_cl_ext:
  "is_extensive (Pow X) (\<lambda>A. fin_inf_cl X A)"
  by (meson PowD extensiveI1 fin_inf_cl_extensive)

lemma fne_inf_cl_ext:
  "is_extensive (Pow X) (\<lambda>A. fne_inf_cl X A)"
  by (meson PowD extensiveI1 fne_inf_cl_extensive)

lemma fne_sup_cl_ext:
  "is_extensive (Pow X) (\<lambda>A. fne_sup_cl X A)"
  by (meson PowD extensiveI1 fne_sup_cl_extensive)

lemma sup_cl_isotone:
  "\<lbrakk>A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> sup_cl X A \<subseteq> sup_cl X B"
  by(auto simp add:sup_cl_def)

lemma inf_cl_isotone:
  "\<lbrakk>A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> inf_cl X A \<subseteq> inf_cl X B"
  by(auto simp add:inf_cl_def)

lemma fin_inf_cl_isotone:
  "\<lbrakk>A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> fin_inf_cl X A \<subseteq> fin_inf_cl X B"
  apply(auto simp add:fin_inf_cl_def) using Fpow_mono by blast

lemma fne_inf_cl_isotone:
  "\<lbrakk>A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> fne_inf_cl X A \<subseteq> fne_inf_cl X B"
  apply(auto simp add:fne_inf_cl_def) by (metis Fpow_mono empty_iff subsetD)

lemma fne_sup_cl_isotone:
  "\<lbrakk>A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> fne_sup_cl X A \<subseteq> fne_sup_cl X B"
  apply(auto simp add:fne_sup_cl_def) by (metis Fpow_mono empty_iff subsetD)
                                                
lemma sup_cl_iso:
  "is_isotone (Pow X) (\<lambda>A. sup_cl X A)"
  by (meson PowD isotoneI1 sup_cl_isotone)

lemma inf_cl_iso:
  "is_isotone (Pow X) (\<lambda>A. inf_cl X A)"
  by (meson PowD isotoneI1 inf_cl_isotone)

lemma fin_inf_cl_iso:
  "is_isotone (Pow X) (\<lambda>A. fin_inf_cl X A)"
  by (meson PowD isotoneI1 fin_inf_cl_isotone)

lemma fne_inf_cl_iso:
  "is_isotone (Pow X) (\<lambda>A. fne_inf_cl X A)"
  by (meson PowD isotoneI1 fne_inf_cl_isotone)

lemma fne_sup_cl_iso:
  "is_isotone (Pow X) (\<lambda>A. fne_sup_cl X A)"
  by (meson PowD isotoneI1 fne_sup_cl_isotone)

lemma sup_cl_idempotent0:
  "s \<in> sup_cl X (sup_cl X A) \<Longrightarrow> (\<exists>E. E \<in> Pow (sup_cl X A) \<and> E \<noteq> {} \<and> is_sup X E s)"
  by (meson sup_cl_imp1)

lemma inf_cl_idempotent0:
  "s \<in> inf_cl X (inf_cl X A) \<Longrightarrow> (\<exists>E. E \<in> Pow (inf_cl X A) \<and> E \<noteq> {} \<and> is_inf X E s)"
  by (meson inf_cl_imp1)

lemma fin_inf_cl_idempotent0:
  "s \<in> fin_inf_cl X (fin_inf_cl X A) \<Longrightarrow> (\<exists>E. E \<in> Fpow (fin_inf_cl X A) \<and> is_inf X E s)"
  by (meson fin_inf_cl_imp1)

lemma fne_inf_cl_idempotent0:
  "s \<in> fne_inf_cl X (fne_inf_cl X A) \<Longrightarrow> (\<exists>E. E \<in> Fpow (fne_inf_cl X A) \<and> E \<noteq> {} \<and> is_inf X E s)"
  by (meson fne_inf_cl_imp1)

lemma fne_sup_cl_idempotent0:
  "s \<in> fne_sup_cl X (fne_sup_cl X A) \<Longrightarrow> (\<exists>E. E \<in> Fpow (fne_sup_cl X A) \<and> E \<noteq> {} \<and> is_sup X E s)"
  by (meson fne_sup_cl_imp1)

lemma sup_cl_idempotent1:
  "\<lbrakk>E \<in> Pow (sup_cl X A); E \<noteq> {}; x \<in> E\<rbrakk> \<Longrightarrow> (\<exists>Ex. Ex \<in> Pow A \<and> Ex \<noteq> {} \<and> is_sup X Ex x)"
  by (meson PowD in_mono sup_cl_imp1)

lemma inf_cl_idempotent1:
  "\<lbrakk>E \<in> Pow (inf_cl X A); E \<noteq> {}; x \<in> E\<rbrakk> \<Longrightarrow> (\<exists>Ex. Ex \<in> Pow A \<and> Ex \<noteq> {} \<and> is_inf X Ex x)"
  by (meson PowD in_mono inf_cl_imp1)

lemma fin_inf_cl_idempotent1:
  "\<lbrakk>E \<in> Pow (fin_inf_cl X A); E \<noteq> {}; x \<in> E\<rbrakk> \<Longrightarrow> (\<exists>Ex. Ex \<in> Fpow A  \<and> is_inf X Ex x)"
  by (meson PowD in_mono fin_inf_cl_imp1)

lemma fne_inf_cl_idempotent1:
  "\<lbrakk>E \<in> Pow (fne_inf_cl X A); E \<noteq> {}; x \<in> E\<rbrakk> \<Longrightarrow> (\<exists>Ex. Ex \<in> Fpow A \<and> Ex \<noteq> {}  \<and> is_inf X Ex x)"
  by (meson PowD in_mono fne_inf_cl_imp1)

lemma fne_sup_cl_idempotent1:
  "\<lbrakk>E \<in> Pow (fne_sup_cl X A); E \<noteq> {}; x \<in> E\<rbrakk> \<Longrightarrow> (\<exists>Ex. Ex \<in> Fpow A \<and> Ex \<noteq> {}  \<and> is_sup X Ex x)"
  by (meson PowD in_mono fne_sup_cl_imp1)


lemma sup_cl_idempotent2:
  "sup_cl X A \<subseteq> sup_cl X (sup_cl X A)"
  by (meson subsetI sup_cl_extensive sup_cl_imp0)

lemma inf_cl_idempotent2:
  "inf_cl X A \<subseteq> inf_cl X (inf_cl X A)"
  by (meson inf_cl_extensive inf_cl_imp0 subsetI)

lemma fin_inf_cl_idempotent2:
  "fin_inf_cl X A \<subseteq> fin_inf_cl X (fin_inf_cl X A)"
  by (meson fin_inf_cl_extensive fin_inf_cl_imp0 subsetI)

lemma fne_inf_cl_idempotent2:
  "fne_inf_cl X A \<subseteq> fne_inf_cl X (fne_inf_cl X A)"
  by (meson fne_inf_cl_extensive fne_inf_cl_imp0 subsetI)

lemma fne_sup_cl_idempotent2:
  "fne_sup_cl X A \<subseteq> fne_sup_cl X (fne_sup_cl X A)"
  by (meson fne_sup_cl_extensive fne_sup_cl_imp0 subsetI)

lemma sup_cl_idempotent:
   "sup_cl X (sup_cl X A) = sup_cl X A"
proof-
  let ?L1="sup_cl X A" let ?L2="sup_cl X ?L1"
  show "sup_cl X (sup_cl X A) = sup_cl X A"
  proof
    show "?L1 \<subseteq>?L2"
      by (meson subset_iff sup_cl_extensive sup_cl_imp0)
    next
    show "?L2 \<subseteq> ?L1"
  proof
    fix s assume P0:"s \<in>?L2"
    show "s \<in> ?L1"
    proof-
      let ?P="\<lambda>E x. E \<in> Pow A \<and> E \<noteq> {} \<and> is_sup X E x"
      let ?f= "(\<lambda>x. SOME Ex. ?P Ex x)"
      obtain E where P1:"E \<in> Pow (?L1) \<and> E \<noteq> {} \<and> is_sup X E s"
        by (meson P0 sup_cl_idempotent0)
      have B0:"\<forall>x \<in> E. (\<exists>Ex. ?P Ex x)"
        using P1 sup_cl_idempotent1 by auto
      let ?fE="?f`E" let ?S="{s \<in> X. \<exists>Ai \<in> ?fE. s = Sup X Ai}"
      have B00:"((\<lambda>Ai. Sup X Ai)`?fE) = ?S" apply(auto) 
          by (metis (mono_tags, lifting) B0 PowD is_supD111 someI_ex sup_equality)
      have B1:"\<forall>x \<in> E. ?P (?f x) x"
        by (metis (mono_tags, lifting) B0 tfl_some)
      have B2:"?S = E"
      proof
        show "?S \<subseteq> E"
          proof
            fix s assume B6A0:"s \<in>?S"
            have B60:"\<exists>Ai \<in> ?fE. s = Sup X Ai"
              using B6A0 by blast
            show "s \<in> E"
              using B1 B60 sup_equality by fastforce
          qed
        next  
        show "E \<subseteq> ?S"
          proof
            fix s assume B6A1:"s \<in> E"
            show "s \<in> ?S"
              using B1 B6A1 is_supD111 sup_equality by fastforce
        qed
      qed
      obtain se where B11A0:"is_sup X E se"
        using P1 by blast
      obtain ss where B11A1:"is_sup X ?S ss"
        using B11A0 B2 by auto
      have B8:"\<forall>Ai \<in> ?fE. (\<exists>si. is_sup X Ai si)"
        using B1 by blast
      have B11:"(\<And>Ai. Ai \<in> ?fE \<Longrightarrow> \<exists>ti. is_sup X Ai ti)"
        using B1 by blast
      have B12:"?fE \<noteq> {}"
        by (simp add: P1)
      have B13:"is_sup X ((\<lambda>Ai. Sup X Ai)`?fE) ss"
        using B00 B11A1 by presburger
      have B14:"is_sup X (\<Union>?fE) ss"
        by (metis (no_types, lifting) B12 B13 B8 sup_families) 
      have B15:"(\<Union>?fE) \<in> Pow A"
        using B1 by blast
      have B16:"(\<Union>?fE) \<noteq> {}"
        using B1 P1 by auto
      show "s \<in> ?L1"
        by (metis (no_types, lifting) B11A1 B14 B15 B16 B2 P1 sup_cl_if1 sup_iff2)
      qed
    qed
  qed
qed


lemma inf_cl_idempotent:
   "inf_cl X (inf_cl X A) = inf_cl X A"
proof-
  let ?L1="inf_cl X A" let ?L2="inf_cl X ?L1"
  show "inf_cl X (inf_cl X A) = inf_cl X A"
  proof
    show "?L1 \<subseteq>?L2"
      by (meson subset_iff inf_cl_extensive inf_cl_imp0)
    next
    show "?L2 \<subseteq> ?L1"
  proof
    fix s assume P0:"s \<in>?L2"
    show "s \<in> ?L1"
    proof-
      let ?P="\<lambda>E x. E \<in> Pow A \<and> E \<noteq> {} \<and> is_inf X E x"
      let ?f= "(\<lambda>x. SOME Ex. ?P Ex x)"
      obtain E where P1:"E \<in> Pow (?L1) \<and> E \<noteq> {} \<and> is_inf X E s"
        by (meson P0 inf_cl_idempotent0)
      have B0:"\<forall>x \<in> E. (\<exists>Ex. ?P Ex x)"
        using P1 inf_cl_idempotent1 by auto
      let ?fE="?f`E" let ?S="{s \<in> X. \<exists>Ai \<in> ?fE. s = Inf X Ai}"
      have B00:"((\<lambda>Ai. Inf X Ai)`?fE) = ?S" apply(auto) 
          by (metis (mono_tags, lifting) B0 PowD is_infD111 someI_ex inf_equality)
      have B1:"\<forall>x \<in> E. ?P (?f x) x"
        by (metis (mono_tags, lifting) B0 tfl_some)
      have B2:"?S = E"
      proof
        show "?S \<subseteq> E"
          proof
            fix s assume B6A0:"s \<in>?S"
            have B60:"\<exists>Ai \<in> ?fE. s = Inf X Ai"
              using B6A0 by blast
            show "s \<in> E"
              using B1 B60 inf_equality by fastforce
          qed
        next  
        show "E \<subseteq> ?S"
          proof
            fix s assume B6A1:"s \<in> E"
            show "s \<in> ?S"
              using B1 B6A1 is_infD111 inf_equality by fastforce
        qed
      qed
      obtain se where B11A0:"is_inf X E se"
        using P1 by blast
      obtain ss where B11A1:"is_inf X ?S ss"
        using B11A0 B2 by auto
      have B8:"\<forall>Ai \<in> ?fE. (\<exists>si. is_inf X Ai si)"
        using B1 by blast
      have B11:"(\<And>Ai. Ai \<in> ?fE \<Longrightarrow> \<exists>ti. is_inf X Ai ti)"
        using B1 by blast
      have B12:"?fE \<noteq> {}"
        by (simp add: P1)
      have B13:"is_inf X ((\<lambda>Ai. Inf X Ai)`?fE) ss"
        using B00 B11A1 by presburger
      have B14:"is_inf X (\<Union>?fE) ss"
        by (metis (no_types, lifting) B12 B13 B8 inf_families) 
      have B15:"(\<Union>?fE) \<in> Pow A"
        using B1 by blast
      have B16:"(\<Union>?fE) \<noteq> {}"
        using B1 P1 by auto
      show "s \<in> ?L1"
        by (metis (no_types, lifting) B11A1 B14 B15 B16 B2 P1 inf_cl_if1 inf_iff2)
      qed
    qed
  qed
qed


lemma fin_inf_cl_idempotent:
   "fin_inf_cl X (fin_inf_cl X A) = fin_inf_cl X A"
proof-
  let ?L1="fin_inf_cl X A" let ?L2="fin_inf_cl X ?L1"
  show "fin_inf_cl X (fin_inf_cl X A) = fin_inf_cl X A"
  proof
    show "?L1 \<subseteq>?L2"
      by (meson subset_iff fin_inf_cl_extensive fin_inf_cl_imp0)
    next
    show "?L2 \<subseteq> ?L1"
  proof
    fix s assume P0:"s \<in>?L2"
    show "s \<in> ?L1"
    proof-
      let ?P="\<lambda>E x. E \<in> Fpow A \<and> is_inf X E x"
      let ?f= "(\<lambda>x. SOME Ex. ?P Ex x)"
      obtain E where P1:"E \<in> Fpow (?L1) \<and> is_inf X E s"
        by (meson P0 fin_inf_cl_idempotent0)
      have B0:"\<forall>x \<in> E. (\<exists>Ex. ?P Ex x)"
        using Fpow_subset_Pow P1 fin_inf_cl_idempotent1 by fastforce
      let ?fE="?f`E" let ?S="{s \<in> X. \<exists>Ai \<in> ?fE. s = Inf X Ai}"
      have B00:"((\<lambda>Ai. Inf X Ai)`?fE) = ?S" apply(auto)
        by (metis (no_types, lifting) B0 inf_equality is_infD111 someI_ex) 
      have B1:"\<forall>x \<in> E. ?P (?f x) x"
        by (metis (mono_tags, lifting) B0 tfl_some)
      have B2:"?S = E"
      proof
        show "?S \<subseteq> E"
          proof
            fix s assume B6A0:"s \<in>?S"
            have B60:"\<exists>Ai \<in> ?fE. s = Inf X Ai"
              using B6A0 by blast
            show "s \<in> E"
              using B1 B60 inf_equality by fastforce
          qed
        next  
        show "E \<subseteq> ?S"
          proof
            fix s assume B6A1:"s \<in> E"
            show "s \<in> ?S"
              by (metis (mono_tags, lifting) B00 B1 B6A1 image_iff inf_equality)
        qed
      qed
      obtain se where B11A0:"is_inf X E se"
        using P1 by blast
      obtain ss where B11A1:"is_inf X ?S ss"
        using B11A0 B2 by auto
      have B8:"\<forall>Ai \<in> ?fE. (\<exists>si. is_inf X Ai si)"
        using B1 by blast
      have B11:"(\<And>Ai. Ai \<in> ?fE \<Longrightarrow> \<exists>ti. is_inf X Ai ti)"
        using B1 by blast
      have B13:"is_inf X ((\<lambda>Ai. Inf X Ai)`?fE) ss"
        using B00 B11A1 by presburger
      have B14:"is_inf X (\<Union>?fE) ss"
        by (metis (no_types, lifting) B11 B13 Sup_empty image_empty inf_families)
      have B15:"(\<Union>?fE) \<in> Fpow A"
      proof-
        have B130: "(\<forall>Ai \<in> ?fE. Ai \<in> Fpow A)"
          using B1 by fastforce
        have B131:"finite ?fE"
          using Fpow_def P1 by blast
       have B132:"finite (\<Union>?fE)"
         using B130 B131 Fpow_def by blast
        have B133:"(\<Union>?fE) \<in> Pow A"
          using B1 Fpow_subset_Pow by blast
       show ?thesis
         using B132 B133 Fpow_Pow_finite by blast
      qed
      show "s \<in> ?L1"
        by (metis (no_types, lifting) B11A1 B14 B15 B2 P0 P1 fin_inf_cl_if1 fin_inf_cl_imp0 is_inf_unique)
      qed
    qed
  qed
qed


lemma fne_inf_cl_idempotent:
  "fne_inf_cl X (fne_inf_cl X A) = fne_inf_cl X A"
proof-
  let ?L1="fne_inf_cl X A" let ?L2="fne_inf_cl X ?L1"
  show "fne_inf_cl X (fne_inf_cl X A) = fne_inf_cl X A"
  proof
    show "?L1 \<subseteq>?L2"
      by (simp add: fne_inf_cl_idempotent2)
    next
    show "?L2 \<subseteq> ?L1"
  proof
    fix s assume P0:"s \<in>?L2"
    show "s \<in> ?L1"
    proof-
      let ?P="\<lambda>E x. E \<in> Fpow A \<and> E \<noteq> {} \<and> is_inf X E x"
      let ?f= "(\<lambda>x. SOME Ex. ?P Ex x)"
      obtain E where P1:"E \<in> Fpow (?L1) \<and> E \<noteq> {} \<and> is_inf X E s"
        using P0 fne_inf_cl_imp1 by blast
      have B0:"\<forall>x \<in> E. (\<exists>Ex. ?P Ex x)"
        using Fpow_subset_Pow P1 fne_inf_cl_idempotent1 by blast
      let ?fE="?f`E" let ?S="{s \<in> X. \<exists>Ai \<in> ?fE. s = Inf X Ai}"
      have B00:"((\<lambda>Ai. Inf X Ai)`?fE) = ?S" apply(auto)
        by (metis (mono_tags, lifting) B0 inf_equality is_infD111 someI_ex)
      have B1:"\<forall>x \<in> E. ?P (?f x) x"
        by (metis (mono_tags, lifting) B0 tfl_some)
      have B2:"?S = E"
      proof
        show "?S \<subseteq> E"
          proof
            fix s assume B6A0:"s \<in>?S"
            have B60:"\<exists>Ai \<in> ?fE. s = Inf X Ai"
              using B6A0 by blast
            show "s \<in> E"
              using B1 B60 inf_equality by fastforce
          qed
        next  
        show "E \<subseteq> ?S"
          proof
            fix s assume B6A1:"s \<in> E"
            show "s \<in> ?S"
              by (metis (mono_tags, lifting) B00 B1 B6A1 image_iff inf_equality)
        qed
      qed
      obtain se where B11A0:"is_inf X E se"
        using P1 by blast
      obtain ss where B11A1:"is_inf X ?S ss"
        using B11A0 B2 by auto
      have B8:"\<forall>Ai \<in> ?fE. (\<exists>si. is_inf X Ai si)"
        using B1 by blast
      have B11:"(\<And>Ai. Ai \<in> ?fE \<Longrightarrow> \<exists>ti. is_inf X Ai ti)"
        using B1 by blast
      have B13:"is_inf X ((\<lambda>Ai. Inf X Ai)`?fE) ss"
        using B00 B11A1 by presburger
      have B14:"is_inf X (\<Union>?fE) ss"
        by (metis (no_types, lifting) B11 B13 Sup_empty image_empty inf_families)
      have B15:"(\<Union>?fE) \<in> Fpow A"
      proof-
        have B130: "(\<forall>Ai \<in> ?fE. Ai \<in> Fpow A)"
          using B1 by fastforce
        have B131:"finite ?fE"
          using Fpow_def P1 by blast
       have B132:"finite (\<Union>?fE)"
         using B130 B131 Fpow_def by blast
        have B133:"(\<Union>?fE) \<in> Pow A"
          using B1 Fpow_subset_Pow by blast
       show ?thesis
         using B132 B133 Fpow_Pow_finite by blast
      qed
      show "s \<in> ?L1"
        by (metis (no_types, lifting) B1 B11A1 B14 B15 B2 P1 SUP_bot_conv(2) equals0I fne_inf_cl_if1 inf_equality is_infD111)
      qed
    qed
  qed
qed


lemma fne_sup_cl_idempotent:
  "fne_sup_cl X (fne_sup_cl X A) = fne_sup_cl X A"
proof-
  let ?L1="fne_sup_cl X A" let ?L2="fne_sup_cl X ?L1"
  show "fne_sup_cl X (fne_sup_cl X A) = fne_sup_cl X A"
  proof
    show "?L1 \<subseteq>?L2"
      by (simp add: fne_sup_cl_idempotent2)
    next
    show "?L2 \<subseteq> ?L1"
  proof
    fix s assume P0:"s \<in>?L2"
    show "s \<in> ?L1"
    proof-
      let ?P="\<lambda>E x. E \<in> Fpow A \<and> E \<noteq> {} \<and> is_sup X E x"
      let ?f= "(\<lambda>x. SOME Ex. ?P Ex x)"
      obtain E where P1:"E \<in> Fpow (?L1) \<and> E \<noteq> {} \<and> is_sup X E s"
        using P0 fne_sup_cl_imp1 by blast
      have B0:"\<forall>x \<in> E. (\<exists>Ex. ?P Ex x)"
        using Fpow_subset_Pow P1 fne_sup_cl_idempotent1 by blast
      let ?fE="?f`E" let ?S="{s \<in> X. \<exists>Ai \<in> ?fE. s = Sup X Ai}"
      have B00:"((\<lambda>Ai. Sup X Ai)`?fE) = ?S" apply(auto)
        by (metis (mono_tags, lifting) B0 sup_equality is_supD111 someI_ex)
      have B1:"\<forall>x \<in> E. ?P (?f x) x"
        by (metis (mono_tags, lifting) B0 tfl_some)
      have B2:"?S = E"
      proof
        show "?S \<subseteq> E"
          proof
            fix s assume B6A0:"s \<in>?S"
            have B60:"\<exists>Ai \<in> ?fE. s = Sup X Ai"
              using B6A0 by blast
            show "s \<in> E"
              using B1 B60 sup_equality by fastforce
          qed
        next  
        show "E \<subseteq> ?S"
          proof
            fix s assume B6A1:"s \<in> E"
            show "s \<in> ?S"
              by (metis (mono_tags, lifting) B00 B1 B6A1 image_iff sup_equality)
        qed
      qed
      obtain se where B11A0:"is_sup X E se"
        using P1 by blast
      obtain ss where B11A1:"is_sup X ?S ss"
        using B11A0 B2 by auto
      have B8:"\<forall>Ai \<in> ?fE. (\<exists>si. is_sup X Ai si)"
        using B1 by blast
      have B11:"(\<And>Ai. Ai \<in> ?fE \<Longrightarrow> \<exists>ti. is_sup X Ai ti)"
        using B1 by blast
      have B13:"is_sup X ((\<lambda>Ai. Sup X Ai)`?fE) ss"
        using B00 B11A1 by presburger
      have B14:"is_sup X (\<Union>?fE) ss"
        by (metis (no_types, lifting) B11 B13 Sup_empty image_empty sup_families)
      have B15:"(\<Union>?fE) \<in> Fpow A"
      proof-
        have B130: "(\<forall>Ai \<in> ?fE. Ai \<in> Fpow A)"
          using B1 by fastforce
        have B131:"finite ?fE"
          using Fpow_def P1 by blast
       have B132:"finite (\<Union>?fE)"
         using B130 B131 Fpow_def by blast
        have B133:"(\<Union>?fE) \<in> Pow A"
          using B1 Fpow_subset_Pow by blast
       show ?thesis
         using B132 B133 Fpow_Pow_finite by blast
      qed
      show "s \<in> ?L1"
        by (metis (no_types, lifting) B1 B11A1 B14 B15 B2 P1 SUP_bot_conv(2) equals0I fne_sup_cl_if1 sup_equality is_supD111)
      qed
    qed
  qed
qed


lemma sup_cl_ide:
  "is_idempotent (Pow X) (\<lambda>A. sup_cl X A)"
  by (simp add: is_idempotent_def sup_cl_idempotent)

lemma inf_cl_ide:
  "is_idempotent (Pow X) (\<lambda>A. inf_cl X A)"
  by (simp add: is_idempotent_def inf_cl_idempotent)

lemma fin_inf_cl_ide:
  "is_idempotent (Pow X) (\<lambda>A. fin_inf_cl X A)"
  by (simp add: is_idempotent_def fin_inf_cl_idempotent)

lemma fne_inf_cl_ide:
  "is_idempotent (Pow X) (\<lambda>A. fne_inf_cl X A)"
  by (simp add: is_idempotent_def fne_inf_cl_idempotent)

lemma fne_sup_cl_ide:
  "is_idempotent (Pow X) (\<lambda>A. fne_sup_cl X A)"
  by (simp add: is_idempotent_def fne_sup_cl_idempotent)

lemma sup_cl_range:
  "(\<lambda>A. sup_cl X A)`(Pow X) \<subseteq> Pow X"
  by (metis PowI idempotentD3 subsetI sup_cl_ide sup_cl_imp0)

lemma inf_cl_range:
  "(\<lambda>A. inf_cl X A)`(Pow X) \<subseteq> Pow X"
  by (metis PowI idempotentD3 inf_cl_ide inf_cl_imp0 subsetI)

lemma fin_inf_cl_range:
  "(\<lambda>A. fin_inf_cl X A)`(Pow X) \<subseteq> Pow X"
  by (metis PowI idempotentD3 subsetI fin_inf_cl_ide fin_inf_cl_imp0)

lemma fne_inf_cl_range:
  "(\<lambda>A. fne_inf_cl X A)`(Pow X) \<subseteq> Pow X"
  by (metis PowI idempotentD3 subsetI fne_inf_cl_ide fne_inf_cl_imp0)

lemma fne_sup_cl_range:
  "(\<lambda>A. fne_sup_cl X A)`(Pow X) \<subseteq> Pow X"
  by (metis PowI idempotentD3 subsetI fne_sup_cl_ide fne_sup_cl_imp0)

lemma sup_cl_is_cl:
  "is_closure (Pow X) (\<lambda>A. sup_cl X A)"
  by (simp add: is_closure_def sup_cl_ext sup_cl_ide sup_cl_iso sup_cl_range)

lemma inf_cl_is_cl:
  "is_closure (Pow X) (\<lambda>A. inf_cl X A)"
  by (simp add: inf_cl_ext inf_cl_ide inf_cl_iso inf_cl_range is_closure_def)

lemma fin_inf_cl_is_cl:
  "is_closure (Pow X) (\<lambda>A. fin_inf_cl X A)"
  by (simp add: fin_inf_cl_ext fin_inf_cl_ide fin_inf_cl_iso fin_inf_cl_range is_closure_def)

lemma fne_inf_cl_is_cl:
  "is_closure (Pow X) (\<lambda>A. fne_inf_cl X A)"
  by (simp add: fne_inf_cl_ext fne_inf_cl_ide fne_inf_cl_iso fne_inf_cl_range is_closure_def)

lemma fne_sup_cl_is_cl:
  "is_closure (Pow X) (\<lambda>A. fne_sup_cl X A)"
  by (simp add: fne_sup_cl_ext fne_sup_cl_ide fne_sup_cl_iso fne_sup_cl_range is_closure_def)

lemma fne_sup_cl_dir:
  assumes A0:"is_sup_semilattice X" and A1:"A \<subseteq> X"
  shows  "is_dir (fne_sup_cl X A) (\<le>)"
proof-
  have B0:"\<And>a b. a \<in> fne_sup_cl X A \<and> b \<in> fne_sup_cl X A \<longrightarrow> (\<exists>c\<in>fne_sup_cl X A. a \<le> c \<and> b \<le> c)"
  proof
    fix a b assume A2:"a \<in> fne_sup_cl X A \<and> b \<in> fne_sup_cl X A "
    obtain Ea where A3:"Ea \<in> Fpow A \<and> Ea \<noteq> {} \<and> is_sup X Ea a"
      using A2 fne_sup_cl_imp1 by blast
    obtain Eb where A4:"Eb \<in> Fpow A \<and> Eb \<noteq> {} \<and> is_sup X Eb b"
      using A2 fne_sup_cl_imp1 by blast
    have B1:"Ea \<union> Eb \<in> Fpow A \<and> Ea \<union> Eb \<noteq> {}"
      by (metis A3 A4 Fpow_Pow_finite Int_Collect Pow_iff Un_empty Un_subset_iff finite_UnI)
    have B2:"(Ea \<union> Eb) \<subseteq> X"
      by (metis A1 A3 A4 Fpow_Pow_finite Int_Collect Pow_iff dual_order.trans sup.boundedI)
    obtain c where A5:"is_sup X (Ea \<union> Eb) c"
      by (metis A0 B1 B2 Fpow_Pow_finite Int_Collect bsup_finite2)
    have B3:"c \<in> fne_sup_cl X A \<and> a \<le> c \<and> b \<le> c"
      by (meson A3 A4 A5 B1 Un_upper2 fne_sup_cl_if1 is_supD111 is_sup_iso1 sup.cobounded1)
    show "(\<exists>c\<in>fne_sup_cl X A. a \<le> c \<and> b \<le> c)"
      using B3 by blast
  qed
  show ?thesis
    by (simp add: B0 is_updirI1)
qed
  
section Compactness


definition is_compact::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "is_compact X c \<equiv> c \<in> X \<and> (\<forall>A. A \<in> Pow_ne X \<and> c \<le> Sup X A \<longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> c \<le> Sup X A0))"

definition compact_elements::"'a::order set \<Rightarrow> 'a::order set" where
  "compact_elements X \<equiv> {c. is_compact X c}"

definition compactly_generated::"'a::order set \<Rightarrow> bool" where
  "compactly_generated X \<equiv> (\<forall>x. x \<in> X \<longrightarrow> (\<exists>C \<in> Pow_ne (compact_elements X). is_sup X C x))"

lemma compcatI:
  "\<lbrakk>c \<in> X; (\<And>A. \<lbrakk>A \<in> Pow_ne X; c \<le> Sup X A\<rbrakk> \<Longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> c \<le> Sup X A0))\<rbrakk> \<Longrightarrow> is_compact X c"
  by(simp add:is_compact_def)

lemma compcatD:
  "\<lbrakk>is_compact X c; A \<in> Pow_ne X; c \<le> Sup X A\<rbrakk> \<Longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> c \<le> Sup X A0)"
  by(simp add:is_compact_def)

lemma compact_elements_mem_iff1:
  "x \<in> compact_elements X \<longleftrightarrow> is_compact X x"
  by (simp add: compact_elements_def)

(*
  in a csup semilattice an element is compact iff directed coverings contain an upper bound
*)

lemma ccompact0:
  assumes A0:"is_sup_semilattice X" and
          A1:"is_compact X c" and
          A2:"A \<in> Pow_ne X" and
          A3:"c \<le> Sup X A" and
          A4:"is_dir A (\<le>)"
  shows "\<exists>a \<in> A. c \<le> a"
proof-
  obtain A0 where A5:"A0 \<in> Fpow_ne A \<and> c \<le> Sup X A0"
    using A1 A2 A3 compcatD by blast  
  obtain a where A6:"a \<in> A \<and> a ub A0"
    by (metis A4 A5 fpow_ne_iff2 updir_finite2)
  have B0:"Sup X A0 \<le> a"
    by (metis A0 A2 A5 A6 bsup_finite2 dual_order.trans fpow_ne_iff2 is_supD42 pow_neD1 subsetD)
  have B1:"c \<le> a"
    using A5 B0 by fastforce
  show ?thesis
    using A6 B1 by blast
qed

lemma ccompact1:
  assumes A0:"is_csup_semilattice X" and
          A1:"c \<in> X" and
          A2:"(\<And>A. \<lbrakk>A \<in> Pow_ne X; c \<le> Sup X A; is_dir A (\<le>)\<rbrakk> \<Longrightarrow> (\<exists>a \<in> A. c \<le> a))"
  shows "is_compact X c"
proof-
  have P0:"(\<And>A. A \<in> Pow_ne X \<and> c \<le> Sup X A \<longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> c \<le> Sup X A0))"
  proof
    fix A assume A3:"A \<in> Pow_ne X \<and> c \<le> Sup X A"
    let ?C="fne_sup_cl X A"
    have B0:"is_dir ?C (\<le>)"
      by (simp add: A0 A3 csup_fsup fne_sup_cl_dir pow_neD1)
    have B1:"A \<subseteq> ?C"
      by (simp add: A3 fne_sup_cl_extensive pow_neD1)
    have B2:"A \<subseteq> X \<and> ?C \<subseteq> X"
      using B1 fne_sup_cl_imp0 by blast
    have B2:"Sup X A \<le> Sup X ?C"
      by (metis A0 A3 B1 B2 bot.extremum_uniqueI csupD2 is_sup_iso1 pow_ne_iff2 sup_equality)
    have B3:"c \<le> Sup X ?C"
      using A3 B2 dual_order.trans by blast
    obtain d where B4:"d \<in> ?C \<and> c \<le> d"
      by (metis A2 A3 B0 B1 B3 bot.extremum_uniqueI fne_sup_cl_range image_subset_iff pow_ne_iff1)
    obtain Fd where B5:"Fd \<in> Fpow_ne A \<and> Sup X Fd = d"
      by (meson B4 fne_sup_cl_imp1 fpow_ne_iff1 sup_equality)
    have B6:"Fd \<in> Fpow_ne A \<and> c \<le> Sup X Fd"
      by (simp add: B4 B5)
    show "(\<exists>A0. A0 \<in> Fpow_ne A \<and> c \<le> Sup X A0)"
      using B6 by blast
  qed
  show ?thesis
    by (simp add: A1 P0 compcatI)
qed

lemma bot_compact:
  assumes A1:"bot \<in> X" and A2:"(\<And>x. x \<in> X \<Longrightarrow> bot \<le> x)"
  shows "is_compact X bot"
proof-
  have P0:"(\<And>A. A \<in> Pow_ne X \<and> bot \<le> Sup X A \<longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> bot \<le> Sup X A0))" 
    proof
      fix A assume A3:"A \<in> Pow_ne X \<and> bot \<le> Sup X A"
      obtain a where A4:"a \<in> A"
        using A3 pow_ne_bot by fastforce
      have B0:"{a} \<in> Fpow_ne A \<and> bot \<le> Sup X {a}"
        by (metis A2 A3 A4 bsup_idem1 empty_subsetI finite.emptyI finite.insertI fpow_neI in_mono insert_absorb2 insert_not_empty insert_subsetI pow_neD1)
      show "(\<exists>A0. A0 \<in> Fpow_ne A \<and> bot \<le> Sup X A0)"
        using B0 by auto
    qed
  show ?thesis
    by (simp add: A1 P0 compcatI)
qed


definition prime::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "prime X A \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. (Sup X {a, b}) \<in> A \<longrightarrow> (a \<in> A \<or> b \<in> A))"

abbreviation pfilter::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "pfilter X A \<equiv> (is_filter X A) \<and> X \<noteq> A"
                    



lemma primefilterD1:
  "\<lbrakk>prime X A; pfilter X A\<rbrakk> \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> X; b \<in> X;  (Sup X {a, b}) \<in> A\<rbrakk> \<Longrightarrow> (a \<in> A \<or> b \<in> A))"
  by (simp add: prime_def)

lemma primefilterD2:
  "\<lbrakk>is_lattice X; prime X A; pfilter X A\<rbrakk> \<Longrightarrow> (\<And>a b.  \<lbrakk>a \<in> X; b \<in> X; (a \<in> A \<or> b \<in> A)\<rbrakk> \<Longrightarrow> (Sup X {a, b}) \<in> A)"
  by (metis doubleton_eq_iff filter_on_lattice_sup01)

lemma primefilterD3:
  "\<lbrakk>is_lattice X; prime X F; pfilter X F\<rbrakk> \<Longrightarrow> (\<And>F1 F2. \<lbrakk>is_filter X F1; is_filter X F2; \<not>(F1 \<subseteq> F); \<not>(F2 \<subseteq> F)\<rbrakk> \<Longrightarrow> \<not>(F1 \<inter> F2 \<subseteq> F))"
  apply(auto simp add:prime_def) apply (meson filterD2 filters_on_lattice_inf02 in_mono) using filterD21 by blast


lemma primefilterI2:
  assumes A0:"is_lattice X" and A1:"pfilter X F" and 
          A2:"(\<And>F1 F2. \<lbrakk>is_filter X F1; is_filter X F2; F1 \<inter> F2 \<subseteq> F\<rbrakk> \<Longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F)"
  shows "prime X F"
proof-
  have B0:"\<And>a b. a \<in> X \<and> b \<in> X \<and> (Sup X {a, b}) \<in> F \<longrightarrow> (a \<in> F \<or> b \<in> F)"
  proof
    fix a b assume A3:" a \<in> X \<and> b \<in> X \<and> (Sup X {a, b}) \<in> F"
    have B1:"(([a)\<^sub>X) \<inter> ([b)\<^sub>X)) \<subseteq> F"
      apply(auto simp add:lorc_def)  by (meson A0 A1 A3 binary_supD4 filterD4 is_ord_clE1 lattD32 latt_iff ssupD4)
    have B2:"([a)\<^sub>X) \<subseteq> F \<or> ([b)\<^sub>X) \<subseteq> F"
      by (simp add: A2 A3 B1 lorc_filter)
    show "(a \<in> F \<or> b \<in> F)"
      using A3 B2 lorc_memI1 by blast
  qed
  show ?thesis
    by (simp add: B0 prime_def)
qed


lemma primefilterI1:
  "\<lbrakk>is_lattice X;  pfilter X A; (\<forall>a b. (a \<in> A \<or> b \<in> A) \<longleftrightarrow> ((Sup X {a, b}) \<in> A)) \<rbrakk> \<Longrightarrow> prime X A"
  by (simp add: prime_def)

lemma primefilter_iff1:
  "is_lattice X \<Longrightarrow> ( prime X A \<and> pfilter X A) \<longleftrightarrow> (pfilter X A \<and>  (\<forall>a \<in> X. \<forall>b \<in> X. (a \<in> A \<or> b \<in> A) \<longleftrightarrow> ((Sup X {a, b}) \<in> A)))"
  by (metis prime_def primefilterD2)

lemma prime_filter_iff2:
  "is_lattice X \<Longrightarrow>  (prime X F \<and> pfilter X F)  \<longleftrightarrow>  (pfilter X F \<and> (\<forall>F1 F2. is_filter X F1 \<and> is_filter X F2 \<and> F1 \<inter> F2 \<subseteq> F \<longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F))"
  by (metis primefilterD3 primefilterI2)

lemma lattice_absorb1:
  "\<lbrakk>is_lattice X; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Sup X {x,Inf X {x, y} } = x"
  by (simp add: binf_leI1 bsup_ge2 latt_iff sinfD4)

lemma lattice_absorb2:
  "\<lbrakk>is_lattice X; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Inf X {x,Sup X {x, y} } = x"
  by (simp add: binf_lt1 bsup_geI1 latt_iff ssupD4)

lemma distrib_sup_le: "\<lbrakk>is_lattice X; x \<in>X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Sup X {x, Inf X {y, z}} \<le> Inf X {Sup X {x, y}, Sup X {x, z}}"
  by(auto simp add: bsup_geI1 lattD42 binary_infD4 bsup_geI2 bsup_iff latt_iff sinfD3 sinfD4 ssupD4 binf_leI3 binf_leI1 binf_leI2)

lemma distrib_inf_le: "\<lbrakk>is_lattice X; x \<in>X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Sup X {Inf X {x, y}, Inf X {x, z}} \<le> Inf X {x, Sup X {y, z}}"
  by(auto simp add:bsup_geI1 lattD42 binary_infD4 bsup_geI2 bsup_iff latt_iff sinfD3 sinfD4 ssupD4 binf_leI1 binf_leI2 binf_leI3)

lemma distibD1:
  assumes A0:"is_lattice X" and 
          A1:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> Inf X {x, Sup X {y, z}} = Sup X {Inf X {x, y}, Inf X {x, z}}" and
          A2:" x \<in> X \<and> y \<in> X \<and> z \<in> X"
  shows "Sup X {x, Inf X {y, z}} = Inf X {Sup X {x, y}, Sup X {x, z}}"
proof-
  have B0:"Sup X {x, Inf X {y, z}} = Sup X {Sup X {x, Inf X {x, z}}, Inf X {y, z}}"
    by (simp add: A0 A2 lattice_absorb1)
  have B1:"... = Sup X {x, Inf X {z, Sup X {x, y}}}"
    by (simp add: A0 A1 A2 binf_commute2 bsup_assoc1 lattD41 lattD42 sinfD4)
  have B2:"... = Sup X {Inf X {Sup X {x, y}, x}, Inf X {Sup X {x, y}, z}}"
    by (simp add: A0 A2 insert_commute lattice_absorb2)
  have B3:"... = Inf X {Sup X {x, y}, Sup X {x, z}}"
    by (simp add: A0 A1 A2 lattD42 ssupD4)
  show ?thesis
    by (simp add: B0 B1 B2 B3)
qed
  
lemma distribD2:
  assumes A0: "is_lattice X" and
          A1: "\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Sup X {x, Inf X {y, z}} = Inf X {Sup X {x, y}, Sup X {x, z}}" and
          A2: "x \<in> X \<and> y \<in> X \<and> z \<in> X"
  shows "Inf X {x, Sup X {y, z}} = Sup X {Inf X {x, y}, Inf X {x, z}}"
proof -
  have B0:"Inf X {x, Sup X {y, z}} = Inf X {Inf X {x, Sup X {x, z}}, Sup X {y, z}}"
    by (simp add: A0 A2 lattice_absorb2)
  have B1:"... = Inf X {x, Sup X {z, Inf X {x, y}}}"
    by (simp add: A0 A1 A2 binf_assoc1 bsup_commute2 lattD41 lattD42 ssupD4)
  have B2:"... = Inf X {Sup X {Inf X {x, y}, x}, Sup X {Inf X {x, y}, z}}"
    by (simp add: A0 A2 insert_commute lattice_absorb1)
  have B3:"... = Sup X {Inf X {x, y}, Inf X {x, z}}"
    by (simp add: A0 A1 A2 lattD41 sinfD4)
  show ?thesis
    by (simp add: B0 B1 B2 B3)
qed




definition distributive_lattice::"'a::order set \<Rightarrow> bool" where
  "distributive_lattice X \<equiv> (is_lattice X) \<and> (\<forall>x \<in> X. \<forall>y \<in> X. \<forall>z \<in> X. Sup X {x, Inf X {y, z}} = Inf X {Sup X {x, y}, Sup X {x, z}})"

lemma distr_latticeD1:
  "\<lbrakk>distributive_lattice X; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow>  Sup X {x, Inf X {y, z}} = Inf X {Sup X {x, y}, Sup X {x, z}} "
  by (simp add: distributive_lattice_def insert_commute)

lemma distr_latticeD2:
  "\<lbrakk>distributive_lattice X; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow>  Sup X {Inf X {y, z}, x} = Inf X {Sup X {y, x}, Sup X {z, x}}"
  by (simp add: distributive_lattice_def insert_commute)
 
lemma distr_latticeD3:
  "\<lbrakk>distributive_lattice X; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow>  Inf X {x, Sup X {y, z}} = Sup X {Inf X {x, y}, Inf X {x, z}}"
  using distribD2 distributive_lattice_def by fastforce
 
lemma distr_latticeD4:
  "\<lbrakk>distributive_lattice X; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow>  Inf X {Sup X {y, z}, x} = Sup X {Inf X {y, x}, Inf X {z, x}}"
  by (simp add: distr_latticeD3 insert_commute)

lemma lattice_ne_inf_le_sup:
  "\<lbrakk>A \<noteq> {}; is_inf X A i; is_sup X A s\<rbrakk> \<Longrightarrow> i \<le> s"
  by (meson all_not_in_conv dual_order.trans is_infD1121 is_supD1121)

lemma lattice_in_inf_le_sup:
  "\<lbrakk>A \<inter> B \<noteq> {}; is_inf X A i; is_sup X B s\<rbrakk> \<Longrightarrow> i \<le> s"
  by (meson Int_emptyI is_infD1121 is_supD1121 order_trans)

lemma lattice_id0:
  "\<lbrakk>is_lattice X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Inf X {x, y} lb  {Sup X {x, y}, Sup X {y, z}, Sup X {x, z}}"
  by (simp add: lb_def binf_leI1 binf_leI2 bsup_geI1 lattD41 lattD42 ssupD4)

lemma lattice_id1:
  "\<lbrakk>is_lattice X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Inf X {y, z} lb  {Sup X {x, y}, Sup X {y, z}, Sup X {x, z}}"
  by(simp add:lb_def  binary_supD32 binf_leI1 binf_leI2 lattD32 latt_iff ssupD4)

lemma lattice_id2:
  "\<lbrakk>is_lattice X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Inf X {x, z} lb  {Sup X {x, y}, Sup X {y, z}, Sup X {x, z}}"
  using lattice_id0[of "X" "x" "z" "y"] by (simp add: insert_commute)


lemma lattice_id3:
  "\<lbrakk>is_lattice X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Sup X {x, y} ub {Inf X {x, y}, Inf X {y, z}, Inf X {x, z}}"
  by (simp add: ub_def binf_leI1 bsup_geI1 bsup_geI2 lattD41 lattD42 sinfD4)

lemma lattice_id4:
  "\<lbrakk>is_lattice X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Sup X {y, z} ub {Inf X {x, y}, Inf X {y, z}, Inf X {x, z}}"
  by (simp add: ub_def binf_leI2 bsup_geI1 bsup_geI2 latt_iff sinfD4)

lemma lattice_id5:
  "\<lbrakk>is_lattice X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Sup X {x, z} ub {Inf X {x, y}, Inf X {y, z}, Inf X {x, z}}"
  using lattice_id3[of X x z y] by (simp add: insert_commute)

lemma lattice_id6:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> X; is_sup X A s; is_inf X B i\<rbrakk> \<Longrightarrow> s \<le> i \<Longrightarrow> (\<forall>a \<in> A. \<forall>b \<in> B. a \<le> b) "
  using is_infD32 is_supD32 by blast

lemma lattice_id7:
  "\<lbrakk>A \<subseteq> Lower_Bounds X B; is_sup X A s; is_inf X B i\<rbrakk> \<Longrightarrow> s \<le> i "
  by (meson Lower_Bounds_sub is_infD1 is_sup_iso1 sup_max_eq)

lemma lattice_id8:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> X; is_sup X A s; is_inf X B i;(\<forall>a \<in> A. \<forall>b \<in> B. a \<le> b)\<rbrakk> \<Longrightarrow> s \<le> i"
  by (meson Lower_BoundsI in_mono lattice_id7 subsetI)

lemma lattice_id9:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> X; is_sup X A s; is_inf X B i;(\<forall>a \<in> A. a lb B)\<rbrakk> \<Longrightarrow> s \<le> i"
  by (meson lattice_id8 lbD)


lemma lattice_id10:
  assumes A0:"is_lattice X" and A1:" x \<in> X \<and> y \<in> X \<and> z \<in> X" 
  shows  "Sup X {Inf X {x, y}, Inf X {y, z}, Inf X {x, z}} \<le> Inf X {Sup X {x, y}, Sup X {y, z}, Sup X {x, z}}"
proof-
  let ?A="{Inf X {x, y}, Inf X {y, z}, Inf X {x, z}}"  let ?B="{Sup X {x, y}, Sup X {y, z}, Sup X {x, z}}"
  have B0:"\<forall>a \<in> ?A. a lb ?B" by (simp add: A0 A1 lattice_id0 lattice_id1 lattice_id2)
  have B1:"finite ?A \<and> ?A \<subseteq> X \<and> finite ?B \<and> ?B \<subseteq> X"
    by (metis A0 A1 empty_subsetI finite.emptyI finite_insert insert_subset latt_iff sinfD4 ssupD4)
  have B2:"is_sup X ?A (Sup X ?A) \<and> is_inf X ?B (Inf X ?B)"
    by (meson A0 B1 binf_finite2 bsup_finite2 insert_not_empty lattD41 lattD42)
  have B3:"Sup X ?A \<le> Inf X ?B"
    by (meson B0 B1 B2 lattice_id9)
  show ?thesis
    using B3 by force
qed

lemma distrib_I3:
  "\<lbrakk>distributive_lattice X ;x \<in> X; y \<in>X; z \<in> X; Inf X {x, z} = Inf X {y, z}; Sup X {x, z}=Sup X {y, z}\<rbrakk> \<Longrightarrow> x=y"
  by (metis distributive_lattice_def doubleton_eq_iff lattice_absorb1)

(*lemma distrib_D3:
  assumes A0:"is_lattice X" and
          A1:"(\<And>x y z. \<lbrakk>x \<in> X; y \<in>X; z \<in> X; Inf X {x, z} = Inf X {y, z}; Sup X {x, z}=Sup X {y, z}\<rbrakk> \<Longrightarrow> x=y)"
  shows "distributive_lattice X"
proof-
  have B0:"\<And>x y z. x \<in> X \<and>  y \<in> X \<and> z \<in> X \<longrightarrow> Sup X {x, Inf X {y, z}} = Inf X {Sup X {x, y}, Sup X {x, z}}"
  proof
    fix x y z assume A2:"x \<in> X \<and>  y \<in> X \<and> z \<in> X " 
    show "Sup X {x, Inf X {y, z}} = Inf X {Sup X {x, y}, Sup X {x, z}}"
*)  
  



unused_thms  

end

