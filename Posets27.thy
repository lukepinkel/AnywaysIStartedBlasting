theory Posets27
  imports Main
begin

section Settings
hide_const top bot
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


lemma leq_iff_leq_eq: 
  "\<lbrakk>(a::'a::order) \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> (\<forall>x \<in> X. x \<le> a \<longleftrightarrow> x \<le> b) \<Longrightarrow> a =b" 
  by (simp add: order_class.order_eq_iff)


definition Pow_ne::"'a set \<Rightarrow> 'a set set" where 
  "Pow_ne X = Pow X - {{}}"

definition Fpow_ne::"'a set \<Rightarrow> 'a set set" where
   "Fpow_ne X = Fpow X - {{}}"

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

lemma pow_ne_iso0: 
  "A \<in> Pow_ne X \<Longrightarrow> B \<in> Pow_ne A \<Longrightarrow> B \<subseteq> X"  
   by (drule pow_neD1)+ simp

lemma pow_ne_iso1:
  "A \<in> Pow_ne X \<Longrightarrow> B \<in> Pow_ne A \<Longrightarrow> B \<in> Pow_ne X"
  by(rule pow_neI,erule pow_ne_iso0,simp,erule pow_neD2)

lemma pow_ne_bot:
  "{} \<notin> Pow_ne X"
  by(simp add:Pow_ne_def)
               
lemma pow_ne_top: 
  "X \<noteq> {} \<Longrightarrow> X \<in> Pow_ne X" 
  by(simp add:Pow_ne_def)

lemma fpow_ne_iff1:
  "A \<in> Fpow_ne X \<longleftrightarrow> A \<in> Fpow X \<and> A \<noteq> {}"
  by (simp add: Fpow_ne_def)

lemma fpow_ne_iff2: 
  "A \<in> Fpow_ne X \<longleftrightarrow> A \<subseteq> X \<and> finite A \<and> A \<noteq> {}" 
  by (simp add: Fpow_Pow_finite fpow_ne_iff1)

lemma fpow_neI: 
  "A \<subseteq> X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> A \<in> Fpow_ne X" 
  by (simp add: Fpow_def fpow_ne_iff1)

lemma fpow_neD1: 
  "A \<in> Fpow_ne X \<Longrightarrow> A \<subseteq> X " 
  by (simp add: fpow_ne_iff2)

lemma fpow_neD3:
  "A \<in> Fpow_ne X \<Longrightarrow> finite A "
  by (simp add: fpow_ne_iff2)

lemma fpow_ne_iso2: 
  "A \<in> Pow_ne X \<Longrightarrow> B \<in> Fpow_ne A \<Longrightarrow> B \<in> Fpow_ne X" 
  by (metis dual_order.trans fpow_ne_iff2 pow_ne_iff2)


lemma ne_subset_ne:
  "A \<subseteq> B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> B \<noteq> {}"
  by blast

section Bounds
subsection UpperBoundsPredicate

definition ub::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> bool" (infix "ub" 50) where 
   "x ub  A \<equiv> (\<forall>a. a \<in> A \<longrightarrow> a \<le> x)"

lemma ub_iff1:
  "x ub A \<longleftrightarrow> (\<forall>a \<in> A. a \<le> x)"
  by(auto simp add:ub_def)

lemma ubI: 
  "(\<And>a. a \<in> A \<Longrightarrow> a \<le> x) \<Longrightarrow> x ub A" 
  by (simp add:ub_def)

lemma ubD:
   "\<lbrakk>x ub A;  a \<in> A\<rbrakk>  \<Longrightarrow> a \<le> x "
    by (simp add:ub_def)

lemma ubE:
  "x ub A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> x)"
  by (simp add: ubD)

lemma ub_ant2:
  "\<lbrakk>A \<subseteq> B; x ub B\<rbrakk> \<Longrightarrow> x ub A"
   by (simp add:ub_def subsetD)

lemma ub_iso1:
  "\<lbrakk>x \<le> y; x ub A\<rbrakk> \<Longrightarrow> y ub A" 
   by(intro ubI; drule ubD, simp+) 

lemma ub_empty:
  "x ub {}"
  by (simp add: ub_def)

lemma ub_singleton:
  "x ub {x}"
  by (simp add: ub_def)

lemma ub_singleton_simp:
  "x ub {y} \<longleftrightarrow> x \<ge> y"
  by (simp add: ub_def)

lemma ub_insert:
  "\<lbrakk>c ub F; c \<ge> x\<rbrakk> \<Longrightarrow> c ub (insert x F)"
  by (simp add: ub_def)

lemma ub_doubleE1:
  "c ub {a, b} \<Longrightarrow> a \<le> c"
  by (simp add: ubD)

lemma ub_doubleE2:
  "c ub {a, b} \<Longrightarrow> b \<le> c"
  by (simp add: ubD)

lemma ub_doubleI:
  "\<lbrakk>a \<le> c; b \<le> c\<rbrakk> \<Longrightarrow> c ub {a, b}"
  by (simp add: ub_empty ub_insert)

lemma ub_double_iff1:
  "c ub {a, b} \<longleftrightarrow> c \<ge> a \<and> c \<ge> b"
  by(auto, erule ub_doubleE1, erule ub_doubleE2, erule ub_doubleI, simp)

lemma ub_unionI:
  "\<lbrakk>x ub A; x ub B\<rbrakk> \<Longrightarrow> x ub A \<union> B"
  by (simp add: ub_def)

lemma ub_unionD1:
  "x ub A \<union> B \<Longrightarrow> x ub A"
  by (simp add: ub_def)

lemma ub_unionD2:
  "x ub A \<union> B \<Longrightarrow> x ub B"
  by (simp add: ub_def)

lemma ub_unI:
  "(\<And>A. A \<in> S \<Longrightarrow> x ub A) \<Longrightarrow> x ub (\<Union>S)"
  by (simp add: ub_iff1)

lemma ub_unD:
  "x ub (\<Union>S) \<Longrightarrow> A \<in> S \<Longrightarrow> x ub A"
 using ub_ant2[of A "\<Union>S" x] by blast

lemma ub_imageI:
  "(\<And>a. a \<in> A \<Longrightarrow> x \<ge> f a) \<Longrightarrow> x ub (f`A)"
  by(simp add:ub_def image_p[of "A" "\<lambda>a. x \<ge> a" "f"])


subsection UpperBoundsSet

definition ubd::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "ubd X A \<equiv> {b \<in> X. b ub A}"

lemma ubdI:
  "\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> a \<le> b); b \<in> X\<rbrakk> \<Longrightarrow> b \<in> ubd X A"
   by(simp add: ubd_def ubI)

lemma ubdI2:
  "\<lbrakk>b ub A; b \<in> X\<rbrakk> \<Longrightarrow> b \<in> ubd X A"
  by (simp add: ubdI ub_def) 

lemma ubdD1:
  "\<lbrakk>b \<in> ubd X A; x \<in> A\<rbrakk> \<Longrightarrow> x \<le> b"
  by (simp add: ubd_def ub_def)

lemma ubdD2:
  "b \<in> ubd X A \<Longrightarrow> b \<in> X"
  by (simp add: ubd_def)

lemma ubdD3:
  "b \<in> ubd X A \<Longrightarrow> b ub A"
  by (simp add: ubd_def)

lemma ubd_mem_iff:
  "b \<in> ubd X A \<longleftrightarrow> (b \<in> X \<and> b ub A)" 
   by(simp add: ubd_def)

lemma ubd_mem_iff2:
  "b \<in> ubd X A \<longleftrightarrow> (b \<in> X \<and> (\<forall>a. a \<in> A \<longrightarrow>  a \<le> b))"
  by (simp add: ubd_mem_iff ub_def)

lemma ubd_mem_iff3:
  "b \<in> ubd X A \<longleftrightarrow> (b \<in> X \<and> (\<forall>a \<in> A. a \<le> b))"
  by (simp add: ubd_mem_iff ub_iff1)

lemma ubd_sub:
  "ubd X A \<subseteq> X"
   by(simp add: ubd_def)

lemma ubd_ant1:
  "A \<subseteq> B \<Longrightarrow> ubd X B \<subseteq> ubd X A"
  by (simp add: ubd_mem_iff subset_iff ub_ant2) 

lemma ubd_ant1b:
  "\<lbrakk>A \<subseteq> B; b \<in> ubd X B\<rbrakk> \<Longrightarrow> b \<in> ubd X A"
  using ubd_ant1 by blast

lemma ubd_iso2:
  "Y \<subseteq> X \<Longrightarrow> ubd Y A \<subseteq> ubd X A" 
  by (simp add:subset_iff ubd_def)

lemma ubd_iso2b:
  "\<lbrakk>Y \<subseteq> X; x \<in> ubd Y A \<rbrakk> \<Longrightarrow> x \<in> ubd X A"
  by (simp add: ubd_mem_iff in_mono)

lemma ubd_empty:
  "ubd X {} = X"
   by(simp add: set_eq_iff ubd_mem_iff ub_def)

lemma ubd_singleton:
  "x \<in> X \<Longrightarrow> x \<in> ubd X {x}"
  by (simp add: ubd_def ub_singleton)

lemma ubd_singleton2:
  "\<lbrakk>x \<in> X; y \<le> x \<rbrakk> \<Longrightarrow>  x \<in> ubd X {y}"
  by (simp add: ubd_mem_iff ub_iso1 ub_singleton)

lemma ubd_singleton_iff:
  "x \<in> ubd X {y} \<longleftrightarrow> (x \<in> X \<and> x \<ge> y)"
  by (simp add: ubd_mem_iff ub_singleton_simp)

lemma ubd_mem_insert:
  "\<lbrakk>c \<in> ubd X F; c \<ge> x\<rbrakk> \<Longrightarrow> c \<in> ubd X (insert x F)"
  by (simp add: ubd_mem_iff ub_insert)

lemma ubd_mem_doubleE1:
  "c \<in> ubd X {a, b} \<Longrightarrow> a \<le> c"
  by (simp add: ubdD1)

lemma ubd_mem_doubleE2:
  "c \<in> ubd X {a, b} \<Longrightarrow> b \<le> c"
  by (simp add: ubdD1)

lemma ubd_mem_doubleI:
  "\<lbrakk>a \<le> c; b \<le> c; c \<in> X\<rbrakk> \<Longrightarrow> c \<in> ubd X {a, b}"
  by (simp add: ubd_empty ubd_mem_insert)

lemma ubd_mem_singleE:
  "x \<in> ubd X {a}\<Longrightarrow> a \<le> x"
  by (simp add: ubdD1)

lemma ubd_mem_double:
  "c \<in> X \<Longrightarrow> c \<in> ubd X {a, b} \<longleftrightarrow> c \<ge> a \<and> c \<ge> b"
  by (simp add: ubd_mem_iff ub_double_iff1)

lemma upbd_neE1:
  "ubd X A \<noteq> {} \<Longrightarrow> a \<in> A \<Longrightarrow> (\<exists>x. x \<in> X \<and> a \<le> x)"
  using ubdD1 ubd_sub by blast

lemma upbd_neE3:
  "ubd X {a} \<noteq> {} \<Longrightarrow> (\<exists>x \<in> X. a \<le> x)"
  using upbd_neE1 by auto

lemma ubd_mem_unionI:
  "\<lbrakk>x \<in> ubd X A; x \<in> ubd X B\<rbrakk> \<Longrightarrow> x \<in> ubd X (A \<union> B)"
  by (simp add: ubd_mem_iff ub_unionI)

lemma ubd_eqI1:
  "(\<And>x. x \<in> X \<Longrightarrow> x ub A \<Longrightarrow> x ub B) \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x ub B \<Longrightarrow> x ub A) \<Longrightarrow> ubd X A = ubd X B"
  by(auto simp add:set_eq_iff ubd_mem_iff)

subsection LowerBoundsPredicate

definition lb::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> bool" (infix "lb" 50) where 
   "x lb  A \<equiv> (\<forall>a. a \<in> A \<longrightarrow> a \<ge> x)"

lemma lb_iff1:
  "x lb A \<longleftrightarrow> (\<forall>a \<in> A. a \<ge> x)"
  by(auto simp add:lb_def)

lemma lbI:
  "(\<And>a. a \<in> A \<Longrightarrow> a \<ge> x) \<Longrightarrow> x lb A" 
  by (simp add: lb_def)

lemma lbD:
  "\<lbrakk>x lb A; a \<in> A\<rbrakk> \<Longrightarrow> a \<ge> x"
  by (simp add: lb_def)

lemma lbE:
  "x lb A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<ge> x)"
  by (simp add: lbD)

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


lemma lb_singletonD:
  "x \<le> y \<Longrightarrow> x lb {y}"
  by (simp add: lb_iso1 lb_singleton)

lemma lb_insert:
  "\<lbrakk>c lb F; c \<le> x\<rbrakk> \<Longrightarrow> c lb (insert x F)"
  by (simp add: lb_def)

lemma lb_binaryI:
  "a \<ge> b \<Longrightarrow> b lb {a, b}"
  by (simp add: lb_insert lb_singleton)


lemma lb_doubleE1:
  "c lb {a, b} \<Longrightarrow> a \<ge> c"
  by (simp add: lbD)

lemma lb_doubleE2:
  "c lb {a, b} \<Longrightarrow> b \<ge> c"
  by (simp add: lbD)

lemma lb_doubleI:
  "\<lbrakk>a \<ge> c; b \<ge> c\<rbrakk> \<Longrightarrow> c lb {a, b}"
  by (simp add: lb_empty lb_insert)

lemma lb_double_iff1:
  "c lb {a, b} \<longleftrightarrow> c \<le> a \<and> c \<le> b"
  using lb_doubleE1 lb_doubleE2 lb_doubleI by blast

lemma lb_unionI:
  "\<lbrakk>x lb A; x lb B\<rbrakk> \<Longrightarrow> x lb A \<union> B"
  by (simp add: lb_def)

lemma lb_unionD1:
  "x lb A \<union> B \<Longrightarrow> x lb A"
  by (simp add: lb_def)

lemma lb_unionD2:
  "x lb A \<union> B \<Longrightarrow> x lb B"
  by (simp add: lb_def)

lemma lb_unI:
  "(\<And>A. A \<in> S \<Longrightarrow> x lb A) \<Longrightarrow> x lb (\<Union>S)"
  by (simp add: lb_iff1)

lemma lb_unD:
  "x lb (\<Union>S) \<Longrightarrow> A \<in> S \<Longrightarrow> x lb A"
 using lb_ant2[of A "\<Union>S" x] by blast

lemma lb_singleton_simp:
  "x lb {y} \<longleftrightarrow> x \<le> y"
  by (simp add: lb_def)

lemma lb_imageI:
  "(\<And>a. a \<in> A \<Longrightarrow> x \<le> f a) \<Longrightarrow> x lb (f`A)"
  by(simp add:lb_def image_p[of "A" "\<lambda>a. x \<le> a" "f"])


subsection LowerBoundsSet
definition lbd::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "lbd X A \<equiv> {b \<in> X. b lb A}"

lemma lbdI:
  "\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> a \<ge> b); b \<in> X\<rbrakk> \<Longrightarrow> b \<in> lbd X A"
   by(simp add: lbd_def lbI)

lemma lbdI2:
  "\<lbrakk>b lb A; b \<in> X\<rbrakk> \<Longrightarrow> b \<in> lbd X A"
  by (simp add: lbdI lb_def) 

lemma lbdD1:
  "\<lbrakk>b \<in> lbd X A; x \<in> A\<rbrakk> \<Longrightarrow> x \<ge> b"
  by (simp add: lbd_def lb_def)

lemma lbdD2:
  "b \<in> lbd X A \<Longrightarrow> b \<in> X"
  by (simp add: lbd_def)

lemma lbdD3:
  "b \<in> lbd X A \<Longrightarrow> b lb A"
  by (simp add: lbd_def)



lemma lbd_mem_iff:
  "b \<in> lbd X A \<longleftrightarrow> (b \<in> X \<and> b lb A)" 
   by(simp add: lbd_def)

lemma lbd_mem_iff2:
  "b \<in> lbd X A \<longleftrightarrow> (b \<in> X \<and> (\<forall>a. a \<in> A \<longrightarrow>  a \<ge> b))"
  by (simp add: lbd_mem_iff lb_def)

lemma lbd_mem_iff3:
  "b \<in> lbd X A \<longleftrightarrow> (b \<in> X \<and> (\<forall>a \<in> A. a \<ge> b))"
  by (simp add: lbd_mem_iff lb_iff1)

lemma lbd_sub:
  "lbd X A \<subseteq> X"
   by(simp add: lbd_def)

lemma lbd_ant1:
  "A \<subseteq> B \<Longrightarrow> lbd X B \<subseteq> lbd X A"
  by (simp add: lbd_mem_iff lb_ant2 subset_iff) 

lemma lbd_ant1b:
  "\<lbrakk>A \<subseteq> B; b \<in> lbd X B\<rbrakk> \<Longrightarrow> b \<in> lbd X A"
  using lbd_ant1 by blast

lemma lbd_iso2:
  "Y \<subseteq> X \<Longrightarrow> lbd Y A \<subseteq> lbd X A" 
  by (simp add:subset_iff lbd_def)

lemma lbd_iso2b:
  "\<lbrakk>Y \<subseteq> X; x \<in> lbd Y A \<rbrakk> \<Longrightarrow> x \<in> lbd X A"
  by (simp add: lbd_mem_iff in_mono)


lemma lbd_empty:
  "lbd X {} = X"
   by(simp add: set_eq_iff lbd_mem_iff lb_def)

lemma lbd_singleton_iff:
  "x \<in> lbd X {y} \<longleftrightarrow> (x \<in> X \<and> x \<le> y)"
  by (simp add: lbd_mem_iff lb_singleton_simp)

lemma lbd_mem_insert:
  "\<lbrakk>c \<in> lbd X F; c \<le> x\<rbrakk> \<Longrightarrow> c \<in> lbd X (insert x F)"
  by (simp add: lbd_mem_iff lb_insert)

lemma lbd_mem_doubleE1:
  "c \<in> lbd X {a, b} \<Longrightarrow> a \<ge> c"
  by (simp add: lbdD1)

lemma lbd_mem_doubleE2:
  "c \<in> lbd X {a, b} \<Longrightarrow> b \<ge> c"
  by (simp add: lbdD1)


lemma lbd_mem_double:
  "c \<in> X \<Longrightarrow> c \<in> lbd X {a, b} \<longleftrightarrow> c \<le> a \<and> c \<le> b"
  by (simp add: lbd_mem_iff lb_double_iff1)

lemma lpbd_neE1:
  "lbd X A \<noteq> {} \<Longrightarrow> a \<in> A \<Longrightarrow> (\<exists>x. x \<in> X \<and> a \<ge> x)"
  using lbdD1 lbd_sub by blast

lemma lpbd_neE3:
  "lbd X {a} \<noteq> {} \<Longrightarrow> (\<exists>x \<in> X. a \<ge> x)"
  using lpbd_neE1 by auto

lemma lbd_eqI1:
  "(\<And>x. x \<in> X \<Longrightarrow> x lb A \<Longrightarrow> x lb B) \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x lb B \<Longrightarrow> x lb A) \<Longrightarrow> lbd X A = lbd X B"
  by(auto simp add:set_eq_iff lbd_mem_iff)

subsection Composition

lemma lubd_comp1:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> lbd X (ubd X A)"
  by (simp add: lbdI ubdD1 subset_iff) 

lemma lubd_comp1b:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> ((\<lambda>E. lbd X E) \<circ> (\<lambda>E. ubd X E)) A"
  by (simp add: lbdI ubdD1 subset_iff) 

lemma ulbd_comp1:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> ubd X (lbd X A)"
  by (simp add: lbdD1 ubdI subset_iff)

lemma ulbd_comp1b:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> ((\<lambda>E. ubd X E) \<circ> (\<lambda>E. lbd X E)) A"
  by (simp add: ubdI lbdD1 subset_iff) 

lemma lubd_comp2:
  "A \<subseteq> B \<Longrightarrow> lbd X (ubd X A) \<subseteq> lbd X (ubd X B)"
  by (simp add: lbd_ant1 ubd_ant1)

lemma lubd_comp2b:
  "A \<subseteq> B \<Longrightarrow> ((\<lambda>E. lbd X E) \<circ> (\<lambda>E. ubd X E)) A  \<subseteq> ((\<lambda>E. lbd X E) \<circ> (\<lambda>E. ubd X E)) B"
  by (simp add: lbd_ant1 ubd_ant1)

lemma ulbd_comp2:
  "A \<subseteq> B  \<Longrightarrow> ubd X (lbd X A) \<subseteq> ubd X (lbd X B)"
  by (simp add: lbd_ant1 ubd_ant1)

lemma ulbd_comp2b:
  "A \<subseteq> B \<Longrightarrow> ((\<lambda>E. ubd X E) \<circ> (\<lambda>E. lbd X E)) A  \<subseteq> ((\<lambda>E. ubd X E) \<circ> (\<lambda>E. lbd X E)) B"
  by (simp add: lbd_ant1 ubd_ant1)

lemma lubd_comp3:
  "lbd X (ubd X A) = lbd X (ubd X (lbd X (ubd X A)))"
  by (simp add: lbd_ant1 lbd_sub lubd_comp1 subset_antisym ubd_sub ulbd_comp1)

lemma lubd_comp3b:
  " ((\<lambda>E. lbd X E) \<circ> (\<lambda>E. ubd X E)) A  = ((\<lambda>E. lbd X E) \<circ> (\<lambda>E. ubd X E) \<circ> (\<lambda>E. lbd X E) \<circ> (\<lambda>E. ubd X E)) A"
  by (simp add: lbd_ant1 lbd_sub lubd_comp1 subset_antisym ubd_sub ulbd_comp1)

lemma ulbd_comp3:
  "ubd X (lbd X A) = ubd X (lbd X (ubd X (lbd X A)))"
  by (simp add: lbd_sub lubd_comp1 subset_antisym ubd_ant1 ubd_sub ulbd_comp1)

lemma ulbd_comp3b:
  "((\<lambda>E. ubd X E) \<circ> (\<lambda>E. lbd X E)) A  = ((\<lambda>E. ubd X E) \<circ> (\<lambda>E. lbd X E) \<circ> (\<lambda>E. ubd X E) \<circ> (\<lambda>E. lbd X E)) A"
  by (simp add: ubd_ant1 lbd_sub ulbd_comp1 subset_antisym ubd_sub lubd_comp1)


section AbsoluteExtrema
subsection GreatestPredicate
definition is_greatest::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "is_greatest A m \<equiv> m \<in> ubd A A"


lemma greatestI2:
  "\<lbrakk>m ub A; m \<in> A\<rbrakk> \<Longrightarrow> is_greatest A m"
  by (simp add: ubd_mem_iff is_greatest_def)

lemma greatestI3:
  "\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> a \<le> m); m \<in> A\<rbrakk> \<Longrightarrow> is_greatest A m"
  by (simp add: ubI greatestI2)

lemma greatestD1:
  "is_greatest A m \<Longrightarrow> (m \<in> A \<and> m ub A)"
  by (simp add: ubd_mem_iff is_greatest_def)

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
  by (simp add: ubd_mem_iff is_greatest_def ub_def)

lemma greatest_unique:
  "is_greatest A m1 \<Longrightarrow> is_greatest A m2 \<Longrightarrow> m1 =m2"
  by (simp add: greatest_iff order_antisym)

lemma greatest_singleton:
  "is_greatest {x} x"
  by (simp add: greatestI2 ub_singleton)

lemma greatest_insert1:
  "x ub A \<Longrightarrow> is_greatest (insert x A) x"
  by (simp add: greatestI2 ub_insert)

lemma greatest_insert2:
  "is_greatest A m \<Longrightarrow> x \<le> m \<Longrightarrow> is_greatest (insert x A) m"
  by (simp add: greatestD11 greatestI2 greatestD12 ub_insert)

lemma greatest_insert3:
  "is_greatest A m \<Longrightarrow> m \<le> x \<Longrightarrow> is_greatest (insert x A) x"
  by (simp add: greatest_insert1 greatestD12 ub_iso1)

subsection GreatestOperator

definition Greatest::"'a::order set \<Rightarrow> 'a::order" where
  "Greatest A \<equiv> (THE m. is_greatest A m)"

lemma greatest_equality:
  "\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> a \<le> m); m \<in> A\<rbrakk> \<Longrightarrow> Greatest A = m"
  by (simp add: Greatest_def greatestI3 greatest_unique the_equality) 

lemma greatest_equality2:
  "is_greatest A m \<Longrightarrow> Greatest A = m"
  by (simp add: greatest_equality greatest_iff)


subsection LeastPredicate

definition is_least::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "is_least A m \<equiv> m \<in> lbd A A"

lemma leastI1:
  "m \<in> lbd A A \<Longrightarrow> is_least A m" 
  by (simp add: is_least_def)

lemma leastI2:
  "\<lbrakk>m lb A; m \<in> A\<rbrakk> \<Longrightarrow> is_least A m"
  by (simp add: lbd_mem_iff is_least_def)

lemma leastI3:
  "\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> m \<le> a); m \<in> A\<rbrakk> \<Longrightarrow> is_least A m"
  by (simp add: lbI leastI2)

lemma leastD1:
  "is_least A m \<Longrightarrow> (m \<in> A \<and> m lb A)"
  by (simp add: lbd_mem_iff is_least_def)

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
  by (simp add: lbd_mem_iff is_least_def lb_def)

lemma least_unique:
  "is_least A m1 \<Longrightarrow> is_least A m2 \<Longrightarrow> m1 =m2"
  by (simp add: least_iff order_antisym)

lemma is_least_iso2:
  "A \<subseteq> B \<Longrightarrow> is_least A ma \<Longrightarrow> is_least B mb \<Longrightarrow> ma \<ge> mb"
  using leastD11 leastD2 by blast

lemma least_singleton:
  "is_least {x} x"
  by (simp add: lb_singleton leastI2)

lemma least_insert1:
  "x lb A \<Longrightarrow> is_least (insert x A) x"
  by (simp add: leastI2 lb_insert)

lemma least_insert2:
  "is_least A m \<Longrightarrow> m \<le> x \<Longrightarrow> is_least (insert x A) m"
  by (simp add: leastD11 leastI2 leastD12 lb_insert)

lemma least_insert3:
  "is_least A m \<Longrightarrow> x \<le> m \<Longrightarrow> is_least (insert x A) x"
  by (simp add: lb_iso1 leastD1 least_insert1)

subsection LeastOperator

definition Least::"'a::order set \<Rightarrow> 'a::order" where
  "Least A \<equiv> (THE m. is_least A m)"

lemma least_equality2:
  "is_least A m \<Longrightarrow> Least A = m"
  by (simp add: Least_def least_unique the_equality) 

lemma ub_single_least1:
  "x \<in> X \<Longrightarrow> is_least (ubd X {x}) x"
  by (simp add: ubdD1 ubd_singleton least_iff)

lemma ub_single_least2:
  "x \<in> X \<Longrightarrow> Least (ubd X {x}) = x"
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
  "is_sup X A x \<equiv> (is_least (ubd X A) x)"

lemma is_supI1:
  "is_least (ubd X A) x \<Longrightarrow> is_sup X A x"
  by (simp add: is_sup_def) 

lemma is_supD1:
  "is_sup X A x \<Longrightarrow> (is_least (ubd X A) x)"
  by (simp add: is_sup_def)


lemma is_supD32:
  "is_sup X A x \<Longrightarrow> x \<in>  (ubd X A)"
  by (simp add: is_supD1 leastD1)

lemma is_supI4:
  "\<lbrakk>x lb (ubd X A); x \<in> X; x ub A\<rbrakk> \<Longrightarrow> is_sup X A x"
  by (simp add: ubd_mem_iff leastI2 is_supI1)

lemma is_supE1:
  "is_sup X A x \<Longrightarrow> x \<in> X" 
  by (simp add:is_supD32[of "X" "A" "x"] ubdD2[of "x" "X" "A"])

lemma is_supI5:
  "\<lbrakk>(\<And>a. a \<in> (ubd X A) \<Longrightarrow> x \<le> a); x \<in> (ubd X A)\<rbrakk> \<Longrightarrow> is_sup X A x"
  by (simp add: is_supI1 leastI3)

lemma is_supI6:
  "\<lbrakk>x \<in> X; x ub A; (\<And>a. a \<in> (ubd X A) \<Longrightarrow> x \<le> a)\<rbrakk> \<Longrightarrow> is_sup X A x"
  by (simp add: is_supI5 ubdI2)

lemma is_supI7:
  "\<lbrakk>x \<in> X; x ub A; (\<And>a. a \<in> X \<Longrightarrow> a ub A \<Longrightarrow>  x \<le> a)\<rbrakk> \<Longrightarrow> is_sup X A x"
  by (simp add: is_supI4 lb_def ubd_mem_iff)

lemma is_supI9:
  "\<lbrakk>x \<in> X; (\<forall>z \<in> X. (z \<ge> x) \<longleftrightarrow> (z ub A))\<rbrakk> \<Longrightarrow> is_sup X A x"
  using is_supI7 by blast

lemma is_supE2:
  "is_sup X A x \<Longrightarrow> x ub A" 
  by(simp add: ubdD3[of "x" "X" "A"] is_supD32[of "X" "A" "x"])            

lemma is_supE3:
  "\<lbrakk> is_sup X A x; y \<in> ubd X A\<rbrakk> \<Longrightarrow> x \<le> y "
  by (simp add: is_sup_def leastD2)
                     
lemma is_supE4:
  "\<lbrakk>is_sup X A x; y \<in> X; y ub A\<rbrakk> \<Longrightarrow> x \<le> y "
  by (simp add: ubd_mem_iff is_supE3)
        
lemma is_supE5:
  "\<lbrakk>is_sup X A x; z \<in> X;  x \<le> z\<rbrakk> \<Longrightarrow> z \<in> ubd X A"
  by (simp add: is_supE2 ub_iso1 ubdI2)

lemma is_supD1121:
  "\<lbrakk>is_sup X A x; a \<in> A \<rbrakk> \<Longrightarrow> a \<le> x"
  using is_supE2 ubE by blast

lemma is_supE6:
  "\<lbrakk>is_sup X A x;  x \<le> z\<rbrakk> \<Longrightarrow> z ub A"
  by (simp add: is_supE2 ub_iso1)

lemma is_supE7:
  "\<lbrakk>is_sup X A x;  x \<le> z; a \<in> A\<rbrakk> \<Longrightarrow> a \<le> z"
  by (simp add: is_supE6[of "X" "A" "x" "z"] ubD[of "z" "A" "a"])

lemma is_supD41:
  "is_sup X A x \<Longrightarrow> (\<And>z. z \<in> X \<Longrightarrow> z \<ge> x \<Longrightarrow> z ub A)"
  by (simp add: is_supE6)

lemma is_supD42:
  "is_sup X A x \<Longrightarrow> (\<And>z. z \<in> X \<Longrightarrow>  z ub A \<Longrightarrow> z \<ge> x)"
  by (simp add: is_supE4)

lemma is_supD5:
  "is_sup X A x \<Longrightarrow> (\<forall>z \<in> X. (z \<ge> x) \<longleftrightarrow> (z ub A))"
  using is_supE4 is_supE6 by blast
   
lemma sup_iff2:
  "is_sup X A s \<longleftrightarrow>  s \<in> X \<and> (\<forall>z \<in> X.  s \<le> z \<longleftrightarrow> z \<in> ubd X A)"
  by (meson dual_order.refl is_supE1 is_supE3 is_supE5 is_supI5 ubdD2)

lemma is_sup_unique:
  "is_sup X A m1 \<Longrightarrow> is_sup X A m2 \<Longrightarrow> m1 = m2"
  using is_supD1 least_unique by blast

lemma is_sup_iso1:
  "A \<subseteq> B \<Longrightarrow> is_sup X A ma \<Longrightarrow> is_sup X B mb \<Longrightarrow> ma \<le> mb "
  by (simp add: is_supE1 is_supE2 is_supE4 ub_ant2)

lemma sup_maxI1:
  "is_sup X A x \<Longrightarrow> x \<in> A \<Longrightarrow> (is_greatest A x)"
  by (simp add: greatestI2 is_supE2)

lemma sup_maxE1:
  "(is_greatest A x) \<Longrightarrow> x \<in> X \<Longrightarrow> is_sup X A x"
  by (simp add: greatestD11 greatestD12 is_supI6 ubdD1)

lemma sup_maxE2:
  "(is_greatest A x) \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_sup X A x"
  using greatestD11 sup_maxE1 by blast

lemma sup_max_eq2:
  "(is_sup A A x) \<longleftrightarrow> (is_greatest A x)"
  using greatestD11 is_supE1 sup_maxE1 sup_maxI1 by blast

lemma sup_in_subset:
  "A \<subseteq> B \<Longrightarrow>  B \<subseteq> X \<Longrightarrow> is_sup X A s \<Longrightarrow> s \<in> B \<Longrightarrow> is_sup B A s"
  by(simp add:in_mono sup_iff2 ubd_mem_iff)

lemma sup_singleton:
  "s \<in> X \<Longrightarrow> is_sup X {s} s"
  by (simp add: is_supI1 ub_single_least1)



lemma binary_supI1:
  "\<lbrakk>a \<in> X; b \<in> X; a \<le> b\<rbrakk> \<Longrightarrow> is_sup X {a, b} b"
  by (simp add: greatest_insert2 greatest_singleton sup_maxE1)

lemma binary_supI2:
  "\<lbrakk>a \<in> X; b \<in> X; b \<le> a\<rbrakk> \<Longrightarrow> is_sup X {a, b} a"
  by (simp add: greatest_insert1 sup_maxE1 ub_singleton_simp)

lemma binary_supD21:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X;s \<in> X;is_sup X {a, b} s; c \<le> a\<rbrakk> \<Longrightarrow>  c \<le> s"
  using is_supD1121 by fastforce

lemma binary_supD22:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X;s \<in> X;is_sup X {a, b} s; c \<le> b\<rbrakk> \<Longrightarrow>  c \<le> s"
  by (simp add: binary_supD21 insert_commute)

lemma binary_supD31:
  "\<lbrakk>a \<in> X; b \<in> X; s \<in> X; is_sup X {a, b} s\<rbrakk>  \<Longrightarrow>  a \<le> s"
  by (simp add: is_supD1121)

lemma binary_supD32:
  "\<lbrakk>a \<in> X; b \<in> X; s \<in> X; is_sup X {a, b} s\<rbrakk>  \<Longrightarrow>  b \<le> s"
  by (simp add: is_supD1121)

lemma binary_supD4:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X; s \<in> X; is_sup X {a, b} s\<rbrakk>  \<Longrightarrow> (s \<le> c \<longleftrightarrow> a \<le> c \<and> b \<le> c)"
  by (simp add: sup_iff2 ubd_mem_double)

lemma sup_insert1:
  "\<lbrakk>x ub A; x \<in> X\<rbrakk> \<Longrightarrow> is_sup X (insert x A) x"
  by (simp add: greatest_insert1 sup_maxE1)

lemma sup_insert61:
  "\<lbrakk>is_sup X A s1; is_sup X {s1, x} s2\<rbrakk> \<Longrightarrow> s2 ub A"
  by (simp add: is_supD1121 is_supE6)

lemma sup_insert62:
  "\<lbrakk>is_sup X A s1; is_sup X {s1, x} s2\<rbrakk> \<Longrightarrow> s2 \<in> ubd X A"
  by (simp add: is_supE1 sup_insert61 ubd_mem_iff)

lemma sup_insert7:
  "\<lbrakk>is_sup X A s1; is_sup X {s1, x} s2; u \<in> ubd X (insert x A)\<rbrakk> \<Longrightarrow>  s2 \<le> u"
  by (simp add: ubd_mem_iff2 is_supE3)

lemma ub_eq_sup_eq:
  "(\<And>x. x ub A \<longleftrightarrow> x ub B) \<Longrightarrow> (is_sup X A s \<longleftrightarrow> is_sup X B s)"
  by (simp add: ubd_mem_iff sup_iff2)

lemma Upper_eq_sup_eq:
  "ubd X A = ubd X B \<Longrightarrow> (is_sup X A s \<longleftrightarrow> is_sup X B s)"
  by (simp add: is_sup_def)

definition Sup::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order" where
  "Sup X A \<equiv> (THE m. is_sup X A m)"

lemma sup_equality:
  "is_sup X A m \<Longrightarrow> Sup X A = m"
  by (simp add: Sup_def is_sup_unique the_equality) 

lemma sup_exI:
  "\<exists>s. is_sup X A s \<Longrightarrow> (\<And>s. is_sup X A s \<Longrightarrow> P s) \<Longrightarrow> P (Sup X A)"
  using sup_equality by auto

lemma sup_unc:
  "\<lbrakk>is_sup X (A \<union> B) s; is_sup X A s1; is_sup X B s2; is_sup X {s1, s2} s3\<rbrakk> \<Longrightarrow> s=s3"
  by (metis binary_supD4 is_supD42 is_supE6 order_class.order_eq_iff sup_iff2 ub_unionD1 ub_unionD2 ub_unionI)

lemma sup_families1:
  "A \<noteq> {} \<Longrightarrow> (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_sup X Ai si) \<Longrightarrow> x \<in> X \<Longrightarrow> x ub Sup X ` A \<Longrightarrow> x ub \<Union> A"
  by (metis imageI is_supD5 sup_equality ub_def ub_unI)

lemma sup_families2:
  "A \<noteq> {} \<Longrightarrow> (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_sup X Ai si) \<Longrightarrow> x \<in> X \<Longrightarrow> x ub \<Union> A \<Longrightarrow>  x ub Sup X ` A"
  by (metis is_supD5 sup_equality ub_imageI ub_unD)

lemma sup_families:
  "A \<noteq> {} \<Longrightarrow>(\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_sup X Ai si) \<Longrightarrow>(is_sup X ((\<lambda>Ai. Sup X Ai)`A) s) \<longleftrightarrow> (is_sup X (\<Union>A) s)"
  apply(rule Upper_eq_sup_eq, rule ubd_eqI1)  using sup_families1 apply blast using sup_families2 by blast


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
    using B0 is_supE1 by blast
  obtain s2 where B2:"is_sup X {s1, x} s2"
    using A0 B1 insert.prems by auto
  have B3:"s2 \<in> ubd X (insert x F)"
    by (meson B0 B2 insertI2 is_supD1121 singleton_iff sup_insert62 ubd_mem_insert)
  have B4:"\<And>u. u \<in> ubd X (insert x F) \<longrightarrow> s2 \<le> u"
    using B0 B2 sup_insert7 by blast
  have B3:"is_sup X (insert x F) s2"
    by (simp add: B3 B4 is_supI5)
  then show ?case
    by (simp add: sup_equality)
qed


lemma bsup_commute2:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> Sup X {a, b} =  Sup X  {b, a}"
  by (simp add: insert_commute)

lemma bsup_idem1:
  "a\<in> X \<Longrightarrow> Sup X {a, a} = a"
  by (simp add: sup_equality sup_singleton)


lemma sup_singleton2:
  "a \<in> X \<Longrightarrow> Sup X {a} = a"
  using bsup_idem1 by auto

lemma ge_sup1:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> a \<le> b \<Longrightarrow>  Sup X {a, b} = b"
  by (simp add: binary_supI1 sup_equality)

lemma ge_sup2:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> b \<le> a \<Longrightarrow> Sup X {a, b} = a"
  by (simp add: binary_supI2 sup_equality)

lemma sup_upper_bounds:
  "is_sup X A s \<Longrightarrow> ubd X {s} = ubd X A"
  by(auto simp add:ubd_mem_iff; simp add: is_supD41 ub_singleton_simp;simp add: is_supE4 ub_singleton)

subsection Infima

definition is_inf::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "is_inf X A x \<equiv> (is_greatest (lbd X A) x)"

lemma is_infI1:
  "is_greatest (lbd X A) x \<Longrightarrow> is_inf X A x"
  by (simp add: is_inf_def) 

lemma is_infD1:
  "is_inf X A x \<Longrightarrow> (is_greatest (lbd X A) x)"
  by (simp add: is_inf_def)

lemma is_infD32:
  "is_inf X A x \<Longrightarrow> x \<in> (lbd X A)"
  by (simp add: is_infD1 greatestD1)

lemma is_infI4:
  "\<lbrakk>x ub (lbd X A); x \<in> X; x lb A\<rbrakk> \<Longrightarrow> is_inf X A x"
  by (simp add: lbd_mem_iff greatestI2 is_infI1)

lemma is_infE1:
  "is_inf X A x \<Longrightarrow> x \<in> X" 
  by (simp add:is_infD32[of "X" "A" "x"] lbdD2[of "x" "X" "A"])

lemma is_infI5:
  "\<lbrakk>(\<And>a. a \<in> (lbd X A) \<Longrightarrow> x \<ge> a); x \<in> (lbd X A)\<rbrakk> \<Longrightarrow> is_inf X A x"
  by (simp add: is_infI1 greatestI3)

lemma is_infI6:
  "\<lbrakk>x \<in> X; x lb A; (\<And>a. a \<in> (lbd X A) \<Longrightarrow> x \<ge> a)\<rbrakk> \<Longrightarrow> is_inf X A x"
  by (simp add: is_infI5 lbdI2)

lemma is_infI7:
  "\<lbrakk>x \<in> X; x lb A; (\<And>a. a \<in> X \<Longrightarrow> a lb A \<Longrightarrow>  x \<ge> a)\<rbrakk> \<Longrightarrow> is_inf X A x"
  by (simp add: is_infI4 ub_def lbd_mem_iff)


lemma is_infI9:
  "\<lbrakk>x \<in> X; (\<forall>z \<in> X. (z \<le> x) \<longleftrightarrow> (z lb A))\<rbrakk> \<Longrightarrow> is_inf X A x"
  using is_infI7 by blast

lemma is_infE2:
  "is_inf X A x \<Longrightarrow> x lb A" 
  by(simp add: lbdD3[of "x" "X" "A"] is_infD32[of "X" "A" "x"])            

lemma is_infE3:
  "\<lbrakk> is_inf X A x; y \<in> lbd X A\<rbrakk> \<Longrightarrow> x \<ge> y "
  by (simp add: is_inf_def greatestD2)

              
lemma is_infE4:
  "\<lbrakk>is_inf X A x; y \<in> X; y lb A\<rbrakk> \<Longrightarrow> x \<ge> y "
  by (simp add: lbd_mem_iff is_infE3)
        
lemma is_infE5:
  "\<lbrakk>is_inf X A x; z \<in> X;  x \<ge> z\<rbrakk> \<Longrightarrow> z \<in> lbd X A"
  by (simp add: is_infE2 lb_iso1 lbdI2)

lemma is_infD1121:
  "\<lbrakk>is_inf X A x; a \<in> A \<rbrakk> \<Longrightarrow> a \<ge> x"
  using is_infE2 lbE by blast

lemma is_infE6:
  "\<lbrakk>is_inf X A x;  x \<ge> z\<rbrakk> \<Longrightarrow> z lb A"
  by (simp add: is_infE2 lb_iso1)

lemma is_infE7:
  "\<lbrakk>is_inf X A x;  x \<ge> z; a \<in> A\<rbrakk> \<Longrightarrow> a \<ge> z"
  by (simp add: is_infE6[of "X" "A" "x" "z"] lbD[of "z" "A" "a"])

lemma is_infD41:
  "is_inf X A x \<Longrightarrow> (\<And>z. z \<in> X \<Longrightarrow> z \<le> x \<Longrightarrow> z lb A)"
  by (simp add: is_infE6)

lemma is_infD42:
  "is_inf X A x \<Longrightarrow> (\<And>z. z \<in> X \<Longrightarrow>  z lb A \<Longrightarrow> z \<le> x)"
  by (simp add: is_infE4)

lemma is_infD5:
  "is_inf X A x \<Longrightarrow> (\<forall>z \<in> X. (z \<le> x) \<longleftrightarrow> (z lb A))"
  using is_infE4 is_infE6 by blast


lemma inf_iff2:
  "is_inf X A s \<longleftrightarrow>  s \<in> X \<and> (\<forall>z \<in> X.  s \<ge> z \<longleftrightarrow> z \<in> lbd X A)"
  by (meson dual_order.refl is_infE1 is_infE3 is_infE5 is_infI5 lbdD2)

lemma is_inf_unique:
  "is_inf X A m1 \<Longrightarrow> is_inf X A m2 \<Longrightarrow> m1 = m2"
  using is_infD1 greatest_unique by blast

lemma is_inf_ant1:
  "A \<subseteq> B \<Longrightarrow> is_inf X A ma \<Longrightarrow> is_inf X B mb \<Longrightarrow> ma \<ge> mb "
  by (simp add: is_infE1 is_infE2 is_infE4 lb_ant2)
lemma inf_minE1:
  "(is_least A x) \<Longrightarrow> x \<in> X \<Longrightarrow> is_inf X A x"
  by (simp add: leastD11 leastD12 is_infI6 lbdD1)

lemma inf_in_subset:
  "A \<subseteq> B \<Longrightarrow>  B \<subseteq> X \<Longrightarrow> is_inf X A s \<Longrightarrow> s \<in> B \<Longrightarrow> is_inf B A s"
  by(simp add:in_mono inf_iff2 lbd_mem_iff)

lemma inf_singleton:
  "s \<in> X \<Longrightarrow> is_inf X {s} s"
  by (simp add: inf_minE1 least_singleton)

lemma binary_infD21:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X; s \<in> X; is_inf X {a, b} s; c \<ge> a\<rbrakk> \<Longrightarrow>  c \<ge> s"
  using is_infD1121 by fastforce

lemma binary_infD22:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X; s \<in> X; is_inf X {a, b} s; c \<ge> b\<rbrakk> \<Longrightarrow>  c \<ge> s"
  by (simp add: binary_infD21 insert_commute)

lemma binary_infD31:
  "\<lbrakk>a \<in> X; b \<in> X; s \<in> X; is_inf X {a, b} s\<rbrakk>  \<Longrightarrow>  a \<ge> s"
  by (simp add: is_infD1121)

lemma binary_infD32:
  "\<lbrakk>a \<in> X; b \<in> X; s \<in> X; is_inf X {a, b} s\<rbrakk>  \<Longrightarrow>  b \<ge> s"
  by (simp add: is_infD1121)

lemma binary_infD4:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X; s \<in> X; is_inf X {a, b} s\<rbrakk>  \<Longrightarrow> (s \<ge> c \<longleftrightarrow> a \<ge> c \<and> b \<ge> c)"
  by (simp add: inf_iff2 lbd_mem_double)

lemma inf_insert1:
  "\<lbrakk>x lb A; x \<in> X\<rbrakk> \<Longrightarrow> is_inf X (insert x A) x"
  by (simp add: least_insert1 inf_minE1)

lemma inf_insert3:
  "\<lbrakk>is_inf X A m; m \<ge> x; x \<in> X\<rbrakk> \<Longrightarrow> is_inf X (insert x A) x"
  by (simp add: is_infD41 inf_insert1)

lemma inf_insert61:
  "\<lbrakk>is_inf X A s1; is_inf X {s1, x} s2\<rbrakk> \<Longrightarrow> s2 lb A"
  by (simp add: is_infD1121 is_infE6)

lemma inf_insert62:
  "\<lbrakk>is_inf X A s1; is_inf X {s1, x} s2\<rbrakk> \<Longrightarrow> s2 \<in> lbd X A"
  by (simp add: is_infE1 inf_insert61 lbd_mem_iff)

lemma inf_insert7:
  "\<lbrakk>is_inf X A s1; is_inf X {s1, x} s2; u \<in> lbd X (insert x A)\<rbrakk> \<Longrightarrow>  s2 \<ge> u"
  by (simp add: lbd_mem_iff2 is_infE3)

lemma lb_eq_inf_eq:
  "(\<And>x. x lb A \<longleftrightarrow> x lb B) \<Longrightarrow> (is_inf X A s \<longleftrightarrow> is_inf X B s)"
  by (simp add: lbd_mem_iff inf_iff2)

lemma Lower_eq_inf_eq:
  "lbd X A = lbd X B \<Longrightarrow> (is_inf X A s \<longleftrightarrow> is_inf X B s)"
  by (simp add: is_inf_def)

definition Inf::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order" where
  "Inf X A \<equiv> (THE m. is_inf X A m)"

lemma inf_equality:
  "is_inf X A m \<Longrightarrow> Inf X A = m"
  by (simp add: Inf_def is_inf_unique the_equality) 

lemma inf_exI:
  "\<exists>t. is_inf X A t \<Longrightarrow> (\<And>t. is_inf X A t \<Longrightarrow> P t) \<Longrightarrow> P (Inf X A)"
  using inf_equality by auto

lemma inf_unc:
  "\<lbrakk>is_inf X (A \<union> B) x; is_inf X A a; is_inf X B b; is_inf X {a, b} c\<rbrakk> \<Longrightarrow> x=c"
  by (metis binary_infD4 inf_iff2 is_infD42 is_infE6 lb_unionD1 lb_unionD2 lb_unionI order_class.order_eq_iff)

lemma inf_families1:
  "A \<noteq> {} \<Longrightarrow> (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_inf X Ai si) \<Longrightarrow> x \<in> X \<Longrightarrow> x lb Inf X ` A \<Longrightarrow> x lb \<Union> A"
  by (metis imageI is_infD5 inf_equality lb_def lb_unI)

lemma inf_families2:
  "A \<noteq> {} \<Longrightarrow> (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_inf X Ai si) \<Longrightarrow> x \<in> X \<Longrightarrow> x lb \<Union> A \<Longrightarrow>  x lb Inf X ` A"
  by (metis is_infD5 inf_equality lb_imageI lb_unD)

lemma inf_families:
  "A \<noteq> {} \<Longrightarrow>(\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_inf X Ai si) \<Longrightarrow>(is_inf X ((\<lambda>Ai. Inf X Ai)`A) s) \<longleftrightarrow> (is_inf X (\<Union>A) s)"
  apply(rule Lower_eq_inf_eq, rule lbd_eqI1) using inf_families1 apply blast using inf_families2 by blast


lemma binf_finite:
  assumes A0: "\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> is_inf X {a1, a2} (Inf X {a1, a2})" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X"
  shows "is_inf X A (Inf X A)"
  using A1 A2 A3 
proof (induct A rule: finite_ne_induct)
  case (singleton x) then show ?case using A0 by force
next
  case (insert x F)
  obtain i1 where B0:"is_inf X F i1"  using insert.hyps(4) insert.prems by blast
  have B1:"i1 \<in> X" using B0 is_infE1 by auto
  obtain i2 where B2:"is_inf X {i1, x} i2" using A0 B1 insert.prems by blast
  have B3:"i2 \<in> lbd X (insert x F)" by (meson B0 B2 inf_insert62 insertI2 is_infD1121 lbd_mem_insert singleton_iff)
  have B4:"\<And>l. l \<in> lbd X (insert x F) \<longrightarrow> l \<le> i2"using B0 B2 inf_insert7 by blast
  have B3:"is_inf X (insert x F) i2" by (simp add: B3 B4 is_infI5)
  then show ?case  by (simp add: inf_equality)
qed

lemma binf_commute2:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> Inf X {a, b}  =  Inf X {b,a}"
  by (simp add: insert_commute)

lemma binf_idem1:
  "a\<in> X \<Longrightarrow>Inf X {a, a} = a"
  by (simp add:  inf_equality inf_singleton)

lemma inf_singleton2:
  "a \<in> X \<Longrightarrow> Inf X {a} = a"
  using binf_idem1 by auto

lemma le_inf_iff:
  "\<lbrakk>is_inf X {a, b} i ;a \<in> X; b \<in> X; c \<in> X\<rbrakk>  \<Longrightarrow> (c \<le> i \<longleftrightarrow> c \<le> a \<and> c \<le> b)"
  by (simp add: binary_infD4 is_infE1)

lemma le_inf1:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> a \<le> b \<Longrightarrow>  Inf X {a, b} = a"
  using inf_equality inf_insert3 inf_singleton by blast

lemma le_inf2:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> b \<le> a \<Longrightarrow> Inf X {a, b} = b"
  by (metis binf_commute2 le_inf1)

lemma inf_lower_bounds:
  "is_inf X A i \<Longrightarrow> lbd X {i} = lbd X A"
  by(auto simp add:lbd_mem_iff; simp add: is_infD41 lb_singleton_simp;simp add: is_infE4 lb_singleton)


subsection Duality

lemma sup_imp_inf_ub:
  "is_sup X A s \<Longrightarrow>  is_inf X (ubd X A) s"
  by(simp add:is_sup_def is_inf_def is_least_def is_greatest_def ubd_def lbd_def lb_def ub_def)
  
lemma sup_if_inf_ub:
  "A \<subseteq> X \<Longrightarrow> is_inf X (ubd X A) s \<Longrightarrow>  is_sup X A s"
  by(auto simp add:is_sup_def is_inf_def is_least_def is_greatest_def ubd_def lbd_def lb_def ub_def)
  
lemma inf_imp_sup_lb:
  "is_inf X A s \<Longrightarrow>  is_sup X (lbd X A) s"
  by(simp add:is_sup_def is_inf_def is_least_def is_greatest_def ubd_def lbd_def lb_def ub_def)
  
lemma inf_if_sup_lb:
  "A \<subseteq> X \<Longrightarrow> is_sup X (lbd X A) s \<Longrightarrow>  is_inf X A s"
  by(auto simp add:is_sup_def is_inf_def is_least_def is_greatest_def ubd_def lbd_def lb_def ub_def)


subsection Misc

lemma sup_of_ineq1:
  "\<lbrakk>a \<le> b; is_sup X {a, c} x; is_sup X {b, c} y\<rbrakk> \<Longrightarrow> x \<le> y"
  by (meson is_supE1 is_supE2 is_supE3 order_trans ub_double_iff1 ubd_mem_double)
 
lemma inf_of_ineq1:
  "\<lbrakk>a \<le> b; is_inf X {a, c} x; is_inf X {b, c} y\<rbrakk> \<Longrightarrow> x \<le> y"
  by (meson dual_order.trans is_infD42 is_infE1 is_infE2 lb_doubleE1 lb_doubleE2 lb_doubleI)

lemma uni_sup1:
  "A \<subseteq> Pow X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> is_sup (Pow X) A  (\<Union>A)"
  by(auto simp add:is_sup_def is_least_def lbd_def ubd_def lb_def ub_def)

lemma uni_sup_fam:
  "\<lbrakk>S \<subseteq> Pow X; A \<subseteq> S; \<Union>A \<in> S\<rbrakk> \<Longrightarrow> is_sup S A (\<Union>A) "
  by (meson Sup_le_iff is_supI9 ub_def)

lemma uni_inf_fam:
  "\<lbrakk>S \<subseteq> Pow X; A \<subseteq> S; \<Inter>A \<in> S\<rbrakk> \<Longrightarrow> is_inf S A (\<Inter>A) "
  by (meson is_infI9 lb_def le_Inf_iff)

lemma union_sup_univ:
  "\<Union>A = Sup UNIV A"
  by (metis UNIV_I subset_Pow_Union sup_equality top_greatest uni_sup_fam)

lemma lattice_id9:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> X; is_sup X A s; is_inf X B i;(\<forall>a \<in> A. a lb B)\<rbrakk> \<Longrightarrow> s \<le> i"
  using is_infD42 is_infE1 is_supD5 ubI by fastforce


subsection MinimaMaxima

definition is_minimal::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "is_minimal A x \<equiv> (x \<in> A) \<and> (\<forall>a. a \<in> A \<and> a \<le> x \<longrightarrow> a =x)"

definition is_maximal::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "is_maximal A x \<equiv> (x \<in> A) \<and> (\<forall>a. a \<in> A \<and> x \<le> a \<longrightarrow> a = x)"

lemma maximalD1:
  "is_maximal A x \<Longrightarrow> x \<in> A"
  by(simp add:is_maximal_def)

lemma maximalD2:
  "is_maximal A x \<Longrightarrow> (\<forall>a. a \<in> A \<and> x \<le> a \<longrightarrow> a = x)"
  by(simp add:is_maximal_def)

lemma maximalD3:
  "is_maximal A x \<Longrightarrow> a \<in> A \<Longrightarrow> x \<le> a \<Longrightarrow> a = x"
  by(simp add:is_maximal_def)

lemma maximalD4:
  "is_maximal A x \<Longrightarrow> \<not>(\<exists>a \<in> A. a > x)"
  by (simp add: maximalD3 order.strict_iff_not)

lemma maximalI1:
  "\<lbrakk>x \<in> A; (\<And>a. \<lbrakk>a \<in> A; x \<le> a\<rbrakk> \<Longrightarrow> a = x)\<rbrakk> \<Longrightarrow> is_maximal A x"
  by(simp add:is_maximal_def)

lemma maximalI2:
  "\<lbrakk>x \<in> A; \<not>(\<exists>a \<in> A. a > x)\<rbrakk> \<Longrightarrow> is_maximal A x"
  by (meson dual_order.order_iff_strict maximalI1)

lemma maximalI3:
  "is_greatest A x \<Longrightarrow> is_maximal A x"
  by (simp add: greatest_iff leD maximalI2)

lemma maximalD5:
  "is_maximal A x \<Longrightarrow> y > x \<Longrightarrow> y \<notin> A"
  using maximalD4 by blast

subsection InfSemilattices

definition is_inf_semilattice::"'a::order set \<Rightarrow> bool" where
  "is_inf_semilattice X \<equiv> (X \<noteq> {}) \<and> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>x. is_inf X {a, b} x))"

definition is_finf_closed::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_finf_closed X A \<equiv> (\<forall>a1 a2. a1 \<in> A \<and>  a2 \<in> A \<longrightarrow> Inf X {a1, a2} \<in> A)"

lemma is_finf_closedI1:
  "(\<And>a1 a2. \<lbrakk>a1 \<in> A; a2 \<in> A\<rbrakk> \<Longrightarrow> Inf X {a1, a2} \<in> A) \<Longrightarrow> is_finf_closed X A"
  by (simp add: is_finf_closed_def)

lemma is_finf_closedI2:
  "(\<And>a1 a2. \<lbrakk>a1 \<in> A; a2 \<in> A\<rbrakk> \<Longrightarrow>(\<exists>i \<in> A. is_inf X {a1, a2} i)) \<Longrightarrow> is_finf_closed X A"
  apply(rule is_finf_closedI1) using inf_equality by blast


lemma sinfD2:
  "\<lbrakk>is_inf_semilattice X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>x. is_inf X {a, b} x) "
  by (simp add: is_inf_semilattice_def)

lemma sinfD3:
  "\<lbrakk>is_inf_semilattice X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> is_inf X {a, b} (Inf X {a, b}) "
  using inf_equality sinfD2 by blast

lemma sinfD4:
  "\<lbrakk>is_inf_semilattice X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> (Inf X {a, b}) \<in> X"
  using is_infE1 sinfD3 by blast

lemma binf_leI1:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X; a \<le> c\<rbrakk>  \<Longrightarrow> Inf X {a, b} \<le> c"
  by (simp add: binary_infD21 sinfD3 sinfD4)

lemma binf_leI2:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X; b \<le> c\<rbrakk>  \<Longrightarrow> Inf X {a, b} \<le> c"
  by (simp add: binary_infD22 sinfD3 sinfD4)

lemma binf_leI3:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X; c \<le>a; c \<le> b\<rbrakk>  \<Longrightarrow>c \<le> Inf X {a, b}"
  by (simp add: binary_infD4 sinfD3 sinfD4)

lemma binf_leI4:
  "\<lbrakk>is_inf_semilattice X; x \<in> X; y \<in> X; z \<in> X; x \<le> y\<rbrakk> \<Longrightarrow> Inf X {x, z} \<le> Inf X {y, z}"
  by (simp add: binf_leI1 binf_leI2 binf_leI3 sinfD4)

lemma binf_leI5:
  "\<lbrakk>is_inf_semilattice X; x1 \<in> X; x2 \<in> X; y1 \<in> X; y2 \<in>X;x1 \<le> y1; x2 \<le> y2\<rbrakk> \<Longrightarrow> Inf X {x1, x2} \<le> Inf X {y1, y2}"
  by (simp add: binf_leI1 binf_leI2 binf_leI3 sinfD4)

lemma binf_finite2:
  "\<lbrakk>is_inf_semilattice X;  A \<subseteq> X;A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow>  is_inf X A (Inf X A)"
  by (meson binf_finite sinfD3)

lemma finf_leI1:
  "\<lbrakk>is_inf_semilattice X;  A \<subseteq> X;A \<noteq> {}; finite A; a \<in> A\<rbrakk> \<Longrightarrow> Inf X A \<le> a"
  using is_infD1121[of X A "Inf X A" a] binf_finite2[of X A] by blast

lemma finf_lb:
  "\<lbrakk>is_inf_semilattice X;  A \<subseteq> X;A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow> Inf X A lb A"
  using is_infD32[of X A "Inf X A"] binf_finite2[of X A] by (simp add: is_infE2)

lemma finf_glb:
   "\<lbrakk>is_inf_semilattice X;  A \<subseteq> X;A \<noteq> {}; finite A; b \<in> lbd X A\<rbrakk> \<Longrightarrow> b \<le> Inf X A"
  using is_infE3[of X A "Inf X A" b] binf_finite2[of X A] by fastforce  

lemma binfI:
  "\<lbrakk>is_inf_semilattice X; (\<And>s. is_inf X {a, b} s \<Longrightarrow> P s); a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> P (Inf X {a, b})"
  by (simp add: sinfD3)

lemma binf_iff:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X\<rbrakk>  \<Longrightarrow> (c \<le> Inf X {a, b} \<longleftrightarrow> c \<le> a \<and> c \<le> b)"
  by (simp add: binary_infD4 sinfD3 sinfD4)

lemma binf_assoc1:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow>  Inf X {Inf X {a, b}, c} = Inf X {a,  Inf X {b, c}}"
  apply(rule order.antisym) by(simp add: binf_leI1 binf_leI2 binf_leI3 sinfD4)+

lemma binf_assoc2:
  "\<lbrakk>is_inf_semilattice X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf X {a, Inf X {b, c}} = Inf X {b, Inf X {a, c}}"
  apply(rule order.antisym) by (simp add: binf_leI1 binf_leI2 binf_leI3 sinfD4)+

lemma binf_idem2:
  "is_inf_semilattice X \<Longrightarrow>a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> Inf X {a, Inf X {a, b}} = Inf X {a, b}"
  by (metis binf_assoc1 binf_idem1)

lemma binf_le1:
  "is_inf_semilattice X\<Longrightarrow>a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> a \<le> b \<Longrightarrow>  Inf X {a, b} = a"
  by (simp add: dual_order.eq_iff binf_iff binf_leI1)

lemma le_binf1:
  "\<lbrakk>is_inf_semilattice X; a \<in> X; b \<in> X; Inf X {a, b} = a\<rbrakk> \<Longrightarrow>  a \<le> b"
  by (metis binf_iff dual_order.refl)

lemma le_binf2:
  "\<lbrakk>is_inf_semilattice X; a \<in> X; b \<in> X; Inf X {a, b} = b\<rbrakk> \<Longrightarrow>  b \<le> a"
  by (simp add: insert_commute le_binf1)


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
  obtain t where A7:"is_inf X {x, i} t" by (meson A4 A5 A6 dual_order.trans insert.prems(1) insert_subset is_infE1 sinfD2)
  have B2:"t \<in> A"
    using A0 A7 B0 B1 inf_equality by blast
  have B3:"t \<in> (lbd X (insert x F))"
    by (meson A6 A7 insertCI is_infD1121 is_infE1 is_infE5 lbd_mem_insert)
  have B4:"\<And>y. y \<in> (lbd X (insert x F)) \<longrightarrow> y \<le>t "
    by (metis A6 A7 lbdD3 lbd_mem_iff2 insertCI is_infD42 lb_double_iff1)
  have B5:"is_inf X (insert x F) t"
    by (simp add: B3 B4 is_infI5)
  then show ?case
    by (simp add: B2 inf_equality)
qed

lemma inf_semilattice_finf_closed:
  "\<lbrakk>is_finf_closed X A; A \<subseteq> X; E \<subseteq> A; finite E; E \<noteq> {}; is_inf_semilattice X\<rbrakk> \<Longrightarrow> Inf X E \<in> A "
  by (metis finite_inf_closed2 is_finf_closed_def)

lemma inf_semilattice_finf_closed2:
  "\<lbrakk>is_finf_closed X A; A \<subseteq> X; E \<in> Fpow_ne A; is_inf_semilattice X\<rbrakk> \<Longrightarrow> Inf X E \<in> A "
  by (simp add: fpow_ne_iff2 inf_semilattice_finf_closed)

lemma inf_semilattice_finf_closed3:
  "\<lbrakk>is_finf_closed X A; A \<subseteq> X; E \<in> Fpow_ne A; is_inf_semilattice X\<rbrakk> \<Longrightarrow> is_inf X E (Inf X E)"
  by (metis binf_finite2 dual_order.trans fpow_ne_iff2)

lemma inf_semilattice_finf:
  "\<lbrakk>is_inf_semilattice X; A \<in> Fpow_ne X\<rbrakk> \<Longrightarrow> is_inf X A (Inf X A)"
  by (simp add: binf_finite2 fpow_ne_iff2)

lemma finfI:
  "\<lbrakk>is_inf_semilattice X; (\<And>s E. is_inf X E s \<Longrightarrow> P s); F \<in> Fpow_ne X\<rbrakk> \<Longrightarrow> P (Inf X F)"
  using inf_semilattice_finf by blast

lemma inf_semilattice_finf_props0:
  "\<lbrakk>is_inf_semilattice X; a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf X {a, b, c}  \<in> X"
  by(erule finfI,simp add:is_infE1, simp add: fpow_ne_iff2)

lemma inf_assoc_lbd1:
  "is_inf X {b, c} i \<Longrightarrow> x \<in> lbd X {a, i} \<Longrightarrow> x \<in> lbd X {a, b, c}"
  by (meson is_infE5 lbdD2 lbd_mem_doubleE1 lbd_mem_doubleE2 lbd_mem_insert)

lemma inf_assoc_lbd1b:
  "is_inf X {a, b} i \<Longrightarrow> is_inf X {c, d} j \<Longrightarrow> x \<in> lbd X {i, j} \<Longrightarrow> x \<in> lbd X {a, b, c, d}"
  by (meson is_infE5 lbdD2 lbd_mem_doubleE1 lbd_mem_doubleE2 lbd_mem_insert)

lemma inf_assoc_lbd2:
  "\<lbrakk>is_inf X {b, c} i\<rbrakk> \<Longrightarrow> lbd X {a, b, c} = lbd X {a, i} "
  by (auto, simp add: is_infE4 lb_def lbd_mem_iff, simp add:inf_assoc_lbd1)

lemma inf_assoc_lbd2b:
  "is_inf X {a, b} i \<Longrightarrow> is_inf X {c, d} j \<Longrightarrow>  lbd X {i, j} =  lbd X {a, b, c, d}"
  by (auto, simp add:inf_assoc_lbd1b, simp add: is_infE4 lb_double_iff1 lbd_mem_iff2)

lemma inf_assoc_lbd3b:
  "\<lbrakk>is_inf X {b, c} i;is_inf X  {a, i} j\<rbrakk> \<Longrightarrow>  is_inf X {a, b, c} j"
  by (simp add: inf_assoc_lbd2 is_inf_def)

lemma inf_assoc_lbd4a:
  "\<lbrakk>is_inf X {a, b} i; is_inf X {c, d} j; is_inf X {a, b, c, d} k\<rbrakk> \<Longrightarrow> is_inf X  {i, j} k "
  by (meson Lower_eq_inf_eq inf_assoc_lbd2b)

lemma inf_semilattice_finf_props1:
  "\<lbrakk>is_inf_semilattice X; a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> is_inf X {a, Inf X {b, c}} (Inf X {a, b, c})"
  by (metis inf_assoc_lbd3b inf_equality sinfD3 sinfD4)

lemma inf_semilattice_finf_props2:
  "\<lbrakk>is_inf_semilattice X; a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf X {a, Inf X {b, c}} = Inf X {a, b, c}"
  by (simp add: inf_equality inf_semilattice_finf_props1)

lemma inf_semilattice_finf_props3:
  "\<lbrakk>is_inf_semilattice X; a \<in> X; b \<in> X; c \<in> X; d \<in> X\<rbrakk> \<Longrightarrow> is_inf X {Inf X {a, b}, Inf X {c, d}} (Inf X {a, b, c, d})"
  by (meson binf_finite2 bot.extremum finite.emptyI finite_insert inf_assoc_lbd4a insert_not_empty insert_subsetI)

lemma inf_semilattice_finf_props4:
  "\<lbrakk>is_inf_semilattice X; a \<in> X; b \<in> X; c \<in> X; d \<in> X\<rbrakk> \<Longrightarrow> Inf X {Inf X {a, b}, Inf X {c, d}} = Inf X {a, b, c, d}"
  by (simp add: inf_equality inf_semilattice_finf_props3)

lemma inf_semilattice_finf_anti:
  "\<lbrakk>is_inf_semilattice X; A \<in> Fpow_ne X; B \<in> Fpow_ne X; A \<subseteq> B\<rbrakk> \<Longrightarrow> Inf X B \<le> Inf X A"
  using is_inf_ant1[of A B X "Inf X A" "Inf X B"] inf_semilattice_finf by blast
    
lemma inf_semilattice_finf_props5:
  "\<lbrakk>is_inf_semilattice X; a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf X {Inf X {a, b}, Inf X {a, c}} = Inf X {a, Inf X {b, c}}"
  by (simp add: binf_assoc1 binf_assoc2 binf_idem2 sinfD4)



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
  using ssupD3 sup_iff2 by blast

lemma bsup_geI1:
  "\<lbrakk>is_sup_semilattice X;a \<in> X; b \<in> X; c \<in> X; a \<ge> c\<rbrakk>  \<Longrightarrow> Sup X {a, b} \<ge> c"
  by (simp add: binary_supD21 ssupD3 ssupD4)

lemma bsup_geI2:
  "\<lbrakk>is_sup_semilattice X;a \<in> X; b \<in> X; c \<in> X; b \<ge> c\<rbrakk>  \<Longrightarrow> Sup X {a, b} \<ge> c"
  by (simp add: binary_supD22 ssupD3 ssupD4)

lemma bsup_geI3:
  "\<lbrakk>is_sup_semilattice X;a \<in> X; b \<in> X; c \<in> X; c \<ge>a; c \<ge> b\<rbrakk> \<Longrightarrow> c \<ge> Sup X {a, b}"
  by (simp add: binary_supD4 ssupD3 ssupD4)

lemma bsup_geI5:
  "\<lbrakk>is_sup_semilattice X; x1 \<in> X; x2 \<in> X; y1 \<in> X; y2 \<in>X;x1 \<le> y1; x2 \<le> y2\<rbrakk> \<Longrightarrow> Sup X {x1, x2} \<le> Sup X {y1, y2}"
  by (simp add: bsup_geI1 bsup_geI2 bsup_geI3 ssupD4)


lemma bsup_iff:
  "\<lbrakk>is_sup_semilattice X; a \<in> X; b \<in> X; c \<in> X\<rbrakk>  \<Longrightarrow> (c \<ge> Sup X {a, b} \<longleftrightarrow> c \<ge> a \<and> c \<ge> b)"
  by (simp add: binary_supD4 ssupD3 ssupD4)

lemma bsup_assoc1:
  "\<lbrakk>is_sup_semilattice X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup X {Sup X {a, b}, c} =Sup X {a, Sup X {b, c}}"
  apply(rule order.antisym) by (simp add:bsup_geI1 bsup_geI2 bsup_geI3 ssupD4)+

lemma bsup_ge1:
  "is_sup_semilattice X\<Longrightarrow>a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> a \<le> b \<Longrightarrow>  Sup X {a, b} = b"
  by (simp add: Orderings.order_eq_iff bsup_geI2 bsup_geI3)

lemma bsup_ge2:
  "is_sup_semilattice X \<Longrightarrow>a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> b \<le> a \<Longrightarrow> Sup X {a, b} = a"
  by (simp add: dual_order.eq_iff bsup_iff bsup_geI1)

lemma ge_bsup1:
  "\<lbrakk>is_sup_semilattice X; a \<in> X; b \<in> X; Sup X {a, b} = b\<rbrakk> \<Longrightarrow> a \<le> b"
  by (metis bsup_geI1 order_refl)

lemma bsup_finite2:
  "\<lbrakk>is_sup_semilattice X;  A \<subseteq> X;A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow>  is_sup X A (Sup X A)"
  by (simp add: bsup_finite ssupD3)


lemma fsup_ub:
  "\<lbrakk>is_sup_semilattice X;  A \<subseteq> X;A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow> Sup X A ub A"
  using is_supD32[of X A "Sup X A"] bsup_finite2[of X A] by (simp add: is_supE2)

lemma fsup_lub:
   "\<lbrakk>is_sup_semilattice X;  A \<subseteq> X;A \<noteq> {}; finite A; b \<in> ubd X A\<rbrakk> \<Longrightarrow> Sup X A \<le> b"
  using is_supE3[of X A "Sup X A" b] bsup_finite2[of X A] by fastforce  

lemma fsup_lub3:
  "\<lbrakk>is_sup_semilattice X;  A \<in> Fpow_ne X; b \<in> ubd X A\<rbrakk> \<Longrightarrow> Sup X A \<le> b"
  by (simp add: fpow_ne_iff2 fsup_lub)


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
    by (meson A4 A5 A6 B1 in_mono is_supE1 ssupD2)
  have B2: "t \<in> A"
    using A0 A7 B0 B1 sup_equality by blast
  have B3: "t \<in> ubd X (insert x F)"
    by (meson A6 A7 insertCI is_supD1121 is_supE1 is_supE5 ubd_mem_insert)
  have B4: "\<And>y. y \<in> ubd X (insert x F) \<longrightarrow> t \<le> y"
    by (metis A6 A7 ubdD3 ubd_mem_iff2 insertCI is_supD42 ub_double_iff1)
  have B5: "is_sup X (insert x F) t"
    by (simp add: B3 B4 is_supI5)
  then show ?case
    by (simp add: B2 sup_equality)
qed

lemma sup_semilattice_fsup_closed:
  "\<lbrakk>is_fsup_closed X A; A \<subseteq> X; E \<subseteq> A; finite E; E \<noteq> {}; is_sup_semilattice X\<rbrakk> \<Longrightarrow> Sup X E \<in> A "
  by (metis finite_sup_closed2 is_fsup_closed_def)


lemma sup_semilattice_fsup:
  "\<lbrakk>is_sup_semilattice X; A \<in> Fpow_ne X\<rbrakk> \<Longrightarrow> is_sup X A (Sup X A)"
  by (simp add: bsup_finite2 fpow_ne_iff2)

lemma sup_assoc_ubd1:
  "is_sup X {b, c} s \<Longrightarrow> x \<in> ubd X {a, s} \<Longrightarrow> x \<in> ubd X {a, b, c}"
  by (metis is_supE5 ubdD2 ubd_mem_doubleE1 ubd_mem_doubleE2 ubd_mem_insert)

lemma sup_assoc_ubd1b:
  "is_sup X {a, b} s \<Longrightarrow> is_sup X {c, d} t \<Longrightarrow> x \<in> ubd X {s, t} \<Longrightarrow> x \<in> ubd X {a, b, c, d}"
  by (metis is_supE5 ubdD2 ubd_mem_double ubd_mem_insert)

lemma sup_assoc_ubd2:
  "is_sup X {b, c} s \<Longrightarrow> ubd X {a, b, c} = ubd X {a, s} "
  by (auto, simp add: is_supE4 ub_def ubd_mem_iff, simp add:sup_assoc_ubd1)

lemma sup_assoc_ubd2b:
  "is_sup X {a, b} s \<Longrightarrow> is_sup X {c, d} t \<Longrightarrow>  ubd X {s, t} =  ubd X {a, b, c, d}"
  by (auto, simp add:sup_assoc_ubd1b, simp add: is_supE4 ub_double_iff1 ubd_mem_iff2)


lemma sup_assoc_ubd3b:
  "\<lbrakk>is_sup X {b, c} s;is_sup X  {a, s} t\<rbrakk> \<Longrightarrow>  is_sup X {a, b, c} t"
  by (simp add: sup_assoc_ubd2 is_sup_def)

lemma sup_assoc_ubd4a:
  "\<lbrakk>is_sup X {a, b} s; is_sup X {c, d} t; is_sup X {a, b, c, d} r\<rbrakk> \<Longrightarrow> is_sup X  {s, t} r"
  by (simp add: sup_iff2 ubd_mem_iff3)


lemma sup_semilattice_fsup_props1:
  "\<lbrakk>is_sup_semilattice X; a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> is_sup X {a, Sup X {b, c}} (Sup X {a, b, c})"
  by (metis ssupD3 ssupD4 sup_assoc_ubd3b sup_equality)

lemma sup_semilattice_supf_props2:
  "\<lbrakk>is_sup_semilattice X; a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup X {a, Sup X {b, c}} = Sup X {a, b, c}"
  by (simp add: sup_equality sup_semilattice_fsup_props1)

lemma sup_semilattice_fsup_props3:
  "\<lbrakk>is_sup_semilattice X; a \<in> X; b \<in> X; c \<in> X; d \<in> X\<rbrakk> \<Longrightarrow> is_sup X {Sup X {a, b}, Sup X {c, d}} (Sup X {a, b, c, d})"
  by (metis (full_types) bsup_finite2 empty_not_insert empty_subsetI finite.emptyI finite.insertI insert_subsetI sup_assoc_ubd4a)

lemma sup_semilattice_fsup_iso:
  "\<lbrakk>is_sup_semilattice X; A \<in> Fpow_ne X; B \<in> Fpow_ne X; A \<subseteq> B\<rbrakk> \<Longrightarrow> Sup X A \<le> Sup X B"
  using is_sup_iso1[of A B X "Sup X A" "Sup X B"] sup_semilattice_fsup by blast
    
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

lemma lattD5:
  "\<lbrakk>is_lattice X; x \<in> X; y \<in> X; Sup X {x, y} = y\<rbrakk> \<Longrightarrow> x \<le> y"
  by (metis bsup_geI1 dual_order.refl lattD42)

lemma latt_iff:
  "is_lattice X \<longleftrightarrow> (is_inf_semilattice X) \<and> (is_sup_semilattice X)"
  using lattD41 lattD42 lattI2 by blast

lemma latt_ge_iff1:
  "\<lbrakk>is_lattice X; x \<in>X; y \<in> X\<rbrakk> \<Longrightarrow> (x \<le> y \<longleftrightarrow> Sup X {x, y} = y)"
  by (auto simp add: bsup_ge1 lattD42 lattD5)

lemma latt_ge_iff2:
  "\<lbrakk>is_lattice X; x \<in>X; y \<in> X\<rbrakk> \<Longrightarrow> (y \<le> x \<longleftrightarrow> Sup X {x, y} = x)"
  by (simp add: bsup_commute2 latt_ge_iff1)

lemma latt_le_iff1:
  "\<lbrakk>is_lattice X; x \<in>X; y \<in> X\<rbrakk> \<Longrightarrow> (x \<le> y \<longleftrightarrow> Inf X {x, y} = x)"
  using binf_le1 lattD41 le_binf1 by blast

lemma lattice_absorb1:
  "\<lbrakk>is_lattice X; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Sup X {x,Inf X {x, y}} = x"
  by (simp add: binf_leI1 bsup_ge2 latt_iff sinfD4)

lemma lattice_absorb2:
  "\<lbrakk>is_lattice X; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Inf X {x,Sup X {x, y} } = x"
  by (simp add: binf_le1 bsup_geI1 latt_iff ssupD4)

lemma distrib_sup_le: "\<lbrakk>is_lattice X; x \<in>X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Sup X {x, Inf X {y, z}} \<le> Inf X {Sup X {x, y}, Sup X {x, z}}"
  by(auto simp add: bsup_geI1 lattD42 binary_infD4 bsup_geI2 bsup_iff latt_iff sinfD3 sinfD4 ssupD4 binf_leI3 binf_leI1 binf_leI2)

lemma distrib_inf_le: "\<lbrakk>is_lattice X; x \<in>X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Sup X {Inf X {x, y}, Inf X {x, z}} \<le> Inf X {x, Sup X {y, z}}"
  by(auto simp add:bsup_geI1 lattD42 binary_infD4 bsup_geI2 bsup_iff latt_iff sinfD3 sinfD4 ssupD4 binf_leI1 binf_leI2 binf_leI3)

lemma mod_sup_le:
  "\<lbrakk>is_lattice X; x \<in> X; y \<in> X; z \<in> X; x \<le> z\<rbrakk> \<Longrightarrow> Sup X {x, Inf X {y, z}} \<le> Inf X {Sup X {x, y}, z}"
  by (metis distrib_sup_le ge_sup1)

subsection DistributiveLattices


(*
x \<and> (y \<or> z) = (x \<and> y) \<or> (x \<and> z) 

x \<or> (y \<and> z)=(x \<or> (x \<and> z)) \<or> (y \<and> z) 
           = x \<or> (x \<and> z)  \<or> (y \<and> z)
           = x \<or> (z \<and> (x \<or> y)) 
           =(x \<and> (x \<or> y)) \<or> (z \<and> (x \<or> y))
           =(x \<or> y) \<and> (x \<or> z)


*)

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

lemma distr_latticeI1:
  "\<lbrakk>is_lattice X; (\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow>  Sup X {x, Inf X {y, z}} \<ge> Inf X {Sup X {x, y}, Sup X {x, z}})\<rbrakk> \<Longrightarrow> distributive_lattice X"
  by (simp add: distrib_sup_le distributive_lattice_def order_class.order_eq_iff)

lemma distr_latticeI2:
  "\<lbrakk>is_lattice X; (\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow>  Inf X {x, Sup X {y, z}} \<le> Sup X {Inf X {x, y}, Inf X {x, z}})\<rbrakk> \<Longrightarrow> distributive_lattice X"
  by (simp add: Orderings.order_eq_iff distrib_inf_le distibD1 distributive_lattice_def)

lemma distr_latticeD1:
  "\<lbrakk>distributive_lattice X; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow>  Sup X {x, Inf X {y, z}} = Inf X {Sup X {x, y}, Sup X {x, z}} "
  by (simp add: distributive_lattice_def insert_commute)

lemma distr_latticeD2:
  "\<lbrakk>distributive_lattice X; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow>  Sup X {Inf X {y, z}, x} = Inf X {Sup X {y, x}, Sup X {z, x}}"
  by (simp add: distributive_lattice_def insert_commute)
 
lemma distr_latticeD3:
  "\<lbrakk>distributive_lattice X; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow>  Inf X {x, Sup X {y, z}} = Sup X {Inf X {x, y}, Inf X {x, z}}"
  using distribD2 distributive_lattice_def by fastforce
 

lemma lattice_id0:
  "\<lbrakk>is_lattice X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Inf X {x, y} lb  {Sup X {x, y}, Sup X {y, z}, Sup X {x, z}}"
  by (simp add: lb_def binf_leI1 binf_leI2 bsup_geI1 lattD41 lattD42 ssupD4)

lemma lattice_id2:
  "\<lbrakk>is_lattice X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Inf X {x, z} lb  {Sup X {x, y}, Sup X {y, z}, Sup X {x, z}}"
  using lattice_id0[of "X" "x" "z" "y"] by (simp add: insert_commute)

lemma distr_latticeD5:"distributive_lattice X \<Longrightarrow> is_lattice X" by (simp add: distributive_lattice_def)




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

lemma cinfD4:
  "\<lbrakk>is_cinf_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_inf X A (Inf X A)"
  using cinfD2 inf_equality by blast

lemma cinfD61:
  "\<lbrakk>is_cinf_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> l \<in> lbd X A \<Longrightarrow> l \<le> Inf X A"
  by (meson cinfD4 is_infD5 lbdD2 lbdD3)

lemma cinfD62:
  "\<lbrakk>is_cinf_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> l \<in> X \<Longrightarrow> l lb A \<Longrightarrow>  l \<le> Inf X A"
  by (simp add: cinfD61 lbdI2)

lemma csupD2:
  "\<lbrakk>is_csup_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup X A x)"
  by (simp add: is_csup_semilattice_def)

lemma clatD21:
  "\<lbrakk>is_clattice X; A \<subseteq> X\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup X A x)"
  by (simp add: is_clattice_def)

lemma clatD22:
  "\<lbrakk>is_clattice X; A \<subseteq> X\<rbrakk> \<Longrightarrow> (\<exists>x. is_inf X A x)"
  by (meson lbd_sub clatD21 inf_if_sup_lb)

lemma clatD1:
  "is_clattice X \<Longrightarrow> is_csup_semilattice X"
  by (simp add: is_clattice_def is_csup_semilattice_def)

lemma clatD2:
  "is_clattice X \<Longrightarrow> is_cinf_semilattice X"
  by (simp add: clatD22 is_cinf_semilattice_def is_clattice_def)

lemma csupD3:
  "is_csup_semilattice X \<Longrightarrow> (\<exists>x. is_greatest X x)"
  by (metis is_csup_semilattice_def order_refl sup_max_eq2)

lemma csupD4:
  "\<lbrakk>is_csup_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_sup X A (Sup X A)"
  using csupD2 sup_equality by blast

lemma csupD61:
  "\<lbrakk>is_csup_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> b \<in> ubd X A \<Longrightarrow> Sup X A \<le> b"
  by (meson csupD4 is_supE3)

lemma csupD62:
  "\<lbrakk>is_csup_semilattice X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> b \<in> X \<Longrightarrow> b ub A \<Longrightarrow> Sup X A \<le> b"
  by (simp add: csupD61 ubdI2)

lemma csup_fsup:
  "is_csup_semilattice X \<Longrightarrow> is_sup_semilattice X"
  by (simp add: is_csup_semilattice_def is_sup_semilattice_def)

lemma cinf_sinf:
  "is_cinf_semilattice X \<Longrightarrow> is_inf_semilattice X"
  by (simp add: is_cinf_semilattice_def is_inf_semilattice_def)

lemma clat_lattice:
  "is_clattice X \<Longrightarrow> is_lattice X"
  by (simp add: cinf_sinf clatD1 clatD2 csup_fsup latt_iff)

lemma sup_iso1b:
  "\<lbrakk>is_csup_semilattice X; A \<noteq> {}; A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> Sup X A \<le> Sup X B"
  by (metis csupD4 dual_order.trans is_sup_iso1 ne_subset_ne)

lemma sup_iso1:
  "\<lbrakk>is_clattice X; A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> Sup X A \<le> Sup X B"
  by (metis clatD21 dual_order.trans is_sup_iso1 sup_equality)

lemma sup_iso2:
  "\<lbrakk>is_clattice X; is_clattice Y;A \<subseteq> Y; Y \<subseteq> X; Y \<noteq> {}\<rbrakk> \<Longrightarrow> Sup X A \<le> Sup Y A"
  by (metis clatD21 dual_order.trans in_mono is_supE2 is_supE4 sup_equality sup_iff2)

lemma inf_anti1:
  "\<lbrakk>is_clattice X; A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> Inf X B \<le> Inf X A"
  by (metis clatD22 dual_order.trans inf_equality is_inf_ant1)


lemma pow_is_clattice1:
  "A \<subseteq> Pow X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> is_inf (Pow X) A  (\<Inter>A)"
  by(auto simp add:is_inf_def is_greatest_def ubd_def lbd_def ub_def lb_def)

lemma pow_is_clattice2:
  "is_inf (Pow X) {} X"
  by(auto simp add:is_inf_def is_greatest_def ubd_def lbd_def ub_def lb_def)

lemma pow_is_clattice3:
  "A \<subseteq> Pow X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> is_sup (Pow X) A  ( \<Union>A)"
  by(auto simp add:is_sup_def is_least_def ubd_def lbd_def ub_def lb_def)

lemma pow_is_clattice:
  "is_clattice (Pow X)"
   using  pow_is_clattice3 apply(auto simp add:is_clattice_def)
   by (metis Pow_not_empty ubd_empty pow_is_clattice1 subset_refl sup_if_inf_ub)

lemma univ_is_clattice:
  "is_clattice (UNIV :: 'a set set)"
  by (metis Pow_UNIV pow_is_clattice)

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
  "\<lbrakk>is_isotone X f; b \<in> ubd X A; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f b) \<in> ubd (f`X) (f`A)"
  by (simp add: ubd_mem_iff isotoneD31)
             
lemma isotoneD42:
  "\<lbrakk>is_isotone X f; b \<in> lbd X A; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f b) \<in> lbd (f`X) (f`A)"
  by (simp add: lbd_mem_iff isotoneD32)

lemma isotoneD61:
  "\<lbrakk>is_isotone X f; is_sup X A x; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f x) ub f`A"
  by (simp add: is_supE1 is_supE2 isotoneD31)

lemma isotoneD62:
  "\<lbrakk>is_isotone X f; is_inf X A x; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f x) lb f`A"
  by (simp add: inf_iff2 is_infE2 isotoneD32)

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
  "\<lbrakk>is_extensive X f ; (f`X \<subseteq> X); A \<subseteq> X ; b \<in> ubd (f`X)  (f`A) \<rbrakk> \<Longrightarrow> b \<in> ubd X A"
  by (metis ubd_mem_iff extensiveD1 extensiveD2 extensiveI1 in_mono)

lemma extensive_ub_imp2:
  "\<lbrakk>is_extensive X f; (f`X \<subseteq> X); A \<subseteq> X; b \<in> ubd X  (f`A)\<rbrakk> \<Longrightarrow> b \<in> ubd X A"
  by (metis ubd_mem_iff extensiveD2 in_mono is_extensive_def)

lemma is_iso_extD1:
  "\<lbrakk>is_isotone X f;  is_extensive X f;  (f`X \<subseteq> X);  x \<in> X\<rbrakk> \<Longrightarrow> f x \<le> f (f x)"
  by (simp add: extensiveD3 image_subset_iff)


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

lemma closureD10:
  "\<lbrakk>is_closure X f;  x \<in> X;  f x \<le> x\<rbrakk> \<Longrightarrow> x = f x"
  by (simp add: closureD5 dual_order.eq_iff)

lemma closureD11:
  "\<lbrakk>is_closure X f;  x \<in> X; f x \<le> x\<rbrakk> \<Longrightarrow> x \<in> f `X"
  using closureD10 by blast

lemma cl_sup_eq_sup_cl1:
  "\<lbrakk>is_closure X f; is_sup X A s; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f s) \<in> ubd (f`X) (f`A)"
  by (simp add: is_closure_def is_supD32 isotoneD41)

lemma cl_sup_eq_sup_cl2:
  "\<lbrakk>is_closure X f;  is_sup X A s; b \<in> ubd (f`X) (f`A); A \<subseteq> X\<rbrakk> \<Longrightarrow> s \<le> b"
  by(simp add: is_closure_def[of "X" "f"] ubdD2[of "b" "f`X" "f`A"]  closureD2[of "X" "f" "b"] extensive_ub_imp[of "X" "f" "A" "b"]  is_supE3[of "X" "A" "s"] )

lemma cl_sup_eq_sup_cl3:
  "\<lbrakk>is_closure X f;  is_sup X A s; b \<in> ubd (f`X) (f`A);A \<subseteq> X\<rbrakk> \<Longrightarrow> f s \<le> b"
  by (meson cl_sup_eq_sup_cl2 closureD7 is_supE1 ubd_mem_iff)

(*
cl_sup_eq_sup and cl_sup_ge_sup_cl have converses in extensiveI4 idempotentI4 and isotoneI4 

*)

lemma cl_sup_eq_sup:
  "\<lbrakk>is_closure X f;  is_sup X A s;A \<subseteq> X\<rbrakk> \<Longrightarrow> is_sup (f`X) (f`A) (f s)"
  by(simp add:is_sup_def[of "f`X" "f`A" "f s"] cl_sup_eq_sup_cl1 cl_sup_eq_sup_cl3 is_least_def lbd_mem_iff2)
         
lemma closure_iff2:
  "is_closure X f \<longleftrightarrow> (f`X \<subseteq> X) \<and> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. x1 \<le> f x2 \<longleftrightarrow> f x1 \<le> f x2)"
  by (meson closureD3 closureI3 closure_cond_def dual_order.trans is_closure_def is_extensive_def order_refl)

lemma cl_sup_ge_sup_cl11:
  "\<lbrakk>is_closure X f; is_sup X A s1; is_sup X (f`A) s2; A \<subseteq> X\<rbrakk> \<Longrightarrow> s1 \<le> s2"
  by (meson extensive_ub_imp2 is_closure_def is_supD32 is_supE3)

lemma cl_sup_ge_sup_cl2:
  "\<lbrakk>is_closure X f;  is_sup X A s1;  is_sup X (f`A) s2; A \<subseteq>  X\<rbrakk> \<Longrightarrow> s2  \<le> f s1"
  by (meson closureD1 is_closure_def is_supD42 isotoneD61 sup_iff2)

lemma cl_sup_ge_sup_cl3:
  "\<lbrakk>is_closure X f;  is_sup X A s1;  is_sup X (f`A) s2; A \<subseteq> X\<rbrakk> \<Longrightarrow> f s2  \<le> f s1"
  by (simp add: cl_sup_ge_sup_cl2 closureD7 is_supE1)

lemma cl_sup_ge_sup_cl4:
  "\<lbrakk>is_closure X f; is_sup X A s1;  is_sup X (f`A) s2; A \<subseteq> X\<rbrakk> \<Longrightarrow> f s1  \<le> f s2"
  by (simp add: cl_sup_ge_sup_cl11 closureD4 is_supE1)

lemma cl_sup_ge_sup_cl:
  "\<lbrakk>is_closure X f; is_sup X A s1;  is_sup X (f`A) s2; A \<subseteq> X\<rbrakk> \<Longrightarrow> f s1  = f s2"
  by (simp add: cl_sup_ge_sup_cl3 cl_sup_ge_sup_cl4 dual_order.eq_iff)

subsection ClosureRanges

definition is_clr::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_clr C X \<equiv> (C \<noteq> {}) \<and> (C \<subseteq> X) \<and> (\<forall>x. x \<in> X \<longrightarrow> (\<exists>c. is_least (ubd C {x}) c))"

lemma clrI1:
  "\<lbrakk>C \<noteq> {}; C \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> (\<exists>c. is_least (ubd C {x}) c)) \<rbrakk> \<Longrightarrow> is_clr C X"
  by (simp add:is_clr_def)

lemma clrD2:
  "is_clr C X \<Longrightarrow> C \<subseteq> X"
  by (simp add:is_clr_def)

lemma clrD2b:
  "is_clr C X \<Longrightarrow> x \<in> C \<Longrightarrow>x \<in> X"
  by(drule clrD2,simp add:subsetD)

lemma clrD3:
  "is_clr C X \<Longrightarrow>  (\<And>x. x \<in> X \<Longrightarrow> (\<exists>c. is_least (ubd C {x}) c))"
  by (simp add:is_clr_def)

lemma clrD4:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> (\<exists>c. is_least (ubd C {x}) c)"
  by (simp add:is_clr_def)

lemma clrD5:
  "is_clr C X \<Longrightarrow>  (\<And>x. x \<in> X  \<Longrightarrow> ((ubd C {x}) \<noteq> {}))"
  by (simp add: clrD4 least_exD0)

lemma clrD6:
  "is_clr C X \<Longrightarrow>  x \<in> X \<Longrightarrow> (ubd C {x}) \<noteq> {}"
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


definition cl_from_clr::"'a::order set \<Rightarrow> ('a::order \<Rightarrow> 'a::order)" where
  "cl_from_clr C \<equiv> (\<lambda>x. Least (ubd C {x}))"

lemma cl_range1:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> (cl_from_clr C) x \<in> C"
  by(simp add:cl_from_clr_def, auto intro: ubdD2 clrD4 least_exD1)

lemma cl_range2:
  "is_clr C X  \<Longrightarrow> (cl_from_clr C)`X \<subseteq> C"
  using cl_range1 by blast

lemma cl_range3:
  "is_clr C X  \<Longrightarrow> x \<in> C \<Longrightarrow> (cl_from_clr C) x = x"
  by (simp add: cl_from_clr_def ub_single_least2)

lemma cl_range3b:
  "is_clr C X  \<Longrightarrow> c \<in> C \<Longrightarrow> (\<exists>x \<in> X.  (cl_from_clr C) x = c)"
  using cl_range3 clrD2b by blast


lemma cl_range5:
  "is_clr C X \<Longrightarrow> x \<in> C  \<Longrightarrow> x \<in>  cl_from_clr C ` X"
  using cl_range3b by blast

lemma clr_induced_closure_id:
  "is_clr C X  \<Longrightarrow>  (cl_from_clr C)`X = C"
   by (rule order_antisym, auto simp add: cl_range2 cl_range5)

lemma cl_ext1:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> x \<le> (cl_from_clr C) x"
  by (metis ubdD1 cl_from_clr_def clrD3 least_exD1 singletonI)

lemma cl_ext2:
  "is_clr C X \<Longrightarrow> is_extensive X (cl_from_clr C)"
  by (simp add: cl_ext1 is_extensive_def)

lemma cl_lt_ub1:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> c \<in> ubd C {x} \<Longrightarrow> (cl_from_clr C) x \<le> c"
  by (simp add: cl_from_clr_def clrD3 least_exD2)

lemma cl_lt_ub2:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> c \<in> C \<Longrightarrow> x \<le> c \<Longrightarrow> (cl_from_clr C) x \<le> c"
  by (simp add: ubd_singleton2 cl_lt_ub1)

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
  "is_closure X f \<Longrightarrow>x \<in> X \<Longrightarrow> (f x) \<in> (ubd (f`X) {x})"
  by (simp add: ubd_singleton2 closureD5)

lemma closure_of_lt_ub:
  "is_closure X f \<Longrightarrow>x \<in> X \<Longrightarrow> y \<in>  (ubd (f`X) {x}) \<Longrightarrow> (f x) \<le> y"
  by (simp add: closureD7 ubd_singleton_iff)

lemma closure_of_least_closed1:
  "is_closure X f \<Longrightarrow> x \<in> X \<Longrightarrow> is_least (ubd (f`X) {x}) (f x)"
  by (simp add: closure_of_in_ub closure_of_lt_ub leastI3)

lemma closure_of_least_closed2:
  "is_closure X f \<Longrightarrow> x \<in> X \<Longrightarrow> Least (ubd (f`X) {x}) =  (f x)"
  by (simp add: closure_of_in_ub closure_of_lt_ub least_equality2 least_iff)

lemma closure_induced_clr:
  "is_closure X f \<Longrightarrow> X \<noteq> {} \<Longrightarrow> is_clr (f`X) X"
  by (metis closure_iff2 closure_of_least_closed1 clrI1 empty_is_image)

lemma closure_induced_clr_id:
  "is_closure X f \<Longrightarrow> X \<noteq> {} \<Longrightarrow> x  \<in> X \<Longrightarrow> (cl_from_clr (f`X)) x = f x"
  by (simp add: cl_from_clr_def closure_of_least_closed2)

lemma closure_induced_clr_dual:
  "is_closure X f1 \<Longrightarrow> is_closure X f2 \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> f1 x \<le> f2 x) \<Longrightarrow> (f2`X) \<subseteq> (f1`X)"
  by (metis closureD11 closureD2 idempotentD3 is_closure_def subsetI)
                    
lemma clr_induced_closure_dual:
  "is_clr C1 X \<Longrightarrow> is_clr C2 X \<Longrightarrow> C2 \<subseteq> C1 \<Longrightarrow>  x \<in> X \<Longrightarrow> ((cl_from_clr C1) x) \<le> ((cl_from_clr C2) x)"
  by (simp add: cl_ext1 cl_lt_ub2 cl_range1 subsetD)


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
  "is_clr C X \<Longrightarrow> A \<subseteq> C  \<Longrightarrow> is_inf X A i \<Longrightarrow> (cl_from_clr C) i \<in> lbd X A"
  by(simp add: lbdI cl_is_closure cl_lt_ub2 closureD1 in_mono is_infE1 is_infE7)

lemma clrD9:
  "is_clr C X \<Longrightarrow> A \<subseteq> C \<Longrightarrow> is_inf X A i \<Longrightarrow> (cl_from_clr C) i \<le> i"
  by (simp add: clrD8 is_infE3)

lemma clrD10:
  "is_clr C X \<Longrightarrow> A \<subseteq> C  \<Longrightarrow> is_inf X A i \<Longrightarrow>  (cl_from_clr C) i = i"
  by (simp add: cl_ext1 clrD9 is_infE1 order_antisym)

lemma clrD11:
  "is_clr C X \<Longrightarrow> A \<subseteq> C  \<Longrightarrow> is_inf X A i \<Longrightarrow>  i \<in> C"
  by (metis cl_range1 clrD10 is_infE1)

lemma moore_clI1:
  "C \<subseteq> Pow X \<Longrightarrow> (\<And>E. E \<subseteq> C \<Longrightarrow> (X \<inter> (\<Inter>E)) \<in> C) \<Longrightarrow> x \<in> Pow X \<Longrightarrow> is_least (ubd C {x})  (X \<inter> (\<Inter>(ubd C {x}))) "
  by(auto simp add:is_clr_def is_least_def ubd_def lbd_def ub_def lb_def)

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

lemma clr_clattice1:
  assumes A0:"is_clr C X" and A1:"is_clattice X"
  shows "\<And>A. A \<subseteq> C \<longrightarrow> (\<exists>x. is_sup C A x \<and> is_inf X (ubd C A) x)"
proof
  fix A assume A2:"A \<subseteq> C"
  obtain x where B0:"is_inf X (ubd C A) x"
    by (meson A0 A1 ubd_sub clatD22 is_clr_def order_trans)
  have B1:"is_sup C A x"
    by (meson A0 A2 B0 ubd_sub clrD11 clrD2 inf_in_subset sup_if_inf_ub)
  show "(\<exists>x. is_sup C A x \<and> is_inf X (ubd C A) x)"
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
subsection GeneralDirectedness  
definition is_dir::"'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "is_dir X ord \<equiv> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>c \<in> X. ord a c \<and> ord b c))"

lemma is_dir_singleton:
  assumes "\<forall>x. ord x x"
  shows "is_dir {x} ord"
  by (simp add: assms is_dir_def)

lemma is_dirE1:
  "is_dir X ord \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>c \<in> X. ord a c \<and> ord b c))"
  by (simp add: is_dir_def)  

lemma is_dirI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. ord a c \<and> ord b c)) \<Longrightarrow> is_dir X ord"
  by (simp add: is_dir_def)

lemma dir_finite1:
  assumes A0: "\<And>a1 a2. \<lbrakk>a1 \<in>X;  a2 \<in> X\<rbrakk> \<Longrightarrow> (\<exists>c \<in> X. ord a1 c \<and> ord a2 c)" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X"  and
          A4:"transp_on X ord" 
  shows " (\<exists>c \<in> X. \<forall>a. a \<in> A \<longrightarrow>ord a c)"  
  using A1 A2 A3 A4 A0
proof (induct A rule: finite_ne_induct)
case (singleton x) then show ?case by auto
next  
  case (insert x F)
  then obtain c0 where "c0 \<in> X" and Fc0:"(\<forall>a. a \<in> F \<longrightarrow> ord a c0)" by blast
  then obtain "x \<in> X" and c0mem:"c0 \<in> X"  using insert.prems(1) by blast
  then obtain c1 where c1mem:"c1 \<in> X" and xc1:"ord x c1" and c0c1:"ord c0 c1"  using A0 by blast
  obtain fsub:"F \<subseteq> X"  using insert.prems(1) by auto
   have "\<And>a. a \<in> (insert x F) \<Longrightarrow> ord a c1"
  proof-
    fix a assume "a \<in> (insert x F)"
    show "ord a c1"
    proof(cases "a \<in> F")
      case True  then obtain "ord a c0" using Fc0 by auto
      also obtain "a \<in> X"   using True fsub by blast
      then show ?thesis using c0c1 c0mem c1mem A4    by (meson calculation transp_onD)
    next
      case False then show ?thesis using \<open>(a::'a::type) \<in> insert (x::'a::type) (F::'a::type set)\<close> xc1 by blast 
    qed
   qed
   then show ?case using c1mem by blast 
qed
  

subsection UpDirectedness

lemma is_updirI1:
  assumes "\<And>A. \<lbrakk>A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. c ub A)"
  shows "is_dir X (\<le>)"
proof(rule is_dirI1)
  show "\<And>a b. a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> \<exists>c\<in>X. a \<le> c \<and> b \<le> c"
  proof-
    fix a b assume "a \<in> X" and "b \<in> X"
    then obtain "{a, b} \<subseteq> X" and "finite {a, b}" and "{a, b} \<noteq> {}"   by blast
    then obtain c where "c \<in> X" and "c ub {a, b}" using assms[of "{a,b}"] by auto
    then obtain "c \<in> X" and "a \<le> c" and "b \<le> c" using ub_doubleE1 ub_doubleE2 by blast
    then show "\<exists>c\<in>X. a \<le> c \<and> b \<le> c" by auto
  qed
qed


lemma updir_finite1:
  assumes A0: "\<And>a1 a2. a1 \<in> (X::'a::order set) \<Longrightarrow> a2 \<in> X \<Longrightarrow>  (\<exists>c \<in> X. a1 \<le> c \<and> a2 \<le> c)" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X"
  shows " (\<exists>c \<in> X. \<forall>a. a \<in> A \<longrightarrow> a \<le> c)"
  using A0 A1 A2 A3
proof(rule dir_finite1)
  show "\<And>(a1::'a) a2::'a. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> a1 \<in> X" by simp
  show "\<And>(a1::'a) a2::'a. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> a2 \<in> X" by simp
  show "transp_on X (\<le>)" by simp
qed        


lemma updir_finite2:
  assumes dir:"is_dir (X::'a::order set) (\<le>)" and
          sub:"A \<subseteq> X" and
          fin:"finite A" and
          nem:"A \<noteq> {}"
  shows "(\<exists>c \<in> X. c ub A)"
proof-
  obtain "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>c \<in> X.  a \<le> c \<and>  b \<le> c))"  using dir is_dirE1[of X "(\<le>)"] by blast  
  then obtain c where "c \<in> X" and "\<forall>a. a \<in> A \<longrightarrow> a \<le> c" using dir sub fin nem updir_finite1[of X A] by blast
  then show "(\<exists>c \<in> X. c ub A)"  using ubI by blast
qed


subsection DownDirectedness




lemma is_dwdirI2:
  assumes exi:"(\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>i. is_inf X {a, b} i))"
  shows "is_dir X (\<ge>)"
proof(rule is_dirI1)
  show "\<And>a b. a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> \<exists>c\<in>X. c \<le> a \<and> c \<le> b"
  proof-
    fix a b assume "a \<in> X" and "b \<in> X" 
    then obtain i where "is_inf X {a,b} i" using assms[of a b] by blast
    then obtain "i \<in> X" and "i \<le> a" and "i \<le> b" by (simp add: is_infD1121 is_infE1)
    then show "\<exists>c\<in>X. c \<le> a \<and> c \<le> b" by auto
  qed
qed




subsection OrderClosure

definition is_ord_cl::"'a set \<Rightarrow> 'a set \<Rightarrow>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "is_ord_cl X A ord \<equiv> (\<forall>a b. a \<in> A \<and> b \<in> X \<and> ord a b \<longrightarrow> b \<in> A )"

lemma is_ord_clE:
  "is_ord_cl X A ord \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> A; b \<in> X; ord a b\<rbrakk> \<Longrightarrow> b \<in> A)" 
  by(simp add:is_ord_cl_def)

lemma is_ord_clI:
  "(\<And>a b. \<lbrakk>a \<in> A; b \<in> X; ord a b\<rbrakk> \<Longrightarrow> b \<in> A) \<Longrightarrow> is_ord_cl X A ord" 
  by(auto simp add:is_ord_cl_def)

lemma is_ord_cl_empty:
  "is_ord_cl X {} ord"
  by (simp add: is_ord_cl_def) 

lemma is_ord_cl_space:
  "is_ord_cl X X ord"
  by (simp add: is_ord_cl_def)

lemma is_ord_cl_comp1:
  "is_ord_cl X A ord \<Longrightarrow> is_ord_cl X (X-A) (\<lambda>a b. ord b a)"
  by(rule is_ord_clI,auto dest: is_ord_clE)

lemma is_ord_cl_comp2:
  "A \<subseteq> X \<Longrightarrow> is_ord_cl X (X-A) (\<lambda>a b. ord b a) \<Longrightarrow> is_ord_cl X A ord"
  by(rule is_ord_clI,auto dest: is_ord_clE)

lemma is_ord_cl_iff_comp:
  "A \<subseteq> X \<Longrightarrow> is_ord_cl (X::'a::order set) A ord \<longleftrightarrow> is_ord_cl (X::'a::order set) (X-A) (\<lambda>a b. ord b a) "
  using is_ord_cl_comp1 is_ord_cl_comp2 by blast

lemma is_ord_cl_un:
  assumes fam:"A \<in> (Pow (Pow X))" and ocl:"(\<And>a. a \<in> A \<Longrightarrow> is_ord_cl X a ord) "
  shows "is_ord_cl X (\<Union>A) ord"
proof(rule is_ord_clI)
  show "\<And>a b. a \<in> \<Union> A \<Longrightarrow> b \<in> X \<Longrightarrow> ord a b \<Longrightarrow> b \<in> \<Union> A"
  proof-
    fix a b assume amem:"a \<in> \<Union> A" and bmem:"b \<in> X" and ab:"ord a b"
    from amem ocl obtain Ai where aimem:"Ai \<in> A" and "a \<in> Ai" and "is_ord_cl X Ai ord" by auto
    then obtain "b \<in> Ai" using bmem ab is_ord_clE[of X Ai ord a b] by auto
    then show "b \<in> \<Union> A" using aimem by blast
  qed
qed

lemma is_ord_cl_in:
  assumes fam:"A \<in> (Pow (Pow X))" and ocl:"(\<And>a. a \<in> A \<Longrightarrow> is_ord_cl X a ord) "
  shows "is_ord_cl X (\<Inter>A) ord"
proof(rule is_ord_clI)
  show "\<And>a b. a \<in> \<Inter> A \<Longrightarrow> b \<in> X \<Longrightarrow> ord a b \<Longrightarrow> b \<in> \<Inter> A"
  proof-
    fix a b assume amem:"a \<in> \<Inter>A" and bmem:"b \<in> X" and ab:"ord a b"
    then have "\<And>Ai. Ai \<in> A \<Longrightarrow> b \<in> Ai"
    proof-
      fix Ai assume "Ai \<in> A"
      then obtain "is_ord_cl X Ai ord" and "a \<in> Ai" and "b \<in> X" and "ord a b"   using ab amem bmem ocl by auto  
      then show "b \<in> Ai" using is_ord_clE[of X Ai ord a b] by auto
   qed
   then show "b \<in> \<Inter> A"  by simp 
  qed
qed

lemma ord_cl_dwdir_inf:
  assumes A0:"A \<subseteq> X" and A1:"is_dir A (\<ge>)" and A2:"is_ord_cl X A (\<le>)"
  shows "\<And>a b. \<lbrakk>a \<in> A; b \<in> A;  is_inf X {a, b} i\<rbrakk> \<Longrightarrow> i \<in> A"
proof-
  fix a b assume amem:"a \<in> A" and bmem:"b \<in> A" and glb:"is_inf X {a, b} i"
  then obtain c where cmem:"c \<in> A" and ca:"c \<le> a" and cb:"c \<le> b" using A1 is_dirE1[of A "(\<ge>)" a b] by blast
  then obtain ci:"c \<le> i" using glb  A0 is_infD42 lb_insert lb_singletonD by blast
  obtain imem:"i \<in> X"   using glb is_infE1 by blast
  then show "i \<in> A" using cmem ci A2 is_ord_clE[of X A "(\<le>)" c i] by blast
qed

lemma ord_cl_dwdir_inf_in:
  assumes A0:"\<A> \<in> Pow (Pow X)" and 
          A1:"\<And>A. A \<in> \<A> \<Longrightarrow> is_dir A (\<ge>)" and
          A2:"\<And>A. A \<in> \<A> \<Longrightarrow> is_ord_cl X A (\<le>)" 
  shows "\<And>a b. \<lbrakk>a \<in> \<Inter>\<A>; b \<in> \<Inter>\<A>;  is_inf X {a, b} i\<rbrakk> \<Longrightarrow> i \<in> \<Inter>\<A>"
proof-
  let ?I=" \<Inter>\<A>"
  fix a b assume a0:"a \<in> ?I" and b0:"b \<in> ?I" and i0:"is_inf X {a, b} i"
  have P0:"\<And>A. A \<in> \<A> \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> A; b \<in> A;  is_inf X {a, b} i\<rbrakk> \<Longrightarrow> i \<in> A)"
  proof-
    fix A assume "A \<in> \<A>" 
    then obtain "A \<subseteq> X" and "is_dir A (\<ge>)" and "is_ord_cl X A (\<le>)" using A0 A1 A2 by blast
    then show "(\<And>a b. \<lbrakk>a \<in> A; b \<in> A;  is_inf X {a, b} i\<rbrakk> \<Longrightarrow> i \<in> A)" using ord_cl_dwdir_inf[of A X] by blast
  qed
  then have "\<And>A. A \<in> \<A> \<Longrightarrow> i \<in> A"
  proof-
    fix A assume Amem:"A \<in> \<A>" 
    then obtain "\<And>a b. \<lbrakk>a \<in> A; b \<in> A;  is_inf X {a, b} i\<rbrakk> \<Longrightarrow> i \<in> A" using P0 by blast
    then show "i \<in> A"  using Amem a0 b0 i0 by blast
  qed
  then show "i \<in> ?I" by blast
qed


lemma up_cl_bot:
  assumes bot:"is_least X bot" and sub:"A \<subseteq> X" and ocl:"is_ord_cl X A (\<le>)" and bin:"bot \<in> A"
  shows "A=X"
proof
  show "A \<subseteq> X" using sub by simp next
  show "X \<subseteq> A"
  proof
    fix x assume xmem:"x \<in> X" then obtain "bot \<in> A" and "bot \<le> x"   using bin bot leastD2 by blast
    then show "x \<in> A" using is_ord_clE[of X A "(\<le>)" "bot" x] ocl xmem by blast  
  qed
qed
  

subsection Filters
subsection DefinitionAndBasicProps

definition is_filter::"'a::order set\<Rightarrow> 'a::order set \<Rightarrow> bool" where 
  "is_filter X F \<equiv> F \<noteq> {} \<and> F \<subseteq> X \<and> (is_dir F (\<ge>)) \<and> is_ord_cl X F (\<le>)"

lemma is_filterI1:
  "\<lbrakk> F \<noteq> {}; F \<subseteq> X; (is_dir F (\<ge>));  (is_ord_cl X F (\<le>))\<rbrakk> \<Longrightarrow> is_filter X F"
  by (simp add: is_filter_def)

lemma is_filterE1:
  "is_filter X F \<Longrightarrow> F \<noteq> {} \<and> F \<subseteq> X \<and> (is_dir F (\<ge>)) \<and> is_ord_cl X F (\<le>)"
  by (simp add: is_filter_def)

lemma is_filter_top:
  assumes top:"is_greatest X top" and fil:"is_filter X F"
  shows "top \<in> F"
proof-
  obtain f where fmem1:"f \<in> F" using fil is_filterE1 by fastforce
  then obtain fmem2:"f \<in> X" using fil is_filterE1 by blast
  then obtain "top \<in> X" and "f \<le> top" using top  by (simp add: greatest_iff)
  then show "top \<in> F" using is_ord_clE[of X F "(\<le>)" f top] fil fmem1 is_filterE1 by blast 
qed


definition is_pfilter::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where 
  "is_pfilter X A \<equiv> (is_filter X A) \<and> X \<noteq> A"

lemma is_pfilterI1:
  "\<lbrakk>is_filter X A; A \<noteq> X\<rbrakk> \<Longrightarrow> is_pfilter X A" 
  by (simp add: is_pfilter_def)

lemma is_pfilterE1:
  "is_pfilter X A \<Longrightarrow> is_filter X A \<and> X \<noteq> A"  
  by (simp add: is_pfilter_def)


subsection FiniteInfClosure

lemma filter_finf_closed:
  assumes fil:"is_filter X F" 
  shows "\<And>a b. \<lbrakk>a \<in> F; b \<in> F;  is_inf X {a, b} i\<rbrakk> \<Longrightarrow> i \<in> F"
  using ord_cl_dwdir_inf[of F X] fil is_filterE1 by blast

lemma filter_finf_closed_isl:
  assumes fil:"is_filter X F"  and isl:"is_inf_semilattice X"
  shows "\<And>a b. \<lbrakk>a \<in> F; b \<in> F\<rbrakk> \<Longrightarrow> Inf X {a,b} \<in> F"
proof-
  fix a b assume a0:"a \<in> F" and b0:"b \<in> F" 
  then obtain a1:"a \<in> X" and b1:"b \<in> X"  using fil is_filterE1 by blast
  then obtain i0:"is_inf X {a,b} (Inf X {a, b})" by (simp add: isl sinfD3)
  then show "Inf X {a,b} \<in>F" using a0 b0 fil filter_finf_closed[of X F a b "Inf X {a,b}"] i0 by auto
qed


lemma filter_finf_closed3:
  "\<lbrakk>is_inf_semilattice X; is_filter X F; A \<subseteq> F; A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow> Inf X A \<in> F"
  by (simp add: is_filter_def filter_finf_closed_isl finite_inf_closed2)



lemma min_filter1:
  "is_greatest X top \<Longrightarrow> is_filter X {top}"
  by (simp add: is_filter_def greatest_iff is_dir_def is_ord_cl_def order_antisym)

lemma filters_max:
  "is_inf_semilattice X \<Longrightarrow> is_filter X X"
  by (simp add: is_filter_def is_dwdirI2 is_inf_semilattice_def is_ord_cl_def)



section SetOfFilters

definition filters_on::"'a::order set \<Rightarrow> 'a::order set set" where
  "filters_on X \<equiv> {F. is_filter X F}"

lemma filters_onI:
  "is_filter X F \<Longrightarrow> F \<in> filters_on X"
  by(simp add:filters_on_def)

lemma filters_onE:
  "F \<in> filters_on X \<Longrightarrow> is_filter X F"
  by(simp add:filters_on_def)

lemma filters_on_iff:
  "F \<in> filters_on X \<longleftrightarrow> is_filter X F"
  by (simp add: filters_on_def)

lemma filter_inter_double:
  assumes isl:"is_inf_semilattice X" and
          ef0:"EF \<in> Pow_ne (filters_on X)" and 
          x0:"x \<in> \<Inter>EF" and 
          y0:"y \<in> \<Inter>EF" and 
          f0:"F \<in> EF"
  shows "Inf X {x, y} \<in> F"
proof-
  from x0 y0 f0 obtain x1:"x \<in> F" and x2:"y \<in> F" by blast
  from ef0 f0 obtain f1:"is_filter X F"   by (simp add: filters_on_iff pow_ne_iff2 subset_eq)
  then show "Inf X {x, y} \<in> F" using x1 x2 isl filter_finf_closed[of X F x y "Inf X {x, y}"]  using binfI is_filterE1 by blast
qed

lemma filter_inter_dir:
  assumes isl:"is_inf_semilattice X" and
          ef0:"EF \<in> Pow_ne (filters_on X)" 
  shows "is_dir (\<Inter>EF) (\<ge>)"
proof(rule is_dirI1)
show " \<And>a b. a \<in> \<Inter> EF \<Longrightarrow> b \<in> \<Inter> EF \<Longrightarrow> \<exists>c\<in>\<Inter> EF. c \<le> a \<and> c \<le> b"
  proof-
    fix a b assume a0:"a \<in> \<Inter> EF" and b0:"b \<in> \<Inter>EF" 
    then obtain i0:"Inf X {a, b} \<in> \<Inter>EF" using isl ef0 filter_inter_double[of X EF a b] by blast
    from ef0 obtain ef1: "EF \<subseteq> filters_on X" and ef2:"EF \<noteq> {}" by (simp add: pow_ne_iff2)
    then obtain "\<And>E. E \<in> EF \<Longrightarrow> is_filter X E" by (simp add: filters_onE subsetD)
    then obtain "\<And>E. E \<in> EF \<Longrightarrow> E \<subseteq> X"   by (simp add: is_filterE1)
    then obtain a1:"a \<in> X" and b1:"b \<in> X" using a0 b0 ef2 by blast
    then obtain "Inf X {a, b} \<le> a" and "Inf X {a, b} \<le> b"  by (simp add: binf_leI1 binf_leI2 isl)
    then show "\<exists>c\<in>\<Inter> EF. c \<le> a \<and> c \<le> b" using i0 by blast
  qed
qed


lemma inter_filters_filter:
  assumes isl:"is_inf_semilattice X" and
          ef0:"EF \<in> Pow_ne (filters_on X)"  and
          top:"is_greatest X top"
  shows "is_filter X (\<Inter>EF)"
proof(rule is_filterI1)
  from ef0 obtain ef1:"\<And>E. E \<in> EF \<Longrightarrow> is_filter X E"  using filters_on_iff pow_neD1 by blast
  then obtain ef2:"\<And>E. E \<in> EF \<Longrightarrow> top \<in> E" using top is_filter_top by blast
  then show "\<Inter> EF \<noteq> {}" by blast
  obtain ef3:"\<And>E. E \<in> EF \<Longrightarrow> E \<subseteq> X" and "EF \<noteq> {}"  using ef1 ef0  by (simp add: is_filterE1 pow_ne_iff2)
  then show "\<Inter> EF \<subseteq> X" by blast
  show "is_dir (\<Inter> EF) (\<lambda>x y. y \<le> x)" using isl ef0 filter_inter_dir[of X EF] by blast
  obtain ef4:"\<And>E. E \<in> EF \<Longrightarrow> is_ord_cl X E (\<le>)" by (simp add: ef1 is_filterE1)
  show "is_ord_cl X (\<Inter> EF) (\<le>)"
  proof(rule is_ord_cl_in)
    show "EF \<in> Pow (Pow X)"  by (simp add: ef3 subsetI)
    show "\<And>a. a \<in> EF \<Longrightarrow> is_ord_cl X a (\<le>)"  by (simp add: ef4)
  qed
qed


section SetOfProperFilters
definition pfilters_on::"'a::order set \<Rightarrow> 'a::order set set" where
  "pfilters_on X \<equiv> {F. is_pfilter X F}"

lemma pfilters_onI:
  "is_pfilter X F \<Longrightarrow> F \<in> pfilters_on X"
  by(simp add:pfilters_on_def)

lemma pfilters_onE:
  "F \<in> pfilters_on X \<Longrightarrow> is_pfilter X F"
  by(simp add:pfilters_on_def)

lemma pfilters_on_iff:
  "F \<in> pfilters_on X \<longleftrightarrow> is_pfilter X F"
  by (simp add: pfilters_on_def)

section MaximalityInFilters


lemma maximal_pfiltersD1:
  "is_maximal (pfilters_on X) F \<Longrightarrow> H \<in>pfilters_on X \<Longrightarrow> F \<subseteq> H \<Longrightarrow> F=H  "
  using maximalD2 by blast

lemma maximal_pfiltersI1:
  "\<lbrakk>F \<in> pfilters_on X; (\<And>H. \<lbrakk>H  \<in> pfilters_on X; F \<subseteq> H\<rbrakk> \<Longrightarrow> F =H)\<rbrakk> \<Longrightarrow>  is_maximal (pfilters_on X) F "
  using maximalI1[of F "pfilters_on X"]  by auto

lemma maximal_pfiltersI2:
  "\<lbrakk>F \<in> pfilters_on X; (\<And>H. \<lbrakk>H  \<in> pfilters_on X; F \<subseteq> H\<rbrakk> \<Longrightarrow> F \<supseteq> H)\<rbrakk> \<Longrightarrow>  is_maximal (pfilters_on X) F "
  by (simp add: is_maximal_def)


lemma filter_is_clr:
  assumes isl:"is_inf_semilattice X" and top:"is_greatest X top" and nem:"X \<noteq> {}"
  shows "is_clr (filters_on X) (Pow X)"
proof(rule moore_clI3)
  show "filters_on X \<subseteq> Pow X"  by(auto simp add:filters_on_def is_filter_def)
  show "X \<in> filters_on X"  by (simp add: filters_max filters_on_iff isl)
  show "\<And>E. E \<subseteq> filters_on X \<Longrightarrow> E \<noteq> {} \<Longrightarrow> \<Inter> E \<in> filters_on X"  using filters_onI inter_filters_filter isl pow_ne_iff2 top by blast
qed

subsection FilterClosure

definition filter_closure::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "filter_closure X A \<equiv> if A={} then {Greatest X} else {x \<in> X. \<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and> Inf X F \<le> x}"

lemma filter_closure_ne_simp:
  "A \<noteq> {} \<Longrightarrow> filter_closure X A = {x \<in> X. \<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and> Inf X F \<le> x}"
  by (simp add: filter_closure_def)

lemma filter_closure_memI1:
  "\<lbrakk>A \<noteq> {}; x \<in> X; (\<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and> Inf X F \<le> x)\<rbrakk> \<Longrightarrow> x \<in>  filter_closure X A"
  by (simp add: filter_closure_ne_simp)

lemma filter_closure_memI2:
  "\<lbrakk>A \<noteq> {}; x \<in> X; F \<subseteq> A; finite F; F \<noteq> {}; Inf X F \<le> x\<rbrakk> \<Longrightarrow> x \<in>  filter_closure X A"
  using filter_closure_memI1 by blast
  

lemma filter_closure_memE1:
  "\<lbrakk>x \<in>  filter_closure X A; A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and> Inf X F \<le> x)"
  by (simp add: filter_closure_ne_simp) 


lemma filter_closure_singleton:
  assumes sub:"A \<subseteq> X"
  shows "A \<subseteq> filter_closure X A"
proof
  fix a assume a0: "a \<in> A" then obtain a1:"a \<in> X" and a6:"A \<noteq> {}" using sub by auto 
  then obtain a2:"{a}\<subseteq>A" and a3:"finite {a}" and a4:"{a} \<noteq> {}" and a5:"Inf X {a} \<le> a" by (simp add: a0 inf_singleton2)
  then show "a \<in> filter_closure X A" using a6 a1 filter_closure_memI2[of A a X "{a}"] by blast
qed

lemma filter_closure_filter:
  assumes isl:"is_inf_semilattice X" and sub:"A \<subseteq> X"  and nem:"A \<noteq> {}"
  shows "is_filter X (filter_closure X A)"
proof(rule is_filterI1)
  show "filter_closure X A \<noteq> {}"  using filter_closure_singleton nem sub by blast
  show " filter_closure X A \<subseteq> X"  by (simp add: filter_closure_ne_simp nem) 
  show "is_dir (filter_closure X A) (\<lambda>x y. y \<le> x)"
  proof(rule is_dirI1)
    show "\<And>a b. a \<in> filter_closure X A \<Longrightarrow> b \<in> filter_closure X A \<Longrightarrow> \<exists>c\<in>filter_closure X A. c \<le> a \<and> c \<le> b"
    proof-
      fix a b assume a0:"a \<in> filter_closure X A" and b0:"b \<in> filter_closure X A "
      obtain Fa  where a1:"Fa \<subseteq> A" and  a2:"finite Fa" and a3:"Fa \<noteq> {}" and a4:"Inf X Fa \<le> a" 
         using a0 nem filter_closure_memE1[of a X A] by blast
      obtain Fb where  b1:"Fb \<subseteq> A" and  b2:"finite Fb" and b3:"Fb \<noteq> {}" and b4:"Inf X Fb \<le> b" 
        using b0 nem filter_closure_memE1[of b X A] by blast
      let ?Fab="Fa \<union> Fb"
      obtain fab1:"?Fab \<subseteq> A" and fab2:"finite ?Fab" and fab3:"?Fab \<noteq> {}" and  fab4:"Inf X ?Fab \<le> Inf X ?Fab"   by (simp add: a1 a2 a3 b1 b2)
      obtain fab0:"?Fab \<subseteq> X" using fab1 sub by auto
      then obtain fab5:"Inf X ?Fab \<in> X" using fab2 fab3 isl is_infE1 binf_finite2 by blast
      then have i0:"Inf X ?Fab \<in> filter_closure X A" 
        using filter_closure_memI2[of A "Inf X ?Fab" X "?Fab"] fab1 fab2 fab3 fab4 fab5   by blast
      obtain "Fa \<subseteq> ?Fab" and "Fb \<subseteq> ?Fab"  by simp 
      then obtain i1:"Inf X ?Fab \<le> Inf X Fa" and i2:"Inf X ?Fab \<le> Inf X Fb"  by (meson a2 a3 b2 b3 dual_order.trans fab0 fab2 fab3 fpow_neI inf_semilattice_finf_anti isl)
      then obtain i3:"Inf X ?Fab \<le> a" and i4:"Inf X ?Fab \<le> b"   using a4 b4 dual_order.trans by blast
      then show "\<exists>c\<in>filter_closure X A. c \<le> a \<and> c \<le> b" using i0 by blast
    qed
  qed
  show "is_ord_cl X (filter_closure X A) (\<le>)"
  proof(rule is_ord_clI)
    show "\<And>a b. a \<in> filter_closure X A \<Longrightarrow> b \<in> X \<Longrightarrow> a \<le> b \<Longrightarrow> b \<in> filter_closure X A"
    proof-
      fix a b assume a0:"a \<in> filter_closure X A" and b0:"b \<in> X" and ab0:"a \<le> b"
      then obtain Fa where a1:"Fa \<subseteq> A" and  a2:"finite Fa" and a3:"Fa \<noteq> {}" and a4:"Inf X Fa \<le> a" 
         using a0 nem filter_closure_memE1[of a X A] by blast
      then obtain b4:"Inf X Fa \<le> b" using a4 ab0 by force
      then show "b \<in> filter_closure X A"  using a1 a2 a3 b0 filter_closure_memI1 by blast
    qed
  qed
qed

lemma filter_closure_lub:
  assumes isl:"is_inf_semilattice X" and sub:"A \<subseteq> X"  and nem:"A \<noteq> {}"
  shows "is_least (ubd (filters_on X) {A}) (filter_closure X A)"
proof(rule leastI3)
  show "\<And>a. a \<in> ubd (filters_on X) {A} \<Longrightarrow> filter_closure X A \<subseteq> a"
  proof-
    fix a assume a0:" a \<in> ubd (filters_on X) {A}"
    then obtain a1:"is_filter X a" and a2:"A \<subseteq> a"  by (simp add: filters_onE ubd_singleton_iff)
    show "filter_closure X A \<subseteq> a"
    proof
      fix x assume x0:"x \<in> filter_closure X A"
      then obtain Fx where x1:"Fx \<subseteq> A" and  x2:"finite Fx" and x3:"Fx \<noteq> {}" and x4:"Inf X Fx \<le> x" 
         using x0 nem filter_closure_memE1[of x X A] by blast
      then obtain x5:"Fx \<subseteq> a" and x6:"Fx \<subseteq> X" using a2 sub by auto
      then obtain x7:"Inf X Fx \<in> a" using x2 x3 x6 isl filter_finf_closed3 a1 by blast
      obtain x8:"x \<in> X"   using filter_closure_filter is_filterE1 isl nem sub x0 by blast
      show "x \<in> a" using is_ord_clE[of X a "(\<le>)" "Inf X Fx" x]  a1 is_filterE1 x4 x7 x8 by blast
    qed
  qed
  show "filter_closure X A \<in> ubd (filters_on X) {A}"
  proof(rule ubdI)
  show "\<And>a. a \<in> {A} \<Longrightarrow> a \<subseteq> filter_closure X A"
  proof-
    fix a assume "a \<in> {A}" then obtain "a=A" by auto
    then show "a \<subseteq> filter_closure X A"  by (simp add: filter_closure_singleton sub)
  qed
  show "filter_closure X A \<in> filters_on X"  by (simp add: filter_closure_filter filters_onI isl nem sub)
  qed
qed


lemma filter_closure_empty:
  "is_greatest X top \<Longrightarrow> filter_closure X {} = {top}"
  by (simp add: filter_closure_def greatest_equality2)

lemma filter_closure_ne_lub:
  assumes isl:"is_greatest X top" 
  shows "is_least (ubd (filters_on X) {{}}) (filter_closure X {})"
proof(rule leastI3)
  show "\<And>a. a \<in> ubd (filters_on X) {{}} \<Longrightarrow> filter_closure X {} \<subseteq> a"
  proof-
    fix a assume a0:"a \<in> ubd (filters_on X) {{}}"
    obtain a1:"is_filter X a"  using a0 filters_onE ubdD2 by blast
    have a2:"filter_closure X {} = {top}"  by (simp add: filter_closure_empty isl)
    also have a3:"... \<subseteq> a"  using a1 is_filter_top isl by auto  
    then show "filter_closure X {} \<subseteq> a" by (simp add: calculation) 
  qed
  show "filter_closure X {} \<in> ubd (filters_on X) {{}}"
  proof(rule ubdI)
    show "\<And>a. a \<in> {{}} \<Longrightarrow> a \<subseteq> filter_closure X {}" by auto
    show " filter_closure X {} \<in> filters_on X"  using filter_closure_empty filters_onI isl min_filter1 by fastforce 
  qed
qed
 
lemma filters_on_lattice_inf02:
  assumes lat:"is_lattice X" and fil1:"is_filter X F1" and fil2:"is_filter X F2" and
          mem1:"f1 \<in> F1" and mem2:"f2 \<in> F2" 
  shows "Sup X {f1, f2} \<in> F1"
proof-
  obtain sub1:"F1 \<subseteq> X" and sub2:"F2 \<subseteq> X"   by (simp add: fil1 fil2 is_filterE1)
  obtain mem3:"f1 \<in> X" and mem4:"f2 \<in> X" using mem1 mem2 sub1 sub2 by auto
  obtain le1:"f1 \<le> Sup X {f1, f2}" and le2:"f2 \<le> Sup X {f1, f2}" by (meson bsup_geI1 bsup_geI2 lat lattD42 mem3 mem4 order_refl)
  then show "Sup X {f1, f2} \<in> F1"  by (metis (full_types) fil1 is_filterE1 is_ord_cl_def lat lattD42 mem1 mem3 mem4 ssupD4)
qed

lemma filters_on_lattice_inf03:
  assumes lat:"is_lattice X" and fil1:"is_filter X F1" and fil2:"is_filter X F2" and
          mem1:"f1 \<in> F1" and mem2:"f2 \<in> F2" 
  shows "Sup X {f1, f2} \<in> F1 \<inter> F2"
proof-
  obtain sub1:"F1 \<subseteq> X" and sub2:"F2 \<subseteq> X"   by (simp add: fil1 fil2 is_filterE1)
  obtain mem3:"f1 \<in> X" and mem4:"f2 \<in> X" using mem1 mem2 sub1 sub2 by auto
  obtain le1:"f1 \<le> Sup X {f1, f2}" and le2:"f2 \<le> Sup X {f1, f2}" by (meson bsup_geI1 bsup_geI2 lat lattD42 mem3 mem4 order_refl)
  then obtain "Sup X {f1, f2} \<in> F1" and "Sup X {f1, f2} \<in> F2"  by (metis bsup_commute2 fil1 fil2 filters_on_lattice_inf02 lat mem1 mem2 mem3 mem4)
  then show "Sup X {f1, f2} \<in> F1 \<inter> F2" by simp
qed

lemma filter_on_lattice_sup01: 
  "\<lbrakk>is_lattice X; is_filter X F; x \<in> X; y \<in> F\<rbrakk> \<Longrightarrow> Sup X {x, y} \<in> F"
  by (metis IntE filters_max filters_on_lattice_inf03 lattD41)


lemma filter_on_lattice_top0:
  "is_lattice X \<Longrightarrow> is_filter X {x} \<Longrightarrow> a \<in> X \<Longrightarrow> a \<le> x"
  by (meson is_filter_def bsup_iff filter_on_lattice_sup01 insertI1 latt_iff subsetD ubD ub_singleton)

lemma filter_inter_dwdir3:
  "\<lbrakk>is_inf_semilattice X; EF \<in> Pow_ne (filters_on X)\<rbrakk> \<Longrightarrow>is_dir (\<Inter>EF) (\<ge>)"
  by (simp add: filter_inter_dir)

lemma filter_inter_dir2:
  "\<lbrakk>is_inf_semilattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> is_dir (\<Inter>{F1, F2}) (\<ge>)"
  by(rule_tac ?X="X" in filter_inter_dwdir3, simp, simp add: filters_on_iff pow_ne_iff2)

lemma filter_inter_dir3:
  assumes "is_inf_semilattice X" "is_filter X F1" "is_filter X F2"
  shows "is_dir (F1 \<inter> F2) (\<ge>)"
  using assms filter_inter_dir2 by auto


lemma filters_on_lattice_inf5b:
  assumes lat:"is_lattice X" and fil1:"is_filter X F1" and fil2:"is_filter X F2"
  shows "is_filter X (F1 \<inter> F2)"
proof(rule is_filterI1)
   show "F1 \<inter> F2 \<noteq> {}" by (metis all_not_in_conv fil1 fil2 filters_on_lattice_inf03 is_filterE1 lat)
   show "F1 \<inter> F2 \<subseteq> X"  by (simp add: fil2 inf.coboundedI2 is_filterE1)
   show "is_dir (F1 \<inter> F2) (\<lambda>x y. y \<le> x)"  using fil1 fil2 filter_inter_dir3 lat lattD41 by auto
   show "is_ord_cl X (F1 \<inter> F2)(\<le>)" using is_ord_cl_in[of "{F1, F2}" X "(\<le>)"] fil1 fil2 is_filterE1 by auto
qed

lemma filters_on_lattice_inf6b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<in> (lbd (filters_on X) {F1, F2})"
  by (simp add: lbd_mem_iff filters_on_iff filters_on_lattice_inf5b lb_double_iff1)

lemma filters_on_lattice_inf7b:
  "\<lbrakk>is_filter X F1; is_filter X F2; G \<in> (lbd (filters_on X) {F1, F2})\<rbrakk>  \<Longrightarrow>  G \<subseteq>  (F1 \<inter> F2)"
  by (simp add: lbd_mem_iff lb_double_iff1)

lemma filters_on_lattice_inf8b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk>\<Longrightarrow> is_inf (filters_on X) {F1, F2} (F1 \<inter> F2)"
  by (meson filters_on_lattice_inf6b filters_on_lattice_inf7b is_infI5)

lemma filters_on_lattice_inf_semilattice1:
  "is_lattice X \<Longrightarrow> is_inf_semilattice (filters_on X)"
  by (metis emptyE filters_max filters_on_iff filters_on_lattice_inf8b is_inf_semilattice_def lattD41)


lemma filters_on_lattice_sup4b:
  "\<lbrakk>is_lattice X; (\<forall>F. F \<in> EF \<longrightarrow> is_filter X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> is_filter X (filter_closure X (\<Union>EF))"
  by (metis (no_types, opaque_lifting) Sup_bot_conv(2) all_not_in_conv cSup_least filter_closure_filter is_filterE1 lattD41)

lemma filters_on_lattice_sup5b:
  "\<lbrakk>(\<forall>F. F \<in> EF \<longrightarrow> is_filter X F); EF \<noteq> {}; F \<in> EF\<rbrakk> \<Longrightarrow>  F \<subseteq> (filter_closure X (\<Union>EF))"
  by (meson Sup_le_iff filter_closure_singleton is_filterE1)

lemma filters_on_lattice_sup6b:
  assumes A0:"is_lattice X" and A1:"(\<forall>F. F \<in> EF \<longrightarrow> is_filter X F)" and A2:"EF \<noteq> {}" and
          A3:"is_filter X G"  and A4:"(\<And>F. F \<in> EF \<Longrightarrow> F \<subseteq> G)"
  shows "filter_closure X (\<Union>EF) \<subseteq> G"
proof
  fix x assume A5:"x \<in> filter_closure X (\<Union>EF)"
  obtain Fx where  B1:"Fx \<subseteq>  (\<Union>EF) \<and> finite Fx \<and> Fx \<noteq> {} \<and> Inf X Fx \<le>x"
  by (metis A1 A2 A5 Pow_empty filter_closure_memE1 insertCI is_filterE1 subset_Pow_Union subset_singletonD)
  have B2:"Fx \<subseteq> G"
    using B1(1) A4  by blast
  have B3:"Fx \<subseteq> X"
    using B2 is_filter_def A3 by auto
  show "x \<in> G"
  by (smt (verit) A0 A1 A2 A3 A5 B1 B2 is_filter_def filter_finf_closed3 filters_on_lattice_inf02 filters_on_lattice_sup4b latt_ge_iff1 latt_iff subsetD)
qed


lemma filters_on_lattice_sup7b:
  "\<lbrakk>is_lattice X; (\<forall>F. F \<in> EF \<longrightarrow> is_filter X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> is_sup (filters_on X) EF (filter_closure X (\<Union>EF))"
  by(simp add:is_sup_def filters_on_lattice_sup4b filters_on_iff  ubd_mem_iff2  filters_on_lattice_sup5b filters_on_lattice_sup6b least_iff)

(*On a lattice filters form a complete sup semilattice*)

lemma filters_is_clr1b:
  "is_inf_semilattice X \<Longrightarrow> X \<in> filters_on X"
  by (simp add: filters_max filters_onI)

lemma filters_on_lattice_csup:
  "is_lattice X \<Longrightarrow> is_csup_semilattice (filters_on X)"
  by (metis empty_not_insert filters_is_clr1b filters_on_iff filters_on_lattice_sup7b insert_absorb insert_subset is_csup_semilattice_def lattD41)

lemma filters_on_lattice_sup_semilattice1b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> is_sup (filters_on X) {F1, F2} (filter_closure X (F1 \<union> F2))"
  by (metis Union_insert ccpo_Sup_singleton empty_not_insert filters_on_lattice_sup7b insertE singleton_iff)

lemma filters_on_lattice_sup_semilattice2b:
  "is_lattice X \<Longrightarrow> is_sup_semilattice (filters_on X)"
  by (metis filters_on_iff filters_on_lattice_inf_semilattice1 filters_on_lattice_sup_semilattice1b is_inf_semilattice_def is_sup_semilattice_def)


definition binary_filter_sup::"'a::order set \<Rightarrow>'a::order set\<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "binary_filter_sup X A B = {x \<in> X. \<exists>a \<in> A. \<exists>b \<in> B. Inf X {a, b} \<le> x}"

lemma filter_bsup_memD1:
  "x \<in> binary_filter_sup X A B \<Longrightarrow> x \<in> X" by (simp add:binary_filter_sup_def)

lemma filter_bsup_mem_iff:
  "x \<in> binary_filter_sup X A B \<longleftrightarrow> (x \<in> X \<and> (\<exists>a \<in> A. \<exists>b \<in> B. Inf X {a, b} \<le> x))"
  by (simp add:binary_filter_sup_def)

lemma binary_filter_sup_obtains:
  assumes A0:"a \<in>  (binary_filter_sup X F1 F2)"
  obtains a1 a2 where "a1 \<in> F1 \<and> a2 \<in> F2 \<and> Inf X {a1, a2} \<le> a"
  by (meson assms filter_bsup_mem_iff)

lemma filters_on_lattice_bsup01:
  assumes A0:"is_lattice X" and A1:"is_filter X F1" and A2:"is_filter X F2" and A3:"a \<in> F1"
  shows "a \<in> binary_filter_sup X F1 F2"
proof-
  obtain y where A4:"y \<in> F2"
  using A2 is_filterE1 by fastforce
  have B0:"Inf X {a, y} \<le> a" using A0 A1 A2 A3 A4 lattD41[of X] binf_leI1[of X a y a] using is_filter_def by blast
  show "a \<in> binary_filter_sup X F1 F2"
  by (meson A1 A3 A4 B0 filter_bsup_mem_iff in_mono is_filterE1)
qed

lemma filters_on_lattice_bsup02:
  assumes A0:"is_lattice X" and A1:"is_filter X F1" and A2:"is_filter X F2" and A3:"b \<in> F2"
  shows "b \<in> binary_filter_sup X F1 F2"
proof-
  obtain x where A4:"x \<in> F1"
  using A1 is_filterE1 by fastforce
  have B0:"Inf X {x, b} \<le> b"  by (metis A0 A1 A2 A3 A4 binf_leI2 dual_order.refl insert_subset is_filterE1 lattD41 mk_disjoint_insert)
  show "b \<in> binary_filter_sup X F1 F2"
  by (meson A0 A2 A3 A4 B0 filter_bsup_mem_iff filters_on_lattice_bsup01)
qed

lemma filters_on_lattice_bsup03:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> F1 \<subseteq> (binary_filter_sup X F1 F2)"
  by (simp add: filters_on_lattice_bsup01 subsetI)

lemma filters_on_lattice_bsup04:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> F2 \<subseteq> (binary_filter_sup X F1 F2)"
  by (simp add: filters_on_lattice_bsup02 subsetI)

lemma filters_on_lattice_bsup1b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow>  is_ord_cl X (binary_filter_sup X F1 F2) (\<le>)"
  apply(auto simp add:binary_filter_sup_def is_ord_cl_def) using dual_order.trans by blast

lemma tmp_inf_lemma:
  assumes "is_lattice X"  "a \<in> X" "a1 \<in> X" "a2 \<in> X" "b1 \<in> X" "b2 \<in> X" "Inf X {a1, a2} \<le> a" 
  shows " Inf X {Inf X {a1, b1}, Inf X {a2, b2}} \<le> a"
proof-
  have B0:"Inf X {Inf X {a1, b1}, Inf X {a2, b2}} = Inf X {a1, b1, a2, b2}"
    by (simp add: assms(1) assms(3-6) inf_semilattice_finf_props4 lattD41)
  have B1:"... \<le> Inf X {a1, a2}"
    using inf_semilattice_finf_anti[of X "{a1, a2}" "{a1, b1, a2, b2}"]
    by (simp add: assms(1) assms(3-6) fpow_ne_iff2 lattD41)
  have B2:"... \<le> a" by (simp add: assms(7)) 
  show ?thesis
    using B0 B1 B2 by auto
qed 
  

lemma filters_on_lattice_bsup2a:
  assumes A0:"is_lattice X" and A1:"is_filter X F1" and A2:"is_filter X F2" and
          A3: "a \<in>  (binary_filter_sup X F1 F2)" and  A4:"b \<in>  (binary_filter_sup X F1 F2)"
  shows "(\<exists>c \<in> (binary_filter_sup X F1 F2).  a \<ge> c \<and>  b \<ge> c)"
proof-
  obtain a1 a2 where B0:"a1 \<in> F1 \<and> a2 \<in> F2 \<and> Inf X {a1, a2} \<le> a"
    using A3 binary_filter_sup_obtains by blast
  obtain b1 b2 where B1:"b1 \<in> F1 \<and> b2 \<in> F2 \<and> Inf X {b1, b2} \<le> b"
    using A4 binary_filter_sup_obtains by blast
  have B0b:"a \<in> X \<and> b \<in> X \<and> a1 \<in> X \<and> a2 \<in> X \<and> b1 \<in> X \<and> b2 \<in> X"
  by (metis A1 A2 A3 A4 B0 B1 filter_bsup_mem_iff in_mono is_filterE1)
  have B2:"Inf X {Inf X {a1, b1}, Inf X {a2, b2}} \<le> a"
    using tmp_inf_lemma[of X a a1 a2 b1 b2]  using A0 B0 B0b by fastforce
  have B3:"Inf X {Inf X {a1, b1}, Inf X {a2, b2}} \<le> b"
    using tmp_inf_lemma[of X b b1 b2 a1 a2] by (simp add: A0 B0b B1 insert_commute)
  obtain ab1 where P1A3:"ab1 \<in> F1 \<and> ab1 \<le> a1 \<and> ab1 \<le> b1"
      by (metis A1 B0 B1 is_dirE1 is_filterE1)
  obtain ab2 where P1A4:"ab2 \<in> F2 \<and> ab2 \<le> a2 \<and> ab2 \<le> b2"
    by (metis A2 B0 B1 is_filterE1 is_dirE1)
  have P1B1:"ab1 \<le> Inf X {a1, b1} \<and> ab2 \<le> Inf X {a2, b2}"
    using A0 A1 A2 B0 B1 P1A3 P1A4 binf_leI3[of X] lattD41[of X]
    by (meson in_mono is_filterE1)
  have P1B2:"Inf X {a1, b1} \<in> F1 \<and> Inf X {a2, b2} \<in> F2"
  by (simp add: A0 A1 A2 B0 B1 filter_finf_closed_isl lattD41)
  have P1B3:"Inf X {Inf X {a1, b1}, Inf X {a2, b2}} \<in> (binary_filter_sup X F1 F2)"
  by (meson A0 B0b P1B2 dual_order.refl filter_bsup_mem_iff lattD41 sinfD4)
  show "(\<exists>c \<in> (binary_filter_sup X F1 F2).  a \<ge> c \<and>  b \<ge> c)"
    using B2 B3 P1B3 by blast
qed
         
lemma filters_on_lattice_bsup2b:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> is_dir (binary_filter_sup X F1 F2) (\<ge>)"
  by (simp add: filters_on_lattice_bsup2a is_dirI1)

lemma filters_on_lattice_bsup3:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> (binary_filter_sup X F1 F2) \<noteq> {}"
  by (metis is_filter_def filters_on_lattice_bsup04 ne_subset_ne)

lemma filters_on_lattice_bsup4:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> (binary_filter_sup X F1 F2) \<in> filters_on X"
  by (metis is_filter_def filter_bsup_mem_iff filters_on_iff filters_on_lattice_bsup1b filters_on_lattice_bsup2b filters_on_lattice_bsup3 subsetI)

lemma filters_on_lattice_bsup5:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> (binary_filter_sup X F1 F2) \<in> ubd (filters_on X) {F1, F2}"
  by (simp add: filters_on_lattice_bsup03 filters_on_lattice_bsup04 filters_on_lattice_bsup4 ubd_mem_doubleI)

lemma filters_on_lattice_bsup6:
  assumes A0:"is_lattice X" and A1:"is_filter X F1" and A2:"is_filter X F2" and A3:"G \<in> (ubd (filters_on X) {F1, F2})"
  shows "(binary_filter_sup X F1 F2) \<subseteq> G" (is "?L \<subseteq> ?R")
proof
  fix x assume A4:"x \<in> ?L"
  obtain a1 a2  where B0:"a1 \<in> F1 \<and> a2 \<in> F2 \<and> Inf X {a1, a2} \<le> x"
    using A4 binary_filter_sup_obtains by blast
  have B1:"a1 \<in> G \<and> a2 \<in> G"
    by (meson A3 B0 subsetD ubd_mem_doubleE1 ubd_mem_doubleE2)
  have B2:"Inf X {a1, a2} \<in> G"
  using A0 A3 B1 filter_finf_closed_isl filters_on_iff lattD41 ubdD2 by blast
  have B3:"is_filter X G "
    using A3 filters_on_iff ubdD2 by blast
  show "x \<in> G"
  by (meson A4 B0 B2 B3 filter_bsup_memD1 is_filterE1 is_ord_clE)
qed

lemma filters_on_lattice_bsup7:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> is_sup (filters_on X) {F1, F2} (binary_filter_sup X F1 F2) "
  by (simp add: filters_on_lattice_bsup5 filters_on_lattice_bsup6 is_supI5)

lemma filters_on_lattice_bsup8:
  "\<lbrakk>is_lattice X; is_filter X F1; is_filter X F2\<rbrakk> \<Longrightarrow> Sup (filters_on X) {F1, F2} = (binary_filter_sup X F1 F2)"
  by (simp add: filters_on_lattice_bsup7 sup_equality)


lemma filters_on_lattice_bsup2:
  assumes A0:"is_lattice X" and A1:"is_filter X F1" and A2:"is_filter X F2" and
          A3:"z \<in> Sup (filters_on X) {F1, F2}"
  shows "(\<exists>f1 \<in>F1. \<exists>f2 \<in> F2. Inf X {f1, f2} \<le>z)"
  by (metis A0 A1 A2 A3 filter_bsup_mem_iff filters_on_lattice_bsup8)


(*On a topped inf semilattice filters form a complete inf semilattice*)

lemma filters_on_top_inf_semilattice_is_cinf:
  "\<lbrakk>is_greatest X top; is_inf_semilattice X\<rbrakk> \<Longrightarrow> is_cinf_semilattice (filters_on X)"
  by (metis clatD2 clr_is_clattice filter_is_clr is_inf_semilattice_def pow_is_clattice)

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

lemma lattice_filter_memI:
  "\<lbrakk>is_lattice X; is_filter X F; x \<in> F; y \<in> X\<rbrakk> \<Longrightarrow> Sup X {x, y} \<in> F"
  using filters_max filters_on_lattice_inf02 lattD41 by blast

lemma lattice_filter_dunion4:
  "\<lbrakk>is_lattice X; D \<noteq> {}; D \<subseteq> filters_on X; is_dir D (\<le>); x \<in> (\<Union>D); y \<in> (\<Union>D)\<rbrakk> \<Longrightarrow> (\<exists>Dxy \<in> D. x\<in> Dxy \<and> y \<in> Dxy)"
  by (meson UnionE in_mono is_dirE1)

lemma lattice_filter_dunion7:
  "\<lbrakk>D \<noteq> {}; D \<subseteq> filters_on X\<rbrakk> \<Longrightarrow> \<Union>D \<subseteq> X"
  by(auto simp add:filters_on_def is_filter_def)


lemma lattice_filters_complete:
  "\<lbrakk>is_lattice X; is_greatest X top\<rbrakk> \<Longrightarrow> is_clattice (filters_on X)"
 by (simp add: filters_on_top_inf_lattice_clattice latt_iff)

lemma filters_inf_semilattice_inf:
  "\<lbrakk>is_inf_semilattice X; EF \<in> Pow_ne (filters_on X); is_greatest X top\<rbrakk> \<Longrightarrow> is_inf (filters_on X) EF (\<Inter>EF)"
  by(rule is_infI1,simp add: Inf_greatest Inf_lower filters_onI greatest_iff inter_filters_filter lbd_mem_iff3)

lemma filters_lattice_inf:
  "\<lbrakk>is_lattice X; F1 \<in> filters_on X; F2 \<in> filters_on X\<rbrakk> \<Longrightarrow> is_inf (filters_on X) {F1 ,F2} (F1 \<inter> F2)"
  by (simp add: filters_on_iff filters_on_lattice_inf8b)

lemma filters_lattice_inf_op:
  "\<lbrakk>is_lattice X; F1 \<in> filters_on X; F2 \<in> filters_on X\<rbrakk> \<Longrightarrow>Inf (filters_on X) {F1, F2} = (F1 \<inter> F2)"
  by (simp add: filters_lattice_inf inf_equality)



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
  "([a)\<^sub>X) = (ubd X {a})"
  by(simp add: set_eq_iff ubd_mem_iff lorc_mem_iff2)

lemma lorc_eq_upbd2:
  "A \<noteq> {} \<Longrightarrow> (\<Inter>a \<in> A. [a)\<^sub>X) = ubd X A"
  by(auto simp add:ubd_mem_iff2 lorc_mem_iff1)

lemma lorc_memI1:
  "a \<in> X \<Longrightarrow> a \<in> [a)\<^sub>X "
  by (simp add: lorcI1)

lemma lorc_mem_point1:
  "a \<in> X \<longleftrightarrow> a \<in> ([a)\<^sub>X)"
  by (simp add: lorc_def)

lemma lorc_subset1:
  "([a)\<^sub>X) \<subseteq> X"
  by (simp add: ubd_sub lorc_eq_upbd)

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
  by (simp add: is_ord_clI lorcD2)

lemma lorc_upclD:
  "U \<subseteq> X \<Longrightarrow> is_ord_cl X U (\<le>) \<Longrightarrow> is_least U x \<Longrightarrow> U = [x)\<^sub>X"
  apply (auto simp add: in_mono leastD2 lorcI1)
  by (meson is_ord_clE leastD11 lorcD1)

lemma lorc_upcl1:
  "\<lbrakk>is_greatest X m; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> m \<in> (\<Inter>a \<in> A. [a)\<^sub>X)"
  by (simp add: greatestD11 greatestD2 in_mono lorcI1)

lemma lorc_upcl3:
  "\<lbrakk>is_greatest X m; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow>  is_ord_cl X (\<Inter>a \<in> A. [a)\<^sub>X) (\<le>)"
  by(rule is_ord_cl_in, auto simp add: lorc_mem_iff1, simp add: in_mono lorc_upclI)
  
definition ord_cl_sets::"'a::order set \<Rightarrow> ('a::order \<Rightarrow> 'a::order \<Rightarrow> bool) \<Rightarrow> 'a::order set set" where
  "ord_cl_sets X ord \<equiv> {A. A \<subseteq> X \<and> is_ord_cl X A (ord)}"

lemma lorc_upcl4:
  "\<lbrakk>is_greatest X m; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> {m} \<in> ord_cl_sets X (\<le>)"
  using is_filterE1 min_filter1 ord_cl_sets_def by fastforce

lemma lorc_moore:
  "\<lbrakk>is_greatest X m\<rbrakk> \<Longrightarrow> is_clr (ord_cl_sets X (\<le>)) (Pow X)"  
proof-
  assume A0:"is_greatest X m" show "is_clr (ord_cl_sets X (\<le>)) (Pow X)"
  proof(rule moore_clI3)
    show "ord_cl_sets X (\<le>) \<subseteq> Pow X" by (metis (no_types, lifting) PowI mem_Collect_eq ord_cl_sets_def subsetI)
    show " X \<in> ord_cl_sets X (\<le>)" by (simp add: is_ord_cl_space ord_cl_sets_def)
    show "\<And>E. E \<subseteq> ord_cl_sets X (\<le>) \<Longrightarrow> E \<noteq> {} \<Longrightarrow> \<Inter> E \<in> ord_cl_sets X (\<le>)"
    proof-
      fix E assume "E \<subseteq> ord_cl_sets X (\<le>)" and e0:"E \<noteq> {}"
      then obtain e1:"\<And>e. e \<in> E \<Longrightarrow> is_ord_cl X e (\<le>) \<and> e \<subseteq> X"   using ord_cl_sets_def by fastforce 
      then obtain e2:"E \<in> Pow (Pow X)" by blast
      then obtain "is_ord_cl X (\<Inter>E) (\<le>)" using is_ord_cl_in[of E X "(\<le>)"] e1 e2 by auto
      then show "\<Inter> E \<in> ord_cl_sets X (\<le>)"   by (simp add: Inter_subset e0 e1 ord_cl_sets_def)
    qed
  qed
qed

lemma lorc_is_clattice:
  "is_greatest X m \<Longrightarrow> is_clattice (ord_cl_sets X (\<le>))"
  using clr_is_clattice lorc_moore pow_is_clattice by blast

lemma lorc_filter:
  "x \<in> X \<Longrightarrow> is_filter X [x)\<^sub>X"
proof-
  assume x0:"x \<in> X" show "is_filter X [x)\<^sub>X"
  proof(rule is_filterI1)
    show "([x)\<^sub>X) \<noteq> {}" using x0 lorc_memI1 by auto
    show "([x)\<^sub>X) \<subseteq> X" by (simp add: lorc_subset1) 
    show "is_dir ([x)\<^sub>X) (\<lambda>x y. y \<le> x)"   by (metis is_dir_def lorcD12 lorc_memI1 x0)
    show "is_ord_cl X ([x)\<^sub>X) (\<le>)" by (simp add: lorc_upclI x0)
  qed
qed


lemma lorc_filter2:
  "x \<in> X \<Longrightarrow>  ([x)\<^sub>X) \<in> filters_on X"
  by (simp add: filters_on_iff lorc_filter)

lemma lorc_sup_superset:
  "\<lbrakk>is_lattice X; is_greatest X top; F \<subseteq> X\<rbrakk>  \<Longrightarrow> {y. \<exists>x \<in> F. y= ([x)\<^sub>X)} \<subseteq> filters_on X"
  by(auto simp add:subset_iff lorc_filter2)

lemma lorc_sup_superset2:
  "\<lbrakk>is_lattice X; is_greatest X top; F \<subseteq> X\<rbrakk> \<Longrightarrow> F \<subseteq> \<Union>{y. \<exists>x \<in> F. y= ([x)\<^sub>X)}"
   using lorc_memI1 by auto

lemma lorc_inter:
  "\<lbrakk>is_lattice X; a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> ([a)\<^sub>X) \<inter> ([b)\<^sub>X) = [Sup X {a, b})\<^sub>X"
  by(auto simp add: bsup_geI3 latt_iff lorc_mem_iff1 bsup_iff)
 
lemma lorc_inter2:
  assumes A0:"is_lattice X" and A1:"F\<in> Fpow_ne X"
  shows "Sup (filters_on X) {([f)\<^sub>X)|f. f \<in> F} = [(Inf X F))\<^sub>X"
proof-
  let ?A="{([f)\<^sub>X)|f. f \<in> F}"
  from A1 obtain A1a:"F \<subseteq> X" and A1b:"finite F" and A1c:"F \<noteq> {}" unfolding Fpow_ne_def Fpow_def by(auto)
  then obtain B0a:"?A \<subseteq> (filters_on X)" using lorc_filter2 by blast
  obtain B0b:"finite ?A"  and B0c:"?A \<noteq> {}" using A1a A1b A1c by(auto)
  have B0:"\<And>f. f \<in> F \<Longrightarrow> ([f)\<^sub>X) \<subseteq> ([(Inf X F))\<^sub>X)" by (meson A0 A1 fpow_neD1 in_mono inf_semilattice_finf is_infD1121 is_infE1 lattD41 lorc_dual_iso) 
  then have B1:" ([(Inf X F))\<^sub>X) \<in> ubd (filters_on X) ?A"  by (smt (verit, best) A0 A1 inf_semilattice_finf is_infE1 lattD41 lorc_filter2 mem_Collect_eq ubd_mem_iff3)
  then have B2:"Sup (filters_on X) ?A\<le> [(Inf X F))\<^sub>X" by (metis (no_types, lifting) A0 B0a B0c csupD61 filters_on_lattice_csup)  
  have B3:"\<And>G. G \<in> ubd (filters_on X) ?A \<Longrightarrow> ([(Inf X F))\<^sub>X) \<subseteq> G"
  proof-
    fix G assume B30:"G \<in> ubd (filters_on X) ?A" then obtain B31:"\<forall>f. f \<in> F \<longrightarrow> f \<in> G"  by (metis (mono_tags, lifting) A1a in_mono lorc_memI1 mem_Collect_eq ubd_mem_iff2)
    then obtain B32:"F \<subseteq> G" and B33:"finite F" and B34:"F \<noteq> {}" using A1b A1c by blast
    then obtain B34:"Inf X F \<in> G"   using A0 B30 filter_finf_closed3 filters_onE lattD41 ubdD2 by blast 
    from B30 have B35:"is_filter X G" unfolding ubd_def filters_on_def by(auto)
    then obtain B36:"is_ord_cl X G (\<le>)" using is_filterE1 by(auto)
    then show "([(Inf X F))\<^sub>X) \<subseteq> G" using B34 B36 by (metis is_ord_clE lorcD11 lorcD12 subsetI)
  qed
  then have "([(Inf X F))\<^sub>X) \<le> Sup (filters_on X) ?A"   using B1 is_supI5 sup_equality by blast
  then show ?thesis using B2 by simp
qed
    
definition rolc::"'a::order \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" ("(2'(_]\<^sub>_)") where
  "(a]\<^sub>X \<equiv> {y \<in> X. y \<le> a} "

lemma rolcI1:
  "y \<in> X \<Longrightarrow> y \<le> a \<Longrightarrow> y \<in> (a]\<^sub>X" 
  by (simp add:rolc_def)

lemma rolcD1:
  "y \<in> (a]\<^sub>X \<Longrightarrow> y \<in> X \<and> y \<le> a"
   by (simp add:rolc_def)

lemma rolcD11:
  "y \<in> (a]\<^sub>X \<Longrightarrow> y \<in> X "
   by (simp add:rolc_def)

lemma rolcD12:
  "y \<in> (a]\<^sub>X \<Longrightarrow> y \<le> a" 
  by (simp add:rolc_def)

lemma rolcD2:"x \<in> X \<Longrightarrow> y \<in> (a]\<^sub>X \<Longrightarrow>  x \<le> y \<Longrightarrow> x \<in> (a]\<^sub>X"
  by(drule rolcD12, erule rolcI1, simp)

lemma rolcD3:
  "(\<exists>b. x \<le> b \<and> b \<in> (a]\<^sub>X) \<Longrightarrow> x \<in> X \<Longrightarrow>  x \<in> (a]\<^sub>X"
  using rolcD2 by blast

lemma rolc_mem_iff1:
  "y \<in> ((a]\<^sub>X) \<longleftrightarrow> (y \<in> X \<and> y \<le> a)"
   by (simp add:rolc_def)

lemma rolc_mem_iff2:
  "y \<in> ((a]\<^sub>X) \<longleftrightarrow> (y \<in> X \<and> y lb {a})" 
  by (simp add:rolc_def lb_def)

lemma rolc_memI1:
  "a \<in> X \<Longrightarrow> a \<in> (a]\<^sub>X "
  by (simp add: rolcI1)

lemma rolc_mem_point1:
  "a \<in> X \<longleftrightarrow> a \<in> ((a]\<^sub>X)"
  by (simp add: rolc_def)

lemma rolc_subset1:
  "((a]\<^sub>X) \<subseteq> X"
  by (simp add: rolc_def)

lemma rolc_dwclI:
  "a \<in> X \<Longrightarrow> is_ord_cl X ((a]\<^sub>X) (\<ge>)"
  by (simp add: is_ord_clI rolcD2)

lemma rolc_eq_lbd:
  "((a]\<^sub>X) = (lbd X {a})"
  by(simp add: set_eq_iff lbd_mem_iff rolc_mem_iff2)

lemma rolc_eq_lbd2:
  "A \<noteq> {} \<Longrightarrow> (\<Inter>a \<in> A. (a]\<^sub>X) = lbd X A"
  by(auto simp add:lbd_mem_iff2 rolc_mem_iff1)

lemma rolc_top:
  "is_least X m \<Longrightarrow> a \<in> X \<Longrightarrow> m \<in> (a]\<^sub>X"
  by (simp add: leastD11 leastD2 rolcI1)

lemma rolc_inf_latticeD1:
  "\<lbrakk>is_inf_semilattice X; x \<in> X; y \<in> X\<rbrakk>\<Longrightarrow> Inf X {x, y} \<in> ((x]\<^sub>X)"
  by (simp add: binf_leI1 rolcI1 sinfD4)

lemma rolc_sup_latticeD1:
  "\<lbrakk>is_greatest X top\<rbrakk> \<Longrightarrow> ((top]\<^sub>X) = X"
  by(auto simp add: rolc_mem_iff1 greatest_iff)

lemma rolc_iso:
  "\<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> ((a]\<^sub>X) \<subseteq> ((b]\<^sub>X)  \<longleftrightarrow> a \<le> b"
  by(auto simp add:rolc_mem_iff1) 

lemma rolc_dwclD:
  "U \<subseteq> X \<Longrightarrow> is_ord_cl X U (\<ge>) \<Longrightarrow> is_greatest U x \<Longrightarrow> U = (x]\<^sub>X"
  apply (auto simp add: greatestD2 in_mono rolcI1)
  by (meson greatestD1 is_ord_clE rolc_mem_iff1)

lemma rolc_dwcl1:
  "\<lbrakk>is_least X m; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> m \<in> (\<Inter>a \<in> A. (a]\<^sub>X)"
  by (simp add: least_iff rolcI1 subset_iff)

lemma rolc_upcl3:
  "\<lbrakk>is_least X m; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow>  is_ord_cl X (\<Inter>a \<in> A. (a]\<^sub>X) (\<ge>)"
  by(rule is_ord_cl_in, auto simp add:rolc_mem_iff1 in_mono rolc_dwclI)

subsection UpDwClosure
subsubsection UpClosure

definition up_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "up_cl X A = {x \<in> X. \<exists>a \<in> A. a \<le> x}"

lemma up_cl_mem_iff:
  "x \<in> up_cl X A \<longleftrightarrow> (x \<in> X \<and> (\<exists>a \<in> A. a \<le> x))"
  by (simp add: up_cl_def)

lemma up_cl_memD1:
  "x \<in> up_cl X A \<Longrightarrow> x \<in> X"
  by (simp add: up_cl_def)

lemma up_cl_memD2:
  "x \<in> up_cl X A \<Longrightarrow> \<exists>a \<in> A. a \<le> x"
  by (simp add: up_cl_def)

lemma up_cl_memI1:
  "x \<in> X \<Longrightarrow> a \<in> A \<Longrightarrow> a \<le> x \<Longrightarrow> x \<in> up_cl X A"
   using up_cl_def by auto 

lemma up_cl_memI2:
  "x \<in> X \<Longrightarrow> (\<exists>a \<in> A. a \<le> x) \<Longrightarrow> x \<in> up_cl X A"
  by (simp add: up_cl_mem_iff)

lemma up_cl_sub1:
  "A \<subseteq> X \<Longrightarrow> a \<in> A \<Longrightarrow> a \<in> up_cl X A"
  by (simp add: subsetD up_cl_memI1)

lemma up_cl_sub2:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq>  up_cl X A"
  by (simp add: subsetI up_cl_sub1)

lemma up_cl_sub3:
  "up_cl X A \<subseteq> X"
  by (simp add: subsetI up_cl_memD1)

lemma up_cl_iso1:
  "A \<subseteq> B \<Longrightarrow> up_cl X A \<subseteq> up_cl X B"
  by (meson in_mono subsetI up_cl_memD1 up_cl_memD2 up_cl_memI1)

lemma up_cl_idem1:
  "x \<in> up_cl X (up_cl X A) \<Longrightarrow> x \<in> up_cl X A"
  by (meson dual_order.trans up_cl_mem_iff)

lemma up_cl_idem2:
  " up_cl X (up_cl X A) \<subseteq> up_cl X A"
  by (simp add: subsetI up_cl_idem1)

lemma up_cl_idem3:
  " up_cl X (up_cl X A) = up_cl X A"
  by (simp add: subset_antisym up_cl_idem2 up_cl_sub2 up_cl_sub3)

lemma up_cl_singleton:
  "x \<in> up_cl X {a}  \<longleftrightarrow> (x \<in> X \<and> a \<le> x)"
  by (simp add: up_cl_mem_iff)

lemma up_cl_lorc:
  "up_cl X {a} = [a)\<^sub>X"
  by (simp add: lorc_mem_iff1 set_eq_iff up_cl_singleton)

lemma up_cl_ext:
  "is_extensive (Pow X) (\<lambda>A. up_cl X A)"
  by (simp add: is_extensive_def up_cl_sub2)

lemma up_cl_iso:
  "is_isotone (Pow X) (\<lambda>A. up_cl X A)"
  by (simp add: is_isotone_def up_cl_iso1)

lemma up_cl_idem:
  "is_idempotent (Pow X) (\<lambda>A. up_cl X A)"
  by (simp add: is_idempotent_def up_cl_idem3)

lemma up_cl_cl:
  "is_closure (Pow X) (\<lambda>A. up_cl X A)"
  by (simp add: image_subsetI is_closure_def up_cl_ext up_cl_idem up_cl_iso up_cl_sub3)

lemma up_cl_memI3:
  "\<And>a b. \<lbrakk>a \<in> (up_cl X A); b \<in> X; a \<le> b\<rbrakk> \<Longrightarrow> b \<in> (up_cl X A)"
  using up_cl_idem3 up_cl_memI1 by blast

lemma up_cl_is_up_cl:
  "is_ord_cl X (up_cl X A) (\<le>)"
  by (simp add: is_ord_clI up_cl_memI3)

lemma dwdir_upcl_is_dwdir:
  assumes A0:"is_dir A (\<ge>)" and A1:"A \<subseteq> X"
  shows "is_dir (up_cl X A) (\<ge>)"
proof(rule is_dirI1)
  show "\<And>a b. a \<in> up_cl X A \<Longrightarrow> b \<in> up_cl X A \<Longrightarrow> \<exists>c\<in>up_cl X A. c \<le> a \<and> c \<le> b"
  proof-
    fix a b assume A2:"a \<in> up_cl X A" and  A3:"b \<in> up_cl X A"
    from A2 obtain a1 where a2:"a1 \<in> A" and a3:"a1 \<le> a"  using up_cl_memD2[of a X A] by blast
    from A3 obtain b1 where b2:"b1 \<in> A" and  b3:"b1 \<le> b"  using up_cl_memD2[of b X A] by blast
    from a2 b2 A1 obtain a4:"a1 \<in> X" and b4:"b1 \<in> X" by blast 
    then obtain c where c0:"c \<in> A" and c1:"c \<le> a1" and c2:"c \<le> b1" using A0 is_dirE1[of A "(\<ge>)" a1 b1] a2 b2 by auto
    obtain c3:"c \<in> up_cl X A"   by (simp add: A1 c0 up_cl_sub1 a3 b3 c1 c2) 
    obtain c4:"c \<le> a" and c5:"c \<le> b"  using a3 b3 c1 c2 by auto
    then show "\<exists>c\<in>up_cl X A. c \<le> a \<and> c \<le> b" using c3 by blast
  qed
qed


subsubsection DownClosure
definition dw_cl::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order set" where
  "dw_cl X A = {x \<in> X. \<exists>a \<in> A. x \<le> a}"

lemma dw_cl_mem_iff:
  "x \<in> dw_cl X A \<longleftrightarrow> (x \<in> X \<and> (\<exists>a \<in> A. x \<le> a))"
  by (simp add: dw_cl_def)

lemma dw_cl_memD1:
  "x \<in> dw_cl X A \<Longrightarrow> x \<in> X"
  by (simp add: dw_cl_def)

lemma dw_cl_memD2:
  "x \<in> dw_cl X A \<Longrightarrow> \<exists>a \<in> A. x \<le> a"
  by (simp add: dw_cl_def)

lemma dw_cl_memI1:
  "x \<in> X \<Longrightarrow> a \<in> A \<Longrightarrow> x \<le> a \<Longrightarrow> x \<in> dw_cl X A"
  using dw_cl_def by auto

lemma dw_cl_sub1:
  "A \<subseteq> X \<Longrightarrow> a \<in> A \<Longrightarrow> a \<in> dw_cl X A"
  by (simp add: subsetD dw_cl_memI1)

lemma dw_cl_sub2:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> dw_cl X A"
  by (simp add: subsetI dw_cl_sub1)

lemma dw_cl_sub3:
  "dw_cl X A \<subseteq> X"
  by (simp add: subsetI dw_cl_memD1)

lemma dw_cl_iso1:
  "A \<subseteq> B \<Longrightarrow> dw_cl X A \<subseteq> dw_cl X B"
  by (meson in_mono subsetI dw_cl_memD1 dw_cl_memD2 dw_cl_memI1)

lemma dw_cl_idem1:
  "x \<in> dw_cl X (dw_cl X A) \<Longrightarrow> x \<in> dw_cl X A"
  by (meson order.trans dw_cl_mem_iff)

lemma dw_cl_idem2:
  "dw_cl X (dw_cl X A) \<subseteq> dw_cl X A"
  by (simp add: subsetI dw_cl_idem1)

lemma dw_cl_idem3:
  "dw_cl X (dw_cl X A) = dw_cl X A"
  by (simp add: subset_antisym dw_cl_idem2 dw_cl_sub2 dw_cl_sub3)

lemma dw_cl_lorc:
  "dw_cl X {a} = (a]\<^sub>X"
  by (simp add: set_eq_iff rolc_mem_iff1 dw_cl_mem_iff)

lemma dw_cl_ext:
  "is_extensive (Pow X) (\<lambda>A. dw_cl X A)"
  by (simp add: is_extensive_def dw_cl_sub2)

lemma dw_cl_iso:
  "is_isotone (Pow X) (\<lambda>A. dw_cl X A)"
  by (simp add: is_isotone_def dw_cl_iso1)

lemma dw_cl_idem:
  "is_idempotent (Pow X) (\<lambda>A. dw_cl X A)"
  by (simp add: is_idempotent_def dw_cl_idem3)

lemma dw_cl_cl:
  "is_closure (Pow X) (\<lambda>A. dw_cl X A)"
  by (simp add: image_subsetI is_closure_def dw_cl_ext dw_cl_idem dw_cl_iso dw_cl_sub3)

lemma dw_cl_memI3:
  "\<And>a b. \<lbrakk>a \<in> (dw_cl X A); b \<in> X; a \<ge> b\<rbrakk> \<Longrightarrow> b \<in> (dw_cl X A)"
  using dw_cl_idem3 dw_cl_memI1 by blast

lemma dw_cl_is_dw_cl:
  "is_ord_cl X (dw_cl X A) (\<ge>)"
  by (simp add: is_ord_clI dw_cl_memI3)


definition galois_conn::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a::order set \<Rightarrow> ('b::order \<Rightarrow> 'a::order) \<Rightarrow> 'b::order set \<Rightarrow> bool" where
  "galois_conn f X g Y \<equiv> (f`X \<subseteq> Y) \<and> (g`Y \<subseteq> X) \<and> (\<forall>x \<in> X. \<forall>y \<in> Y.  (x \<le> g y \<longleftrightarrow> y \<le> f x))"

lemma galois_connD11:
  "galois_conn f X g Y \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> x \<le>  g y \<Longrightarrow> y \<le> f x"
   by (simp add:galois_conn_def)

lemma galois_connD21:
  "galois_conn f X g Y \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> y \<le> f x \<Longrightarrow> x \<le> g y" 
  by (simp add:galois_conn_def)

lemma galois_connD12:
  "galois_conn f X g Y \<Longrightarrow> y \<in> Y \<Longrightarrow> g y \<in> X" 
  by (simp add:galois_conn_def image_subset_iff)

lemma galois_connD22:
  "galois_conn f X g Y \<Longrightarrow> x \<in> X  \<Longrightarrow> f x \<in> Y" 
  by (simp add:galois_conn_def image_subset_iff)

lemma galois_connD3:
  "galois_conn f X g Y \<Longrightarrow> A \<subseteq> X \<Longrightarrow> f`A \<subseteq> Y"
  using galois_connD22 by blast

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
  "galois_conn (\<lambda>A. ubd X A) (Pow X) (\<lambda>A. lbd X A) (Pow X)"
  apply(rule gcI) 
  apply(simp add: ubd_ant1 is_antitone_def)
  apply(simp add: lubd_comp1 is_extensive_def)
  apply(simp add: lbd_ant1 is_antitone_def)
  apply(simp add: ulbd_comp1 is_extensive_def)
  apply (simp add: ubd_sub image_subset_iff)
  by (simp add: lbd_sub image_subset_iff)

lemma ul_closure:
  "is_closure (Pow X) ((\<lambda>A. ubd X A) \<circ> (\<lambda>A. lbd X A))"
  using gc_closure2 ul_galois by blast

lemma lu_closure:
  "is_closure (Pow X) ((\<lambda>A. lbd X A) \<circ> (\<lambda>A. ubd X A))"
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

subsubsection ThisIsAMess

lemma gc_sup_lb1:
  "\<lbrakk>galois_conn f X g Y; A \<subseteq> X; is_sup X A s\<rbrakk> \<Longrightarrow> f s lb f`A"
  by (simp add: gc_anti1 is_supE1 is_supE7 lb_imageI subsetD)

lemma gc_sup_lb2:
  "\<lbrakk>galois_conn f X g Y; B \<subseteq> Y; is_sup Y B s\<rbrakk> \<Longrightarrow> g s lb g`B"
  by (simp add: gc_anti2 is_supE1 is_supE7 lb_imageI subsetD)

lemma gc_reverse1:
  "\<lbrakk>galois_conn f X g Y;y \<in> Y; A \<subseteq> X; y lb f`A\<rbrakk> \<Longrightarrow> g y ub A"
  by (simp add: galois_conn_def in_mono lbE ub_def)

lemma gc_reverse11:
  "\<lbrakk>galois_conn f X g Y; x \<in> X; B \<subseteq> Y; x lb g`B\<rbrakk> \<Longrightarrow> f x ub B"
  by (meson gcD gcI gc_reverse1)

lemma gc_reverse2:
  "\<lbrakk>galois_conn f X g Y;y \<in> Y; A \<subseteq> X; g y ub A\<rbrakk> \<Longrightarrow> y lb f`A"
  by (simp add: galois_connD11 in_mono lb_imageI ubE)

lemma gc_reverse21:
  "\<lbrakk>galois_conn f X g Y; x \<in> X; B \<subseteq> Y; f x ub B\<rbrakk> \<Longrightarrow> x lb g`B"
  by (simp add: galois_connD21 in_mono lb_imageI ub_def)

lemma gc_sup_inf11:
  "\<lbrakk>galois_conn f X g Y; A \<subseteq> X; y \<in> Y; is_inf Y (f`A) i; is_sup X A s;y \<le> i\<rbrakk> \<Longrightarrow> y \<le> f s"
  by (simp add: galois_connD11 galois_connD12 gc_reverse1 is_infE6 is_supE1 is_supE4)

lemma gc_sup_inf12:
  "\<lbrakk>galois_conn f X g Y; B \<subseteq> Y; x \<in> X; is_inf X (g`B) i; is_sup Y B s; x \<le> i\<rbrakk> \<Longrightarrow> x \<le> g s"
  by (simp add: galois_connD21 galois_connD22 gc_reverse11 is_infE6 is_supE1 is_supE4)

lemma gc_sup_inf21:
  "\<lbrakk>galois_conn f X g Y; A \<subseteq> X; y \<in> Y; is_inf Y (f`A) i; is_sup X A s; y \<le> f s\<rbrakk> \<Longrightarrow> y \<le> i"
  by (meson gc_sup_lb1 is_infD42 lb_iso1)

lemma gc_sup_inf22:
  "\<lbrakk>galois_conn f X g Y; B \<subseteq> Y; x \<in> X; is_inf X (g`B) i; is_sup Y B s; x \<le> g s\<rbrakk> \<Longrightarrow> x \<le> i"
  by (meson gc_sup_lb2 is_infE4 lb_iso1)

lemma gc_sup_inf31:
  "\<lbrakk>galois_conn f X g Y; A \<subseteq> X; is_inf Y (f`A) i; is_sup X A s\<rbrakk> \<Longrightarrow> (\<forall>y \<in> Y. y \<le> i \<longleftrightarrow> y \<le> f s)"
  by (meson gc_sup_inf11 gc_sup_inf21)

lemma gc_sup_inf32:
  "\<lbrakk>galois_conn f X g Y; B \<subseteq> Y; is_inf X (g`B) i; is_sup Y B s\<rbrakk> \<Longrightarrow> (\<forall>x \<in> X. x \<le> i \<longleftrightarrow> x \<le> g s)"
  by (meson gc_sup_inf12 gc_sup_inf22)

lemma gc_sup_inf41:
  "\<lbrakk>galois_conn f X g Y; A \<subseteq> X; is_inf Y (f`A) i; is_sup X A s\<rbrakk> \<Longrightarrow>f s = i"
  by(rule leq_iff_leq_eq, erule galois_connD22, erule is_supE1, erule is_infE1, simp add: gc_sup_inf31)

lemma gc_sup_inf42:
  "\<lbrakk>galois_conn f X g Y; B \<subseteq> Y; is_inf X (g`B) i; is_sup Y B s\<rbrakk> \<Longrightarrow>g s = i"
  by(rule leq_iff_leq_eq, erule galois_connD12, erule is_supE1, erule is_infE1, simp add: gc_sup_inf32)

lemma gc_sup_inf:
  "\<lbrakk>is_clattice X; is_clattice Y; galois_conn f X g Y; A \<subseteq> X\<rbrakk> \<Longrightarrow> Inf Y (f`A) = f (Sup X A)"
  using gc_sup_inf41[of f X g Y A "Inf Y (f`A)" "Sup X A"]  by (metis clatD21 clatD22 galois_connD3 inf_exI sup_equality)

lemma gc_inf_sup:
  "\<lbrakk>is_clattice X; is_clattice Y; galois_conn f X g Y; B \<subseteq> Y\<rbrakk> \<Longrightarrow> Inf X (g`B) = g (Sup Y B)"
  using gc_sup_inf42[of f X g Y B "Inf X (g`B)" "Sup Y B"]
  by (metis (no_types, opaque_lifting) clatD21 clatD22 dual_order.trans galois_conn_def image_mono inf_exI sup_equality)

definition extrema_dual::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a::order set \<Rightarrow> 'b::order set  \<Rightarrow> bool" where
  "extrema_dual f X Y \<equiv>(\<forall>A. A \<subseteq> X \<longrightarrow> f (Sup X A) = Inf Y (f`A))"

definition dual_adj::"('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a::order set \<Rightarrow> 'b::order set \<Rightarrow> ('b::order \<Rightarrow> 'a::order)" where
  "dual_adj f X Y \<equiv> (\<lambda>y. Sup X {x \<in> X. y \<le> f x})"

lemma gc_extrema_dual:
  "\<lbrakk>is_clattice X; is_clattice Y; galois_conn f X g Y; A \<subseteq> X\<rbrakk> \<Longrightarrow> extrema_dual f X Y"
  by (simp add: extrema_dual_def gc_sup_inf)

lemma gc_extrema_dual2:
  "\<lbrakk>is_clattice X; is_clattice Y; galois_conn f X g Y; A \<subseteq> X\<rbrakk> \<Longrightarrow> extrema_dual g Y X"
  by (simp add: extrema_dual_def gc_inf_sup)


lemma extrema_dual_antitone1:
  assumes A0:"extrema_dual f X Y" and A1:"f`X \<subseteq> Y" and A2:"x1 \<in> X \<and> x2 \<in> X" and A3:"x1 \<le> x2" and A4:"is_lattice X" "is_lattice Y"
  shows "f x2 \<le> f x1"
proof-
  have B0:"f x2 = f (Sup X {x1, x2})" by (simp add: A2 A3 ge_sup1)
  have B1:"...  = Inf Y (f`{x1, x2})" by (meson A0 A2 empty_subsetI extrema_dual_def insert_subsetI)
  have B2:"...  = Inf Y {f x1, f x2}" by simp
  have B3:"...  \<le> f x1"
    by (metis A1 A2 B0 B1 B2 assms(6) imageI in_mono lattD41 le_binf2)
  show ?thesis
    using B0 B1 B2 B3 by presburger
qed

lemma extrema_dual_antitone1b:
  "\<lbrakk>extrema_dual f X Y; f`X \<subseteq> Y; is_lattice X; is_lattice Y\<rbrakk> \<Longrightarrow> is_antitone X f"
  by (simp add: extrema_dual_antitone1 is_antitone_def)

lemma extrema_dual_antitone1c:
  "\<lbrakk>extrema_dual f X Y; f`X \<subseteq> Y; is_clattice X; is_clattice Y\<rbrakk> \<Longrightarrow> is_antitone X f"
  by (simp add: clat_lattice extrema_dual_antitone1b)

lemma extrema_dual_adj_antitone2:
  assumes A0:"extrema_dual f X Y" and A1:"f`X \<subseteq> Y" and A2:"y1 \<in> Y \<and> y2 \<in> Y" and A3:"y1 \<le> y2" and
          A4:"is_clattice X" "is_clattice Y"
  shows "(dual_adj f X Y) y2 \<le> (dual_adj f X Y) y1"
proof-
  have B0:"{x \<in> X. y2 \<le> f x} \<subseteq> {x \<in> X. y1 \<le> f x}"
    using A3 by force
  have B1:"(dual_adj f X Y) y2 = Sup X {x \<in> X. y2 \<le> f x}" by (simp add: dual_adj_def)
  have B2:"...                 \<le> Sup X {x \<in> X. y1 \<le> f x}" by (simp add: B0 assms(5) sup_iso1)
  have B3:"...                 = (dual_adj f X Y) y1"  by (simp add: dual_adj_def)
  show ?thesis
    by (simp add: B2 dual_adj_def)
qed

lemma extrema_dual_antitone2b:
  "\<lbrakk>extrema_dual f X Y; f`X \<subseteq> Y; is_clattice X; is_clattice Y\<rbrakk> \<Longrightarrow> is_antitone Y (dual_adj f X Y)"
  by (simp add: extrema_dual_adj_antitone2 is_antitone_def)

lemma extrema_dual_cext1:
  assumes A0:"extrema_dual f X Y" and A1:"f`X \<subseteq> Y" and A2:"x \<in> X" and A4:"is_clattice X" "is_clattice Y"
  shows "x \<le> (dual_adj f X Y) (f x)"
  apply(auto simp add:dual_adj_def)
  by (metis (no_types, lifting) A2 assms(4) clatD21 dual_order.refl is_supD1121 mem_Collect_eq subsetI sup_equality)

lemma extrema_dual_cext1b:
  "\<lbrakk>extrema_dual f X Y; f`X \<subseteq> Y; is_clattice X; is_clattice Y\<rbrakk> \<Longrightarrow> is_extensive X ((dual_adj f X Y) \<circ> f)"
  by (simp add: extensiveI1 extrema_dual_cext1)

lemma im_le2:
  "f`X \<subseteq> Y \<Longrightarrow> y lb f`{x \<in> X. y \<le> f x}"
  by (metis (no_types, lifting) lb_imageI mem_Collect_eq)

lemma im_le3:
  "f`X \<subseteq> Y \<Longrightarrow> y \<in> Y \<Longrightarrow> y \<in> lbd Y (f`{x \<in> X. y \<le> f x})"
  by (simp add: im_le2 lbd_mem_iff)

lemma extrema_dual_cext2:
  assumes A0:"extrema_dual f X Y" and A1:"f`X \<subseteq> Y" and A2:"y \<in> Y" and A4:"is_clattice X" "is_clattice Y"
  shows "y \<le> f ((dual_adj f X Y) y)"
proof-
  let ?g="dual_adj f X Y"
  have B0:"f (?g y) = f (Sup X {x \<in> X. y \<le> f x})"  by (simp add: dual_adj_def)
  have B1:"...      = Inf Y (f`{x \<in> X. y \<le> f x})" by (metis (no_types, lifting) A0 extrema_dual_def mem_Collect_eq subsetI)
  have B2:"...     \<ge> y " using im_le3[of f X Y y] by (metis (no_types, lifting) A1 A2 assms(5) binf_idem1 cinfD61 clatD2 image_Collect_subsetI image_subset_iff inf_anti1 insert_absorb insert_subsetI singletonI subset_insertI)
  show ?thesis by (simp add: B1 B2 dual_adj_def)
qed

lemma extrema_dual_cext2b:
  "\<lbrakk>extrema_dual f X Y; f`X \<subseteq> Y; is_clattice X; is_clattice Y\<rbrakk> \<Longrightarrow> is_extensive Y (f \<circ> (dual_adj f X Y))"
  by (simp add: extensiveI1 extrema_dual_cext2)

lemma adj_range: 
  "\<lbrakk>extrema_dual f X Y; f`X \<subseteq> Y; is_clattice X; is_clattice Y\<rbrakk> \<Longrightarrow> (dual_adj f X Y)`Y \<subseteq> X"
  apply(auto simp add:dual_adj_def)  by (metis (full_types) Collect_subset clatD21 is_supE1 sup_equality)

lemma extrema_dual_gc:
  "\<lbrakk>extrema_dual f X Y; f`X \<subseteq> Y; is_clattice X; is_clattice Y\<rbrakk> \<Longrightarrow> galois_conn f X (dual_adj f X Y) Y"
  by(rule gcI; simp add:extrema_dual_antitone1c extrema_dual_cext1b extrema_dual_antitone2b extrema_dual_cext2b adj_range)


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


abbreviation sup_inv where  "sup_inv X A \<equiv> (\<lambda>y. SOME E. E \<in> Pow A \<and> E \<noteq> {} \<and> is_sup X E y)"

abbreviation inf_inv where "inf_inv X A \<equiv> (\<lambda>y. SOME E. E \<in> Pow A \<and> E \<noteq> {} \<and> is_inf X E y)"

abbreviation fne_inf_inv where "fne_inf_inv X A \<equiv> (\<lambda>y. SOME E. E \<in> Fpow A \<and> E \<noteq> {} \<and> is_inf X E y)"

abbreviation fne_sup_inv where "fne_sup_inv X A \<equiv> (\<lambda>y. SOME E. E \<in> Fpow A \<and> E \<noteq> {} \<and> is_sup X E y)"

abbreviation fin_inf_inv where "fin_inf_inv X A \<equiv> (\<lambda>y. SOME E. E \<in> Fpow A \<and>  is_inf X E y)"


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

lemma fne_inf_cl_obtains:
  assumes "x \<in> fne_inf_cl X A"
  obtains F where "F \<in> Fpow A \<and> F \<noteq> {} \<and> is_inf X F x"
  by (meson assms fne_inf_cl_imp1)

lemma fne_sup_cl_obtains:
  assumes "x \<in> fne_sup_cl X A"
  obtains F where "F \<in> Fpow A \<and> F \<noteq> {} \<and> is_sup X F x"
  by (meson assms fne_sup_cl_imp1)

lemma sup_cl_vimage:
  "x \<in> sup_cl X A \<Longrightarrow> vimage (\<lambda>E. Sup X E) {x} \<noteq> {}"
  by (metis empty_iff sup_cl_imp0 sup_equality sup_singleton vimage_singleton_eq)

lemma sup_cl_inv:
  "x \<in> sup_cl X A \<Longrightarrow> Sup X (sup_inv X A x) =x"
  by(rule someI2_ex, meson sup_cl_obtains, simp add: sup_equality)

lemma sup_cl_inv2:
  "x \<in> sup_cl X A \<Longrightarrow> Sup X (sup_inv X A x)  \<in> sup_cl X A"
  using sup_cl_inv by force

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
  using is_supE1 is_supE7 is_ord_clE by fastforce 

lemma up_closed_supin_closed:
  "is_ord_cl X A (\<le>) \<Longrightarrow> is_sup_cl X A"
  using is_sup_cl_def up_closed_supin_closed0 by blast

lemma dw_closed_infin_closed0:
  "is_ord_cl X A (\<ge>) \<Longrightarrow> E \<in> Pow A \<Longrightarrow> E \<noteq> {} \<Longrightarrow> is_inf X E x  \<Longrightarrow> x \<in> A"
  using is_infE1 is_infD1121 is_ord_clE by fastforce

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
  show "a \<in> fin_inf_cl X A" apply(simp add:fin_inf_cl_def) using B0 B2 is_infE1 by blast
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
          by (metis (mono_tags, lifting) B0 PowD is_supE1 someI_ex sup_equality)
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
              using B1 B6A1 is_supE1 sup_equality by fastforce
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
          by (metis (mono_tags, lifting) B0 PowD is_infE1 someI_ex inf_equality)
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
              using B1 B6A1 is_infE1 inf_equality by fastforce
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
        by (metis (no_types, lifting) B0 inf_equality is_infE1 someI_ex) 
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
        by (metis (mono_tags, lifting) B0 inf_equality is_infE1 someI_ex)
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
        by (metis (no_types, lifting) B1 B11A1 B14 B15 B2 P1 SUP_bot_conv(2) equals0I fne_inf_cl_if1 inf_equality is_infE1)
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
        by (metis (mono_tags, lifting) B0 sup_equality is_supE1 someI_ex)
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
        by (metis (no_types, lifting) B1 B11A1 B14 B15 B2 P1 SUP_bot_conv(2) equals0I fne_sup_cl_if1 sup_equality is_supE1)
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
      by (meson A3 A4 A5 B1 Un_upper2 fne_sup_cl_if1 is_supE1 is_sup_iso1 sup.cobounded1)
    show "(\<exists>c\<in>fne_sup_cl X A. a \<le> c \<and> b \<le> c)"
      using B3 by blast
  qed
  show ?thesis
    by (simp add: B0 is_dirI1)
qed
  
lemma sup_density_test1:
  "\<lbrakk>sup_cl X A =X; x \<in> X\<rbrakk> \<Longrightarrow> (\<exists>Ex \<in> Pow A. Sup X Ex = x)"
  using sup_cl_imp1 sup_equality by blast

section Compactness


definition is_compact::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "is_compact X c \<equiv> c \<in> X \<and> (\<forall>A. A \<in> Pow_ne X \<and> c \<le> Sup X A \<longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> c \<le> Sup X A0))"

definition compact_elements::"'a::order set \<Rightarrow> 'a::order set" where
  "compact_elements X \<equiv> {c. is_compact X c}"

definition compactly_generated::"'a::order set \<Rightarrow> bool" where
  "compactly_generated X \<equiv> (\<forall>x. x \<in> X \<longrightarrow> (\<exists>C \<in> Pow (compact_elements X). is_sup X C x))"


lemma compactI:
  "\<lbrakk>c \<in> X; (\<And>A. \<lbrakk>A \<in> Pow_ne X; c \<le> Sup X A\<rbrakk> \<Longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> c \<le> Sup X A0))\<rbrakk> \<Longrightarrow> is_compact X c"
  by(simp add:is_compact_def)

lemma compactD:
  "\<lbrakk>is_compact X c; A \<in> Pow_ne X; c \<le> Sup X A\<rbrakk> \<Longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> c \<le> Sup X A0)"
  by(simp add:is_compact_def)

lemma compact_element_memD1:"x \<in> compact_elements X  \<Longrightarrow> is_compact X x" by (simp add: compact_elements_def)
lemma compactD2:"is_compact X x \<Longrightarrow> x \<in> X" by (simp add: is_compact_def)
lemma compact_element_memD2:"x \<in> compact_elements X  \<Longrightarrow> x \<in> X" using compactD2 compact_element_memD1 by blast 
lemma compact_elements_sub:"compact_elements X \<subseteq> X"  by (simp add: compact_element_memD2 subsetI) 

lemma compact_elements_mem_iff1: "x \<in> compact_elements X \<longleftrightarrow> is_compact X x" by (simp add: compact_elements_def)

lemma compactly_generatedD1:
  "compactly_generated X \<Longrightarrow> x \<in> X \<Longrightarrow> (\<exists>C \<in> Pow (compact_elements X). is_sup X C x)"
  by(simp add:compactly_generated_def)

lemma compactly_generatedI1:
  "(\<And>x. x \<in> X \<Longrightarrow>  (\<exists>C \<in> Pow (compact_elements X). is_sup X C x)) \<Longrightarrow> compactly_generated X"
  by(simp add:compactly_generated_def)


definition join_dense::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where "join_dense X D \<equiv> (\<forall>x \<in> X. \<exists>Dx \<in> Pow D. is_sup X Dx x)"
definition meet_dense::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where "meet_dense X D \<equiv> (\<forall>x \<in> X. \<exists>Dx \<in> Pow D. is_inf X Dx x)"

lemma join_denseD1:"\<lbrakk>join_dense X D; x \<in> X\<rbrakk> \<Longrightarrow> (\<exists>Dx \<in> Pow D. is_sup X Dx x)" by (simp add:join_dense_def)
lemma meet_denseD1:"\<lbrakk>meet_dense X D; x \<in> X\<rbrakk> \<Longrightarrow> (\<exists>Dx \<in> Pow D. is_inf X Dx x)" by (simp add:meet_dense_def)

lemma cmeet_dense_iff:"\<lbrakk>D \<subseteq> X; is_clattice X\<rbrakk> \<Longrightarrow> (meet_dense X D \<longleftrightarrow> (\<forall>x \<in> X. \<exists>Dx \<in> Pow D. x = Inf X Dx))"  apply(auto) using meet_denseD1 inf_equality apply blast  by (metis (no_types, opaque_lifting) Pow_iff clatD22 dual_order.trans meet_dense_def inf_equality)

lemma join_denseD2:"\<lbrakk>join_dense X D; D \<subseteq> X\<rbrakk> \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x = Sup X (x]\<^sub>D)"
proof-
  assume P:"join_dense X D" "D \<subseteq> X" 
  show "(\<And>x. x \<in> X \<Longrightarrow> x = Sup X (x]\<^sub>D)"
  proof- 
    fix x assume P1:"x \<in> X" 
    obtain Dx where "Dx \<in> Pow D" "is_sup X Dx x" by (meson P(1) P1 join_denseD1)
    have B0:"\<forall>d. d \<in> Dx \<longrightarrow> d \<le> x"     using \<open>is_sup (X::'a::order set) (Dx::'a::order set) (x::'a::order)\<close> is_supD1121 by blast
    have B1:"Dx \<subseteq> X"  using P(2) \<open>(Dx::'a::order set) \<in> Pow (D::'a::order set)\<close> by blast
    have B2:"Dx \<subseteq> (x]\<^sub>D"    by (meson B0 PowD \<open>(Dx::'a::order set) \<in> Pow (D::'a::order set)\<close> rolcI1 subset_eq)
      have B3:"is_sup X ((x]\<^sub>D) x" 
      proof(rule is_supI5)
        show "\<And>a. a \<in> ubd X (x]\<^sub>D \<Longrightarrow> x \<le> a" using B2 \<open>is_sup (X::'a::order set) (Dx::'a::order set) (x::'a::order)\<close> is_supE3 ubd_ant1b by blast
        show " x \<in> ubd X (x]\<^sub>D"   by (meson P1 rolcD12 ubd_mem_iff3)
      qed
    show "x= Sup X (x]\<^sub>D" using B3 sup_equality by force
  qed
qed

lemma join_denseI2:"\<lbrakk>D \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> is_sup X ((x]\<^sub>D) x) \<rbrakk> \<Longrightarrow> join_dense X D" by (meson Pow_iff join_dense_def rolc_subset1)

lemma meet_denseD2:"\<lbrakk>meet_dense X D; D \<subseteq> X\<rbrakk> \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x = Inf X [x)\<^sub>D)"
proof-
  assume P:"meet_dense X D" "D \<subseteq> X" 
  show "(\<And>x. x \<in> X \<Longrightarrow> x = Inf X [x)\<^sub>D)"
  proof- 
    fix x assume P1:"x \<in> X" 
    obtain Dx where "Dx \<in> Pow D" "is_inf X Dx x" by (meson P(1) P1 meet_denseD1)
    have B0:"\<forall>d. d \<in> Dx \<longrightarrow> x \<le> d"     using \<open>is_inf (X::'a::order set) (Dx::'a::order set) (x::'a::order)\<close> is_infD1121 by blast
    have B1:"Dx \<subseteq> X"  using P(2) \<open>(Dx::'a::order set) \<in> Pow (D::'a::order set)\<close> by blast
    have B2:"Dx \<subseteq> [x)\<^sub>D"    by (meson B0 PowD \<open>(Dx::'a::order set) \<in> Pow (D::'a::order set)\<close> lorcI1 subset_eq)
      have B3:"is_inf X ([x)\<^sub>D) x" 
      proof(rule is_infI5)
        show "\<And>a. a \<in> lbd X [x)\<^sub>D \<Longrightarrow> a \<le> x" using B2 \<open>is_inf (X::'a::order set) (Dx::'a::order set) (x::'a::order)\<close> is_infE3 lbd_ant1b by blast
        show " x \<in> lbd X [x)\<^sub>D"   by (meson P1 lorcD12 lbd_mem_iff3)
      qed
    show "x= Inf X [x)\<^sub>D" using B3 inf_equality by force
  qed
qed

lemma meet_denseI2:"\<lbrakk>D \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> is_inf X ([x)\<^sub>D) x) \<rbrakk> \<Longrightarrow> meet_dense X D" by (meson Pow_iff meet_dense_def lorc_subset1)
lemma join_denseD4:"\<lbrakk>D \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> is_sup X ((x]\<^sub>D) x)\<rbrakk> \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> X; b \<in> X ; b < a\<rbrakk>  \<Longrightarrow>(\<exists>x \<in> D. x \<le> a \<and> \<not> (x \<le> b)))" by (metis is_sup_iso1 less_le_not_le rolc_mem_iff1 subsetI)
lemma meet_denseD4:"\<lbrakk>D \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> is_inf X ([x)\<^sub>D) x)\<rbrakk> \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> X; b \<in> X ; a < b\<rbrakk>  \<Longrightarrow>(\<exists>x \<in> D. a \<le> x \<and> \<not> (b \<le> x)))" by (metis is_inf_ant1 less_le_not_le lorc_mem_iff1 subsetI)

lemma join_denseD5:"\<lbrakk>D \<subseteq> X; is_clattice X;  (\<And>a b. \<lbrakk>a \<in> X; b \<in> X ; b < a\<rbrakk>  \<Longrightarrow>(\<exists>x \<in> D. x \<le> a \<and> \<not> (x \<le> b)))\<rbrakk> \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> is_sup X ((x]\<^sub>D) x)"
proof-
  assume A0:"D \<subseteq> X" "is_clattice X"  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X ; b <a \<rbrakk>\<Longrightarrow>(\<exists>x \<in> D. x \<le> a \<and> \<not> (x \<le> b)))"
  show "(\<And>x. x \<in> X \<Longrightarrow> is_sup X ((x]\<^sub>D) x)"
  proof-
    fix a assume A1:"a \<in> X"
    obtain b where B0:"is_sup X ((a]\<^sub>D) b"   by (meson A0 clatD21 order_trans rolc_subset1)
    have B1:"b \<le> a"  by (meson A1 B0 is_supD42 rolc_mem_iff1 ub_def)
    have "b=a"
    proof(rule ccontr)
      assume con1:"\<not> (b=a)" obtain con2:"b < a"     by (simp add: B1 con1 order_less_le)
      obtain x where  B2:"x \<in> D \<and> x \<le> a \<and> \<not>(x \<le> b)"   using A0(3) A1 B0 con2 is_supE1 by blast
      have B3:"x \<in> (a]\<^sub>D"   using B2 rolcI1 by blast
      show False
        using B0 B2 B3 is_supD1121 by blast
    qed
    show "is_sup X ((a]\<^sub>D) a"
      using B0 \<open>(b::'a::order) = (a::'a::order)\<close> by blast
  qed
qed
lemma meet_denseD5:"\<lbrakk>D \<subseteq> X; is_clattice X;  (\<And>a b. \<lbrakk>a \<in> X; b \<in> X ; a < b\<rbrakk>  \<Longrightarrow>(\<exists>x \<in> D. a \<le> x \<and> \<not> (b \<le> x)))\<rbrakk> \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> is_inf X ([x)\<^sub>D) x)"
proof-
  assume A0:"D \<subseteq> X" "is_clattice X"  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X ; a < b \<rbrakk>\<Longrightarrow>(\<exists>x \<in> D. a \<le> x \<and> \<not> (b \<le> x)))"
  show "(\<And>x. x \<in> X \<Longrightarrow> is_inf X ([x)\<^sub>D) x)"
  proof-
    fix a assume A1:"a \<in> X"
    obtain b where B0:"is_inf X ([a)\<^sub>D) b"   by (meson A0 clatD22 order_trans lorc_subset1)
    have B1:"a \<le> b"  by (meson A1 B0 is_infD42 lorc_mem_iff1 lb_def)
    have "b=a"
    proof(rule ccontr)
      assume con1:"\<not> (b=a)" obtain con2:"a < b"  using B1 con1 by auto 
      obtain x where  B2:"x \<in> D \<and> a \<le> x \<and> \<not>(b \<le> x)"   using A0(3) A1 B0 con2 is_infE1 by blast
      have B3:"x \<in> [a)\<^sub>D"   using B2 lorcI1 by blast
      show False using B0 B2 B3 is_infD1121 by blast
    qed
    show "is_inf X ([a)\<^sub>D) a"using B0 \<open>(b::'a::order) = (a::'a::order)\<close> by blast
  qed
qed


(*
  in a csup semilattice an element is compact iff directed coverings contain an upper bound
*)


lemma compactD1:
  "\<lbrakk>is_compact X c; A \<in> Pow_ne X; c \<le> Sup X A; is_dir A (\<le>)\<rbrakk> \<Longrightarrow> (\<exists>A0. \<exists>a. a \<in> A \<and> a ub A0 \<and> A0 \<in> Fpow_ne A \<and> c \<le> Sup X A0)"
  by (metis compactD fpow_ne_iff2 updir_finite2)


lemma ccompact0:
  assumes A0:"is_sup_semilattice X" and
          A1:"is_compact X c" and
          A2:"A \<in> Pow_ne X" and
          A3:"c \<le> Sup X A" and
          A4:"is_dir A (\<le>)"
  shows "\<exists>a \<in> A. c \<le> a"
proof-
  obtain A0 a where A5:"a \<in> A \<and> a ub A0 \<and> A0 \<in> Fpow_ne A \<and> c \<le> Sup X A0"
    using A1 A2 A3 A4 compactD1 by blast
  have A7:"a \<in> ubd X A0"
     using A2 A5 pow_neD1 ubdI2 by blast 
  have B0:"Sup X A0 \<le> a" 
    using fsup_lub3[of X A0 a] A0 A2 A5 A7 fpow_ne_iso2 by blast
  have B1:"c \<le> a"
    using A5 B0 by fastforce
  show ?thesis
    using A5 B1 by blast
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
    by (simp add: A1 P0 compactI)
qed

lemma dir_set_closure_subset:
  assumes A0:"is_clr C (Pow X)" and 
          A1:"(\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C)" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (\<le>) \<Longrightarrow> \<Union>D \<in> C)" and
          A3:"x \<in> X" and 
          A4:"A \<in> Pow_ne C" and
          A5:"cl_from_clr C {x} \<subseteq> Sup C A" and 
          A6:"is_dir A (\<subseteq>)"
  shows "\<exists>a \<in> A. cl_from_clr C {x} \<subseteq> a"
proof-
  let ?f="cl_from_clr C"
  have B2:"Sup C A = \<Union>A"
    by (metis A0 A2 A4 A6 clrD2 pow_neD1 pow_ne_iff1 sup_equality uni_sup_fam)
  have B2:"{x} \<subseteq> ?f {x}"
    by (metis A0 A3 PowD PowI Pow_bottom cl_ext1 insert_subsetI)
  have B3:"... \<subseteq> \<Union>A"
    by (metis A0 A2 A4 A5 A6 clrD2 pow_neD1 pow_ne_iff1 sup_equality uni_sup_fam)
  have B4:"{x} \<subseteq> \<Union>A"
    using B2 B3 by blast
  obtain a where B5:"a \<in> A \<and> x \<in> a"
    using B4 by auto
  have B6:"a \<in> ubd C {{x}}"
    using A4 B5 pow_neD1 ubd_singleton_iff by fastforce
  have B7:"?f {x} \<subseteq> a"
    by (metis A0 A3 B6 Pow_iff cl_lt_ub1 empty_subsetI insert_subset)
  show "(\<exists>a\<in>A. cl_from_clr C {x} \<subseteq> a)"
   using B5 B7 by auto
qed

      

lemma singleton_closure_compact:
  assumes A0:"is_clr C (Pow X)" and 
          A1:"(\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C)" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk>\<Longrightarrow> is_dir D (\<le>) \<Longrightarrow> \<Union>D \<in> C)" and
          A3:"x \<in> X"
  shows "is_compact C (cl_from_clr C {x})"
  apply(rule ccompact1) 
   using A0 clatD1 clr_is_clattice pow_is_clattice apply blast
  using A0 A3 cl_range1 apply fastforce
  by (metis A0 A1 A2 A3 dir_set_closure_subset)

lemma closed_compgen:
  assumes A0:"is_clr C (Pow X)" and 
          A1:"(\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C)" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (\<le>) \<Longrightarrow> \<Union>D \<in> C)" and
          A3:"E \<in> C"
  shows "(\<exists>A \<in> Pow (compact_elements C). is_sup C A E)"
proof-
   let ?f="cl_from_clr C"
   let ?A="{y. (\<exists>x \<in> E. y= ?f {x})}"
  have B0:"is_clattice C"
    using A0 clr_is_clattice pow_is_clattice by blast
  have B1:"\<And>x. x \<in> X \<longrightarrow> is_compact C (?f {x})"
    by (metis A0 A1 A2 singleton_closure_compact)
   have P1:"E \<in> Pow X"
      using A0 A3 clrD2b by blast
    have P2:"\<forall>x. x \<in> E \<longrightarrow> {x} \<in> Pow X"
      using P1 by blast 
    have P3:"?A \<subseteq> C"
    proof 
      fix y assume A9:"y \<in> ?A" 
      obtain x where P30:"x \<in> E \<and> y = ?f {x}" using A9 by blast
      show "y \<in> C" using A0 P2 P30 cl_range1 by fastforce
    qed
    have B9:"\<forall>x. x \<in> E \<longrightarrow> {x} \<subseteq> ?f {x}"
      by (meson A0 P2 cl_ext1)
    have B10:"?f E = E"
      by (simp add: A3 cl_from_clr_def ub_single_least2)
    have B11:"\<And>x. x \<in> E \<longrightarrow> ?f {x} \<subseteq> ?f E"
      by (metis A0 A3 B10 P2 cl_lt_ub2 empty_subsetI insert_subsetI)
    have B11b:"E ub ?A"
      using B10 B11 ub_def by force
    have B11c:"E \<in> ubd C ?A"
      by (simp add: A3 B11b ubd_mem_iff)
    have B12:"E = (\<Union>x \<in> E. {x})"
      by simp
    have B13:"... \<subseteq> (\<Union>x \<in> E. ?f {x})"
      using B9 by blast
    have B14:"... = (\<Union>?A)"
      by blast
    have B15:"... = Sup UNIV ?A"
      by (meson union_sup_univ)
    have B16:"... \<subseteq> Sup C ?A"
      using sup_iso2[of UNIV C ?A] univ_is_clattice using A3 B0 P3 by blast
    have B17:"... \<subseteq> E"
      by (metis (no_types, lifting) A3 B0 B11b P3 clatD21 is_supD5 sup_equality)
    have B18:"\<forall>x. x \<in> ?A \<longrightarrow> x \<in> compact_elements C"
      using A0 A3 B1 PowD clrD2 compact_elements_mem_iff1 mem_Collect_eq by fastforce
    have B19:"?A \<in> Pow (compact_elements C)"
      using B18 by blast
    have B20:"E = Sup C ?A"
      using B13 B15 B16 B17 by auto
    have B21:"is_sup C ?A E"
      by (metis (mono_tags, lifting) A3 B11b B12 B13 B14 Sup_le_iff is_supI7 subset_antisym ub_def)
    show "\<exists>A \<in> Pow (compact_elements C). is_sup C A E"
      using B19 B21 by blast
qed


lemma clr_compgen1:
  assumes A0:"is_clr C (Pow X)" and 
          A1:"(\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C)" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (\<le>) \<Longrightarrow> \<Union>D \<in> C)"
  shows "compactly_generated C \<and> (\<forall>x. x \<in> X \<longrightarrow> is_compact C ((cl_from_clr C) {x}))"
proof-
  have P0:"C \<subseteq> Pow X"
    by (simp add: A0 clrD2)
  let ?f="cl_from_clr C"
  have B0:"is_clattice C"
    using A0 clr_is_clattice pow_is_clattice by blast
  have B1:"\<And>x. x \<in> X \<longrightarrow> is_compact C (?f {x})"
    by (metis A0 A1 A2 singleton_closure_compact)
  have B8:"\<And>E. E \<in> C \<longrightarrow>  (\<exists>A \<in> Pow (compact_elements C). is_sup C A E)"
    by (metis A0 A1 A2 closed_compgen)
  show ?thesis
    by (simp add: B1 B8 compactly_generatedI1)
qed


lemma clr_compgen2:
 "\<lbrakk>is_clr C (Pow X); (\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C);(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (\<le>) \<Longrightarrow> \<Union>D \<in> C)\<rbrakk> \<Longrightarrow> compactly_generated C"
  by (simp add: clr_compgen1)

lemma filters_on_lattice_compactgen0:
  assumes lat:"is_lattice X" and top:"is_greatest X top" and nem:"X \<noteq> {}"
  shows filters_on_lattice_compactgen01:"is_clr (filters_on X) (Pow X)" and 
        filters_on_lattice_compactgen02:"(\<And>A. \<lbrakk>A \<subseteq>  (filters_on X) ; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in>  (filters_on X) )" and
        filters_on_lattice_compactgen03:"(\<And>D. \<lbrakk>D \<subseteq>  (filters_on X) ; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (\<le>) \<Longrightarrow> \<Union>D \<in>  (filters_on X) )"
proof-
  show "is_clr (filters_on X) (Pow X)"  using filter_is_clr lat lattD41 nem top by blast
  show " \<And>A. A \<subseteq> filters_on X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<Inter> A \<in> filters_on X"  using filters_onI inter_filters_filter lat latt_iff pow_ne_iff2 top by blast
  show " \<And>D. D \<subseteq> filters_on X \<Longrightarrow> D \<noteq> {} \<Longrightarrow> is_dir D (\<subseteq>) \<Longrightarrow> \<Union> D \<in> filters_on X"
  proof-
    fix D assume A0:"D \<subseteq> filters_on X" and A1:"D \<noteq> {}" and A2:"is_dir D (\<subseteq>)"
    have A3:"is_filter X (\<Union> D)"
    proof(rule is_filterI1)
      show "\<Union> D \<noteq> {}" using A0 A1 filters_on_iff is_filter_top top by fastforce
      show "\<Union> D \<subseteq> X" using A0 filters_onE is_filterE1 by fastforce
      show "is_dir (\<Union> D) (\<lambda>x y. y \<le> x)"
      proof(rule is_dirI1)
        show "\<And>a b. a \<in> \<Union> D \<Longrightarrow> b \<in> \<Union> D \<Longrightarrow> \<exists>c\<in>\<Union> D. c \<le> a \<and> c \<le> b"
        proof-
          fix a b assume A4:"a \<in> \<Union> D " and A5:"b \<in> \<Union> D"
          then obtain Fa Fb where fa1:"Fa \<in> D" and fb1:"Fb \<in>D" and fa2:"a \<in> Fa" and fb2:"b\<in> Fb" by blast
          then obtain Fab where fab1:"Fab \<in> D" and  fab2:"Fa \<subseteq>  Fab" and fab3: "Fb \<subseteq> Fab" using A2 is_dirE1[of D "(\<le>)" Fa Fb] by blast
          then obtain fab4:"a \<in> Fab" and fab5:"b \<in> Fab" and fab6:"is_filter X Fab"     using A0 fa2 fb2 filters_onE by blast
          then obtain fab5:"Inf X {a, b} \<in> Fab"  using filter_finf_closed_isl lat lattD41 by blast
          obtain "Inf X {a, b} \<le> a" and "Inf X {a, b} \<le> b" by (meson A4 A5 \<open>\<Union> (D::'a::order set set) \<subseteq> (X::'a::order set)\<close> binary_infD32 binf_leI1 dual_order.refl lat lattD41 sinfD3 sinfD4 subset_iff)
          then show "\<exists>c\<in>\<Union> D. c \<le> a \<and> c \<le> b"   using fab1 fab5 by blast
        qed
    qed
    show " is_ord_cl X (\<Union> D) (\<le>)"
    proof(rule is_ord_clI)
      show " \<And>a b. a \<in> \<Union> D \<Longrightarrow> b \<in> X \<Longrightarrow> a \<le> b \<Longrightarrow> b \<in> \<Union> D"
      proof-
        fix a b assume a0:"a \<in> \<Union> D " and b0:" b \<in> X " and ab:"a \<le> b"
        then obtain F where f0:"F \<in> D" and "a \<in> F"  and "is_filter X F"  using A0 filters_onE by auto 
        then obtain "b \<in> F" using ab b0 is_filterE1[of X F] is_ord_clE[of X F "(\<le>)" a b] by blast
        then show "b \<in> \<Union> D" using f0 by blast
      qed
   qed
 qed
 then show " \<Union> D \<in> filters_on X"  by (simp add: filters_on_iff)
qed

qed

lemma filters_on_lattice_compactgen:
  "\<lbrakk>is_lattice X; is_greatest X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> compactly_generated (filters_on X)" 
proof-
  assume lat:"is_lattice X" and top:" is_greatest X top" and nem:"X \<noteq> {}"
  show "compactly_generated (filters_on X)"
  by (metis clr_compgen2 filters_on_lattice_compactgen01 filters_on_lattice_compactgen02 filters_on_lattice_compactgen03 lat nem top)
qed

lemma principal_filters_compact:
  assumes A0:"is_lattice X" and A1:"is_greatest X top" and A2:"X \<noteq> {}" and A3:"F \<in> filters_on X"
  shows "is_compact (filters_on X) F \<longleftrightarrow> (\<exists>x \<in> X. F = (lorc x X))" (is "?L \<longleftrightarrow> ?R")
proof-
  let ?A="{lorc x X|x. x \<in>F}"
  have B0:"F \<subseteq> X" by (simp add: A3 filters_onE is_filterE1)
  have B1:"\<And>x. x \<in> F \<Longrightarrow> x \<in> lorc x X"  using B0 lorc_memI1 by blast
  have B3:"{lorc x X|x. x \<in>F} \<in> Pow_ne (filters_on X)"   unfolding Pow_ne_def apply(auto)   using B0 lorc_filter2 apply auto[1]    using A3 filters_on_def is_filterE1 by blast
  obtain s where iss:"is_sup (filters_on X) ?A s"  by (metis (no_types, lifting) A0 B3 csupD2 filters_on_lattice_csup pow_ne_iff2)
  have B2:"F \<subseteq>\<Union>?A" using B0 B1 by blast
  also have B21:"... \<le>  s" using is_supD1121 iss by fastforce
  also have B22:"... = Sup (filters_on X) ?A" using iss sup_equality by blast
  then obtain B4:"F \<le> Sup (filters_on X) {lorc x X|x. x \<in>F}"   using calculation by blast
  have B5:" Sup (filters_on X) {lorc x X|x. x \<in>F} \<in> filters_on X"  using B22 is_supE1 iss by blast
  then have B6:"is_dir ( Sup (filters_on X) {lorc x X|x. x \<in>F}) (\<le>)"    by (smt (verit) A1 filters_onE greatest_iff in_mono is_dirI1 is_filterE1 is_filter_top) 
  have B4:" (\<exists>x \<in> X.  lorc x X = F ) \<Longrightarrow> is_compact (filters_on X) F "
  proof-
    assume "(\<exists>x \<in> X. lorc x X = F)" then obtain x where "x \<in> X" and B40:"lorc x X = F"  by auto
    then obtain B41:"is_compact (filters_on X) (cl_from_clr (filters_on X) {x})"
      by (metis A0 A1 A2 filters_on_lattice_compactgen01 filters_on_lattice_compactgen02 filters_on_lattice_compactgen03 singleton_closure_compact)
    have B42:"lorc x X \<in> ubd (filters_on X) {{x}}" 
     proof(rule  ubdI)
        show "\<And>a::'a set. a \<in> {{x}} \<Longrightarrow> a \<subseteq> [x)\<^sub>X"  using \<open>(x::'a::order) \<in> (X::'a::order set)\<close> lorc_memI1 by force
        show "([x)\<^sub>X) \<in> filters_on X"   by (simp add: A3 B40)
     qed
   have B43:"is_least (ubd (filters_on X) {{x}}) (lorc x X)"
    proof(rule leastI3)
      show " \<And>a::'a set. a \<in> ubd (filters_on X) {{x}} \<Longrightarrow> ([x)\<^sub>X) \<subseteq> a"
      proof-
        fix a assume  "a \<in> ubd (filters_on X) {{x}}" then obtain "x \<in> a"  and "is_ord_cl X a (\<le>)"
        by (meson filters_on_iff insert_subset is_filterE1 ubdD2 ubd_mem_singleE)  
        then show "([x)\<^sub>X) \<subseteq> a"
        by (metis B0 B40 is_ord_clE lorc_eq_upbd subset_iff ubd_mem_singleE)
      qed 
     show "([x)\<^sub>X) \<in> ubd (filters_on X) {{x}}" using B42 by auto
  qed
  then show "is_compact (filters_on X) F"
  by (metis B40 B41 cl_from_clr_def least_equality2)
  qed 
  have B3:"is_compact (filters_on X) F \<Longrightarrow>  (\<exists>x \<in> X.  lorc x X = F )"
  proof-
    assume B3A0:"is_compact (filters_on X) F"  
    obtain A0 where B31:"A0 \<in> Fpow_ne ?A " and B32:"F \<le> Sup (filters_on X) A0" using B3A0 B4 B3 compactD[of "filters_on X" F ?A]
    using \<open>\<And>thesis::bool. ((F::'a::order set) \<subseteq> Posets27.Sup (filters_on (X::'a::order set)) {[x)\<^sub>X |x::'a::order. x \<in> F} \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by blast 
    have B33:"\<And>Ai. Ai \<in> A0 \<Longrightarrow> (\<exists>x. is_least Ai x)"
    proof-
      fix Ai assume "Ai \<in> A0" then obtain x where "x \<in> F" and "Ai = lorc x X"   using B31 fpow_neD1 by blast
      then obtain "is_least Ai x"  by (simp add: B1 leastI3 lorcD12)
      then show "(\<exists>x. is_least Ai x)" by blast
    qed
    define S where "S \<equiv> (\<lambda>Ai. THE x. x \<in> F \<and> is_least Ai x)"
    have B34:"\<And>Ai. Ai \<in> A0 \<Longrightarrow> (S Ai) \<in> F \<and> is_least Ai (S Ai) \<and> lorc (S Ai) X = Ai" 
    proof-
      fix Ai assume "Ai \<in> A0" then obtain x where B340:"x \<in> F" and B34A0:"Ai = lorc x X"   using B31 fpow_neD1 by blast
      then obtain B341:"is_least Ai x"  by (simp add: B1 leastI3 lorcD12)
      then obtain B342: "(S Ai) \<in>F" and B343:"is_least Ai (S Ai)" unfolding S_def   by (metis (no_types, lifting) B340 least_unique theI')
       obtain "lorc (S Ai) X = Ai"   by (metis B341 B343 B34A0 least_unique)
      then show "(S Ai) \<in> F \<and> is_least Ai (S Ai) \<and> lorc (S Ai) X = Ai" using B342 B343 by blast
    qed
    then obtain B35:"(S`A0) \<subseteq> F" and B36:"finite (S`A0)"   using B31 fpow_ne_iff2 by blast 
    then obtain B37:"Inf X (S`A0) \<in> F"   by (metis (no_types, lifting) A0 A3 B31 empty_is_image filter_finf_closed3 filters_on_iff fpow_ne_iff2 latt_iff)
    then obtain B38:"lorc (Inf X (S`A0)) X \<subseteq> F " unfolding lorc_def using filters_onE[of F X] is_filterE1[of X F] is_ord_clE[of X F "(\<le>)"] A3 by blast
    have B39:"\<And>Ai. Ai \<in> {lorc f X|f. f \<in>  (S`A0)} \<Longrightarrow> Ai \<in> A0" using B34 by force
    also have B40:"\<And>Ai. Ai \<in> A0 \<Longrightarrow>  Ai \<in> {lorc f X|f. f \<in>  (S`A0)} " using B34 by force
    then have B41:"A0 =  {lorc f X|f. f \<in>  (S`A0)}"   using calculation by blast 
    obtain B42:"lorc (Inf X (S`A0)) X = Sup (filters_on X) A0" unfolding S_def using lorc_inter2[of X "(S`A0)"] B41
    by (metis (no_types, lifting) A0 B0 B31 B35 B36 S_def fpow_ne_iff2 image_cong image_is_empty subset_trans)
    then show " (\<exists>x \<in> X.  lorc x X = F )"
    using B0 B32 B37 B38 by blast
  qed
  then show ?thesis
  using B4 by blast
qed 


lemma distr_lattice_filters:
  "distributive_lattice X \<Longrightarrow> is_lattice (filters_on X)"
  by (simp add: distributive_lattice_def filters_on_lattice_inf_semilattice1 filters_on_lattice_sup_semilattice2b lattI2)
  
lemma lattice_filters_distr:
  assumes A0:"distributive_lattice X" 
  shows "distributive_lattice (filters_on X)"
proof-
  let ?F="filters_on X"
  have B01:"is_lattice X"  using assms distributive_lattice_def by blast
  have B02:"is_lattice ?F"
    by (simp add: assms distr_lattice_filters)
  have B1:" \<And>x y z. x \<in> ?F \<and>  y \<in>?F \<and> z \<in> ?F \<longrightarrow> Inf ?F {Sup ?F {x, y}, Sup ?F {x, z}} \<subseteq> Sup ?F {x, Inf ?F {y, z}}"
  proof
    fix f g h assume A1:" f \<in> ?F \<and>  g \<in>?F \<and> h \<in> ?F"
    let ?sfg="Sup ?F {f, g}" and ?sfh="Sup ?F {f, h}" and  ?igh="Inf ?F {g, h}"
    show "Inf ?F {?sfg, ?sfh} \<subseteq> Sup ?F {f, ?igh}"
    proof
      fix z assume A2:"z \<in> (Inf ?F {?sfg, ?sfh})"
      have B2:"Inf ?F {?sfg, ?sfh} =?sfg \<inter> ?sfh"
        by (meson A1 B01 filters_on_iff filters_on_lattice_inf8b filters_on_lattice_sup_semilattice2b inf_equality ssupD4)
      have B3:"z \<in> ?sfg \<and> z \<in> ?sfh"
        using A2 B2 by blast
      obtain x1 y where B4:"x1 \<in> f \<and> y \<in> g \<and> Inf X {x1, y} \<le> z"
        using A1 B01 B3 filters_on_iff filters_on_lattice_bsup2 by blast
      obtain x2 t where B5:"x2 \<in> f \<and> t \<in> h \<and> Inf X {x2, t} \<le> z"
        using A1 B01 B3 filters_on_iff filters_on_lattice_bsup2 by blast
      have B450:"x1 \<in> X \<and> y \<in> X \<and> x2 \<in> X \<and> t \<in> X"
      by (meson A1 B4 B5 filters_on_iff in_mono is_filterE1)
      have B6:"Sup X {x1, Inf X {x2, t}} \<in> f"
      by (simp add: A1 B01 B4 B450 filters_onE lattD41 lattice_filter_memI sinfD4)
      have B7:"Sup X {y, x2} \<in> f"
      by (simp add: A1 B01 B450 B5 filter_on_lattice_sup01 filters_onE)
      have B8:"Sup X {y, t} \<in> g"
      by (simp add: A1 B01 B4 B450 filters_onE lattice_filter_memI)
      have B9:"Sup X {y, t} \<in> h"
      by (simp add: A1 B01 B450 B5 filter_on_lattice_sup01 filters_onE)
      have B10:"Inf X {Sup X {x1, Inf X {x2, t}}, Sup X {y, x2}} \<in> f"
      by (simp add: A1 B01 B6 B7 filter_finf_closed_isl filters_onE lattD41)
      have B11:"Inf X {Sup X {y, x2}, Sup X {y, t}} = Sup X {y, Inf X {x2, t}}"
        by (simp add: B450 assms distr_latticeD1)
      have B12:"Inf X {Sup X {x1, Inf X {x2, t}}, Inf X {Sup X {y, x2}, Sup X {y, t}}} =
                Inf X {Sup X {x1, Inf X {x2, t}},  Sup X {y, Inf X {x2, t}}}"
        by (simp add: B11)
      have B13:"... = Sup X {Inf X {x2, t}, Inf X {x1, y}}"
        by (simp add: B01 B450 assms bsup_commute2 distr_latticeD2 lattD41 sinfD4)
      have B14:"... = Sup X {Inf X {x1, y}, Inf X {x2, t}}"
        by (simp add: insert_commute)
      have B15:"Sup X {Inf X {x1, y}, Inf X {x2, t}} = Inf X {Sup X {x1, Inf X {x2, t}}, Inf X {Sup X {y, x2}, Sup X {y, t}}} "
        using B11 B13 B14 by presburger
      have B16:"... =  Inf X {Inf X {Sup X {x1, Inf X {x2, t}}, Sup X {y, x2}}, Sup X {y, t}}"
        by (simp add: B01 B450 binf_assoc1 lattD41 lattD42 sinfD4 ssupD4)
      have B17:"z \<ge> Sup X {Inf X {x1, y}, Inf X {x2, t}}"
      by (metis A1 B01 B3 B4 B450 B5 bsup_iff filter_bsup_mem_iff filters_onE filters_on_lattice_bsup8 lattD41 lattD42 sinfD4)
      have B18:"z \<ge>  Inf X {Inf X {Sup X {x1, Inf X {x2, t}}, Sup X {y, x2}}, Sup X {y, t}}"
        using B11 B13 B14 B16 B17 by presburger
      have B19:"Inf X {Sup X {x1, Inf X {x2, t}}, Sup X {y, x2}} \<in> f"
        by (simp add: B10)
      have B20:"Sup X {y, t} \<in> Inf ?F {g, h}"
        by (metis A1 B01 B8 B9 IntI filters_on_iff filters_on_lattice_inf8b inf_equality)
      have B21:"z \<in> binary_filter_sup X f ?igh"
        by (metis A1 B01 B10 B18 B20 B3 filter_bsup_mem_iff filters_on_iff filters_on_lattice_bsup8)
      have B22:" binary_filter_sup X f ?igh = Sup ?F {f, ?igh}"
        by (metis A1 B01 B02 filters_on_iff filters_on_lattice_bsup8 lattD41 sinfD4)
      show "z \<in> Sup ?F {f, ?igh}"
        using B21 B22 by blast
    qed
  qed
  show ?thesis
    by (simp add: B02 B1 distr_latticeI1)
qed
(*
TODO:  the converse: first prove some lemmas about sublattices and inheritance then specify
       using the principal embedding.  Or just use the latter straight off the bat.
*)

(*
                   (y \<or> x2) \<and> (y \<or> t) = y \<or> (x2 \<and> t)

(x1 \<or> (x2 \<and> t)) \<and> (y \<or> x2) \<and> (y \<or> t) = (x1 \<or> (x2 \<and> t)) \<and> (y \<or> (x2 \<and> t))

= (x2 \<and> t) \<or> (x1 \<and> y)

*)



definition sup_prime::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "sup_prime X A \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. (Sup X {a, b}) \<in> A \<longrightarrow> (a \<in> A \<or> b \<in> A))"

definition inf_prime::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "inf_prime X A \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. (Inf X {a, b}) \<in> A \<longrightarrow> (a \<in> A \<or> b \<in> A))"

lemma sup_primeD1:
  "\<lbrakk>sup_prime X A; a \<in> X; b \<in> X; Sup X {a, b} \<in> A\<rbrakk> \<Longrightarrow> a \<in> A \<or> b \<in> A"
  by (simp add:sup_prime_def)

lemma inf_primeD1:
  "\<lbrakk>inf_prime X A; a \<in> X; b \<in> X; Inf X {a, b} \<in> A\<rbrakk> \<Longrightarrow> a \<in> A \<or> b \<in> A"
  by (simp add:inf_prime_def)

lemma sup_primeI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; Sup X {a, b} \<in> A\<rbrakk> \<Longrightarrow> (a \<in> A \<or> b \<in> A)) \<Longrightarrow> sup_prime X A"
  by (simp add:sup_prime_def)

lemma inf_primeI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; Inf X {a, b} \<in> A\<rbrakk> \<Longrightarrow> (a \<in> A \<or> b \<in> A)) \<Longrightarrow> inf_prime X A"
  by (simp add:inf_prime_def)

definition elem_sup_prime::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "elem_sup_prime X x \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. x \<le> Sup X {a, b} \<longrightarrow> (x \<le> a \<or> x \<le> b))"

definition elem_inf_prime::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "elem_inf_prime X x \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. x \<ge> Inf X {a, b} \<longrightarrow> (x \<ge> a \<or> x \<ge> b))"

lemma elem_sup_primeD1:
  "\<lbrakk>elem_sup_prime X x; a \<in> X; b \<in> X; x \<le> Sup X {a, b}\<rbrakk> \<Longrightarrow> (x \<le> a \<or> x \<le> b)"
  by(simp add:elem_sup_prime_def)

lemma elem_inf_primeD1:
  "\<lbrakk>elem_inf_prime X x; a \<in> X; b \<in> X; x \<ge> Inf X {a, b}\<rbrakk> \<Longrightarrow> (x \<ge> a \<or> x \<ge> b)"
  by(simp add:elem_inf_prime_def)

lemma elem_sup_primeI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; x \<le> Sup X {a, b}\<rbrakk> \<Longrightarrow> (x \<le> a \<or> x \<le> b)) \<Longrightarrow> elem_sup_prime X x"
  by (simp add:elem_sup_prime_def)

lemma elem_inf_primeI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; x \<ge> Inf X {a, b}\<rbrakk> \<Longrightarrow> (x \<ge> a \<or> x \<ge> b)) \<Longrightarrow> elem_inf_prime X x"
  by (simp add:elem_inf_prime_def)

lemma elem_sup_primeE1:
  "\<lbrakk>x \<in> X; elem_sup_prime X x\<rbrakk> \<Longrightarrow> sup_prime X ([x)\<^sub>X)"
  by (metis elem_sup_prime_def lorcD12 lorcI1 sup_prime_def)       

lemma elem_inf_primeE1:
  "\<lbrakk>x \<in> X; elem_inf_prime X x\<rbrakk> \<Longrightarrow> inf_prime X ((x]\<^sub>X)"
  by (metis elem_inf_prime_def rolcD12 rolcI1 inf_prime_def)

lemma elem_sup_primeI2:
  "\<lbrakk>x \<in> X;sup_prime X ([x)\<^sub>X); is_sup_semilattice X\<rbrakk> \<Longrightarrow> elem_sup_prime X x"
  by (metis elem_sup_prime_def lorcD12 lorcI1 ssupD4 sup_prime_def)

lemma elem_inf_primeI2:
  "\<lbrakk>x \<in> X; inf_prime X ((x]\<^sub>X); is_inf_semilattice X\<rbrakk> \<Longrightarrow> elem_inf_prime X x"
  by (metis elem_inf_prime_def rolcD12 rolcI1 sinfD4 inf_prime_def)


definition fin_sup_irr::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where
  "fin_sup_irr X x \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. x = Sup X {a, b} \<longrightarrow> (x = a \<or> x = b))" 

definition fin_inf_irr::"'a::order set \<Rightarrow> 'a::order \<Rightarrow> bool" where 
  "fin_inf_irr X x \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. x = Inf X {a, b} \<longrightarrow> x = a \<or> x =b)"

lemma fin_sup_irrD1:
  "\<lbrakk>fin_sup_irr X x; a \<in> X; b \<in> X; x=Sup X {a, b}\<rbrakk> \<Longrightarrow> (x = a \<or> x =b)"
  by (simp add:fin_sup_irr_def)

lemma fin_inf_irrD1:
  "\<lbrakk>fin_inf_irr X x; a \<in> X; b \<in> X; x=Inf X {a, b}\<rbrakk> \<Longrightarrow> (x = a \<or> x =b)"
  by (simp add:fin_inf_irr_def)

lemma fin_sup_irrI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; x = Sup X {a, b}\<rbrakk> \<Longrightarrow> x =a \<or> x =b) \<Longrightarrow> fin_sup_irr X x"
  by (simp add: fin_sup_irr_def)

lemma fin_inf_irrI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; x = Inf X {a, b}\<rbrakk> \<Longrightarrow> x =a \<or> x =b) \<Longrightarrow> fin_inf_irr X x"
  by (simp add: fin_inf_irr_def)

lemma fin_sup_irrE1:
  "\<lbrakk>distributive_lattice X; x \<in> X; elem_sup_prime X x\<rbrakk> \<Longrightarrow> fin_sup_irr X x"
  by (simp add: bsup_iff distributive_lattice_def elem_sup_primeD1 fin_sup_irr_def lattD42 order_class.order_eq_iff)

lemma fin_inf_irrE1:
  "\<lbrakk>distributive_lattice X; x \<in> X; elem_inf_prime X x\<rbrakk> \<Longrightarrow> fin_inf_irr X x"
  by (simp add: binf_iff distributive_lattice_def elem_inf_primeD1 fin_inf_irr_def lattD41 order_class.order_eq_iff)
(*(\<forall>a \<in> X. \<forall>b \<in> X. x \<le> Sup X {a, b} \<longrightarrow> (x \<le> a \<or> x \<le> b))*)
(*(\<forall>a \<in> X. \<forall>b \<in> X. x = Sup X {a, b} \<longrightarrow> (x = a \<or> x = b)*)

(*
  x \<le> a \<or> b \<longleftrightarrow> x \<and> (a \<or> b) = x \<longleftrightarrow> (x \<and> a) \<or> (x \<and> b) = x \<longleftrightarrow> (x \<and> a) = a \<or> (x \<and> b) = x \<longleftrightarrow> x \<le> a \<or> x \<le> b
*)

lemma elem_sup_primeI3:
  assumes A0:"distributive_lattice X" and A1:"x \<in> X" and A2: "fin_sup_irr X x"
  shows "elem_sup_prime X x"
proof-
  have B0:"\<And>a b. a \<in> X \<and> b \<in> X \<and> x \<le> Sup X {a, b} \<longrightarrow> (x \<le> a \<or> x \<le> b)"
  proof
    fix a b assume P:"a \<in> X \<and>b \<in> X \<and> x \<le> Sup X {a, b}"
    have B1:"x = Inf X {x, Sup X {a, b}}"
      using A0 A1 P distributive_lattice_def lattD42 le_inf1 ssupD4 by fastforce
    have B2:"... = Sup X {Inf X {x, a}, Inf X {x, b}}"
      by (simp add: A0 A1 P distr_latticeD3)
    have B3:"x = Inf X {x, a} \<or> x = Inf X {x, b}"
      by (metis A0 A1 A2 B1 B2 P distributive_lattice_def fin_sup_irr_def lattD41 sinfD4)
    show "x \<le>a \<or> x \<le> b"
      by (metis A0 A1 B3 P distributive_lattice_def latt_le_iff1)
  qed
  show ?thesis
    by (simp add: B0 elem_sup_primeI1)
qed
  
  
lemma elem_inf_primeI3:
  assumes A0:"distributive_lattice X" and A1:"x \<in> X" and A2: "fin_inf_irr X x"
  shows "elem_inf_prime X x"
proof-
  have B0:"\<And>a b. a \<in> X \<and> b \<in> X \<and> x \<ge> Inf X {a, b} \<longrightarrow> (x \<ge> a \<or> x \<ge> b)"
  proof
    fix a b assume P:"a \<in> X \<and>b \<in> X \<and> x \<ge> Inf X {a, b}"
    have B1:"x = Sup X {x, Inf X {a, b}}"
      using A0 A1 P distributive_lattice_def ge_sup2 lattD41 sinfD4 by fastforce
    have B2:"... = Inf X {Sup X {x, a}, Sup X {x, b}}"
      by (simp add: A0 A1 P distr_latticeD1)
    have B3:"x = Sup X {x, a} \<or> x = Sup X {x, b}"
      by (metis A0 A1 A2 B1 P distributive_lattice_def fin_inf_irr_def lattD42 ssupD4)
    show "x \<ge>a \<or> x \<ge> b"
      by (metis A0 A1 B3 P distributive_lattice_def latt_ge_iff2)
  qed
  show ?thesis
    by (simp add: B0 elem_inf_primeI1)
qed


lemma sup_prime_iff:
  "\<lbrakk>distributive_lattice X; x \<in> X\<rbrakk> \<Longrightarrow> (elem_sup_prime X x \<longleftrightarrow> fin_sup_irr X x)"
  using elem_sup_primeI3 fin_sup_irrE1 by auto

lemma inf_prime_iff:
  "\<lbrakk>distributive_lattice X; x \<in> X\<rbrakk> \<Longrightarrow> (elem_inf_prime X x \<longleftrightarrow> fin_inf_irr X x)"
  using elem_inf_primeI3 fin_inf_irrE1 by auto

lemma fin_sup_irrI2:
  "\<lbrakk>distributive_lattice X; x \<in> X;  sup_prime X ([x)\<^sub>X)\<rbrakk> \<Longrightarrow> fin_sup_irr X x"
  by (simp add: distributive_lattice_def elem_sup_primeI2 fin_sup_irrE1 lattD42)
  
lemma fin_inf_irrI2:
  "\<lbrakk>distributive_lattice X; x \<in> X; inf_prime X ((x]\<^sub>X)\<rbrakk> \<Longrightarrow> fin_inf_irr X x"
  by (simp add: distributive_lattice_def elem_inf_primeI2 fin_inf_irrE1 lattD41)
  
lemma sup_primeI4:
  "\<lbrakk>distributive_lattice X; x \<in> X; fin_sup_irr X x\<rbrakk> \<Longrightarrow> sup_prime X ([x)\<^sub>X)"
  by (simp add: elem_sup_primeE1 elem_sup_primeI3)

lemma inf_primeI4:
  "\<lbrakk>distributive_lattice X; x \<in> X; fin_inf_irr X x\<rbrakk> \<Longrightarrow> inf_prime X ((x]\<^sub>X)"
  by (simp add: elem_inf_primeE1 elem_inf_primeI3)

lemma sup_prime_pfilterD1:
  "\<lbrakk>sup_prime X A; is_pfilter X A\<rbrakk> \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> X; b \<in> X;  (Sup X {a, b}) \<in> A\<rbrakk> \<Longrightarrow> (a \<in> A \<or> b \<in> A))"
  by (simp add: sup_prime_def)

lemma sup_prime_pfilterD2:
  "\<lbrakk>is_lattice X; sup_prime X A; is_pfilter X A\<rbrakk> \<Longrightarrow> (\<And>a b.  \<lbrakk>a \<in> X; b \<in> X; (a \<in> A \<or> b \<in> A)\<rbrakk> \<Longrightarrow> (Sup X {a, b}) \<in> A)"
  by (meson filter_on_lattice_sup01 is_pfilterE1 lattice_filter_memI)

lemma sup_prime_pfilterD3:
  "\<lbrakk>is_lattice X; sup_prime X F; is_pfilter X F\<rbrakk> \<Longrightarrow> (\<And>F1 F2. \<lbrakk>is_filter X F1; is_filter X F2; \<not>(F1 \<subseteq> F); \<not>(F2 \<subseteq> F)\<rbrakk> \<Longrightarrow> \<not>(F1 \<inter> F2 \<subseteq> F))"
  by (meson is_filter_def filters_on_lattice_inf03 subset_eq sup_prime_pfilterD1)

lemma sup_prime_pfilterD4:
  "\<lbrakk>is_lattice X; sup_prime X F; is_pfilter X F; is_filter X F1; is_filter X F2; F1 \<inter> F2 \<subseteq> F\<rbrakk> \<Longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F"
  using sup_prime_pfilterD3 by blast

lemma lorc_sup_filter_subset:
  "\<lbrakk>is_lattice X; (\<And>F1 F2. \<lbrakk> is_filter X F1; is_filter X F2; F1 \<inter> F2 \<subseteq> F\<rbrakk> \<Longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F); is_filter X F\<rbrakk> \<Longrightarrow>(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; (Sup X {a, b}) \<in> F\<rbrakk>\<Longrightarrow> (a \<in> F \<or> b \<in> F))"
proof-
  assume A0:"is_lattice X" "(\<And>F1 F2. \<lbrakk> is_filter X F1; is_filter X F2; F1 \<inter> F2 \<subseteq> F\<rbrakk> \<Longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F)" "is_filter X F"
  have B0:"\<And>a b. a \<in> X \<and> b \<in> X \<and> (Sup X {a, b}) \<in> F \<longrightarrow> (a \<in> F \<or> b \<in> F)" 
  proof 
    fix a b assume A1:"a \<in> X \<and> b \<in> X \<and> (Sup X {a, b}) \<in> F"
    let ?F1="([a)\<^sub>X)" let ?F2="([b)\<^sub>X)"
    have B1:"?F1 \<inter> ?F2 \<subseteq> F" using lorc_inter[of X a b] A0(1,3)
    by (smt (verit) A1 is_filterE1 is_ord_clE lorcD12 lorc_subset1 subset_eq)
    have B2:"is_filter X ?F1 \<and> is_filter X ?F2"  by (simp add: A1 lorc_filter)
    have B3:"?F1 \<subseteq> F \<or> ?F2 \<subseteq> F"  by (simp add: A0(2) B1 B2)
    show "a \<in> F \<or> b \<in> F"
      by (meson A1 B3 in_mono lorc_memI1)
  qed
  show "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; (Sup X {a, b}) \<in> F\<rbrakk>\<Longrightarrow> (a \<in> F \<or> b \<in> F))"
    by (simp add: B0)
qed

lemma sup_prime_pfilterI2:
  "\<lbrakk>is_lattice X; (\<And>F1 F2. \<lbrakk> is_filter X F1; is_filter X F2; F1 \<inter> F2 \<subseteq> F\<rbrakk> \<Longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F); is_pfilter X F\<rbrakk> \<Longrightarrow> sup_prime X F"
  by (simp add: is_pfilterE1 lorc_sup_filter_subset sup_prime_def)


lemma not_prime_obtain:
  assumes A0:"is_lattice X" and A1:"is_pfilter X F" and A2:"\<not>(sup_prime X F)"
  obtains x y where "x \<in> X \<and> y \<in> X \<and> Sup X {x, y} \<in> F \<and> x \<notin> F \<and> y \<notin> F"
  using A2 sup_prime_def by blast

lemma primefilterD1:
  "\<lbrakk>sup_prime X A; is_pfilter X A\<rbrakk> \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> X; b \<in> X;  (Sup X {a, b}) \<in> A\<rbrakk> \<Longrightarrow> (a \<in> A \<or> b \<in> A))"
  by (simp add: sup_prime_def)

lemma primeidealD1:
  "\<lbrakk>inf_prime X A; is_pfilter X A\<rbrakk> \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> X; b \<in> X;  (Inf X {a, b}) \<in> A\<rbrakk> \<Longrightarrow> (a \<in> A \<or> b \<in> A))"
  by (simp add: inf_prime_def)

lemma primefilterD2:
  "\<lbrakk>is_lattice X; sup_prime X A; is_pfilter X A\<rbrakk> \<Longrightarrow> (\<And>a b.  \<lbrakk>a \<in> X; b \<in> X; (a \<in> A \<or> b \<in> A)\<rbrakk> \<Longrightarrow> (Sup X {a, b}) \<in> A)"
  by (simp add: sup_prime_pfilterD2)

lemma primefilterD3:
  "\<lbrakk>is_lattice X; sup_prime X F; is_pfilter X F\<rbrakk> \<Longrightarrow> (\<And>F1 F2. \<lbrakk>is_filter X F1; is_filter X F2; \<not>(F1 \<subseteq> F); \<not>(F2 \<subseteq> F)\<rbrakk> \<Longrightarrow> \<not>(F1 \<inter> F2 \<subseteq> F))"
  by (simp add: sup_prime_pfilterD3)


lemma notprimeobtain:
  assumes A0:"is_lattice X" and A1:"is_pfilter X F" and A2:"\<not>(sup_prime X F)"
  obtains x y where "x \<in> X \<and> y \<in> X \<and> Sup X {x, y} \<in> F \<and> x \<notin> F \<and> y \<notin> F"
  using A2 sup_prime_def by blast

(*
need more robust intro and dest lemmas for filters and more generally  ord closure and directedness
 
*)

lemma element_filter:
  assumes A0:"is_lattice X" and A1:"is_filter X F" and A2:"a \<in> X"
  defines "G \<equiv> {x \<in> X. \<exists>y \<in> F. Inf X {a, y} \<le> x}"
  shows "is_filter X G"
proof(rule is_filterI1)
  obtain x y where "x \<in> X" and "y \<in> F" and "Inf X {a, y} \<le> x"  by (metis A0 A1 A2 dual_order.refl ex_in_conv in_mono is_filterE1 lattD41 sinfD4)
  then show "G \<noteq> {}" using G_def by blast
  show g0:"G \<subseteq> X"  using G_def by blast
  show "is_dir G (\<lambda>x y. y \<le> x)"
  proof(rule is_dirI1)
    show "\<And>x1 x2. x1 \<in> G \<Longrightarrow> x2 \<in> G \<Longrightarrow> \<exists>c\<in>G. c \<le> x1 \<and> c \<le> x2"
    proof-
      fix x1 x2 assume x10:"x1 \<in> G" and x20:"x2 \<in> G"  then obtain x11:"x1 \<in> X" and x21:"x2 \<in> X" using g0 by blast
      then obtain y1 y2 where y10:"y1 \<in> F" and y20:"y2 \<in> F" and y11:"Inf X {a, y1} \<le> x1" and  y21:"Inf X {a, y2} \<le> x2" using G_def x10 x20 by blast
      have B3:"Inf X {y1, y2} \<in> F" by (simp add: A0 A1 filter_finf_closed_isl lattD41 y10 y20)
      have B30:"Inf X {y1, y2} \<in> X \<and> a \<in> X \<and> x1 \<in> X \<and> x2 \<in> X \<and> y1 \<in> X \<and> y2 \<in> X"  using A1 A2 x10 x20 y10 y20 B3 G_def is_filterE1 by auto
      have B4:"Inf X {x1, x2} \<ge> Inf X {Inf X {a, y1}, Inf X {a, y2}}"  by (simp add: A0 B30 binf_leI5 lattD41 sinfD4 y11 y21)
      have B5:" Inf X {Inf X {a, y1}, Inf X {a, y2}}  = Inf X {a, Inf X {y1, y2}}"  using inf_semilattice_finf_props5[of X a y1 y2] A0 B30 lattD41[of X] by fastforce
      have B6:"Inf X {Inf X {y1, y2}, a} \<le> Inf X {x1, x2}"     by (metis B4 B5 insert_commute)
      have B7:"\<exists>y \<in> F. Inf X {a, y} \<le> Inf X {x1, x2}"   using B3 B4 B5 by auto
      have  "Inf X {x1, x2} \<in> G"  by (simp add: A0 B7 G_def lattD41 sinfD4 x11 x21)
      then show "\<exists>c\<in>G. c \<le> x1 \<and> c \<le> x2"  by (meson A0 B30 binf_leI1 binf_leI2 dual_order.refl lattD41)
    qed
  qed
  show "is_ord_cl X G (\<le>)"
  proof(rule is_ord_clI)
    show "\<And>a b. a \<in> G \<Longrightarrow> b \<in> X \<Longrightarrow> a \<le> b \<Longrightarrow> b \<in> G"
    using G_def order.trans by blast
  qed
qed


lemma primefilterI1:
  "\<lbrakk>is_lattice X;  is_pfilter X A; (\<forall>a b. (a \<in> A \<or> b \<in> A) \<longleftrightarrow> ((Sup X {a, b}) \<in> A)) \<rbrakk> \<Longrightarrow> sup_prime X A"
  by (simp add: sup_prime_def)

lemma primefilter_iff1:
  "is_lattice X \<Longrightarrow> ( sup_prime X A \<and> is_pfilter X A) \<longleftrightarrow> (is_pfilter X A \<and>  (\<forall>a \<in> X. \<forall>b \<in> X. (a \<in> A \<or> b \<in> A) \<longleftrightarrow> ((Sup X {a, b}) \<in> A)))"
  by (metis sup_prime_def primefilterD2)

lemma prime_filter_iff2:
  "is_lattice X \<Longrightarrow>  (sup_prime X F \<and> is_pfilter X F)  \<longleftrightarrow>  (is_pfilter X F \<and> (\<forall>F1 F2. is_filter X F1 \<and> is_filter X F2 \<and> F1 \<inter> F2 \<subseteq> F \<longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F))"
  by (meson sup_prime_pfilterD3 sup_prime_pfilterI2)

lemma prime_filter_fin_irr1:
  "\<lbrakk>is_lattice X; sup_prime X F; is_pfilter X F; G \<in> filters_on X; H \<in> filters_on X; G \<inter> H = F\<rbrakk> \<Longrightarrow> G=F \<or> H=F"
  by (meson filters_on_iff semilattice_inf_class.inf_le1 semilattice_inf_class.inf_le2 subset_antisym subset_refl sup_prime_pfilterD4)

lemma prime_filter_fin_irr2:
  "\<lbrakk>is_lattice X; sup_prime X F; is_pfilter X F; G \<in> filters_on X; H \<in> filters_on X; Inf (filters_on X) {G, H} = F\<rbrakk> \<Longrightarrow> G=F \<or> H=F"
  by (simp add: filters_lattice_inf_op prime_filter_fin_irr1)

lemma prime_filter_irr3:
  "\<lbrakk>is_lattice X; sup_prime X F; is_pfilter X F\<rbrakk> \<Longrightarrow> fin_inf_irr (filters_on X) F"
  by (metis fin_inf_irr_def prime_filter_fin_irr2)

lemma proper_principal_prime:
  "\<lbrakk>is_pfilter X [a)\<^sub>X; (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; a \<le> Sup X {x, y}\<rbrakk> \<Longrightarrow> a \<le> x \<or> a \<le> y)\<rbrakk> \<Longrightarrow> sup_prime X [a)\<^sub>X"
  by (metis lorcD12 lorcI1 sup_prime_def)

lemma proper_principal_prime2:
  "\<lbrakk>is_lattice X; is_pfilter X [a)\<^sub>X; (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; a \<le> Sup X {x, y}\<rbrakk> \<Longrightarrow> a \<le> x \<or> a \<le> y)\<rbrakk> \<Longrightarrow> (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; a = Sup X {x, y}\<rbrakk> \<Longrightarrow> a =x \<or> a=y)"
  by (metis binary_supD31 binary_supD32 is_supE1 lattD32 order_class.order_eq_iff)

lemma proper_principal_fin_irr:
  "\<lbrakk>is_lattice X; is_pfilter X [a)\<^sub>X; (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; a \<le> Sup X {x, y}\<rbrakk> \<Longrightarrow> a \<le> x \<or> a \<le> y)\<rbrakk> \<Longrightarrow>fin_inf_irr (filters_on X) [a)\<^sub>X"
  by (simp add: prime_filter_irr3 proper_principal_prime)


lemma fin_irr_filter_prime:
  "\<lbrakk>distributive_lattice X;is_pfilter X F;fin_inf_irr (filters_on X) F\<rbrakk> \<Longrightarrow> inf_prime X F"
  by (metis distr_latticeD5 filter_on_lattice_sup01 inf_prime_def is_pfilterE1 lattice_absorb1)
(*on lattice prime filters are finite inf irr
  prime_filter_irr3 
    \<lbrakk>is_lattice X; sup_prime X F; pfilter X F\<rbrakk> \<Longrightarrow> fin_inf_irr (filters_on X) F"
  while if the lattice is distributive the conver
*)

lemma distr_lattice_maximal_prime:
  assumes A0:"distributive_lattice X" and A1:"is_maximal (pfilters_on X) F" 
  shows "sup_prime X F"
proof-
  have B00:"is_lattice X"
    using A0 distributive_lattice_def by blast
  have B0:"is_pfilter X F"  by (simp add: A1 maximalD1 pfilters_onE)
  have P:"\<And>a b. a \<in> X \<and> b \<in> X \<and> Sup X {a, b} \<in> F \<and>  a \<notin> F \<longrightarrow> b \<in> F"
  proof
    fix a b assume A2:"a \<in> X \<and> b \<in> X \<and> Sup X {a, b} \<in> F \<and> a \<notin> F"
    let ?Fa="binary_filter_sup X F [a)\<^sub>X"
    have B1:"a \<in> ?Fa - F" by (meson A2 B0 B00 DiffI filters_on_lattice_bsup02 is_pfilter_def lorc_filter lorc_mem_iff2 ub_singleton)
    have B2:"F \<subset> ?Fa"  by (metis A2 B0 B00 B1 DiffD1 filters_on_lattice_bsup03 is_pfilterE1 lorc_filter psubsetI)
    have B3:"?Fa \<notin> pfilters_on X"   using A1 B2 maximalD4 by auto
    have B4:"?Fa \<in> filters_on X"  by (simp add: A2 B0 B00 filters_on_lattice_bsup4 is_pfilterE1 lorc_filter)
    have B5:"?Fa = X"  by (metis B3 B4 filters_onE is_pfilter_def pfilters_onI)
    have B6:"b \<in> ?Fa"    by (simp add: A2 B5)
    obtain f c where B7:"f \<in> F \<and> c \<in> ([a)\<^sub>X) \<and> b \<ge> Inf X {f, c}"   using B6 binary_filter_sup_obtains by blast
    have B8:"b = Sup X {b, Inf X {f, c}}"  by (metis A2 B00 B2 B5 B7 ge_sup2 insert_Diff insert_subset lattD41 lorcD11 order.strict_implies_order sinfD4)
    have B9:"... = Inf X {Sup X {b, f}, Sup X {b, c}}"  by (metis (mono_tags, lifting) A0 A2 B2 B5 B7 distr_latticeD1 insert_Diff insert_subset lorcD11 order.strict_implies_order)
    have B10:"Sup X {b, f} \<in> F \<and> Sup X {b, c} \<in> ([a)\<^sub>X) \<and> b = Inf X {Sup X {b, f}, Sup X {b, c}}"  by (metis A2 B0 B00 B7 B8 B9 filter_on_lattice_sup01 is_pfilterE1 lorc_filter)
    let ?f="Sup X {b, f}" and ?c="Sup X {b, c}"
    have B11:"?c \<ge> a"  using B10 lorcD12 by blast
    have B110:"b \<in> X \<and> ?f \<in> X \<and> ?c \<in> X \<and> c \<in> X \<and> a \<in> X"   using A2 B10 B2 B5 B7 lorcD11 by blast
    have B111:"Sup X {b, ?f} \<ge> ?f"  by (meson A0 B110 bsup_geI2 distributive_lattice_def dual_order.refl lattD42)
    have B112:"Sup X {b, ?c} \<ge> Sup X {b, a}"  by (simp add: B00 B11 B110 bsup_geI5 lattD42)
    have B12:"b = Sup X {b, Inf X {?f, ?c}}"   using A2 B10 bsup_idem1 by force
    have B13:"... = Inf X {Sup X {b, ?f}, Sup X {b, ?c}}"  by (simp add: A0 B110 distr_latticeD1)
    have B14:"... \<ge> Inf X {?f, Sup X {b, a}}"  by (simp add: B00 B110 B111 B112 binf_leI5 lattD41 lattD42 ssupD4)
    have B15:"... \<in> F"
    by (smt (verit, ccfv_SIG) A2 B0 B00 B10 B110 B14 B2 B5 antisym binf_leI3 bsup_geI1 filter_finf_closed_isl insert_commute is_pfilterE1 lattD41 lattD42 latt_ge_iff1 lattice_absorb1 psubsetD)
    show "b \<in> F"
      using B12 B13 B15 by presburger
  qed
  show ?thesis
    by (meson P sup_primeI1)
qed



lemma tmp1:"\<lbrakk>a1 \<in> X; a2 \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>{Inf X {b, a}|a. a \<in> {a1, a2}} = {Inf X {b, a1}, Inf X {b, a2}}" by auto


lemma tmp4:"\<lbrakk>a1 \<in> X; a2 \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>{Sup  X {b, a}|a. a \<in> {a1, a2}} = {Sup X {b, a1}, Sup X {b, a2}}" by auto



lemma distr_eq_tmp1:"\<lbrakk>distributive_lattice X; a1 \<in> X; a2 \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> Inf X {b, Sup X {a1, a2}} = Sup X {Inf X {b, a}|a. a \<in> {a1, a2}}" using distr_latticeD3 tmp1 by fastforce


lemma distr_eq_tmp3:"\<lbrakk>distributive_lattice X; a1 \<in> X; a2 \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> Sup X {b, (Inf X {a1, a2})} = Inf X {Sup X {b, a}|a. a \<in> {a1, a2}}" using distr_latticeD1 tmp4 by fastforce


lemma l_inf_closed:"\<lbrakk>is_lattice X;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Inf X {x, y} \<in> X" by (simp add: lattD41 sinfD4)
lemma l_finsup:"\<lbrakk>is_lattice X; A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>s. is_sup X A s"  using bsup_finite2 lattD42 by blast 


lemma l_sup_closed:"\<lbrakk>is_lattice X;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Sup X {x, y} \<in> X" by (simp add: lattD42 ssupD4)
lemma l_fininf:"\<lbrakk>is_lattice X; A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>s. is_inf X A s"  using binf_finite2 lattD41 by blast 


lemma sup_insert9: "\<lbrakk>is_sup Y A s1; is_sup Y {s1, x} s2\<rbrakk> \<Longrightarrow>  s2 \<in> (ubd Y (insert x A))" by (simp add: is_supD1121 sup_insert62 ubd_mem_insert)
lemma inf_insert9: "\<lbrakk>is_inf Y A s1; is_inf Y {s1, x} s2\<rbrakk> \<Longrightarrow>  s2 \<in> (lbd Y (insert x A))" by (simp add: is_infD1121 inf_insert62 lbd_mem_insert)



lemma sup_ubd: "\<lbrakk>is_sup Y F s; is_sup Y {x, s} t\<rbrakk> \<Longrightarrow> is_sup Y (insert x F) t"  by(rule is_supI1, simp add: insert_commute leastI3 sup_insert7 sup_insert9)
lemma sup_ex:"\<lbrakk>is_lattice X;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> is_sup X {x, y} (Sup X {x, y})" by (simp add: lattD32)

lemma inf_lbd: "\<lbrakk>is_inf Y F s; is_inf Y {x, s} t\<rbrakk> \<Longrightarrow> is_inf Y (insert x F) t" by (rule is_infI1, simp add: insert_commute greatestI3 inf_insert7 inf_insert9)
lemma inf_ex:"\<lbrakk>is_lattice X;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> is_inf X {x, y} (Inf X {x, y})" by (simp add: lattD31)




lemma fsup_insert:"\<lbrakk>is_lattice X; finite F; F \<subseteq> X; F \<noteq> {}; x \<in> X\<rbrakk> \<Longrightarrow> Sup X {x, (Sup X F)} = Sup X (insert x F)"  by (metis l_finsup is_supE1 sup_equality sup_ex sup_ubd)
lemma finf_insert:"\<lbrakk>is_lattice X; finite F; F \<subseteq> X; F \<noteq> {}; x \<in> X\<rbrakk> \<Longrightarrow> Inf X {x, (Inf X F)} = Inf X (insert x F)"  by (metis l_fininf is_infE1 inf_equality inf_ex inf_lbd)

             
lemma sfsup_insert:"\<lbrakk>is_sup_semilattice X; finite F; F \<subseteq> X; F \<noteq> {}; x \<in> X\<rbrakk> \<Longrightarrow> Sup X {x, (Sup X F)} = Sup X (insert x F)"  by (metis bsup_finite2 is_supE1 ssupD3 sup_equality sup_ubd) 
lemma sfinf_insert:"\<lbrakk>is_inf_semilattice X; finite F; F \<subseteq> X; F \<noteq> {}; x \<in> X\<rbrakk> \<Longrightarrow> Inf X {x, (Inf X F)} = Inf X (insert x F)"  by (metis binf_finite2 is_infE1 sinfD3 inf_equality inf_lbd)




lemma distr_finite2:
  assumes A0:"b \<in> X" and
          A1: "\<And>a1 a2. \<lbrakk>a1 \<in> X; a2 \<in> X\<rbrakk> \<Longrightarrow> Inf X {b, (Sup X {a1, a2})} = Sup X {Inf X {b, a}|a. a \<in> {a1, a2}}" and 
          A2:"finite A" and
          A3:"A \<noteq> {}" and
          A4:"A \<subseteq> X" and
          A5:"distributive_lattice X"
  shows "Inf X {b, (Sup X A)} = Sup X {Inf X {b, a}|a. a \<in> A}"
  using A2 A3 A4 A1 A0
proof (induct A rule: finite_ne_induct)
  case (singleton x) then show ?case using A5 by fastforce 
next
  case (insert x F)
  obtain P0:"x \<in> X" and P1:"F \<subseteq> X" and P2:"finite F" and P3:"F \<noteq> {}"
    using insert.hyps(1,2) insert.prems(1) by blast
  have L:"is_lattice X"  by (simp add: A5 distr_latticeD5) 
  let ?ba="{Inf X {b, a} |a::'a. a \<in> F}" and ?xba="{Inf X {b, a}|a. a \<in> (insert x F)}"
  let ?s="Sup X F" and ?sba="Sup X ?ba" and ?sxba="Sup X ?xba"
  have P4:"?ba \<subseteq> X" using L A0 P1 l_inf_closed by blast 
  have P5:"?xba \<subseteq> X" using L A0 P0 P1 l_inf_closed by blast
  have P6:"finite ?ba" using P2 by force
  have P7:"finite ?xba"  by (simp add: insert.hyps(1))
  have P8:"?xba = {Inf X {b, x}} \<union> ?ba" by (auto)
  have P9:"Inf X {b, x} \<in> X" by (simp add: L A0 P0 l_inf_closed) 
  have P10:"?ba \<noteq> {}"  using P3 by blast
  have P11:"?xba \<noteq> {}" using P3 by blast
  have P12:"?sba \<in> X" using L P10 P4 P6 bsup_finite2 is_supE1 latt_iff by blast 
  have P13:"?sxba \<in> X" using L P11 P5 P7 bsup_finite2 is_supE1 latt_iff by blast 
  have P14:"(Sup X {?sba, (Inf X {b, x})}) \<in> X" using  P12 P9  L l_sup_closed by blast 
  have B0:"Inf X {b, ?s} = ?sba"  using A0 A1 insert.hyps(4) insert.prems(1) by blast
  have B1:"Inf X {b, (Sup X {?s, x})} = Sup X {(Inf X {b, ?s}), (Inf X {b, x})}" by (meson A0 A5 L P0 P1 P2 P3 bsup_finite2 distr_latticeD3 is_supE1 lattD42)
  have B2:"... = Sup X {(?sba), (Inf X {b, x})}"  using B0 by fastforce
  have B3:"... = Sup X {Inf X {b, a}|a. a \<in> (insert x F)}" 
  proof-
    have B4:"?ba \<subseteq> ?xba" by blast
    have B5:"is_sup X ?ba ?sba" by (simp add: P3 P4 P6 L l_finsup sup_exI)
    have B6:"is_sup X {Inf X {b, x},?sba} (Sup X {(Inf X {b, x}), (?sba)} )" by (simp add: L P12 P9 lattD32) 
    have B7:"is_sup X {Inf X {b, x},?sba} (Sup X {(?sba), (Inf X {b, x})})" by (metis B6 insert_commute) 
    have B8:"is_sup X (insert (Inf X {b, x}) ?ba) (Sup X {(?sba), (Inf X {b, x})})"  using B5 B7 sup_ubd by blast 
    have B9:"insert (Inf X {b, x}) ?ba =  {Inf X {b, a}|a. a \<in> (insert x F)}"  using B5 B7 sup_ubd by blast
    show "(Sup X {(?sba), (Inf X {b, x})}) =  Sup X {Inf X {b, a}|a. a \<in> (insert x F)}"
      using B8 B9 sup_equality by force
  qed
  have B10:"Inf X {b, (Sup X {?s, x})} = Sup X {Inf X {b, a}|a. a \<in> (insert x F)}" using B0 B1 B3 by presburger
  have B11:"Inf X {b, (Sup X {?s, x})} = Inf X {b, (Sup X (insert x F))}"
  proof-
    have B12:"Sup X {Sup X F, x} = Sup X (insert x F)"
      by (simp add: L P0 P1 P2 P3 fsup_insert insert_commute)
    show " Inf X {b, Sup X {Sup X F, x}} = Inf X {b, Sup X (insert x F)}"
      by (simp add: B12)
  qed
  have B13:"Inf X {b, (Sup X (insert x F))} =  Sup X {Inf X {b, a}|a. a \<in> (insert x F)}" using B10 B11 by presburger
  then show ?case
    by auto
qed



lemma distr_finite1:
  assumes A0:"b \<in> X" and
          A1: "\<And>a1 a2. \<lbrakk>a1 \<in> X; a2 \<in> X\<rbrakk> \<Longrightarrow> Sup X {b, (Inf X {a1, a2})} = Inf X {Sup X {b, a}|a. a \<in> {a1, a2}}" and 
          A2:"finite A" and
          A3:"A \<noteq> {}" and
          A4:"A \<subseteq> X" and
          A5:"distributive_lattice X"
  shows "Sup X {b, (Inf X A)} = Inf X {Sup X {b, a}|a. a \<in> A}"
  using A2 A3 A4 A1 A0
proof (induct A rule: finite_ne_induct)
  case (singleton x) then show ?case using A5 by fastforce 
next
  case (insert x F)
  obtain P0:"x \<in> X" and P1:"F \<subseteq> X" and P2:"finite F" and P3:"F \<noteq> {}"
    using insert.hyps(1,2) insert.prems(1) by blast
  have L:"is_lattice X"  by (simp add: A5 distr_latticeD5) 
  let ?ba="{Sup X {b, a} |a::'a. a \<in> F}" and ?xba="{Sup X {b, a}|a. a \<in> (insert x F)}"
  let ?s="Inf X F" and ?sba="Inf X ?ba" and ?sxba="Inf X ?xba"
  have P4:"?ba \<subseteq> X" using L A0 P1 l_sup_closed by blast 
  have P5:"?xba \<subseteq> X" using L A0 P0 P1 l_sup_closed by blast
  have P6:"finite ?ba" using P2 by force
  have P7:"finite ?xba"  by (simp add: insert.hyps(1))
  have P8:"?xba = {Sup X {b, x}} \<union> ?ba" by (auto)
  have P9:"Inf X {b, x} \<in> X" by (simp add: L A0 P0 l_inf_closed) 
  have P10:"?ba \<noteq> {}"  using P3 by blast
  have P11:"?xba \<noteq> {}" using P3 by blast
  have P12:"?sba \<in> X" using L P10 P4 P6 binf_finite2 is_infE1 latt_iff by blast 
  have P13:"?sxba \<in> X" using L P11 P5 P7 binf_finite2 is_infE1 latt_iff by blast 
  have P14:"(Inf X {?sba, (Sup X {b, x})}) \<in> X" by (simp add: A0 L P0 P12 l_inf_closed l_sup_closed)
  have B0:"Sup X {b, ?s} = ?sba"  using A0 A1 insert.hyps(4) insert.prems(1) by blast
  have B1:"Sup X {b, (Inf X {?s, x})} = Inf X {(Sup X {b, ?s}), (Sup X {b, x})}" by (meson A0 A5 L P0 P1 P2 P3 binf_finite2 distr_latticeD1 is_infE1 lattD41)
  have B2:"... = Inf X {(?sba), (Sup X {b, x})}"  using B0 by fastforce
  have B3:"... = Inf X {Sup X {b, a}|a. a \<in> (insert x F)}" 
  proof-
    have B4:"?ba \<subseteq> ?xba" by blast
    have B5:"is_inf X ?ba ?sba" by (simp add: P3 P4 P6 L l_fininf inf_exI)
    have B6:"is_inf X {Sup X {b, x},?sba} (Inf X {(Sup X {b, x}), (?sba)} )" by (simp add: A0 L P0 P12 l_sup_closed lattD31)
    have B7:"is_inf X {Sup X {b, x},?sba} (Inf X {(?sba), (Sup X {b, x})})" by (metis B6 insert_commute) 
    have B8:"is_inf X (insert (Sup X {b, x}) ?ba) (Inf X {(?sba), (Sup X {b, x})})"  using B5 B7 inf_lbd by blast 
    have B9:"insert (Sup X {b, x}) ?ba =  {Sup X {b, a}|a. a \<in> (insert x F)}"  using B5 B7 inf_lbd by blast
    show "(Inf X {(?sba), (Sup X {b, x})}) =  Inf X {Sup X {b, a}|a. a \<in> (insert x F)}"   using B8 B9 inf_equality by force
  qed
  have B10:"Sup X {b, (Inf X {?s, x})} = Inf X {Sup X {b, a}|a. a \<in> (insert x F)}" using B0 B1 B3 by presburger
  have B11:"Sup X {b, (Inf X {?s, x})} = Sup X {b, (Inf X (insert x F))}"
  proof-
    have B12:"Inf X {Inf X F, x} = Inf X (insert x F)"by (simp add: L P0 P1 P2 P3 finf_insert insert_commute)
    show "Sup X {b, Inf X {Inf X F, x}} = Sup X {b, Inf X (insert x F)}"   by (simp add: B12)
  qed
  have B13:"Sup X {b, (Inf X (insert x F))} =  Inf X {Sup X {b, a}|a. a \<in> (insert x F)}" using B10 B11 by presburger
  then show ?case  by auto
qed


lemma fin_distr2:"\<lbrakk>distributive_lattice X ;finite A;A \<noteq> {};A \<subseteq> X; b \<in> X\<rbrakk>\<Longrightarrow>Inf X {b, (Sup X  A)} = Sup X {Inf X {b, a}|a. a \<in> A}" using distr_finite2[of b X A]  by (simp add: distr_eq_tmp1)

lemma fin_distr1:"\<lbrakk>distributive_lattice X; finite A;A \<noteq> {};A \<subseteq> X; b \<in> X\<rbrakk>\<Longrightarrow>Sup X{ b, (Inf X  A)} = Inf X {Sup X {b, a}|a. a \<in> A}"  using distr_finite1[of b X A]  by (simp add: distr_eq_tmp3)


lemma finite_ind_in:
  "\<lbrakk>is_inf_semilattice X; finite I; I \<noteq> {}; (\<forall>i. i \<in> I \<longrightarrow> f i \<in> X)\<rbrakk> \<Longrightarrow>is_inf X (f`I) (Inf X (f`I))"
  by (simp add: binf_finite2 image_subset_iff)

lemma finite_ind_fil:
   "\<lbrakk>is_inf_semilattice X; finite I; I \<noteq> {}; is_greatest X top; (\<forall>i. i \<in> I \<longrightarrow> is_filter X (f i))\<rbrakk> \<Longrightarrow> is_inf (filters_on X) (f`I) (\<Inter>(f`I))"
  by (simp add: filters_inf_semilattice_inf filters_on_iff image_subsetI pow_neI)

lemma finite_ind_fil_lattice:
   "\<lbrakk>is_lattice X; finite I; I \<noteq> {}; is_greatest X top; (\<forall>i. i \<in> I \<longrightarrow> is_filter X (f i))\<rbrakk> \<Longrightarrow> is_inf (filters_on X) (f`I) (\<Inter>(f`I))"
  by (simp add: finite_ind_fil lattD41)

lemma finite_ind_fil2:
  fixes f::"'b \<Rightarrow> 'a::order set" and x::"'b \<Rightarrow> 'a::order" and I::"'b set"
  assumes A0:"is_lattice X" "is_greatest X top" and A1:"finite I" "I \<noteq> {}""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))" and
          A2:"(\<And>i. i \<in> I \<Longrightarrow> (x i) \<in> (f i))" and A3:"is_sup X (x` I) s"
  shows "s \<in> (\<Inter>(f` I))"
proof-
  have B0:"\<And>i. i \<in> I \<longrightarrow> s \<in> f i"
    proof
      fix i assume A4:"i \<in> I"
      have B1:"(x i) \<in> (f i)" using A0 A1 A2 A4 by blast
      have B2:"(x i) \<in> (x` I)"  by (simp add: A4)
      have B5:"s \<in> X"  using A3 is_supE1 by auto
      have B6:"x i \<le> s" using A3 B2 by(rule is_supD1121[of X "x` I" s "x i"]) 
      show "s \<in> f i"  by (meson A4 B1 B5 B6 assms(5) is_filterE1 is_ord_clE)   
  qed
  show "s \<in>  (\<Inter>(f` I))"
    using B0 by blast
qed

lemma finite_ind_fil3:
  fixes f::"'b \<Rightarrow> 'a::order set"  and I::"'b set"
  assumes A0:"is_lattice X" "is_greatest X top" and A1:"finite I" "I \<noteq> {}""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))" and
          A2: "s \<in> (\<Inter>(f` I))" 
  shows "\<exists>(x::'b \<Rightarrow> 'a::order). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> is_sup X (x` I) s"
proof-
  define x where "x = (\<lambda>(i::'b). s)"
  have B0:"is_sup X (x` I) s"
  proof(rule is_supI7)
    show " s \<in> X"   by (meson A2 assms(1-5)  filters_on_iff finite_ind_fil_lattice in_mono is_filterE1 is_infE1)
    show "s ub x ` I"  by (simp add: ub_imageI x_def)
    show "\<And>a. a \<in> X \<Longrightarrow> a ub x ` I \<Longrightarrow> s \<le> a"  by (simp add: assms(4) ex_in_conv image_iff ubE x_def)
  qed
  have B1:" (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))"
    using A2 x_def by blast
  show ?thesis
    using B0 B1 by auto
qed


lemma finite_ind_fil4:
  fixes f::"'b \<Rightarrow> 'a::order set" and x::"'b \<Rightarrow> 'a::order" and I::"'b set"
  assumes A0:"is_lattice X" "is_greatest X top" and A1:"finite I" "I \<noteq> {}""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))" and
          A2:"(\<And>i. i \<in> I \<Longrightarrow> (x i) \<in> (f i))" 
  shows "Sup X (x` I) \<in> \<Inter>(f`I)"
  using A0 A1 A2 finite_ind_fil2[of X top I f x] l_finsup sup_equality
  by (smt (verit, ccfv_threshold) finite_imageI image_iff image_is_empty insert_absorb insert_subset is_filterE1 subsetI)



lemma finite_ind_fil5:
  fixes f::"'b \<Rightarrow> 'a::order set"  and I::"'b set"
  assumes A0:"is_lattice X" "is_greatest X top" and A1:"finite I" "I \<noteq> {}""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))" and
          A2: "s \<in> (\<Inter>(f` I))" 
  shows "s \<in> {Sup X (x` I)|x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))}"
  using A0 A1 A2 finite_ind_fil3[of X top I f s]  using sup_equality by fastforce

lemma finite_ind_fil6:
  fixes f::"'b \<Rightarrow> 'a::order set" and x::"'b \<Rightarrow> 'a::order" and I::"'b set"
  assumes A0:"is_lattice X" "is_greatest X top" and A1:"finite I" "I \<noteq> {}""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))"
  shows "\<Inter>(f`I) = {Sup X (x` I)|x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))}"
  apply(auto)
  apply (metis all_not_in_conv assms(4) assms(5) image_constant_conv in_mono is_filterE1 sup_singleton2)
  by (metis (no_types, lifting) INT_E assms(1) assms(2) assms(3) assms(4) assms(5) finite_ind_fil4)

lemma filter_cl_least1a:
  "\<lbrakk>is_inf_semilattice X; is_filter X F; A \<noteq> {};A \<subseteq> F; x \<in> (filter_closure X A)\<rbrakk> \<Longrightarrow> \<exists>Fx. Fx \<in> Fpow_ne A \<and> Inf X Fx \<le> x \<and> Inf X Fx \<in> F"
  by (meson dual_order.trans filter_closure_memE1 filter_finf_closed3 fpow_neI)

lemma filter_cl_least1b:
  "\<lbrakk>is_inf_semilattice X; is_filter X F; A \<noteq> {};A \<subseteq> F; x \<in> (filter_closure X A)\<rbrakk> \<Longrightarrow> x \<in> F"
  by (smt (verit, best) filter_cl_least1a filter_closure_filter in_mono is_filterE1 is_ord_clE order_trans)

lemma filter_cl_least1:
  assumes A0:"is_greatest X top" and A1:" is_inf_semilattice X" and A2:"is_filter X F" and A3:"A \<subseteq> F" and 
  A4:"x \<in>  (filter_closure X A)"
  shows " x \<in>F"
proof(cases "A={}")
  case True
  then show ?thesis
  by (metis A0 A2 A4 filter_closure_def greatest_equality2 is_filter_top singletonD)
next
  case False
  then show ?thesis
    using A1 A2 A3 A4 filter_cl_least1b by blast
qed

lemma filter_cl_least2:
  "\<lbrakk>is_greatest X top; is_inf_semilattice X; is_filter X F; A \<subseteq> F\<rbrakk> \<Longrightarrow> (filter_closure X A) \<subseteq> F"
  using filter_cl_least1 by blast

lemma filter_cl_is_ub_ne:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (filter_closure X A) \<in>  (ubd (filters_on X) {A})"
  by (simp add: filter_closure_lub leastD11)

lemma filter_cl_is_ub:
  "\<lbrakk>is_greatest X top; is_inf_semilattice X;A \<subseteq> X\<rbrakk> \<Longrightarrow> (filter_closure X A) \<in>  (ubd (filters_on X) {A})"
  by (metis filter_cl_is_ub_ne filter_closure_ne_lub leastD11)

lemma filter_cl_lt_ub:
  "\<lbrakk>is_greatest X top; is_inf_semilattice X;A \<subseteq> X\<rbrakk>  \<Longrightarrow> F \<in>  (ubd (filters_on X) {A}) \<Longrightarrow> (filter_closure X A) \<le> F"
  by (meson ubdD1 ubd_mem_iff filter_cl_least2 filters_on_iff insertI1)

lemma filter_cl_is_lcl:
  "\<lbrakk>is_greatest X top; is_inf_semilattice X;A \<subseteq> X\<rbrakk> \<Longrightarrow>  is_least (ubd (filters_on X) {A}) (filter_closure X A) "
  by (simp add: filter_cl_is_ub filter_cl_lt_ub leastI3)

lemma filter_closure_eq_closure:                                      
  "\<lbrakk>is_greatest X top; is_inf_semilattice X;A \<subseteq> X;A \<subseteq> X\<rbrakk>  \<Longrightarrow> filter_closure X A = (cl_from_clr (filters_on X)) A "
  by (metis cl_from_clr_def filter_cl_is_lcl least_equality2)

lemma filter_closure_of_filters1:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X\<rbrakk> \<Longrightarrow> F \<in> A \<Longrightarrow> F \<subseteq> (filter_closure X (\<Union>A))"
  by (metis Union_upper empty_iff filter_closure_singleton lattice_filter_dunion7 subset_trans)

lemma filter_closure_of_filters2_ne:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (filter_closure X (\<Union>A)) \<in>filters_on X"
  by (metis (no_types, lifting) Sup_bot_conv(2) filter_closure_filter filters_onE filters_onI is_filterE1 lattice_filter_dunion7 ne_subset_ne subset_iff)

lemma filter_closure_of_filters2:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X;is_greatest X top\<rbrakk> \<Longrightarrow>  (filter_closure X (\<Union>A)) \<in>filters_on X"
  by (metis Union_empty filter_closure_empty filter_closure_of_filters2_ne filters_on_iff min_filter1)

lemma filter_closure_of_filters3:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X; is_greatest X top\<rbrakk> \<Longrightarrow>  (filter_closure X (\<Union>A)) \<in>ubd (filters_on X) A"
  by (simp add: filter_closure_of_filters1 filter_closure_of_filters2 ubdI)

lemma filter_closure_of_filters4:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X;is_greatest X top; G \<in> ubd (filters_on X) A\<rbrakk> \<Longrightarrow> (filter_closure X (\<Union>A)) \<subseteq> G"
  by (simp add: Union_least filter_cl_least2 filters_on_iff ubd_mem_iff2)

lemma filter_closure_of_filters5:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X; is_greatest X top\<rbrakk> \<Longrightarrow> is_sup (filters_on X) A  (filter_closure X (\<Union>A))"
  by (simp add: filter_closure_of_filters3 filter_closure_of_filters4 is_supI5)

lemma filter_closure_of_filters7:
  "\<lbrakk>is_inf_semilattice X;A \<subseteq> filters_on X; is_greatest X top\<rbrakk> \<Longrightarrow> Sup (filters_on X) A = (filter_closure X (\<Union>A))"
  by (simp add: filter_closure_of_filters5 sup_equality)

lemma filter_closure_of_filters8:
  "\<lbrakk>is_lattice X;A \<subseteq> filters_on X; is_greatest X top\<rbrakk> \<Longrightarrow> Sup (filters_on X) A = (filter_closure X (\<Union>A))"
  by (simp add: filter_closure_of_filters7 lattD41)




lemma finite_ind_fil7:
  fixes f::"'b \<Rightarrow> 'a::order set" and I::"'b set"
  assumes A0:"is_lattice X" "is_greatest X top" and A1:"I \<noteq> {}""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))"
  shows "Sup (filters_on X) (f`I) = {x \<in> X. \<exists>F \<in> Fpow_ne (\<Union>(f`I)). Inf X F \<le> x}"
proof-
  let ?A="\<Union>(f`I)"
  have B0:"?A \<noteq> {}" using assms(3) assms(4) is_filterE1 by fastforce 
  have B1:"filter_closure X (?A) = {x \<in> X. \<exists>F \<subseteq> ?A. finite F \<and> F \<noteq> {} \<and> Inf X F \<le> x} " using B0 by(rule filter_closure_ne_simp)
  have B2:"... = {x \<in> X. \<exists>F \<in> Fpow_ne ?A. Inf X F \<le> x}"  using fpow_ne_iff2 using fpow_ne_iff2 by(fastforce)
  have B3:"filter_closure X (?A) = {x \<in> X. \<exists>F \<in> Fpow_ne ?A. Inf X F \<le> x}" using B1 B2 by auto
  show ?thesis using filter_closure_of_filters8[of X "(f`I)"] B3 A0 A1(2) filters_on_iff by blast
qed

lemma inf_comp:
  "\<lbrakk>is_inf X A1 i1; is_inf X A2 i2; (\<And>a2. a2 \<in> A2 \<longrightarrow> (\<exists>a1 \<in> A1. a1 \<le> a2)) \<rbrakk> \<Longrightarrow> i1 \<le> i2"
  by (metis inf_iff2 is_infD1121 is_infD42 lb_def order_trans)


lemma finite_ind_fil8:
  fixes f::"'b \<Rightarrow> 'a::order set" and x::"'b \<Rightarrow> 'a::order" and I::"'b set"
  assumes A0:"is_lattice X" "is_greatest X top" and A1:"finite I" "I \<noteq> {}""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))" and
          A2:"F \<in> Fpow_ne (\<Union>(f`I))" "Inf X F \<le> y" "y \<in> X"
  shows "\<exists>(x::'b \<Rightarrow> 'a::order). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) \<le> y "
proof-
  define G where "G = {(i, z)|z i. z \<in> F \<and> (z \<in> f i)}"
  define x where "x = (\<lambda>i. if G``{i} \<noteq> {} then Inf X (G``{i}) else SOME z. z \<in> (f i))"
  have B0:"\<And>i. i \<in> I \<Longrightarrow>  G``{i} \<subseteq> F"
  proof-
    fix i assume i0:"i \<in>I"
    then show "G``{i} \<subseteq> F" using G_def by blast
  qed
  have B1:"\<And>i z. \<lbrakk>i \<in> I; z \<in> G``{i}\<rbrakk> \<Longrightarrow> z \<in> (f i)"
  proof-
    fix i z assume i0:"i \<in> I"  and z0:"z \<in> G``{i}"
    then show "z \<in> (f i)" using G_def by blast
  qed
  have B2:"\<And>i. i \<in> I \<Longrightarrow> (x i) \<in> (f i)"
  proof-
    fix i assume i0:"i \<in>I"
    then show "x i \<in> (f i)"
    proof(cases "G``{i} \<noteq> {}")
    case True then obtain B20:"x i =  Inf X (G``{i})" using x_def by auto
    then obtain B21:"G``{i} \<subseteq> (f i)" and B22:"finite (G``{i})" and  B23:"Inf X (G``{i}) \<in> (f i)"
      by (meson B0 B1 True assms(1) assms(5) assms(6) filter_finf_closed3 fpow_ne_iff2 i0 infinite_super lattD41 subsetI)
    then show ?thesis  by (simp add: B20)
    next
    case False then obtain "x i = (SOME z. z \<in> (f i))" using x_def by auto
    then show ?thesis
    by (metis assms(2) assms(5) i0 is_filter_top someI_ex) 
    qed
  qed
  have B3:"\<And>z. z \<in> F \<Longrightarrow> (\<exists>w \<in> (x` I). w \<le> z)"
  proof-
    fix z assume B30:"z \<in> F" then obtain i where B31:"i \<in> I" and B32:"z \<in> (f i)" by (metis UN_iff assms(6) fpow_ne_iff2 in_mono)
    then obtain B33:"G``{i} \<noteq> {}" using  B30 G_def by blast
    then obtain B34:"x i =  Inf X (G``{i})"  by (simp add: x_def) 
    have B35:"z \<in> G``{i}" using G_def B32 B30 by auto
    have B36:"finite (G``{i})"  by (meson B0 B31 assms(6) fpow_neD3 rev_finite_subset) 
    have B37:"(G``{i}) \<subseteq> X" using B1 B31 assms(5) is_filterE1 by blast
    then have B38:"Inf X (G``{i}) \<le> z"  using B35 B36 assms(1) finf_leI1 latt_iff by blast 
    then show " (\<exists>w \<in> (x` I). w \<le> z)"    by (metis B31 B34 imageI)
  qed
  obtain B4:"finite (x` I)" and B5:"(x` I) \<subseteq> X"  by (meson B2 assms(3) assms(5) finite_imageI image_subset_iff in_mono is_filterE1)
  
  have B6:"\<And>i. i \<in> I \<longrightarrow> (f i) \<subseteq> X"  by (simp add: assms(5) is_filterE1) 
  have B7:"\<Union>(f`I) \<subseteq> X" by (simp add: B6 UN_least)
  have B8:"finite F"  using assms(6) fpow_neD3 by blast
  have B9:"F \<subseteq> X"  by (meson B7 assms(6) dual_order.trans fpow_ne_iff2) 
  have B10:"Inf X (x` I) \<le> Inf X F "
  proof(rule_tac ?X="X" and ?A1.0="x` I" and ?A2.0="F" in inf_comp)
    show "is_inf X (x ` I) (Inf X (x ` I))" by(simp add:B4 B5 assms(1,4) binf_finite2 lattD41)
    show "is_inf X F (Inf X F)" by (metis B9 assms(1) assms(6) fpow_ne_iff2 inf_semilattice_finf latt_iff)
    show "\<And>a2. a2 \<in> F \<longrightarrow> (\<exists>a1\<in>x ` I. a1 \<le> a2)"  using B3 by blast
  qed
  show ?thesis
  using B10 B2 assms(7) dual_order.trans by blast
qed  


lemma finite_ind_fil9:
  fixes f::"'b \<Rightarrow> 'a::order set" and x::"'b \<Rightarrow> 'a::order" and I::"'b set"
  assumes A0:"is_lattice X" "is_greatest X top" and A1:"I \<noteq> {}""finite I""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))"
  shows "Sup (filters_on X) (f`I)  \<subseteq> {y \<in> X. \<exists>(x::'b \<Rightarrow> 'a::order). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) \<le> y}" (is "?L \<subseteq> ?R")
proof
  fix z assume A2:"z \<in> ?L"
  obtain F where B0:"F \<in> Fpow_ne (\<Union>(f`I)) \<and> Inf X F \<le> z" using A0 A1 A2 finite_ind_fil7[of X top I] by auto
  have B1:"(f`I) \<noteq> {}" using A0 A1 by simp
  have B2:"z \<in> X" using A0 A1 B1 by (metis (no_types, lifting) A2 CollectD finite_ind_fil7)
  have B3:"F \<in> Fpow_ne (\<Union>(f`I)) \<and> Inf X F \<le> z  \<and> z \<in> X"   by (simp add: B0 B2)
  obtain x where B4:"(\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) \<le> z" using A0 A1 A2 B0 B3 finite_ind_fil8[of X top I f F z] by(auto)
  show "z \<in> ?R" using B3 B4 by(auto)
qed



lemma finite_ind_fil10:
  fixes f::"'b \<Rightarrow> 'a::order set" and I::"'b set"
  assumes A0:"is_lattice X" "is_greatest X top" and A1:"I \<noteq> {}""finite I""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))"
  shows "{y \<in> X. \<exists>(x::'b \<Rightarrow> 'a::order). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) \<le> y} \<subseteq> Sup (filters_on X) (f`I) " (is "?L \<subseteq> ?R")
proof
  fix z assume A2:"z \<in> ?L"
  obtain x where B0:"(\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) \<le> z" using A2 by auto
  have B1:"(x` I) \<in> Fpow_ne (\<Union>(f`I))"  by(auto simp add:Fpow_ne_def Fpow_def B0 assms)
  show "z \<in> ?R" using assms B0 B1 A2 finite_ind_fil7[of X top I] by auto
qed


lemma finite_ind_fil11:
  fixes f::"'b \<Rightarrow> 'a::order set" and I::"'b set"
  assumes A0:"is_lattice X" "is_greatest X top" and A1:"I \<noteq> {}""finite I""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))"
  shows "Sup (filters_on X) (f`I) = {y \<in> X. \<exists>(x::'b \<Rightarrow> 'a::order). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) \<le> y}  "
  apply(rule order.antisym) 
  using A0 A1 apply(rule finite_ind_fil9, simp)
  using A0 A1 by(rule finite_ind_fil10, simp)

lemma finite_ind_fil11b:
  fixes f::"'b \<Rightarrow> 'a::order set" and I::"'b set"
  assumes A0:"is_lattice X" "is_greatest X top" and A1:"I \<noteq> {}""finite I""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))" and
          A2:"y \<in> Sup (filters_on X) (f`I)"
  shows "\<exists>(x::'b \<Rightarrow> 'a::order). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) \<le> y"
  using finite_ind_fil11[of X top I f] assms by(auto)

lemma finite_ind_fil12:
  fixes f::"'b \<Rightarrow> 'a::order set" and x::"'b \<Rightarrow> 'a::order" and I::"'b set"
  assumes A0:"distributive_lattice X" "is_greatest X top" and A1:"I \<noteq> {}""finite I""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))" and
          A2:"y \<in> X" "(\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))"  "Inf X (x` I) \<le> y"
  shows " \<exists>(x1::'b \<Rightarrow> 'a::order). (\<forall>i. i \<in> I \<longrightarrow> (x1 i) \<in> (f i)) \<and> Inf X (x1` I) =y "
proof-
  define x1 where "x1 = (\<lambda>i. Sup X {y, x i})"
  have B00:"finite (x` I)" by (simp add: assms(4))
  have B01:"x` I \<subseteq> X"  by (meson assms(5) assms(7) image_subset_iff in_mono is_filterE1) 
  have B02:"x` I \<noteq> {}"  by (simp add: assms(3))
  have B03:"finite (x1 ` I)"  by (simp add: assms(4))
  have B04:"(x1 ` I) \<subseteq> X"  by (metis B01 assms(1) assms(6) distr_latticeD5 image_subset_iff l_sup_closed x1_def)
  have B05:"(x1 ` I) \<noteq> {}"  using assms(3) by force
  have B0:"y = Sup X {y, Inf X (x` I)}" by (metis assms(6,8)  greatest_insert3 greatest_singleton sup_equality sup_maxE1) 
  have B1:"... = Inf X {Sup X {y,a}|a.  a \<in> (x` I)}" using B00 B01 B02 assms(1,6) fin_distr1 by blast
  have B2:"... = Inf X {Sup X {y, x i}|i. i \<in> I}" by (metis (no_types, opaque_lifting) image_iff)
  have B3:"... = Inf X {x1 i|i. i \<in> I}"  using x1_def by auto
  have B4:"... = Inf X (x1 ` I)"  by (simp add: Setcompr_eq_image)
  have B5:"Inf X (x1 ` I) = y"  using B0 B1 B2 B3 B4 by presburger
  have B6:"\<forall>i. i \<in> I \<longrightarrow> (x1 i) \<in> (f i)"  by (simp add: assms(1) assms(5) assms(6) assms(7) distr_latticeD5 filter_on_lattice_sup01 x1_def)
  show ?thesis
    using B5 B6 by blast
qed


lemma finite_ind_fil13:
  fixes f::"'b \<Rightarrow> 'a::order set" and I::"'b set"
  assumes A0:"distributive_lattice X" "is_greatest X top" and A1:"I \<noteq> {}""finite I""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))"
  shows "Sup (filters_on X) (f`I) \<subseteq> {y \<in> X. \<exists>(x::'b \<Rightarrow> 'a::order). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) = y}" (is "?L \<subseteq> ?R")
proof
  fix y assume A2:"y \<in> ?L"
  have B0:"is_lattice X" by (simp add: assms(1) distr_latticeD5)
  have B1:"y \<in> X" by (metis (no_types, lifting) A2 B0 CollectD assms(2) assms(3) assms(4) assms(5) finite_ind_fil11)
  obtain x where B2:"(\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) \<le> y"  by (metis A2 B0 assms(2) assms(3) assms(4) assms(5) finite_ind_fil11b) 
  obtain x1 where B3:"(\<forall>i. i \<in> I \<longrightarrow> (x1 i) \<in> (f i)) \<and> Inf X (x1` I) =y" using finite_ind_fil12[of X top I f y x] A0 A1 A2  B1 B2 by presburger
  show "y \<in> ?R"
    using B1 B3 by blast
qed


lemma finite_ind_fil14:
  fixes f::"'b \<Rightarrow> 'a::order set" and I::"'b set"
  assumes A0:"distributive_lattice X" "is_greatest X top" and A1:"I \<noteq> {}""finite I""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))"
  shows "{y \<in> X. \<exists>(x::'b \<Rightarrow> 'a::order). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) = y} \<subseteq> Sup (filters_on X) (f`I) " (is "?L \<subseteq> ?R")
proof
  fix y assume A2:"y \<in> ?L"
  have B0:"is_lattice X" by (simp add: assms(1) distr_latticeD5)
  have B1:"y \<in> X"  using A2 by blast
  obtain x1 where B3:"(\<forall>i. i \<in> I \<longrightarrow> (x1 i) \<in> (f i)) \<and> Inf X (x1` I) =y" using A2 by blast
  have B2:"(\<forall>i. i \<in> I \<longrightarrow> (x1 i) \<in> (f i)) \<and> Inf X (x1` I) \<le> y"  by (simp add: B3)
  have B3:"y \<in> {y \<in> X. \<exists>(x::'b \<Rightarrow> 'a::order). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) \<le> y}"  using B1 B2 by blast
  show "y \<in> ?R"   by (meson B0 B3 assms(2) assms(3) assms(4) assms(5) finite_ind_fil10 subset_iff)
qed


lemma finite_ind_fil15:
  fixes f::"'b \<Rightarrow> 'a::order set" and I::"'b set"
  assumes A0:"distributive_lattice X" "is_greatest X top" and A1:"I \<noteq> {}""finite I""(\<And>i. i \<in> I \<Longrightarrow> is_filter X (f i))"
  shows "Sup (filters_on X) (f`I) = {y \<in> X. \<exists>(x::'b \<Rightarrow> 'a::order). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf X (x` I) = y}  "
  using assms finite_ind_fil13[of X top I f] finite_ind_fil14[of X top I f] by fastforce



(*
lemma fin_distr2:"\<lbrakk>distributive_lattice X ;finite A;A \<noteq> {};A \<subseteq> X; b \<in> X\<rbrakk>\<Longrightarrow>Inf X {b, (Sup X  A)} = Sup X {Inf X {b, a}|a. a \<in> A}" using distr_finite2[of b X A]  by (simp add: distr_eq_tmp1)

lemma fin_distr1:"\<lbrakk>distributive_lattice X; finite A;A \<noteq> {};A \<subseteq> X; b \<in> X\<rbrakk>\<Longrightarrow>Sup X{ b, (Inf X  A)} = Inf X {Sup X {b, a}|a. a \<in> A}"  using distr_finite1[of b X A]  by (simp add: distr_eq_tmp3)
*)

definition subsemilattice_inf::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "subsemilattice_inf X A\<equiv> (A \<subseteq> X) \<and> (\<forall>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>i \<in> A. is_inf X {a, b} i))"

definition subsemilattice_sup::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "subsemilattice_sup X A\<equiv> (A \<subseteq> X) \<and> (\<forall>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>i \<in> A. is_sup X {a, b} i))"


definition sublattice::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "sublattice X A\<equiv> (A \<subseteq> X) \<and> (\<forall>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>s \<in> A. is_sup X {a, b} s) \<and> (\<exists>i \<in> A. is_inf X {a, b} i))"


lemma subsemilattice_infD:"subsemilattice_inf X A \<Longrightarrow>  (A \<subseteq> X) \<and> (\<forall>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>i \<in> A. is_inf X {a, b} i))" by (simp add:subsemilattice_inf_def)
lemma subsemilattice_infD1:"subsemilattice_inf X A \<Longrightarrow>  (A \<subseteq> X)" by (simp add:subsemilattice_inf_def)
lemma subsemilattice_infD2:"subsemilattice_inf X A \<Longrightarrow>  (\<And>a b. \<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> (\<exists>i \<in> A. is_inf X {a, b} i))" by (simp add:subsemilattice_inf_def)
lemma subsemilattice_infI1:"\<lbrakk>(A \<subseteq> X); (\<forall>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>i \<in> A. is_inf X {a, b} i)) \<rbrakk> \<Longrightarrow> subsemilattice_inf X A " by (simp add:subsemilattice_inf_def)

lemma subsemilattice_supD:"subsemilattice_sup X A \<Longrightarrow> (A \<subseteq> X) \<and> (\<forall>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>i \<in> A. is_sup X {a, b} i))" by (simp add:subsemilattice_sup_def)
lemma subsemilattice_supD1:"subsemilattice_sup X A \<Longrightarrow> (A \<subseteq> X)" by (simp add:subsemilattice_sup_def)
lemma subsemilattice_supD2:"subsemilattice_sup X A \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> (\<exists>i \<in> A. is_sup X {a, b} i))" by (simp add:subsemilattice_sup_def)
lemma subsemilattice_supI1:"\<lbrakk>(A \<subseteq> X); (\<forall>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>i \<in> A. is_sup X {a, b} i)) \<rbrakk> \<Longrightarrow> subsemilattice_sup X A " by (simp add:subsemilattice_sup_def)




definition homoinf::"'a::order set \<Rightarrow> 'b::order set \<Rightarrow> ('a::order \<Rightarrow> 'b::order) \<Rightarrow> bool" where
 "homoinf X Y f \<equiv> (\<forall>x y i. is_inf X {x, y} i \<longrightarrow>  is_inf Y {f x , f y} (f i))"


lemma homoinfsD1:"\<lbrakk>is_inf_semilattice X; is_inf_semilattice Y; homoinf X Y f; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> f (Inf X {x, y}) = Inf Y {f x, f y}" by(simp add:homoinf_def) (metis inf_equality sinfD3)

lemma homoinfsD2:
  assumes A0: "\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow>  f (Inf X {a1, a2}) = Inf Y {f a1, f a2}" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X" and
          A4:"is_inf_semilattice X" and 
          A5:"is_inf_semilattice Y" and 
          A6:"f`X \<subseteq> Y"
  shows "f (Inf X A) = Inf Y (f`A)"
  using A1 A2 A3 
proof (induct A rule: finite_ne_induct)
  case (singleton x) then show ?case using A0 singleton by fastforce
next
  case (insert x F)
  have B0:"f`(insert x F) = (insert (f x) (f`F))" by auto
  obtain B1:"f x \<in> Y" and B2:"f`F \<subseteq> Y"    by (meson A6 dual_order.trans image_eqI image_mono insert.prems insert_subset)
  obtain B3:"finite F" and B4:"F \<noteq> {}"    using insert.hyps(1) insert.hyps(2) by blast
  have B7:"Inf X (insert x F) = Inf X {x, Inf X F}"   using A4 B3 B4 insert.prems sfinf_insert by fastforce
  let ?a1="x"  let ?a2="Inf X F" let  ?i="Inf X {?a1, ?a2}"
  have B6:"?a1 \<in> X \<and> ?a2 \<in> X"  by (meson A4 B3 B4 binf_finite2 insert.prems insert_subset is_infE1)
  have B7:"is_inf X {?a1, ?a2} ?i" by (simp add: A4 B6 sinfD3)
  have B8:"is_inf Y {f ?a1, f ?a2} (f?i)"  by (metis A0 A5 A6 B6 image_subset_iff sinfD3)
  then show ?case
    by (metis A0 A4 A5 B0 B1 B2 B3 B4 B6 empty_is_image finite_imageI insert.hyps(4) insert.prems insert_subset sfinf_insert)
qed

lemma homoinfsD3:"\<lbrakk>f`X \<subseteq> Y;is_inf_semilattice X; is_inf_semilattice Y; homoinf X Y f; F \<subseteq> X; finite F; F \<noteq> {}\<rbrakk> \<Longrightarrow> f (Inf X F) = Inf Y (f`F)"by (meson homoinfsD1 homoinfsD2)


definition homosup::"'a::order set \<Rightarrow> 'b::order set \<Rightarrow> ('a::order \<Rightarrow> 'b::order) \<Rightarrow> bool" where 
   "homosup X Y f \<equiv> (\<forall>x y s. is_sup X {x, y} s \<longrightarrow> is_sup Y {f x, f y} (f s))"

lemma homosupD1:"\<lbrakk>is_sup_semilattice X; is_sup_semilattice Y; homosup X Y f; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> f (Sup X {x, y}) = Sup Y {f x, f y}" by (simp add:homosup_def) (metis sup_equality ssupD3)

lemma homosupD2:
  assumes A0: "\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> f (Sup X {a1, a2}) = Sup Y {f a1, f a2}" and
  A1: "finite A" and  A2: "A \<noteq> {}" and  A3: "A \<subseteq> X" and
  A4: "is_sup_semilattice X" and    A5: "is_sup_semilattice Y" and  A6: "f`X \<subseteq> Y" shows "f (Sup X A) = Sup Y (f`A)"
  using A1 A2 A3
proof (induct A rule: finite_ne_induct)
  case (singleton x) then show ?case using A0 singleton by fastforce
next
  case (insert x F)
  have B0:"f`(insert x F) = (insert (f x) (f`F))" by auto
  obtain B1: "f x \<in> Y" and B2: "f`F \<subseteq> Y" by (meson A6 dual_order.trans image_eqI image_mono insert.prems insert_subset)
  obtain B3: "finite F" and B4: "F \<noteq> {}" using insert.hyps(1) insert.hyps(2) by blast
  have B7: "Sup X (insert x F) = Sup X {x, Sup X F}"  by (metis A4 B3 B4 insert.prems insert_subset sfsup_insert)
  let ?a1 = "x" let ?a2 = "Sup X F" let ?s = "Sup X {?a1, ?a2}"
  have B6: "?a1 \<in> X \<and> ?a2 \<in> X" by (meson A4 B3 B4 bsup_finite2 insert.prems insert_subset is_supE1)
  have B7: "is_sup X {?a1, ?a2} ?s" by (simp add: A4 B6 ssupD3)
  have B8: "is_sup Y {f ?a1, f ?a2} (f ?s)" by (metis A0 A5 A6 B6 image_subset_iff ssupD3)
  then show ?case
    by (metis A4 A5 B0 B1 B2 B3 B4 finite_imageI image_is_empty insert.hyps(4) insert.prems insert_subset sfsup_insert sup_equality)
qed



lemma homoinfD4:"\<lbrakk>f`X \<subseteq> Y; is_inf_semilattice X; is_inf_semilattice Y; homoinf X Y f; x \<in> X; y \<in> X; x \<le> y\<rbrakk> \<Longrightarrow> f x \<le> f y"
  by(rule_tac ?X="Y" in le_binf1; auto; frule_tac ?a="x" and ?b="y" in binf_le1, simp_all)
    (frule_tac ?Y="Y" and ?f="f" and ?x="x" and ?y="y" in homoinfsD1, simp_all)

lemma subsemilattice_homomorphism1:"\<lbrakk>f`X \<subseteq> Y; is_inf_semilattice X; is_inf_semilattice Y; homoinf X Y f\<rbrakk> \<Longrightarrow> subsemilattice_inf Y (f`X)"
   by(rule subsemilattice_infI1;auto) (metis homoinf_def is_infE1 sinfD2)

lemma subsemilattice_homomorphism2:"\<lbrakk>f`X \<subseteq> Y; is_sup_semilattice X; is_sup_semilattice Y; homosup X Y f\<rbrakk> \<Longrightarrow> subsemilattice_sup Y (f`X)"
   by(rule subsemilattice_supI1;auto) (metis homosup_def is_supE1 ssupD2)


definition homolatt::"'a::order set \<Rightarrow> 'b::order set \<Rightarrow> ('a::order \<Rightarrow> 'b::order) \<Rightarrow> bool" where 
   "homolatt X Y f \<equiv> (\<forall>x y s. is_sup X {x, y} s \<longrightarrow> is_sup Y {f x, f y} (f s)) \<and> (\<forall>x y i. is_inf X {x, y} i \<longrightarrow>  is_inf Y {f x , f y} (f i))"


lemma homolattD1:"homolatt X Y f \<Longrightarrow> homoinf X Y f" by (simp add: homolatt_def homoinf_def)
lemma homolattD2:"\<lbrakk>is_lattice X; is_lattice Y; homolatt X Y f; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> f (Sup X {x, y}) = Sup Y {f x, f y}" by (simp add:homolatt_def; metis lattD32 sup_equality)


lemma homolattD3:
  assumes A0: "\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> f (Sup X {a1, a2}) = Sup Y {f a1, f a2}" and
  A1: "finite A" and  A2: "A \<noteq> {}" and  A3: "A \<subseteq> X" and
  A4: "is_lattice X" and    A5: "is_lattice Y" and  A6: "f`X \<subseteq> Y" shows "f (Sup X A) = Sup Y (f`A)"
  using A1 A2 A3
proof (induct A rule: finite_ne_induct)
  case (singleton x) then show ?case using A0 singleton by fastforce
next
  case (insert x F)
  have P0:"is_sup_semilattice X"  by (simp add: A4 lattD42)
  have B0:"f`(insert x F) = (insert (f x) (f`F))" by auto
  obtain B1: "f x \<in> Y" and B2: "f`F \<subseteq> Y" by (meson A6 dual_order.trans image_eqI image_mono insert.prems insert_subset)
  obtain B3: "finite F" and B4: "F \<noteq> {}" using insert.hyps(1) insert.hyps(2) by blast
  have B7: "Sup X (insert x F) = Sup X {x, Sup X F}"   using B3 B4 P0 insert.prems sfsup_insert by fastforce 
  let ?a1 = "x" let ?a2 = "Sup X F" let ?s = "Sup X {?a1, ?a2}"
  have B6: "?a1 \<in> X \<and> ?a2 \<in> X" by (meson B3 B4 P0 bsup_finite2 insert.prems insert_subset is_supE1) 
  have B7: "is_sup X {?a1, ?a2} ?s" by (simp add: A4 B6 lattD32)
  have B8: "is_sup Y {f ?a1, f ?a2} (f ?s)" by (metis A0 A5 A6 B6 image_subset_iff lattD32) 
  then show ?case
    by (metis A0 A4 A5 B0 B1 B2 B3 B4 B6 empty_is_image finite_imageI fsup_insert insert.hyps(4) insert.prems insert_subset)
qed

definition sup_distributive where
  "sup_distributive X \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. \<forall>x \<in> X. x \<le> Sup X {a, b} \<longrightarrow> (\<exists>a1 b1. a1 \<in> X \<and> b1 \<in> X \<and> a1 \<le> a \<and> b1 \<le> b \<and> x = Sup X {a1, b1}))"

definition inf_distributive where
  "inf_distributive X \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. \<forall>x \<in> X.  Inf X {a, b} \<le> x \<longrightarrow> (\<exists>a1 b1. a1 \<in> X \<and> b1 \<in> X \<and> a \<le> a1 \<and> b \<le> b1 \<and> x = Inf X {a1, b1}))"

lemma sup_distributiveI1:
  "(\<And>a b x. \<lbrakk>a \<in> X; b \<in> X; x \<in> X; x \<le> Sup  X {a, b}\<rbrakk> \<Longrightarrow> (\<exists>a1 b1. a1 \<in> X \<and> b1 \<in> X \<and> a1 \<le> a \<and> b1 \<le> b \<and> x = Sup X {a1, b1})) \<Longrightarrow> sup_distributive X"
  by(simp add:sup_distributive_def)

lemma sup_distributiveD1:
  "sup_distributive X \<Longrightarrow> (\<And>a b x. \<lbrakk>a \<in> X; b \<in> X; x \<in> X; x \<le> Sup  X {a, b}\<rbrakk> \<Longrightarrow> (\<exists>a1 b1. a1 \<in> X \<and> b1 \<in> X \<and> a1 \<le> a \<and> b1 \<le> b \<and> x = Sup X {a1, b1}))"
  by(simp add:sup_distributive_def)

lemma inf_distributiveI1:
  "(\<And>a b x. \<lbrakk>a \<in> X; b \<in> X; x \<in> X;  Inf X {a, b} \<le> x\<rbrakk> \<Longrightarrow> (\<exists>a1 b1. a1 \<in> X \<and> b1 \<in> X \<and> a \<le> a1 \<and> b \<le> b1 \<and> x = Inf X {a1, b1})) \<Longrightarrow> inf_distributive X"
  by(simp add:inf_distributive_def)

lemma inf_distributiveD1:
  "inf_distributive X \<Longrightarrow> (\<And>a b x. \<lbrakk>a \<in> X; b \<in> X; x \<in> X; Inf  X {a, b} \<le> x\<rbrakk> \<Longrightarrow> (\<exists>a1 b1. a1 \<in> X \<and> b1 \<in> X \<and> a \<le> a1 \<and> b \<le> b1 \<and> x = Inf X {a1, b1}))"
  by(simp add:inf_distributive_def)

lemma lat_binf_leI1: "\<lbrakk>is_lattice X;x \<in> X; y \<in> X; z \<in> X; Inf X {x, y} = z \<rbrakk> \<Longrightarrow>z \<le> x" using binf_leI1 lattD41 by blast
lemma lat_bsup_geI1: "\<lbrakk>is_lattice X;x \<in> X; y \<in> X; z \<in> X; Sup X {x, y} = z\<rbrakk>  \<Longrightarrow> x \<le> z" using bsup_geI1 lattD42 by blast

lemma sup_distributiveD2:
  "\<lbrakk>sup_distributive X; is_lattice X\<rbrakk> \<Longrightarrow> distributive_lattice X"
  apply(rule distr_latticeI2)
proof-
  fix x y z assume P:"sup_distributive X" "is_lattice X" "x \<in> X" "y \<in> X" "z \<in> X"
  have B1:"Inf X {x, Sup X {y, z}} \<le> Sup X {y, z}"  by (simp add: P(2-5) binf_leI2 l_sup_closed lattD41)
  obtain y1 z1 where dist:"y1 \<in> X \<and> z1 \<in> X \<and> y1 \<le> y \<and> z1 \<le> z \<and> (Inf X {x, Sup X {y, z}}) = Sup X {y1, z1}"  by (metis B1 P(1) P(2) P(3) P(4) P(5) l_inf_closed l_sup_closed sup_distributiveD1)
  have B2:"Sup X {y1, z1} \<le> x"by (metis P(2-5) dist l_sup_closed lat_binf_leI1) 
  have B3:"y1 \<le> x \<and> z1 \<le> x"  using B2 P(2) P(3) bsup_iff dist lattD42 by blast
  have B4:"y1 = Inf X {x, y1} \<and> z1 = Inf X {x, z1}" by (simp add: B3 P(3) dist le_inf2)
  have B40:"Inf X {x, y1} \<le> Inf X {x, y}" using lattD41[of X] binf_leI4[of X y1 y x] by (simp add: P(2-4) dist insert_commute)
  have B41:"Inf X {x, z1} \<le> Inf X {x, z}" using lattD41[of X] binf_leI4[of X z1 z x] by (simp add: P(1-5) dist insert_commute)
  have B5:"Inf X {x, Sup X {y, z}} = Sup X {Inf X {x, y1}, Inf X {x, z1}}"  using B4 dist by presburger
  have B6:"... \<le> Sup X {Inf X {x, y}, Inf X {x, z}}" by (simp add: B40 B41 P(2) P(3) P(4) P(5) bsup_geI5 dist l_inf_closed lattD42)  
  show "Inf X {x, Sup X {y, z}} \<le> Sup X {Inf X {x, y}, Inf X {x, z}}"  by (simp add: B5 B6)
qed

lemma inf_distributiveD2:
  "\<lbrakk>inf_distributive X; is_lattice X\<rbrakk> \<Longrightarrow> distributive_lattice X"
apply(rule distr_latticeI1)
proof-
  fix x y z assume P:"inf_distributive X" "is_lattice X" "x \<in> X" "y \<in> X" "z \<in> X"
  have B0:" Sup X {Inf X {x, y}, Inf X {x, z}} \<le> Inf X {x, Sup X {y, z}}"  by (simp add: P(2-5) distrib_inf_le) 
  have B1:" Inf X {y, z} \<le> Sup X {x, Inf X {y, z}}" by (simp add: P(2-5) bsup_geI2 l_inf_closed lattD42)
  obtain y1 z1 where dist:"y1 \<in> X \<and> z1 \<in> X \<and> y \<le> y1 \<and> z \<le> z1 \<and>  (Sup X {x, Inf X {y, z}}) = Inf X {y1, z1}" by (metis B1 P(1,2-5) inf_distributiveD1 l_inf_closed l_sup_closed) 
  have B2:"x \<le> Inf X {y1, z1}" by (metis P(2-5)  dist l_inf_closed lat_bsup_geI1)
  have B3:"x \<le> y1 \<and> x \<le> z1"  using B2 P(2-3) binf_iff dist lattD41 by blast 
  have B4:"y1 = Sup X {x, y1} \<and> z1 = Sup X {x, z1}" by (simp add: B3 P(3) dist ge_sup1)
  have B5:"Sup X {x, Inf X {y, z}} = Inf X {Sup X {x, y1}, Sup X {x, z1}}"  using B4 dist by presburger
  have B6:"... \<ge> Inf X {Sup X {x, y}, Sup X {x, z}}" by (metis B3 B4 P(2-5) binf_leI5 bsup_geI3 dist lattD41 lattD42 ssupD4) 
  show "Inf X {Sup X {x, y}, Sup X {x, z}} \<le> Sup X {x, Inf X {y, z}}" by (simp add: B5 B6) 
qed

lemma pfilter_compl3: "\<lbrakk>is_lattice X; is_pfilter X F; x \<in> (X-F); y \<in> X; y \<le> x\<rbrakk> \<Longrightarrow>y \<in> (X-F)"
by (metis Diff_iff is_filterE1 is_ord_clE is_pfilterE1)

lemma pfilter_compl4: "\<lbrakk>is_lattice X; is_pfilter X F\<rbrakk> \<Longrightarrow> is_ord_cl X (X-F) (\<ge>)"
by (simp add: is_filterE1 is_ord_cl_comp1 is_pfilterE1) 

lemma prime_filter_compl5: "\<lbrakk>is_lattice X; is_pfilter X F; sup_prime X F; x \<in> (X-F); y \<in> (X-F)\<rbrakk> \<Longrightarrow> Sup X {x, y} \<in> (X-F)"
by (metis Diff_iff l_sup_closed sup_primeD1)


lemma prime_filter_on_lattice:
  assumes A0:"is_lattice X" and A1:"is_pfilter X F" and A2:"sup_prime X F" and
          A3:"a \<in> filters_on X" and
          A4:"b \<in> filters_on X" and
          A5:"F=Inf (filters_on X) {a, b}"
  shows "F = a \<or> F =b"
proof-
  have B0:"F=a \<inter> b" by (simp add: A0 assms(4) assms(5) assms(6) filters_lattice_inf_op)
  have B1:"a \<subseteq> F \<or> b \<subseteq> F" using B0 A0 A1 A2 A3 A4 B0 sup_prime_pfilterD4[of X F a b]  by (simp add:filters_on_iff)
  have B2:"\<not>(a \<subseteq> F) \<longrightarrow> b = F" using B0 B1 by blast
  show ?thesis
    using B0 B2 by blast
qed

(*
  using 
    sup_prime_pfilterD4 sup_prime_pfilterI2 
    prime_filter_compl prime_ideal_compl 
  we have the characterization of sup prime proper filters on a lattice in terms of
    \<forall>F1 F2 \<in> filters_on X. F1 \<inter> F2 \<subseteq> F \<Longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F
  and in terms of 
    is_pideal (X-F)  \<and> inf_prime (X-F)
*)


lemma top_lattice_inf:"\<lbrakk> x \<in> X; y \<in> X; is_greatest X top; is_inf X {x, y} top\<rbrakk> \<Longrightarrow> x =top \<and> y=top"by (simp add: binary_infD31 binary_infD32 greatestD2 is_infE1 order_class.order_eq_iff)



definition meet_reducible::"'a::order set \<Rightarrow> 'a \<Rightarrow> bool" where "meet_reducible X x \<equiv> (\<exists>A \<in> Pow_ne X. x \<notin> A \<and> is_inf X A x)"
abbreviation meet_irr where "meet_irr X x \<equiv> \<not>(meet_reducible X x)"
lemma mredI1:"\<lbrakk>A \<in> Pow_ne X; x \<notin> A; is_inf X A x\<rbrakk> \<Longrightarrow> meet_reducible X x" using meet_reducible_def by blast 
lemma mredI2:"\<exists>A \<in> Pow_ne X. x \<notin> A \<and> is_inf X A x \<Longrightarrow> meet_reducible X x" by (simp add: meet_reducible_def)
lemma mredD1:"meet_reducible X x \<Longrightarrow> (\<exists>A \<in> Pow_ne X. x \<notin> A \<and> is_inf X A x)"  by (simp add: meet_reducible_def) 
lemma mredD2:"meet_reducible X x \<Longrightarrow> \<not>(is_greatest X x)"
proof-
  assume A0:"meet_reducible X x"
  obtain A where B0:"A \<in> Pow_ne X" "x \<notin> A" "is_inf X A x"  using A0 mredD1 by blast
  have B1:"A \<subseteq> X"  by (simp add: B0(1) pow_neD1)
  obtain a where  B2:"a \<in> A"  using B0(1) pow_ne_iff2 by fastforce
  have B3:"x < a"  using B0(2) B0(3) B2 is_infD1121 order_less_le by blast
  show "\<not>(is_greatest X x)"  by (meson B1 B2 B3 in_mono maximalD4 maximalI3)
qed

lemma mredD3:
  "\<lbrakk>m \<in> X; is_clattice X;  \<not>(is_greatest X m)\<rbrakk> \<Longrightarrow> {x \<in> X. m < x} \<noteq> {}" 
   by (metis Collect_empty_eq antisym_conv2 clatD1 csupD3 greatest_iff)
lemma mredD4:
  assumes A0:"is_clattice X" and A1:"m \<in> X" and A2:"\<not>(is_greatest X m)" and A3:"\<not>(m < Inf X {x \<in> X. m < x})"
  shows "meet_reducible X m"
proof-
  let ?A="{x \<in> X. m < x}"
  obtain B0:"?A \<subseteq> X" and B1:"?A \<noteq> {}" using A0 A1 A2 mredD3 by auto
  have B2:"m \<le> Inf X ?A"  by (metis (no_types, lifting) A0 A1 B0 B1 CollectD cinfD62 clatD2 lb_def order.strict_implies_order)
  have B3:"m = Inf X ?A"  using A3 B2 order_less_le by blast
  have B4:"?A \<in> Pow_ne X"  using B1 pow_ne_iff2 by blast
  have B5:"m \<notin> ?A"   by simp
  have B6:"is_inf X ?A m"  by (metis A0 B0 B1 B3 cinfD4 clatD2)
  show "meet_reducible X m"  using B4 B6 mredI1 by blast
qed

lemma mredD5:
  "\<lbrakk>is_clattice X; m \<in> X; \<not>(is_greatest X m); meet_irr X m\<rbrakk> \<Longrightarrow> m < Inf X {x \<in> X. m < x}"
   using mredD4 by blast

lemma mredD6:
  assumes A0:"is_clattice X" and A1:"m \<in> X" and A2:"\<not>(is_greatest X m)" and A3:"meet_reducible X m"
  shows "\<not> ( m < Inf X {x \<in> X. m < x})"
proof-
  let ?A="{x \<in> X. m < x}"
  obtain A where B0:"A \<in> Pow_ne X" "m \<notin> A" "is_inf X A m"  using A3 meet_reducible_def by blast 
  obtain B1:"\<And>x. x \<in> A \<Longrightarrow> m < x"  using B0(2) B0(3) is_infD1121 order_less_le by blast
  obtain B2:"A \<subseteq> ?A"  using B0(1) \<open>\<And>thesis::bool. ((\<And>x::'a::order. x \<in> (A::'a::order set) \<Longrightarrow> (m::'a::order) < x) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> pow_neD1 by auto
  have B3:"?A \<subseteq> X" "?A \<noteq> {}"  apply simp  using A0 A1 A2 mredD3 by blast
  have B4:"m \<le> Inf X ?A"   by (metis (no_types, lifting) A0 A1 B3(1) B3(2) CollectD cinfD62 clatD2 lb_def order.strict_implies_order)
  have B5:"... \<le> Inf X A"  by (simp add: A0 B2 inf_anti1)
  have B6:"... = m "    by (simp add: B0(3) inf_equality)
  show "\<not> ( m < Inf X {x \<in> X. m < x})"  using B5 B6 leD by blast
qed
lemma mredD7:
  "\<lbrakk>is_clattice X; m \<in> X; \<not>(is_greatest X m); m < Inf X {x \<in> X. m < x} \<rbrakk> \<Longrightarrow>meet_irr X m " 
  using mredD6 by auto

lemma mred_iff1:
  "\<lbrakk>is_clattice X; m \<in> X; \<not>(is_greatest X m)\<rbrakk> \<Longrightarrow>  m < Inf X {x \<in> X. m < x} \<longleftrightarrow> meet_irr X m "
   using mredD5 mredD7 by blast
lemma mredD8:
  "\<lbrakk>m \<in> X; is_clattice X;  (is_greatest X m)\<rbrakk> \<Longrightarrow> meet_irr X m"   
  using mredD2 by blast 

lemma mirredD1:
  "\<lbrakk>A \<in> Pow_ne X; is_inf X A x; meet_irr X x\<rbrakk> \<Longrightarrow>x \<in> A " 
  using mredI1 by blast 
lemma mirredI1:
  "(\<And>A.  \<lbrakk>A \<in> Pow_ne X; is_inf X A x\<rbrakk> \<Longrightarrow> x \<in> A) \<Longrightarrow>  meet_irr X x " 
   using mredD1 by blast
lemma mirredD2:
  " meet_irr X x \<Longrightarrow>(\<And>A.  \<lbrakk>A \<in> Pow_ne X; is_inf X A x\<rbrakk> \<Longrightarrow> x \<in> A)"
   using mredI1 by blast 


lemma compact_dense:
  assumes A0:"is_clattice X" and A1:"compactly_generated X" and A2:"x \<in> X"
  shows "x = Sup X {k \<in> compact_elements X. k \<le> x}"
proof-
  let ?K=" compact_elements X"
  let ?Kd="{k \<in> ?K. k \<le> x}"
  obtain Kx where A3:"Kx \<in> Pow ?K" "is_sup X Kx x" by (meson A1 A2 compactly_generatedD1)
  have B0:"?K \<subseteq> X"   by (simp add: compact_elements_sub)
  have B1:"?Kd \<subseteq> X" using B0 by blast
  have B2:"Kx \<subseteq> ?Kd" using A3(1) A3(2) is_supD1121 by fastforce
  have B3:"Sup X ?Kd \<le> Sup X Kx"   by (metis (no_types, lifting) A0 A2 A3(2) B1 B2 clatD1 csupD62 dual_order.trans empty_iff mem_Collect_eq subsetI sup_equality sup_iso1 ub_def)
  have B4:"... = x"  by (simp add: A3(2) sup_equality)
  have B6:"x \<le> Sup X ?Kd"   using A0 B1 B2 B4 sup_iso1 by blast
  show ?thesis using B3 B4 B6 by auto
qed

lemma compactly_generated_meets:
  assumes A0:"is_clattice X" and A1:"compactly_generated X" and A2:"x \<in> X" and A3:"y \<in> X" and 
          A4:"\<not>(y \<le> x)"
  shows "\<exists>k \<in> compact_elements X. k \<le> y \<and> \<not>(k \<le> x)"
  by (meson A1 A2 A3 A4 PowD compactly_generatedD1 is_supD1121 is_supE4 subset_iff ub_def)

lemma meet_reduction1:"\<lbrakk>is_clattice X; m \<in> X; meet_reducible X m\<rbrakk> \<Longrightarrow> m \<in> lbd X {x \<in> X. m < x}" using lbd_mem_iff2 by fastforce

lemma meet_reduction2:"\<lbrakk>is_clattice X; m \<in> X; meet_reducible X m\<rbrakk> \<Longrightarrow>  m=Inf X {x \<in> X. m < x}"
proof-
  let ?A="{x \<in> X. m < x}"
  assume A0:"is_clattice X" "m \<in> X" "meet_reducible X m"
  obtain A where B0:"A \<in> Pow_ne X" "m \<notin> A" "is_inf X A m"  using A0(3) mredD1 by blast
  obtain B1:"\<And>x. x \<in> A \<Longrightarrow> m < x"  using B0(2) B0(3) is_infD1121 order_less_le by blast
  obtain B2:"A \<subseteq> ?A"  using B0(1) \<open>\<And>thesis::bool. ((\<And>x::'a::order. x \<in> (A::'a::order set) \<Longrightarrow> (m::'a::order) < x) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> pow_neD1 by auto
  have B3:"?A \<subseteq> X"  by simp
  have B4:"?A \<noteq> {}"  using B0(1) B2 pow_ne_iff2 by fastforce 
  have B5:"m \<le> Inf X ?A" by (metis (no_types, lifting) A0(1) A0(2) B3 B4 CollectD cinfD62 clatD2 lb_def order.strict_implies_order)
  have B6:"... \<le> Inf X A"  by (simp add: A0 B2 inf_anti1)
  have B7:"... = m "  by (simp add: B0(3) inf_equality)
  show "m=Inf X {x \<in> X. m < x}"
    using B5 B6 B7 by auto
qed

lemma mirred_temp1:
  assumes A0:"is_clattice X" and A1:"compactly_generated X" and A2:"a \<in> X" and A3:"b \<in> X" and 
          A4:"\<not>(b \<le> a)" and A5:"is_compact X k" and A6:"k \<le> b" and A7:"\<not>(k \<le> a)" and 
          A9:"D \<subseteq>  {q \<in> X. a \<le> q \<and> \<not> (k \<le> q)}" and A10:"is_dir D (\<le>)" and A11:"D \<noteq> {}"
  shows "Sup X D \<in> {q \<in> X. a \<le> q \<and> \<not> (k \<le> q)}"
proof-
  let ?Q="{q \<in> X. a \<le> q \<and> \<not> (k \<le> q)}"
  have B0:"?Q \<subseteq> X" by simp
  obtain j where B1:"is_sup X D j"   by (meson A0 A9 B0 clatD21 dual_order.trans)
  have B2:"j \<in> X"    using B1 is_supE1 by blast
  have B3:"\<forall>d. d \<in> D \<longrightarrow> a \<le> d"   using A9 by blast
  have B4:"a \<in> lbd X D"   by (simp add: A2 B3 lbdI)
  have B5:"a \<le> j"   by (meson A11 B1 B3 bot.extremum_uniqueI dual_order.trans is_supE2 subset_emptyI ub_def)
  have B6:"\<not> (k \<le> j)"
  proof(rule ccontr)
    assume P0:"\<not>(\<not> (k \<le> j))" obtain P1:"k \<le> j"  using P0 by auto
    have B7:"k \<le> Sup X D"   using B1 P1 sup_equality by blast
    have B8:"D \<in> Pow_ne X" by (meson A11 A9 B0 pow_neI subset_trans)
    have B9:"is_sup_semilattice X"    by (simp add: A0 clatD1 csup_fsup)
    obtain d where B10:"d \<in> D \<and> k \<le> d" using ccompact0   using A10 A5 B7 B8 B9 by blast
    show False   using A9 B10 by blast
  qed
  have B11:"j \<in> ?Q"   by (simp add: B2 B5 B6)
  show "Sup X D \<in> ?Q"
    using B1 B11 sup_equality by blast
qed




lemma mirred_temp2b:
  assumes A0:"is_clattice X" and A1:"compactly_generated X" and A2:"a \<in> X" and A3:"b \<in> X" and 
          A4:"\<not>(b \<le> a)" and A5:"is_compact X k" and A6:"k \<le> b" and A7:"\<not>(k \<le> a)"
  shows "\<exists>m \<in> {q \<in> X. a \<le> q \<and> \<not> (k \<le> q)}. \<forall>q \<in> {q \<in> X. a \<le> q \<and> \<not> (k \<le> q)}.  m \<le> q \<longrightarrow> q = m"
proof(rule predicate_Zorn)
  show "partial_order_on {q \<in> X. a \<le> q \<and> \<not> k \<le> q} (relation_of (\<le>) {q \<in> X. a \<le> q \<and> \<not> k \<le> q})"
    by (smt (verit, del_insts) dual_order.antisym order_trans partial_order_on_relation_ofI verit_comp_simplify1(2))
  show "\<And>C. C \<in> Chains (relation_of (\<le>) {q \<in> X. a \<le> q \<and> \<not> k \<le> q}) \<Longrightarrow> \<exists>u\<in>{q \<in> X. a \<le> q \<and> \<not> k \<le> q}. \<forall>q\<in>C. q \<le> u"
proof-
    let ?Q="{q \<in> X. a \<le> q \<and> \<not> k \<le> q}"
    fix C assume A8:"C \<in> Chains (relation_of (\<le>) ?Q)"
    have B0:"C \<subseteq> X"   using A8 Chains_relation_of by blast
    have B1:"\<forall>c. c \<in> C \<longrightarrow> a \<le> c"   using A8 Chains_relation_of by force
    have B2:"\<forall>c. c \<in> C \<longrightarrow> \<not> (k \<le> c)"   using A8 Chains_relation_of by blast
    show "\<exists>u\<in>{q \<in> X. a \<le> q \<and> \<not> k \<le> q}. \<forall>q\<in>C. q \<le> u"
      proof(cases "C = {}")
        case True
        then show ?thesis  using A2 A7 by blast
      next
        case False
        have B3:"C \<noteq> {}"   by (simp add: False)
        have B4:"\<And>x y. x \<in> C \<and> y \<in> C \<longrightarrow> (\<exists>z \<in> C. x \<le> z \<and> y \<le> z)"
        proof
          fix x y assume A10:"x \<in> C \<and>  y \<in> C"
          have B1:"(x, y) \<in> relation_of (\<le>) ?Q \<or> (y, x) \<in> relation_of (\<le>) ?Q" using Chains_def[of " relation_of (\<le>) ?Q"] A8 A10 by auto
          have B2:"x \<le> y \<or> y \<le> x" using B1  relation_of_def[of "(\<le>)" "?Q"] by blast
          show "(\<exists>z \<in> C. x \<le> z \<and> y \<le> z)"  using A10 B2 by blast
        qed
        have B5:"is_dir C (\<le>)" by (simp add: B4 is_dirI1)
        have B6:"C \<subseteq> ?Q"    using A8 Chains_relation_of by blast
        have B7:"Sup X C \<in> ?Q" using A0 A1 A2 A3 A4 A5 A6 A7 B3 B5 B6  mirred_temp1[of X a b k C] by blast
        have B8:"\<forall>c  \<in> C. c \<le> Sup X C" by (meson A0 B0 False clatD1 csupD4 is_supD1121)   
        then show ?thesis    using B7 by blast 
    qed
  qed
qed

lemma mirred_temp2c:
  assumes A0:"is_clattice X" and A1:"compactly_generated X" and A2:"a \<in> X" and A3:"b \<in> X" and 
          A4:"\<not>(b \<le> a)" and A5:"is_compact X k" and A6:"k \<le> b" and A7:"\<not>(k \<le> a)" and
          A8:"m \<in> {q \<in> X. a \<le> q \<and> \<not> (k \<le> q)} \<and> ( \<forall>q \<in> {q \<in> X. a \<le> q \<and> \<not> (k \<le> q)}.  m \<le> q \<longrightarrow> q = m)"
  shows "\<not>(meet_reducible X m)"
proof(rule ccontr)
  let ?Q="{q \<in> X. a \<le> q \<and> \<not> (k \<le> q)}"
  assume P:"\<not>\<not>(meet_reducible X m)"
  obtain P1:"meet_reducible X m"
    using P by auto
  have B0:"\<And>x. x \<in> X \<and> x > m \<longrightarrow> k \<le> x"
  proof
    fix x assume A9: "x \<in> X \<and> x > m"
    have B01:"x \<notin> ?Q" using A8 A9 nless_le by blast 
    have B02:"a \<le> x"  using A8 A9 by force
    show "k \<le> x" using A9 B01 B02 by blast
  qed
  have B1:"m=Inf X {x \<in> X. m < x}"  using A0 A8 P meet_reduction2 by blast
  have B2:"k \<in> lbd X {x \<in> X. m < x}"  by (metis (mono_tags, lifting) A5 B0 CollectD compactD2 lbdI)
  have B3:"k \<le> m"    by (metis A0 B1 B2 Collect_subset P cinfD61 clatD2 clatD22 inf_equality is_inf_def lbd_empty mredD2)
  show False
    using A8 B3 by blast
qed


lemma mirred_temp2d:
  assumes A0:"is_clattice X" and A1:"compactly_generated X" and A2:"a \<in> X" and A3:"b \<in> X" and 
          A4:"\<not>(b \<le> a)"
  obtains m where "m \<in> X" "meet_irr X m" "a \<le> m" "\<not> (b \<le> m)"
proof-
  obtain k where B0:"k \<in> compact_elements X" and  B1:"k \<le> b" and B2: "\<not> (k \<le> a)"  using A0 A1 A2 A3 A4 compactly_generated_meets by blast
  have B0b:"is_compact X k"   using B0 compact_elements_mem_iff1 by blast
  obtain m where B3:"m \<in> {q \<in> X. a \<le> q \<and> \<not> (k \<le> q)} \<and> (\<forall>q \<in> {q \<in> X. a \<le> q \<and> \<not> (k \<le> q)}.  m \<le> q \<longrightarrow> q = m)"   using A0 A1 A2 A3 A4 B0b B1 B2 mirred_temp2b[of X a b k] by blast
  have B4:"\<not>(meet_reducible X m)" using mirred_temp2c[of X a b  k m] A0 A1 A2 A3 A4 B0b B1 B2 B3  by blast 
  show ?thesis
    using B1 B3 B4 that by force
qed


lemma mirred_temp3:
  assumes A0:"is_clattice X" and A1:"compactly_generated X" and A2:"a \<in> X"
  shows "a = Inf X {m \<in> X. meet_irr X m \<and> a \<le> m}"
proof-
  let ?M="{m \<in> X. meet_irr X m \<and> a \<le> m}" 
  obtain top where top:"is_greatest X top" using A0 clatD1 csupD3 by blast
  obtain B0:"?M \<subseteq> X" and B1:"top \<in> ?M" and B2:"?M \<noteq> {}"   by (metis (no_types, lifting) A2 empty_iff greatestD11 greatestD2 mem_Collect_eq mredD2 subsetI top)
  obtain b where idef:"is_inf X ?M b"  using A0 B0 clatD22 by blast
  have B4:"a \<le> b"  using A2 idef is_infE4 lb_def by blast
  have B5: "\<not> (a < b)"
  proof(rule ccontr)
    assume B5dneg:"\<not> \<not> (a < b)" obtain B5neg:"a < b"  using B5dneg by auto
    obtain m where B50:"m \<in> X" and B51:"meet_irr X m" and  B52:"a \<le> m" and B53:"\<not> (b \<le> m)" by (meson A0 A1 A2 B5neg idef is_infE1 leD mirred_temp2d)
    have B54:"m \<in> ?M"   by (simp add: B50 B51 B52)
    have B55:"b \<le> m"  using B54 idef is_infD1121 by blast
    show False
      using B53 B55 by auto
  qed
  have "a = b"  using B4 B5 nless_le by blast
  show ?thesis
    using \<open>(a::'a::order) = (b::'a::order)\<close> idef inf_equality by fastforce
qed

lemma meet_irr_imp_fmeet_irr:
  "\<lbrakk>m \<in> X; is_lattice X;  meet_irr X m\<rbrakk> \<Longrightarrow> fin_inf_irr X m"
proof-
  assume A0:"m \<in> X" "is_lattice X" "meet_irr X m"
  have B0:"\<And>a b. a \<in> X \<and> b \<in> X \<and>  m = Inf X {a, b} \<longrightarrow> m = a \<or> m = b"
  proof
    fix a b assume A1:" a \<in> X \<and> b \<in> X \<and>  m = Inf X {a, b} "
    have B1:" {a, b} \<in> Pow_ne X"   by (simp add: A1 pow_ne_iff2)
    have B2:"is_inf X {a, b} m" by (simp add: A0(2) A1 lattD31)
    have B3:"m \<in> {a, b}"   using A0(3) B1 B2 mredI1 by blast
    show "m = a \<or> m = b"  using B3 by fastforce
  qed
  show "fin_inf_irr X m"
    using B0 fin_inf_irr_def by blast  
qed

lemma pfilters_metofprimes:
  assumes A0:"distributive_lattice X" and A1:"is_greatest X top" and A2:"F \<in> pfilters_on X"
  obtains M where "\<forall>Fm. Fm \<in> M \<longrightarrow> Fm \<in> filters_on X \<and> meet_irr (filters_on X) Fm " and "F = Inf (filters_on X) M"
proof-
  let ?FX="(filters_on X)"
  have B0:"compactly_generated ?FX"   using A0 A1 distr_latticeD5 filters_on_lattice_compactgen lattD1 by auto
  have B1:"is_clattice ?FX"  using A0 A1 distr_latticeD5 lattice_filters_complete by auto
  have B2:"F \<in> ?FX"   using A2 filters_onI is_pfilterE1 pfilters_onE by blast 
  have B3:"F = Inf ?FX {Fm \<in> ?FX. meet_irr ?FX Fm \<and> F \<le> Fm}"   by (simp add: B0 B1 B2 mirred_temp3)
  have B4:"\<forall>Fm.  Fm \<in> {Fm \<in> ?FX. meet_irr ?FX Fm \<and> F \<le> Fm} \<longrightarrow> Fm \<in> ?FX \<and> meet_irr ?FX Fm "  by fastforce
  then show ?thesis  using B3 that by blast
qed



lemma sup_prime_pfilterI3:
  assumes A0:"distributive_lattice X" and A1:"fin_inf_irr (filters_on X) F" and A2:"is_pfilter X F"
  shows "sup_prime X F"
proof-
  have B1:"(\<And>F1 F2. \<lbrakk> is_filter X F1; is_filter X F2; F1 \<inter> F2 \<subseteq> F\<rbrakk> \<Longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F)" 
   by (metis A0 A1 A2 distributive_lattice_def elem_inf_primeI3 elem_inf_prime_def filters_lattice_inf_op filters_on_iff is_pfilter_def lattice_filters_distr)
  show ?thesis by (simp add: A0 A2 B1 distr_latticeD5 sup_prime_pfilterI2)
qed

lemma prime_filter_irr3_converse:
  "\<lbrakk>distributive_lattice X; fin_inf_irr (filters_on X) F; is_pfilter X F\<rbrakk> \<Longrightarrow> sup_prime X F"  
  by (simp add: is_pfilterI1 sup_prime_pfilterI3)


lemma pfilters_metofprimes2:
  assumes A0:"distributive_lattice X" and A1:"is_greatest X top" and A2:"F \<in> pfilters_on X"
  obtains M where "\<forall>Fm. Fm \<in> M \<longrightarrow> Fm \<in> filters_on X \<and> sup_prime X Fm " and "F = Inf (filters_on X) M"
proof-
  let ?FX="(filters_on X)"
  have B0:"compactly_generated ?FX"   using A0 A1 distr_latticeD5 filters_on_lattice_compactgen lattD1 by auto
  have B1:"is_clattice ?FX"  using A0 A1 distr_latticeD5 lattice_filters_complete by auto
  have B2:"F \<in> ?FX" using A2 filters_onI is_pfilterE1 pfilters_onE by blast
  have B3:"F = Inf ?FX {Fm \<in> ?FX. meet_irr ?FX Fm \<and> F \<le> Fm}"   by (simp add: B0 B1 B2 mirred_temp3)
  have B4:"\<And>Fm.  Fm \<in> {Fm \<in> ?FX. meet_irr ?FX Fm \<and> F \<le> Fm} \<Longrightarrow> Fm \<in> ?FX \<and> sup_prime X Fm " 
  proof-
    fix Fm assume A3:"Fm \<in> {Fm \<in> ?FX. meet_irr ?FX Fm \<and> F \<le> Fm}" 
    have B40:"Fm \<in> ?FX \<and> meet_irr ?FX Fm"  using A3 by blast
    have B41:"fin_inf_irr ?FX Fm"  using A0 B40 distr_lattice_filters meet_irr_imp_fmeet_irr by blast
    have B43:"is_greatest ?FX X" by (metis A0 Sup_le_iff distr_latticeD5 empty_iff filters_is_clr1b greatestI3 lattD41 lattice_filter_dunion7 subsetI)  
    have B44:"sup_prime X Fm"
    proof(cases "is_pfilter X Fm")
      case True then show ?thesis   using A0 B40 B41 filters_on_iff prime_filter_irr3_converse sup_prime_def by blast
    next
      case False obtain B45:"Fm = X"  using B40 False filters_on_iff    using is_pfilterI1 by blast
      then show ?thesis using sup_primeI1 by blast
    qed
    show "Fm \<in> ?FX \<and> sup_prime X Fm"  by (simp add: B40 B44)
  qed
  then show ?thesis  using B3 that by blast
qed


lemma is_dwdirI1sets:
  "(\<And>A B. \<lbrakk>A \<in> F; B \<in> F\<rbrakk> \<Longrightarrow> A \<inter> B \<in> F) \<Longrightarrow> is_dir F (\<lambda>(x::'a set) y::'a set. y \<subseteq> x)"
proof-
    assume dwdir:"\<And>A B. \<lbrakk>A \<in> F; B \<in> F\<rbrakk> \<Longrightarrow> A \<inter> B \<in> F"
    show "is_dir F (\<lambda>(x::'a set) y::'a set. y \<subseteq> x)"
    proof(rule is_dirI1)
      fix A B assume "A \<in> F" "B \<in> F"
      then obtain "A \<inter> B \<in> F \<and> A \<inter> B \<subseteq> A \<and>  A \<inter> B \<subseteq> B" by (simp add: dwdir)
      then show "\<exists>c\<in>F. c \<subseteq> A \<and> c \<subseteq> B" by blast
    qed
qed

lemma is_dwdir_obtain:
  assumes "is_dir F (\<lambda>(x::'a set) y::'a set. y \<subseteq> x)" and "A \<in> F" and "B \<in> F"
  obtains C where "C \<in> F" and "C \<subseteq> A" and "C \<subseteq> B"
  by (metis assms(1) assms(2) assms(3) is_dirE1) 


lemma is_dwdirD1sets:
  assumes sub:"F \<subseteq> Pow X" and 
          dir:"is_dir F (\<lambda>(x::'a set) y::'a set. y \<subseteq> x)" and
          upc:"is_ord_cl (Pow X) F (\<subseteq>) " 
  shows "(\<And>A B. \<lbrakk>A \<in> F; B \<in> F\<rbrakk> \<Longrightarrow> A \<inter> B \<in> F)"
proof-
  fix A B assume "A \<in> F" and "B \<in> F" 
  then obtain C where "C \<in> F" and "C \<subseteq> A" and  "C \<subseteq> B" using dir is_dwdir_obtain[of F A B] by auto
  then obtain "C \<subseteq> A \<inter> B" by simp
  also have "A \<inter> B \<in> Pow X" using \<open>(A::'a::type set) \<in> (F::'a::type set set)\<close> sub by auto
  then show "A \<inter> B \<in> F" using \<open>(C::'a::type set) \<in> (F::'a::type set set)\<close> calculation is_ord_clE upc by metis
qed

lemma filter_sets:
  assumes sub:"F \<subseteq> Pow X" and 
          nem:"F \<noteq> {}" and
          dir:"(\<And>A B. \<lbrakk>A \<in> F; B \<in> F\<rbrakk> \<Longrightarrow> A \<inter> B \<in> F)" and
          upc:"(\<And>A B. \<lbrakk>A \<in> F; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> B \<in> F)" 
  shows "is_filter (Pow X) F"
proof(rule is_filterI1)
 show "F \<noteq> {}" by (simp add:nem)
 show "F \<subseteq> Pow X" by (simp add:sub)
 show "is_dir F (\<lambda>(x::'a set) y::'a set. y \<subseteq> x)"  by (simp add: dir is_dwdirI1sets)
 show "is_ord_cl (Pow X) F (\<subseteq>)" by(auto intro:upc is_ord_clI)
qed


lemma sets_filter:
  assumes "is_filter (Pow X) F"
  shows sets_filter_nem:"F \<noteq> {}" and
        sets_filter_sub:"F \<subseteq> Pow X" and 
        sets_filter_dir:"(\<And>A B. \<lbrakk>A \<in> F; B \<in> F\<rbrakk> \<Longrightarrow> A \<inter> B \<in> F)" and
        sets_filter_upc:"(\<And>A B. \<lbrakk>A \<in> F; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> B \<in> F)" and
        sets_filter_top:"X \<in> F"
        using assms is_filterE1 apply blast
        apply (simp add: assms is_filterE1)
        apply (meson assms is_filterE1  is_dwdirD1sets)
        apply (meson assms is_filterE1 is_ord_clE)
        by (meson Pow_iff Pow_top assms greatest_iff is_filter_top)
        
 


lemma pfilter_sets:
  assumes A0:"F \<subseteq> Pow X" and 
          A1:"F \<noteq> {}" and
          A2:"F \<noteq> Pow X" and
          A3:"(\<And>A B. \<lbrakk>A \<in> F; B \<in> F\<rbrakk> \<Longrightarrow> A \<inter> B \<in> F)" and
          A4:"(\<And>A B. \<lbrakk>A \<in> F; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> B \<in> F)" 
  shows "is_pfilter (Pow X) F "
proof(rule is_pfilterI1) 
  show "is_filter (Pow X) F" using filter_sets[of F X] A0 A1 A3 A4 by auto
  show "F \<noteq> Pow X" using A2 by simp
qed
 
lemma sets_pfilter:
  assumes "is_pfilter (Pow X) F"
  shows sets_pfilter_nem:"F \<noteq> {}" and 
        sets_pfilter_sub:"F \<subseteq> Pow X" and 
        sets_pfilter_ntp:"F \<noteq> Pow X" and
        sets_pfilter_dir:"(\<And>A B. \<lbrakk>A \<in> F; B \<in> F\<rbrakk> \<Longrightarrow> A \<inter> B \<in> F)" and
        sets_pfilter_upcl:"(\<And>A B. \<lbrakk>A \<in> F; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> B \<in> F)" and
        sets_pfilter_emp:"{} \<notin> F"
using assms is_filterE1 is_pfilter_def apply blast
apply (simp add: assms is_filterE1 is_pfilterE1)
using assms is_pfilterE1 apply blast
using assms is_pfilterE1 sets_filter_dir apply blast
apply (meson assms is_pfilterE1 sets_filter_upc)
proof-
   show "{} \<notin> F"
   proof(rule ccontr)
      assume "\<not> ({} \<notin> F)" then obtain "{} \<in> F" by blast
      then obtain "F = (Pow X)"
        by (meson Pow_bottom assms empty_subsetI is_filterE1 is_pfilterE1 least_iff up_cl_bot)
      show False  using \<open>(F::'a::type set set) = Pow (X::'a::type set)\<close> assms is_pfilterE1 by auto 
  qed
qed
     



lemma sets_pfilter2:
  assumes "is_pfilter (Pow X) F"
  shows   sets_pfilter2_dir:"is_dir F (\<lambda>(x::'a set) y::'a set. y \<subseteq> x)" and
          sets_pfilter2_upc:"is_ord_cl (Pow X) F (\<subseteq>) "
          using assms is_filterE1 is_pfilterE1 apply blast
          by (simp add: assms is_filterE1 is_pfilterE1)
 
lemma pfilter_sets_comp:
  assumes A0:"is_pfilter (Pow X) F" and A1:"(X-A) \<in> F"
  shows "A \<notin> F"
  by (metis A0 A1 Diff_disjoint is_pfilterE1 sets_filter_dir sets_pfilter_emp)

    
lemma pfilters_sets_comp2:
   "is_pfilter (Pow X) F \<Longrightarrow> A \<in> F \<Longrightarrow> (X-A) \<notin> F"
  using pfilter_sets_comp by blast

lemma pfilters_sets_comp3:
   "\<lbrakk>is_pfilter (Pow X) F; A \<subseteq> X; \<exists>U \<in> F. U \<inter> (X-A) = {}\<rbrakk> \<Longrightarrow> A \<in> F"
   by (metis (no_types, lifting) Diff_eq_empty_iff Int_Diff PowI is_ord_clE is_pfilterE1 sets_filter_top sets_pfilter2_upc sets_pfilter_dir)

lemma pfilters_sets_comp4:
   "\<lbrakk>is_pfilter (Pow X) F; A \<subseteq> X;  A \<notin> F\<rbrakk> \<Longrightarrow> \<forall>U \<in> F. U - A \<noteq> {}"
   by (meson PowI diff_shunt_var is_pfilter_def sets_filter_upc)

abbreviation convergence0 where
  "convergence0 R X \<equiv> R \<subseteq> {(F, x). F \<in> pfilters_on (Pow X) \<and> x \<in> X}" 

abbreviation convergence1 where
  "convergence1 R X \<equiv> (\<forall>x. x \<in> X \<longrightarrow> (lorc {x} (Pow X), x) \<in> R)"

abbreviation convergence2 where
  "convergence2 R X \<equiv> (\<forall>x \<in> X. \<forall>F \<in> pfilters_on (Pow X). \<forall>G \<in> pfilters_on (Pow X). (F, x) \<in> R \<and> F \<subseteq> G \<longrightarrow> (G, x)\<in>R)"

abbreviation convergence3 where
  "convergence3 R X \<equiv> (\<forall>x \<in> X. (\<Inter>{F. (F, x) \<in> R}, x) \<in> R)"

abbreviation pretop where
  "pretop R X \<equiv> convergence0 R X \<and> convergence1 R X \<and> convergence2 R X \<and> convergence3 R X"

lemma principal_filter_sets:
  "x \<in> X \<Longrightarrow> is_filter (Pow X) (lorc {x} (Pow X))"
  by (simp add: lorc_filter)

lemma principal_pfilter_sets:
  "x \<in> X \<Longrightarrow> is_pfilter (Pow X) (lorc {x} (Pow X))"
  by (metis Pow_bottom insert_not_empty is_pfilter_def lorc_eq_upbd principal_filter_sets subset_antisym subset_insertI ubd_mem_singleE)


lemma pmb_filters2:
  assumes A0:"is_pfilter (Pow X) F" and A1:"\<And>x. x \<in> (Pow X) \<Longrightarrow> (x \<in> F \<or> (X-x) \<in> F) \<and> \<not>(x \<in> F \<and> (X-x) \<in> F)"
  shows "is_maximal (pfilters_on (Pow X)) F"
proof-
  let ?X="Pow X"
  have B0:"F \<in> pfilters_on ?X"  by (simp add: A0 pfilters_onI) 
  have B1:"\<And>G. \<lbrakk>G \<in> filters_on ?X;  F \<subset> G \<rbrakk> \<Longrightarrow> G = ?X"
  proof-
    fix G assume A2:"G \<in> filters_on ?X" and A3:"F \<subset> G"
    obtain z where B10: "z \<in> G - F"  using A3 by auto
    have B11:"z \<notin> F" using B10 by blast 
    have B12:"X-z \<in> F" by (metis A1 A2 B10 B11 DiffD1 filters_onE in_mono is_filterE1) 
    have B13:"X-z \<in> G \<and> z \<in> G"  using A3 B10 B12 by blast
    have B14:"is_filter ?X G"   using A2 filters_on_iff by auto
    show "G=?X"  using B13 B14 is_pfilterI1 pfilters_sets_comp2 by blast 
  qed
  have B2:"\<And>G. \<lbrakk>G \<in> pfilters_on ?X;  F \<subseteq> G \<rbrakk> \<Longrightarrow> G = F"  by (metis B1 filters_on_iff is_pfilter_def pfilters_on_iff psubsetI) 
  show ?thesis
    by (metis (no_types, lifting) B0 B2 is_maximal_def)
qed

lemma filter_refinment:
  assumes A0:"is_filter (Pow X) F" and A1:"A \<in> Pow X"
  defines "H \<equiv> {E \<in> Pow X. \<exists>B \<in> F. A \<inter> B \<subseteq> E}" 
  shows filter_refinment_sub:"H \<subseteq> Pow X" and
        filter_refinment_top:"X \<in> H" and
        filter_refinment_nem:"H \<noteq> {}" and
        filter_refinement_dir:"is_dir H (\<lambda>(x::'a set) y::'a set. y \<subseteq> x)" and
        filter_refinement_upc:"is_ord_cl (Pow X) H (\<subseteq>) "  and
        filter_refinment_fil:"is_filter (Pow X) H" 
proof-
 show "X \<in> H" using A0 H_def sets_filter_top by fastforce
 show "H \<noteq> {}" using A0 H_def sets_filter_top by force
 show "H \<subseteq> Pow X" using H_def by blast
 show "is_dir H (\<lambda>(x::'a set) y::'a set. y \<subseteq> x)"
 proof(rule is_dirI1)
    show "\<And>(a::'a set) b::'a set. a \<in> H \<Longrightarrow> b \<in> H \<Longrightarrow> \<exists>c::'a set\<in>H. c \<subseteq> a \<and> c \<subseteq> b"
    proof-
      fix a b assume A3:"a \<in> H" and A4:"b \<in> H"  
      then obtain aB bB where B0:"aB \<in> F" and B1:"bB \<in> F" and B2:"A \<inter> aB \<subseteq> a" and B3:"A \<inter> bB \<subseteq> b"  using H_def by auto 
      then obtain B4:"aB \<inter> bB \<in> F"  using A0 sets_filter_dir by blast 
      then obtain B5:"A \<inter> aB \<inter> bB \<in> H"  using A1 H_def subset_trans by auto  
      also have B6:"A \<inter> aB \<inter> bB \<subseteq> a \<and> A \<inter> aB \<inter> bB \<subseteq> b"  using B2 B3 by blast
      then show "\<exists>c::'a set\<in>H. c \<subseteq> a \<and> c \<subseteq> b"   using calculation by auto
    qed
 qed
 also show "is_ord_cl (Pow X) H (\<subseteq>)"  apply(rule is_ord_clI) using H_def inf.absorb_iff2 by fastforce
 then show "is_filter (Pow X) H"
 by (simp add: \<open>(H::'a::type set set) \<noteq> {}\<close> \<open>(H::'a::type set set) \<subseteq> Pow (X::'a::type set)\<close> calculation is_filterI1)
qed  


lemma pfilter_refinment:
  assumes A0:"is_pfilter (Pow X) F" and A1:"A \<in> Pow X" and A2:"\<forall>B \<in> F. B \<inter> A \<noteq> {}"
  defines "H \<equiv> {E \<in> Pow X. \<exists>B \<in> F. A \<inter> B \<subseteq> E}" 
  shows pfilter_refinment_sub:"H \<subseteq> Pow X" and
        pfilter_refinment_top:"X \<in> H" and
        pfilter_refinment_nem:"H \<noteq> {}" and
        pfilter_refinement_dir:"is_dir H (\<lambda>(x::'a set) y::'a set. y \<subseteq> x)" and
        pfilter_refinement_upc:"is_ord_cl (Pow X) H (\<subseteq>) "  and
        pfilter_refinement_nce:"{} \<notin> H" and
        pfilter_refinement_ntp:"Pow X \<noteq> H" and
        pfilter_refinment_fil:"is_pfilter (Pow X) H" 
proof-
 obtain B0:"H \<subseteq> Pow X" and B1:"X \<in> H" and B2:"H \<noteq> {}" and B3:"is_dir H (\<lambda>(x::'a set) y::'a set. y \<subseteq> x)" and
        B4:"is_ord_cl (Pow X) H (\<subseteq>) "  and B5:"is_filter (Pow X) H" using A0 A1 filter_refinment[of X F A]
        by (simp add: H_def is_pfilter_def)
 then show "X \<in> H" by simp
 then show "H \<noteq> {}" by auto
 show "H \<subseteq> Pow X" by(simp add:B0)
 show "is_dir H (\<lambda>(x::'a set) y::'a set. y \<subseteq> x)" by(simp add:B3)
 show "is_ord_cl (Pow X) H (\<subseteq>)" by(simp add:B4)
 show "{} \<notin> H" by (simp add: A2 H_def Int_commute)
 then show "Pow X \<noteq> H" by blast
 then show "is_pfilter (Pow X) H" by (simp add: is_pfilter_def B5)
qed  


lemma finer_proper_filter:
  assumes A0:"is_pfilter (Pow X) F" and A1:"A \<in> Pow X" and A2:"\<forall>B \<in> F. B \<inter> A \<noteq> {}"
  defines "H \<equiv> {E \<in> Pow X. \<exists>B \<in> F. A \<inter> B \<subseteq> E}" 
  shows "is_pfilter (Pow X) H" and "F \<subseteq> H"
  using  pfilter_refinment_fil[of X F A] A0 A1 A2 H_def apply(fastforce)
  using A0 H_def is_filterE1 is_pfilterE1 by blast


lemma set_filter_inter_ne:
  assumes A0:"EF \<subseteq> filters_on (Pow X)" and A1:"EF \<noteq> {}"
  shows "X \<in> \<Inter>EF"
proof-
  have B0:"\<And>F. F \<in> EF \<Longrightarrow> X \<in> F" using A0 filters_on_iff sets_filter_top by blast
  then show ?thesis
    by simp
qed

        
lemma set_filter_inter:
  assumes A0:"EF \<subseteq> filters_on (Pow X)" and A1:"EF \<noteq> {}"
  shows "is_filter (Pow X) (\<Inter>EF)"
proof(rule is_filterI1)
  show "\<Inter> EF \<noteq> {}"
    by (metis A0 A1 equals0D set_filter_inter_ne)
  show "\<Inter> EF \<subseteq> Pow X"
    by (meson A0 A1 Inf_le_Sup dual_order.trans lattice_filter_dunion7)
  show  "is_dir (\<Inter> EF) (\<lambda>x y. y \<subseteq> x)"
  proof(rule is_dirI1)
    fix a b assume amem:"a \<in> \<Inter> EF" and  bmem:"b \<in> \<Inter> EF" 
    then obtain "\<And>F. F \<in> EF \<Longrightarrow> a \<in> F \<and> b \<in> F" by blast
    then obtain "\<And>F. F \<in> EF \<Longrightarrow> a \<inter> b \<in> F" using A0 filters_on_iff sets_filter_dir by blast
    then obtain "a \<inter> b \<in> \<Inter> EF" by blast
    then show "\<exists>c::'a set\<in>\<Inter> EF. c \<subseteq> a \<and> c \<subseteq> b"   by (metis inf.cobounded1 inf.cobounded2)
  qed
  show "is_ord_cl (Pow X) (\<Inter> EF) (\<subseteq>)"
  proof(rule is_ord_clI)
    fix a b assume amem:"a \<in> \<Inter> EF" and bmem:"b \<in> Pow X" and asb:" a \<subseteq> b"
    then obtain "\<And>F. F \<in> EF \<Longrightarrow> b \<in> F"  by (meson A0 InterD filters_onE sets_filter_upc subsetD)
    then show "b \<in> \<Inter> EF" by blast
  qed
qed

lemma pwr_least:
  "is_least (Pow X) {}"
  by (simp add: least_iff)
lemma pwr_greatesst:
  "is_greatest (Pow X) X"
  by (simp add: greatest_iff)
  
lemma pfilter_nem:
  "is_pfilter (Pow X) F \<Longrightarrow> {} \<notin> F"
  by (simp add: is_pfilter_def sets_pfilter_emp)
        
lemma set_pfilter_inter:
  assumes A0:"EF \<subseteq> pfilters_on (Pow X)" and A1:"EF \<noteq> {}"
  shows "is_pfilter (Pow X) (\<Inter>EF)"
proof(simp add:is_pfilter_def, auto)
  show "is_filter (Pow X) (\<Inter> EF)" by (meson A0 A1 filters_onI in_mono is_pfilterE1 pfilters_onE set_filter_inter subsetI)
  show "Pow X = \<Inter> EF \<Longrightarrow> False"
  by (metis A0 A1 Inter_lower in_mono is_filterE1 is_pfilterE1 pfilters_onE subsetI subset_antisym subset_empty)
qed


lemma principal_ufilter_sets:
  "x \<in> X \<Longrightarrow> is_maximal (pfilters_on (Pow X)) (lorc {x} (Pow X))"
  apply(rule pmb_filters2)
  apply (simp add: principal_pfilter_sets)
  by (simp add: lorc_mem_iff1)

abbreviation ccl where
  "ccl X Cl \<equiv> (Cl {} = {}) \<and> (\<forall>A. A \<in> Pow X \<longrightarrow> A \<subseteq> Cl A) \<and> (\<forall>A B. A \<in> Pow X \<and> B \<in> Pow X \<longrightarrow> Cl (A \<union> B) = (Cl A) \<union> (Cl B)) \<and>  (\<forall>A. A \<in> Pow X \<longrightarrow> Cl A \<subseteq> X) "


lemma pretop_to_cc:
  fixes q::"('a set set \<times> 'a) set" and X::"'a set"
  assumes A0:"pretop q X"
  defines "Cl \<equiv> (\<lambda>A. {x \<in> X. \<exists>G \<in> pfilters_on (Pow X). (G, x) \<in> q \<and> A \<in> G})"
  shows CCL0:"Cl {} = {}" and
        CCL1:"\<And>A. A \<in> Pow X \<Longrightarrow> A \<subseteq> Cl A" and
        CCL2:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X\<rbrakk> \<Longrightarrow> Cl (A \<union> B) = (Cl A) \<union> (Cl B)"
proof-
  have B0:"\<forall>G \<in>  pfilters_on (Pow X). {} \<notin> G" by (simp add: pfilters_on_iff sets_pfilter_emp) 
  then show "Cl {} = {}"  using Cl_def by blast
  show "\<And>A. A \<in> Pow X \<Longrightarrow> A \<subseteq> Cl A"
  proof-
    fix A assume A1:"A \<in> Pow X"
    show "A \<subseteq> Cl A"
    proof
      fix a assume A2:"a \<in> A"
      obtain B0:"a \<in> X"    using local.A1 local.A2 by blast 
      then obtain B1:"A \<in> (lorc {a} (Pow X))" and B2:"(lorc {a} (Pow X), a) \<in> q"     using A0 local.A1 local.A2 lorc_mem_iff1 by auto
      then show "a \<in> Cl A" using Cl_def A0 by auto
    qed
  qed
  show " \<And>A B. A \<in> Pow X \<Longrightarrow> B \<in> Pow X \<Longrightarrow> Cl (A \<union> B) = Cl A \<union> Cl B"
  proof-
    fix A B assume A3:"A \<in> Pow X" and A4:"B \<in> Pow X" 
    show "Cl (A \<union> B) = Cl A \<union> Cl B" (is "?lhs = ?rhs")
    proof
      show "?lhs \<subseteq> ?rhs"
      proof
        fix x assume L:"x \<in> ?lhs"
        obtain G where B2:"G \<in> pfilters_on (Pow X)" and  B3:"(G, x) \<in> q \<and> A \<union> B \<in> G" using Cl_def L by blast
        have B4:"x \<notin> Cl A \<Longrightarrow> x \<in> Cl B"
        proof-
          assume A5:"x \<notin> Cl A"
          then obtain B5:"A \<notin> G"   using B2 B3 Cl_def L by blast
          have B6:"\<forall>g \<in> G. g \<inter> (X-A) \<noteq> {}"by (meson A3 B2 B5 PowD pfilters_on_iff pfilters_sets_comp3) 
          have B7:"is_pfilter (Pow X) G"   by (simp add: B2 pfilters_onE)
          have B8:"(X-A) \<in> Pow X"    by simp
          define H where "H \<equiv> {E \<in> Pow X. \<exists>g \<in> G. (X-A) \<inter> g \<subseteq> E}" 
          obtain B9:"is_pfilter (Pow X) H"  using finer_proper_filter[of X G "(X-A)"] B6 B7 B8 H_def by blast
          obtain B10:"G \<subseteq> H"  using finer_proper_filter[of X G "(X-A)"] B6 B7 B8 H_def by blast
          have B11:"(X - A) \<inter> (A \<union> B) \<subseteq> B"   by blast
          have B12:"(X - A) \<inter> (A \<union> B) \<in> H"      using B3 H_def by blast
          have B13:"B \<in> H" using A4 B11 B3 H_def by blast
          have B14a:"H \<in> pfilters_on (Pow X) \<and>  (G, x) \<in> q \<and> G \<subseteq> H"    by (simp add: B10 B3 B9 pfilters_on_iff)
          then have B14:"(H, x) \<in> q"  using A0 by blast
          show "x \<in> Cl B"  using B13 B14 B14a Cl_def L by blast
        qed
        have B15:"x \<in> Cl A \<or> x \<in> Cl B"  using B4 by blast
        then show "x \<in> Cl A \<union> Cl B" by simp
      qed
    next
      show "?rhs \<subseteq> ?lhs"
      proof
        fix x assume R:"x \<in> ?rhs"
        then obtain B0:"x \<in> Cl A \<or> x \<in> Cl B" by auto
        then obtain G where B1:"G \<in> pfilters_on (Pow X)" and B2:"(G, x) \<in> q \<and> (A \<in> G \<or>  B \<in> G)"  using Cl_def by blast
        then obtain B3:"A \<union> B \<in> G" using A3 A4 is_ord_clE pfilters_onE sets_pfilter2_upc by fastforce
        then have B4:"G \<in>  pfilters_on (Pow X) \<and> (G, x) \<in> q \<and> (A \<union> B) \<in> G" by (simp add: B1 B2)
        then obtain B5:"\<exists>G1 \<in> pfilters_on (Pow X). (G1, x) \<in> q \<and> (A \<union>B ) \<in> G1" by blast
        also obtain "x \<in> X" using B0 Cl_def by blast
        then show "x \<in> ?lhs" using Cl_def    using calculation by blast
      qed
    qed
  qed
qed

    
          


lemma cc_to_pretop:
  fixes Cl::"'a set \<Rightarrow> 'a set" and X::"'a set"
  assumes A0:"ccl X Cl"
  defines "N \<equiv> (\<lambda>x. {V \<in> Pow X. x \<notin> Cl (X-V)})"
  defines "q \<equiv> {(EF, x). EF \<in>  pfilters_on (Pow X) \<and> N x \<subseteq> EF}"
  shows gc1:"\<And>x. x \<in> X \<Longrightarrow> (lorc {x} (Pow X), x) \<in> q" and
        gc2:"\<And>x F G. \<lbrakk>x\<in> X; F\<in> pfilters_on (Pow X); G \<in> pfilters_on (Pow X); (F, x) \<in> q; F \<subseteq> G\<rbrakk> \<Longrightarrow> (G, x)\<in>q" and
        gc3:"\<And>x. x \<in> X \<Longrightarrow>  (\<Inter>{F. (F, x) \<in> q}, x) \<in> q"
proof-
  show "\<And>x. x \<in> X \<Longrightarrow> (lorc {x} (Pow X), x) \<in> q"
  proof-
     fix x assume A1:"x \<in> X" 
     let ?U="(lorc {x} (Pow X))"
     obtain B0:"?U \<in> pfilters_on (Pow X)"    using local.A1 maximalD1 principal_ufilter_sets by fastforce
     have B1:"N x \<subseteq> ?U"
     proof
      fix V assume A2:"V \<in> N x"
      have B2:"x \<notin> Cl (X-V)"   using N_def local.A2 by auto
      have B3:"Cl (X-V) \<supseteq> X-V"   by (simp add: A0)
      obtain B4:"x \<in> V"   using B2 B3 local.A1 by blast
      show "V \<in> ?U"   using A0 B4 N_def local.A2 lorc_mem_iff1 by auto
     qed
     show "(?U, x)\<in> q" using B0 B1 q_def by blast
  qed
  show "\<And>x F G. \<lbrakk>x\<in> X; F\<in> pfilters_on (Pow X); G \<in> pfilters_on (Pow X); (F, x) \<in> q; F \<subseteq> G\<rbrakk> \<Longrightarrow> (G, x)\<in>q"
    using q_def by auto 
  show "\<And>x. x \<in> X \<Longrightarrow>  (\<Inter>{F. (F, x) \<in> q}, x) \<in> q"
  proof-
    fix x assume A1:"x \<in> X"
    have B0:"\<And>F. (F, x) \<in> q \<Longrightarrow> F \<in> pfilters_on (Pow X) \<and>  N x \<subseteq> F"  using q_def by fastforce
    have B1:"N x \<subseteq>  \<Inter>{F. (F, x) \<in> q}"  using B0 by blast
    have B2:"\<And>F. (F, x) \<in> q \<Longrightarrow> F \<in> filters_on (Pow X) " using B0 filters_on_iff is_pfilterE1 pfilters_on_iff by blast  
    have B3:"is_filter (Pow X) (\<Inter>{F. (F, x) \<in> q} )" by (smt (verit, del_insts) A1 B2 Collect_mono_iff \<open>\<And>x::'a::type. x \<in> (X::'a::type set) \<Longrightarrow> (lorc {x} (Pow X), x) \<in> (q::('a::type set set \<times> 'a::type) set)\<close> empty_Collect_eq filters_on_def filters_on_iff set_filter_inter)
    have B4:"(\<Inter>{F. (F, x) \<in> q}) \<noteq> Pow X"by (metis A1 Inter_iff PowI \<open>\<And>x::'a::type. x \<in> (X::'a::type set) \<Longrightarrow> (lorc {x}(Pow X), x) \<in> (q::('a::type set set \<times> 'a::type) set)\<close> empty_iff empty_subsetI insert_subset lorc_mem_iff1 mem_Collect_eq)
    have B5:"is_pfilter (Pow X) (\<Inter>{F. (F, x) \<in> q} )" using B3 B4 is_pfilterI1 by blast
    show "(\<Inter>{F. (F, x) \<in> q}, x) \<in> q" using B5 pfilters_onI q_def by fastforce
  qed
qed

lemma pretop_cl_nh:
  fixes q::"('a set set \<times> 'a) set" and X::"'a set"
  assumes A0:"pretop q X" 
  defines "Clq \<equiv> (\<lambda>A. {x \<in> X. \<exists>G \<in> pfilters_on (Pow X). (G, x) \<in> q \<and> A \<in> G})"
  defines "NClq \<equiv> (\<lambda>x. {V \<in> Pow X. x \<notin> Clq (X-V)})"
  shows "\<And>x. x \<in> X \<Longrightarrow> NClq x = \<Inter>{F. (F, x) \<in> q} "
proof-
  fix x assume A1:"x \<in> X"
  let ?N="\<Inter>{F. (F, x) \<in> q}"
  have B0:"\<And>U. \<lbrakk>U \<in> Pow X; U \<notin> ?N\<rbrakk> \<Longrightarrow> U \<notin> NClq x"
  proof-
    fix U assume A2:"U \<in> Pow X" and A3:"U \<notin> ?N"
    have B01:"is_pfilter (Pow X) ?N" using A0 A1 pfilters_onE by fastforce 
    obtain G where B02:"(G, x)\<in>q" and B03:"U \<notin> G" using local.A3 by auto
    have B04:"G \<in> pfilters_on (Pow X)"   using A0 B02 by auto
    have B05:"\<forall>g \<in> G. g \<inter> (X-U) \<noteq> {}"  by (meson A2 B03 B04 Pow_iff pfilters_on_iff pfilters_sets_comp3) 
    have B06:"(X-U) \<in> Pow X" by simp
    define H where "H \<equiv> {E \<in> Pow X. \<exists>g \<in> G. (X-U) \<inter> g \<subseteq> E}" 
    obtain B07:"is_pfilter (Pow X) H"  using finer_proper_filter[of X G "(X-U)"]  using B04 B05 H_def is_pfilterI1   by (simp add: pfilters_on_iff) 
    obtain B08:"G \<subseteq> H"  using finer_proper_filter[of X G "(X-U)"]  using B04 B05 H_def is_pfilterI1  by (simp add: pfilters_on_iff) 
    have B010:"(H, x) \<in> q"by (meson A0 A1 B02 B04 B07 B08 pfilters_onI) 
    have B011:"(X-U) \<in>H"    using B04 H_def is_pfilterE1 pfilters_on_iff sets_filter_top by fastforce
    have B012:"x \<in> Clq (X-U)"     using A0 B010 B011 Clq_def by auto
    show "U \<notin> NClq x" using B012 NClq_def by fastforce
  qed
  have B1:"\<And>U. \<lbrakk>U \<in> Pow X; U \<notin> NClq x\<rbrakk> \<Longrightarrow> U \<notin> ?N"
  proof-
    fix U assume A2:"U \<in> Pow X" and A3:"U \<notin> NClq x"
    then obtain B10:"x \<in> Clq (X-U)" using NClq_def by auto
    then obtain G where B11:"G \<in> pfilters_on (Pow X)" and  B12:"(G, x) \<in> q"  and B13:"(X-U) \<in> G"  using Clq_def by auto
    then show "U \<notin> ?N"  by (meson CollectI Inter_iff pfilter_sets_comp pfilters_onE) 
  qed
  show "NClq x = \<Inter>{F. (F, x) \<in> q}"
  proof
    show "NClq x \<subseteq> \<Inter>{F. (F, x) \<in> q}"  using B0 NClq_def by blast
    next
    show " \<Inter>{F. (F, x) \<in> q} \<subseteq> NClq x"by (smt (verit, ccfv_SIG) A0 A1 B1 Inf_lower lorc_mem_iff1 mem_Collect_eq subsetD subsetI)
  qed
qed

lemma pretop_cc_pretop:
  fixes q::"('a set set \<times> 'a) set" and X::"'a set"
  assumes A0:"pretop q X"
  defines "Clq \<equiv> (\<lambda>A. {x \<in> X. \<exists>G \<in> pfilters_on (Pow X). (G, x) \<in> q \<and> A \<in> G})"
  defines "NClq \<equiv> (\<lambda>x. {V \<in> Pow X. x \<notin> Clq (X-V)})"
  defines "qClq \<equiv> {(EF, x). x \<in> X \<and> EF \<in>  pfilters_on (Pow X) \<and> NClq x \<subseteq> EF}"
  shows "qClq = q"
proof
  show "qClq \<subseteq> q"
  proof
    fix z assume LA0:"z\<in>qClq" then obtain EF x where LA1:"z=(EF, x)"  by fastforce
    then obtain LA2:"(EF, x) \<in> qClq"  and LA3:"EF \<in>  pfilters_on (Pow X)" and LA4:"NClq x \<subseteq> EF" and LA5:"x \<in> X" using LA0 qClq_def by fastforce
    have LB0:"\<Inter>{F. (F, x) \<in> q}=NClq x" using pretop_cl_nh[of q X x] LA5 A0 NClq_def Clq_def by presburger
    then have LB1:" \<Inter>{F. (F, x) \<in> q}  \<subseteq> EF"  by (simp add: LA4) 
    have LB2:"\<Inter>{F. (F, x) \<in> q} \<in>  pfilters_on (Pow X)"   by (metis (mono_tags, lifting) A0 Ball_Collect LA5 case_prodD)
    have LB3:"(\<Inter>{F. (F, x) \<in> q}, x) \<in> q"   using A0 LA5 by fastforce
    have LB4:"(EF, x) \<in> q"  by (meson A0 LA3 LA5 LB1 LB2) 
    then show "z\<in> q" using LA1 by blast
  qed
  next
  show "q \<subseteq> qClq"
  proof
    fix z assume RA0:"z \<in> q" then obtain EF x where RA1:"z=(EF, x)"  by fastforce
    then obtain RA2:"(EF, x) \<in> q"  and RA3:"EF \<in>  pfilters_on (Pow X)" and RA4:"\<Inter>{F. (F, x) \<in> q} \<subseteq> EF" and RA5:"x \<in> X" using A0 RA1  using Inf_lower RA0 by auto
    have RB0:"\<Inter>{F. (F, x) \<in> q}=NClq x" using pretop_cl_nh[of q X x] RA5 A0 NClq_def Clq_def by presburger
    then have RB1:" \<Inter>{F. (F, x) \<in> q}  \<subseteq> EF" using RA4 by blast 
    then have RB2:"NClq x \<subseteq> EF"  by (simp add: RB0)
    then have RB3:"(EF, x) \<in> qClq"   using RA3 RA5 qClq_def by blast
    then show "z \<in> qClq"    by (simp add: RA1)
  qed  
qed

lemma cc_cl_mem:
  fixes Cl::"'a set \<Rightarrow> 'a set" and X::"'a set"
  assumes A0:"ccl X Cl"
  defines "NCl \<equiv> (\<lambda>x. {V \<in> Pow X. x \<notin> Cl (X-V)})"
  shows "\<And>A x. \<lbrakk>A \<in> Pow X; x \<in> X\<rbrakk> \<Longrightarrow> (x \<in> Cl A \<longleftrightarrow> (\<forall>V \<in> Pow X. V \<in> NCl x \<longrightarrow> V \<inter> A \<noteq> {})) "
proof-
  fix A x assume A1:"A \<in> Pow X" and A2:"x \<in> X"
  have B0:"\<not>(x \<in> Cl A) \<Longrightarrow> (\<not>(\<forall>V \<in> Pow X. V \<in> NCl x \<longrightarrow> V \<inter> A \<noteq> {}))"
  proof-
    assume "\<not>(x \<in> Cl A)" then obtain B0A0:"x \<notin> Cl A" by auto
    obtain B01:"(X-A) \<in> Pow X" and B02:"x \<notin> Cl(X-(X-A))"    using B0A0 double_diff local.A1 by fastforce
    then have B02:"(X-A) \<in> NCl x" by (simp add: NCl_def)
    also have B03:"A \<inter> (X-A) = {}"  by simp
    then show "(\<not>(\<forall>V \<in> Pow X. V \<in> NCl x \<longrightarrow> V \<inter> A \<noteq> {}))"  using calculation by blast
  qed
  have B1:" (\<not>(\<forall>V \<in> Pow X. V \<in> NCl x \<longrightarrow> V \<inter> A \<noteq> {})) \<Longrightarrow> \<not>(x \<in> Cl A) "
  proof-
      assume " \<not>(\<forall>V \<in> Pow X. V \<in> NCl x \<longrightarrow> V \<inter> A \<noteq> {})" 
      then obtain V where B1A0:"V \<in> Pow X" and B1A1:"V \<in> NCl x" and B1A2:" V \<inter> A = {}" by auto
      then obtain B10:"A \<subseteq> (X-V)"   using local.A1 by blast
      have B11:"Cl A \<subseteq> Cl (X-V)"  by (metis A0 B10 Diff_subset PowI local.A1 sup.orderE sup.orderI)
      also have B12:"x \<notin> Cl (X - V)"   using B1A1 NCl_def by blast
      then show "\<not>(x \<in> Cl A)"  using calculation by blast
  qed
  show "(x \<in> Cl A \<longleftrightarrow> (\<forall>V \<in> Pow X. V \<in> NCl x \<longrightarrow> V \<inter> A \<noteq> {}))"
  using B0 B1 by blast
qed
  
lemma cc_pretop_nhf:
  fixes Cl::"'a set \<Rightarrow> 'a set" and X::"'a set"
  assumes A0:"ccl X Cl"
  defines "NCl \<equiv> (\<lambda>x. {V \<in> Pow X. x \<notin> Cl (X-V)})"
  shows "\<And>x. x \<in> X \<Longrightarrow> is_pfilter (Pow X) (NCl x)"
proof-
  fix x assume A1:"x \<in> X"
  have B0:"{} \<notin> NCl x" using A0 NCl_def local.A1 by auto
  have B1:"is_filter (Pow X) (NCl x)"
  proof(rule is_filterI1)
    show "NCl x \<noteq> {}"  using A0 NCl_def by fastforce
    show "NCl x \<subseteq> Pow X"  using NCl_def by blast
    show "is_dir (NCl x) (\<lambda>x y. y \<subseteq> x)"
    proof(rule is_dirI1)
      fix a b assume " a \<in> NCl x " and "b \<in> NCl x "
      then have "x \<notin> Cl (X -(a \<inter> b))"  by (metis (no_types, lifting) A0 CollectD Diff_Int Diff_subset NCl_def Pow_iff Un_iff)
      then have "(a \<inter> b) \<in> NCl x"
      using NCl_def \<open>(a::'a::type set) \<in> (NCl::'a::type \<Rightarrow> 'a::type set set) (x::'a::type)\<close> by blast
      then show "\<exists>c::'a set\<in>NCl x. c \<subseteq> a \<and> c \<subseteq> b"
      by (metis Int_lower2 inf.cobounded1)
    qed
    show "is_ord_cl (Pow X) (NCl x) (\<subseteq>)"
    proof(rule is_ord_clI)
      fix a b assume "a \<in> NCl x" and "b \<in> Pow X" and  "a \<subseteq> b" 
      then show " b \<in> NCl x"  by (auto simp add:NCl_def,metis A0 Diff_Int Diff_subset PowI UnCI inf.absorb_iff2)
    qed
  qed
  then show "is_pfilter (Pow X) (NCl x)"
  using B0 is_pfilterI1 by auto
qed

lemma cc_pretop_cc:
  fixes Cl::"'a set \<Rightarrow> 'a set" and X::"'a set"
  assumes A0:"ccl X Cl"
  defines "NCl \<equiv> (\<lambda>x. {V \<in> Pow X. x \<notin> Cl (X-V)})"
  defines "qCl \<equiv> {(EF, x). x \<in> X \<and> EF \<in>  pfilters_on (Pow X) \<and> NCl x \<subseteq> EF}"
  defines "ClqCl \<equiv> (\<lambda>A. {x \<in> X. \<exists>G \<in> pfilters_on (Pow X). (G, x) \<in> qCl \<and> A \<in> G})"
  shows "\<And>A. A \<in> Pow X \<Longrightarrow> Cl A = ClqCl A"
proof-
  fix A assume A1:"A \<in> Pow X"
  have B0:"\<And>x. x \<in> X \<Longrightarrow> (x \<in> Cl A    \<longleftrightarrow> (\<forall>V \<in> Pow X. V \<in> NCl x \<longrightarrow> V \<inter> A \<noteq> {}))" using cc_cl_mem[of Cl X A]  using A0 NCl_def local.A1 by presburger
  have B1:"\<And>x. x \<in> X \<Longrightarrow> (x \<in> ClqCl A \<longleftrightarrow> (\<forall>V \<in> Pow X. V \<in> NCl x \<longrightarrow> V \<inter> A \<noteq> {}))"
    proof-
      fix x assume A2:"x \<in> X"
      have B10:"x \<in> ClqCl A \<Longrightarrow> (\<forall>V \<in> Pow X. V \<in> NCl x \<longrightarrow> V \<inter> A \<noteq> {})"
      proof-
        assume B10A0:"x \<in> ClqCl A"  then obtain G where B10A1:"G \<in> pfilters_on (Pow X)" and 
         B10A2:"(G, x) \<in> qCl" and B10A3:"A \<in> G" using ClqCl_def by blast
        then have B101:"NCl x \<subseteq> G "  using qCl_def by auto
        have B102:"\<And>V. V \<in> NCl x \<Longrightarrow> V \<inter> A \<noteq> {}" 
        proof-
          fix V assume B103:"V \<in> NCl x"
          obtain B104:"V \<in> G"  and B105:"A \<in> G" and B106:"is_pfilter (Pow X) G" using B101 B103 B10A1 B10A3 pfilters_on_iff by blast
          then show " V \<inter> A \<noteq> {}"   by (metis sets_pfilter_dir sets_pfilter_emp)
        qed
        then show "(\<forall>V \<in> Pow X. V \<in> NCl x \<longrightarrow> V \<inter> A \<noteq> {})"
        by blast
      qed
      have B11:"(\<forall>V \<in> Pow X. V \<in> NCl x \<longrightarrow> V \<inter> A \<noteq> {}) \<Longrightarrow> x \<in> ClqCl A "
      proof-
        assume B11A0:"(\<forall>V \<in> Pow X. V \<in> NCl x \<longrightarrow> V \<inter> A \<noteq> {})"  then obtain  B6:"\<forall>V \<in> NCl x. V \<inter>A  \<noteq> {}"   using NCl_def by blast 
        also have  B7:"is_pfilter (Pow X) (NCl x)" using cc_pretop_nhf[of Cl X x] A0 NCl_def local.A2 by blast 
        define H where "H \<equiv> {E \<in> Pow X. \<exists>V \<in> (NCl x). A \<inter> V \<subseteq> E}" 
        obtain B9:"is_pfilter (Pow X) H"  using finer_proper_filter[of X "NCl x" "A"] B6 A1 B7  using H_def by blast
        obtain B10:"H \<in>  pfilters_on (Pow X)"  using B9 CollectI is_pfilter_def  by (simp add: pfilters_on_iff) 
        obtain B11:"NCl x \<subseteq> H" using finer_proper_filter[of X "NCl x" "A"]  using B7 H_def calculation local.A1 by fastforce 
        then obtain B010:"(H, x) \<in> qCl" using B10 local.A2 qCl_def by blast 
        have  B011:"A \<in> H" using B7 H_def using A1 is_filterE1 is_pfilterE1 by fastforce
        then show "x \<in> ClqCl A"
        using B010 B10 ClqCl_def local.A2 by blast
     qed
    then show "(x \<in> ClqCl A \<longleftrightarrow> (\<forall>V \<in> Pow X. V \<in> NCl x \<longrightarrow> V \<inter> A \<noteq> {}))"
    using B10 by linarith
  qed
  obtain B2:"Cl A \<subseteq> X" and B3:"ClqCl A \<subseteq> X" using A0 ClqCl_def local.A1 by auto
  show "Cl A = ClqCl A"
  proof 
  show "Cl A \<subseteq> ClqCl A"
    proof
       fix x assume L:"x \<in> Cl A" then obtain L0:"x \<in> X"   using B2 by blast
       then obtain "(\<forall>V \<in> Pow X. V \<in> NCl x \<longrightarrow> V \<inter> A \<noteq> {})"  using B0 L by presburger
       show "x \<in> ClqCl A" using B0 B1 L L0 by blast
    qed
  next
 show "ClqCl A \<subseteq> Cl A"
    proof
       fix x assume R:"x \<in> ClqCl A" then obtain L0:"x \<in> X"  using B2 ClqCl_def by blast
       then obtain "(\<forall>V \<in> Pow X. V \<in> NCl x \<longrightarrow> V \<inter> A \<noteq> {})"  using B1 R by presburger
       show "x \<in> Cl A"
       using B0 B1 L0 R by presburger 
    qed
 qed
qed


definition preceq::"'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" (infixl "(\<preceq>)" 70)where "A \<preceq> B \<equiv> (\<forall>a. a \<in> A \<longrightarrow> (\<exists>b \<in> B. b \<subseteq> a))"



lemma preceq_refl:
  "reflp_on (Pow X) preceq"
  by(auto simp add:reflp_on_def preceq_def)


lemma preceq_trans:
  "transp_on (Pow X) preceq"
  by(simp add:transp_on_def preceq_def,meson subset_trans)

lemma subset_preceq:
  "A \<subseteq> B \<Longrightarrow> A \<preceq> B"
  by(auto simp add:preceq_def)

lemma preceq_upcl_subset:
  "\<lbrakk>A \<subseteq> Pow X; B \<subseteq> Pow X; is_ord_cl (Pow X)  B (\<subseteq>)\<rbrakk>  \<Longrightarrow> A \<preceq> B \<Longrightarrow> A \<subseteq> B"
  by(auto simp add:preceq_def,meson in_mono is_ord_clE)

lemma preceq_fip:
  "(\<And>a b. \<lbrakk>a \<in> B; b \<in> B\<rbrakk> \<Longrightarrow> a \<inter> b \<noteq> {}) \<Longrightarrow> A \<preceq> B \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> a \<inter> b \<noteq> {})"
proof-
  assume bfip:"(\<And>a b. \<lbrakk>a \<in> B; b \<in> B\<rbrakk> \<Longrightarrow> a \<inter> b \<noteq> {}) " and pr:"A \<preceq>  B" then show "(\<And>a b. \<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> a \<inter> b \<noteq> {})"
  proof-
    fix a b assume "a \<in> A" and "b \<in> A" then obtain c d where "c \<in> B" and "d \<in> B" and "c \<subseteq> a" and "d \<subseteq> b" using pr  by (meson preceq_def)
    then have "{} \<noteq>  c \<inter> d"   using bfip by blast
    also have "c \<inter> d \<subseteq> a \<inter> b"  using \<open>(c::'a::type set) \<subseteq> (a::'a::type set)\<close> \<open>(d::'a::type set) \<subseteq> (b::'a::type set)\<close> by blast  
    then show "a \<inter> b \<noteq> {}" using calculation by blast 
  qed
qed

definition mesh::"'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" (infixl "(#)" 70)
   where "A # B \<equiv> (\<forall>a. \<forall>b. a \<in> A \<longrightarrow> b \<in> B \<longrightarrow> a \<inter> b \<noteq> {})"

definition grill::"'a set set \<Rightarrow> 'a set set \<Rightarrow> 'a set set" 
  where "grill PX A \<equiv> {E \<in> PX. {E}#A}"

lemma mesh_singleE:
  "{b} # A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> b \<inter> a \<noteq> {})"
  by (simp add:  mesh_def)

lemma mesh_singleI:
  "(\<And>a. a \<in> A \<Longrightarrow> b \<inter> a  \<noteq> {}) \<Longrightarrow> {b} # A "
  by (simp add: mesh_def)

lemma mesh_sym:
  "A # B \<longleftrightarrow> B # A" 
  by (auto simp add: mesh_def)

lemma mesh_sub:
  assumes fam:"EF \<in> (Pow (Pow X))" and A1:"A \<in> Pow X" and A2:"B \<in> Pow X" and msh:"{A}#EF" and sub:"A \<subseteq> B"
  shows "{B}#EF"
proof(rule mesh_singleI)
  fix a assume "a \<in> EF" then obtain "{} \<noteq> a \<inter> A" using msh mesh_singleE by fastforce
  also have "a \<inter> A \<subseteq> a \<inter> B "  by (simp add: inf.coboundedI2 sub)
  then show "B \<inter> a \<noteq> {}"  using calculation by blast
qed


lemma meshI:
  "(\<And>a b. \<lbrakk>a \<in> A; b \<in> B\<rbrakk> \<Longrightarrow> a \<inter> b \<noteq> {}) \<Longrightarrow> A # B"
  by (simp add: mesh_def)

lemma mesh_single_iff:
  "({a} # B) \<longleftrightarrow> (\<forall>b \<in> B. a \<inter> b \<noteq> {})"
  using mesh_def by auto

lemma mesh_up:
  assumes fam:"EF \<in> (Pow (Pow X))" and A1:"A \<in> Pow X" and up:"is_ord_cl (Pow X) EF (\<subseteq>)"
  shows 1134:"\<not>(A \<in> EF \<and> {X-A}#EF)"  and
        1135:"\<not>(A \<in> EF) \<or> \<not>({X-A}#EF)" and
        1136:"A \<in> EF \<Longrightarrow> \<not>({X-A}#EF)" 
        using mesh_singleE by fastforce+

lemma pfilter_mesh1:
  assumes pfil1:"EF \<in> pfilters_on (Pow X)" and pfil2:"GF \<in> pfilters_on (Pow X)" and finer:"EF \<preceq> GF"
  shows "EF#GF"
proof(rule ccontr)
  assume c:"\<not>(EF#GF)" then obtain F G where fmem:"F \<in> EF" and gmem:"G \<in> GF" and dis:"F \<inter> G={}" by (meson meshI)
  from  pfil1 pfil2 obtain "is_pfilter (Pow X) EF" and  pfil:"is_pfilter (Pow X) GF"  using pfilters_onE by blast 
  then obtain "EF \<subseteq> Pow X" and  "GF \<subseteq> Pow X"  and  "is_ord_cl (Pow X) GF (\<subseteq>)"  by (simp add: sets_pfilter2_upc sets_pfilter_sub)  
  then have "EF \<subseteq> GF" using preceq_upcl_subset[of EF X GF] finer by auto 
  also have "F \<in> EF" using fmem by auto
  then obtain "F \<in> GF" and "G \<in> GF" and "F \<inter> G \<in> GF"  using pfil calculation gmem sets_pfilter_dir by blast
  then obtain "{} \<in> GF" using dis  by auto
  then show False using pfil sets_pfilter_emp by blast
qed

lemma pfilter_mesh2:
  assumes pfil1:"EF \<in> pfilters_on (Pow X)" and pfil2:"GF \<in> pfilters_on (Pow X)" and finer:"EF \<subseteq> GF"
  shows "EF#GF" using assms subset_preceq[of EF GF] pfilter_mesh1[of EF X GF] by auto


lemma upcl_meet:
  assumes fam:"A \<in> Pow( Pow X)" and upcl:"is_ord_cl (Pow X) A (\<subseteq>)" and bsub:"b \<in> Pow X" and notin:"b \<notin> A" and ain:"a \<in> A "
  shows "a \<inter> (X-b) \<noteq>{}"
proof(rule ccontr)
  assume  "\<not> (a \<inter> (X-b) \<noteq> {})" then obtain "a \<inter> (X-b) = {}" by auto 
  then have "a \<subseteq> b" using fam ain by fastforce 
  then have "b \<in> A"  by (meson ain bsub is_ord_clE upcl) 
  then show False using notin by auto
qed


lemma isotone_mesh:
  assumes fam:"A \<in> Pow(Pow X)" and upcl:"is_ord_cl (Pow X) A (\<subseteq>)" and st:"E \<in> Pow X"  
  shows 11371:"E \<notin> A \<longleftrightarrow> {X-E}#A" and 11372:"E \<in> A \<longleftrightarrow> \<not> ({X-E}#A)"
proof-
  show "E \<notin> A \<longleftrightarrow> {X-E}#A"
  proof
    assume ena:"E \<notin> A"  show "{X-E}#A" 
    proof(rule mesh_singleI)
      fix a assume ana:"a \<in> A" show "(X - E) \<inter> a \<noteq> {}" using fam upcl st ena  ana upcl_meet[of A X E a] by auto
    qed
   next
    assume cms:"{X-E}#A" then show "E \<notin> A"  using "1136"  fam st upcl by auto 
  qed
  then show "E \<in> A \<longleftrightarrow> \<not> ({X-E}#A)" by auto
qed

lemma notin_mesh:
  "\<lbrakk>A \<in> Pow (Pow X); b \<in> Pow X; {X-b}#A\<rbrakk> \<Longrightarrow> b \<notin> A"
  using mesh_singleE by fastforce

lemma grill_space[iff]:
  "grill (Pow X) A \<subseteq> Pow X"
  unfolding grill_def by blast
  

lemma mesh_iff_grill1:
  assumes fam1:"A \<in> Pow( Pow X)" and  fam2:"B \<in> Pow (Pow X)"
  shows "A#B \<longleftrightarrow> A \<subseteq> grill (Pow X) B"
proof-
  have "A#B \<longleftrightarrow> (\<forall>a \<in> A. \<forall>b \<in> B. a \<inter> b \<noteq> {})"   using mesh_def by auto 
  also have "... \<longleftrightarrow> (\<forall>a \<in> A. {a}#B)"  by (simp add: mesh_single_iff)
  also have "... \<longleftrightarrow> (\<forall>a \<in> A. a \<in> grill (Pow X) B)" using fam1 grill_def by fastforce
  also have "... \<longleftrightarrow>  A \<subseteq> grill (Pow X) B" by blast
  finally show ?thesis by simp
qed


lemma mesh_iff_grill2:
  assumes fam1:"A \<in> Pow( Pow X)" and  fam2:"B \<in> Pow (Pow X)"
  shows "A#B \<longleftrightarrow> B \<subseteq> grill (Pow X) A"   using fam1 fam2 mesh_sym[of A B] mesh_iff_grill1[of B X A]  by presburger

lemma disj_sub:
  "\<lbrakk>a \<in> Pow X; E \<in> Pow X\<rbrakk> \<Longrightarrow> (X-E) \<inter> a = {} \<longleftrightarrow>  a \<subseteq> E" by blast


lemma grill_reform1:
  assumes fam:"A \<in> Pow( Pow X)" and upcl:"is_ord_cl (Pow X) A (\<subseteq>)" and st:"E \<in> Pow X"  
  shows 11391:"(X-E) \<notin> grill (Pow X) A \<longleftrightarrow> E \<in> A " and 
        11392:"(X-E) \<in> grill (Pow X) A \<longleftrightarrow> E \<notin> A" 
proof-
  show "(X-E) \<notin> grill (Pow X) A \<longleftrightarrow> E \<in> A " 
  proof-
    have "(X-E) \<notin> grill (Pow X) A \<longleftrightarrow> \<not>({X-E}#A)"   by (simp add: grill_def)
    then show ?thesis using "11372" fam st upcl by blast 
  qed
  then show "(X-E) \<in> grill (Pow X) A \<longleftrightarrow> E \<notin> A" by auto
qed


lemma grill_reform2:
  assumes fam:"A \<in> Pow( Pow X)" and upcl:"is_ord_cl (Pow X) A (\<subseteq>)" and st:"E \<in> Pow X"  
  shows 11393:"E \<in> grill (Pow X) A \<longleftrightarrow> (X-E) \<notin> A" and
        11394:"E \<notin> grill (Pow X) A \<longleftrightarrow> (X-E) \<in> A"
proof-
  obtain st2:"(X-E) \<in> Pow X" by simp
  then show "E \<in> grill (Pow X) A \<longleftrightarrow> (X-E) \<notin> A" using "11392"[of A X "X-E"] fam upcl st by (simp add: double_diff) 
  then show "E \<notin> grill (Pow X) A \<longleftrightarrow> (X-E) \<in> A" by simp
qed

lemma grill_reform3:
  assumes fam:"A \<in> Pow( Pow X)" and upcl:"is_ord_cl (Pow X) A (\<subseteq>)" 
  shows 11395:"grill (Pow X) A = {E \<in> Pow X. (X-E) \<notin> A}"
  using assms grill_def[of "Pow X" A] "11393"[of A X] by auto

lemma grill_anti1:
  "\<lbrakk>A \<in> Pow (Pow X); B \<in> Pow (Pow X); A \<subseteq> B\<rbrakk> \<Longrightarrow> grill (Pow X) B \<subseteq> grill (Pow X) A"
  by (simp add: grill_def mesh_single_iff subset_eq)
  
lemma grill_anti2:
  assumes anx:"A \<in> Pow (Pow X)" and bnx:"B \<in> Pow (Pow X)" and
          up1:"is_ord_cl (Pow X) A (\<subseteq>)" and up2:"is_ord_cl (Pow X) B (\<subseteq>)" and 
          sub:"grill (Pow X) B \<subseteq> grill (Pow X) A"
  shows "A \<subseteq> B"
proof
  fix a assume a0:"a \<in> A"  then obtain a1:"a \<in> Pow X" using anx by blast
  then obtain "(X-a) \<notin>  grill (Pow X) A" using "11392"[of A X a] a0 anx up1 by blast
  then obtain "(X-a) \<notin>  grill (Pow X) B" using sub by blast
  then show "a \<in> B" using "11391"[of B X a] bnx up2 a1  by fastforce
qed

lemma grill_upcl:
  assumes anx:"A \<in> Pow (Pow X)" shows "is_ord_cl (Pow X) (grill (Pow X) A) (\<subseteq>)"
proof(rule is_ord_clI)
  fix a b assume a0:"a \<in> grill (Pow X) A"  and b0:"b \<in> Pow X" and ab:"a \<subseteq> b" 
  then show "b \<in> grill (Pow X) A" using mesh_sub anx
  by (metis (no_types, lifting) grill_def mem_Collect_eq)
qed

lemma double_grill1:
  assumes anx:"A \<in> (Pow (Pow X))" 
  shows "grill (Pow X) (grill (Pow X) A) = {E \<in> Pow X. \<exists>a \<in> A. a \<subseteq>E}"
proof-
  let ?G1="grill (Pow X) A" let ?G2="grill (Pow X) ?G1" let ?R="{E \<in> Pow X. \<exists>a \<in> A. a \<subseteq> E}"
  have up1:"is_ord_cl (Pow X) ?G1 (\<subseteq>)" using grill_upcl  using assms by blast
  have gnx:"?G1 \<in> Pow (Pow X)"  by simp
  have "\<And>E. E \<in> Pow X \<Longrightarrow> E \<in> ?G2 \<longleftrightarrow> E \<in> ?R"
  proof-
    fix E assume enx:"E \<in> Pow X"
    have "E \<in> ?G2 \<longleftrightarrow> (X-E) \<notin> ?G1" using "11393"[of ?G1 X E] gnx up1 enx  by fastforce
    also have "... \<longleftrightarrow> \<not>({X-E}#A)"  by (simp add: grill_def)
    also have "... \<longleftrightarrow> (\<exists>a \<in> A. a \<subseteq> E)" using anx mesh_single_iff by fastforce
    also have "... \<longleftrightarrow> E \<in> ?R" using enx by blast
    finally show "E \<in> ?G2 \<longleftrightarrow> E \<in> ?R"
    by blast
  qed
  then show ?thesis using grill_def Collect_cong mem_Collect_eq
  by (smt (verit))
qed

lemma grill_of_filter:
  assumes A0:"\<F> \<in> pfilters_on (Pow X)"
  shows "\<F> \<subseteq> grill (Pow X) \<F>"
proof
  fix F assume "F \<in> \<F>" then show "F \<in> grill (Pow X) \<F>" unfolding grill_def mesh_def
  using assms mesh_def pfilter_mesh2 pfilters_onE sets_pfilter_sub by fastforce
qed 


lemma double_grill2:
  assumes anx:"A \<in> (Pow (Pow X))" 
  shows "grill (Pow X) (grill (Pow X) A) = A \<longleftrightarrow> is_ord_cl (Pow X) A (\<subseteq>)" (is "?L \<longleftrightarrow> ?R")
proof-
  obtain f1: "grill (Pow X) (grill (Pow X) A) \<in> Pow( Pow X)"  and  f2:"grill (Pow X) A \<in> Pow (Pow X)"  by simp
   show ?thesis
  proof
    assume ?L then show ?R using f2 grill_upcl[of "grill (Pow X) A"  X]   by auto
  next
    assume ?R then show ?L
    by (meson PowD Pow_top assms f1 f2 grill_anti2 grill_upcl mesh_iff_grill1 mesh_iff_grill2 subset_antisym)
  qed
qed


lemma double_grill21:
  assumes anx:"A \<in> (Pow (Pow X))"  and upcl:"is_ord_cl (Pow X) A (\<subseteq>)"
  shows "grill (Pow X) (grill (Pow X) A) = A" 
  using assms double_grill2 by blast 

lemma grill_union_inter1:
  assumes A0:"\<AA> \<in> Pow (Pow (Pow X))" and A1:"\<AA> \<noteq> {}" and A2:"\<And>\<A>. \<A> \<in> \<AA> \<Longrightarrow> is_ord_cl (Pow X) \<A> (\<subseteq>)"
  shows "grill (Pow X) (\<Inter>\<AA>) = \<Union>{grill (Pow X) \<A>|\<A>. \<A> \<in> \<AA>}" (is "?L = ?R")
proof-
  let ?I ="\<Inter>\<AA>"
  have B0:"?I \<in> (Pow (Pow X))" using A0 A1 by blast
  have B1:"?R \<subseteq> ?L" 
  proof-
    have B10:"\<And>\<A>. \<A> \<in> \<AA> \<Longrightarrow> grill (Pow X) \<A> \<subseteq> grill (Pow X) ?I"
    proof-
      fix \<A> assume A3:"\<A> \<in> \<AA>" 
      then obtain B100:"\<A> \<in> Pow (Pow X)" and B101:"is_ord_cl (Pow X) \<A> (\<subseteq>)"  and B103:"?I \<subseteq> \<A>"  using A0 A2 by auto
      then show "grill (Pow X) \<A> \<subseteq> grill (Pow X) ?I" by (simp add: grill_anti1)
    qed
    then show ?thesis
    by blast
  qed
  have B2:"\<And>A. \<lbrakk>A \<in> Pow X; A \<notin> ?R\<rbrakk> \<Longrightarrow> A \<notin> ?L "
  proof-
    fix A assume B2A0:"A \<in> Pow X" and B2A1:"A \<notin> ?R"
    then obtain B22:"\<And>\<A>. \<A> \<in> \<AA> \<Longrightarrow> A \<notin> grill (Pow X) \<A>" by blast
    then obtain B23:"\<And>\<A>. \<A> \<in>\<AA> \<Longrightarrow> (\<exists>B. B \<in> \<A> \<and> B \<inter> A = {})" unfolding grill_def mesh_def using  B2A0 by fastforce
    define f where "f \<equiv> (\<lambda>\<A>. SOME B. B \<in> \<A> \<and> B \<inter> A = {})"
    have B24:"\<And>\<A>. \<A> \<in> \<AA> \<Longrightarrow> (f \<A>) \<in> \<A>  \<and> (f \<A>) \<inter> A = {}"
    proof-
      fix \<A> assume B24A0:"\<A> \<in> \<AA>" then obtain "(\<exists>B. B \<in> \<A> \<and> B \<inter> A = {})" using B23 B24A0 by auto
      then show "(f \<A>) \<in> \<A>  \<and> (f \<A>) \<inter> A = {}" unfolding f_def using someI_ex[of "\<lambda>B. B \<in> \<A> \<and> B \<inter> A = {}"] by blast
    qed
    have B25:"(\<Union>{f \<A> |\<A> . \<A>  \<in> \<AA>}) \<in> Pow X" using B24 A0 by blast
    have B26:"\<And>\<A>. \<A> \<in> \<AA> \<Longrightarrow> (\<Union>{f \<A> |\<A> . \<A>  \<in> \<AA>}) \<in> \<A>"
    proof-
      fix \<A> assume B26A0:"\<A> \<in> \<AA>"  
      then obtain B260:"is_ord_cl (Pow X) \<A> (\<subseteq>)"  using A2 by auto
      also obtain B261:"f \<A> \<in> \<A>" and B262:"f \<A> \<subseteq> (\<Union>{f \<A> |\<A> . \<A>  \<in> \<AA>})"   using B24 B26A0 by auto  
      then show "(\<Union>{f \<A> |\<A> . \<A>  \<in> \<AA>}) \<in> \<A>"  using B25 calculation is_ord_clE by fastforce
    qed
    then obtain B27:"(\<Union>{f \<A> |\<A> . \<A>  \<in> \<AA>}) \<in> (\<Inter>\<AA>)" and B28:"A \<inter> (\<Union>{f \<A> |\<A> . \<A>  \<in> \<AA>}) = {}"  using B24 by blast
    then show "A \<notin> ?L" unfolding grill_def mesh_def by(auto)
  qed
  have B3:"?R \<subseteq> Pow X"   using grill_space by blast
  from B2 B3 have B4:"?L \<subseteq> ?R" unfolding grill_def mesh_def by blast
  from B1 B4 show ?thesis by blast
qed

lemma grill_union_inter:
  assumes A0:"\<AA> \<in> Pow (Pow (Pow X))" and A1:"\<AA> \<noteq> {}"
  shows "grill (Pow X) (\<Union>\<AA>) = \<Inter>{grill (Pow X) \<A>|\<A>. \<A> \<in> \<AA>}"
  unfolding grill_def using assms apply(auto, simp add: mesh_single_iff)
  unfolding mesh_def using assms apply(auto) by(blast)

lemma ideals_filter_grill:
  assumes A0:"\<G> \<in> (Pow (Pow X))"  and A1:"\<G> \<noteq> {}" and A2:"{} \<notin> \<G>"
  shows "(\<exists>\<F> \<in> pfilters_on (Pow X). \<G> = grill (Pow X) \<F>) \<longleftrightarrow>   (\<forall>A \<in> Pow X. \<forall>B \<in> Pow X. A \<union> B \<in> \<G> \<longrightarrow> A \<in> \<G> \<or> B \<in> \<G>) \<and> is_ord_cl (Pow X) \<G> (\<subseteq>)"
  (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L then obtain F where B0:"F \<in> pfilters_on (Pow X)" and B1:" \<G> = grill (Pow X) F" by auto
  from B0 have B2:"F \<in> Pow (Pow X)"   by (simp add: pfilters_onE sets_pfilter_sub)
  from B1 B2 obtain B3:" is_ord_cl (Pow X) \<G> (\<subseteq>)" using grill_upcl[of F X] by blast
  have B4:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X; A \<notin> \<G>; B \<notin> \<G>\<rbrakk> \<Longrightarrow> A \<union> B \<notin> \<G>"
  proof-
    fix A B assume B4A0:"A \<in> Pow X" and B4A1:"B \<in> Pow X" and B4A2:"A \<notin> \<G>" and B4A3:"B \<notin> \<G>"
    then obtain B40:"A \<notin> grill (Pow X) F" and B41:"B \<notin> grill (Pow X) F" using B1 by auto
    then obtain Fa Fb where B42:"Fa \<in> F" and B43:"Fb \<in> F" and B44:"Fa \<inter> A = {}" and B45:"Fb \<inter> B = {}"
      by (metis "11393" B0 B2 B4A0 B4A1 Diff_disjoint Int_commute pfilters_on_iff sets_pfilter2_upc)
    then obtain "Fa \<inter> Fb \<in> F" and "(Fa \<inter> Fb) \<inter> (A \<union> B) = {}"
      by (metis B0 boolean_algebra.de_Morgan_disj inf_mono inf_shunt pfilters_onE sets_pfilter_dir)
    then obtain "A \<union> B \<notin> grill (Pow X) F" 
       by (metis A0 B1 B2 Int_absorb inf.absorb_iff2 mesh_def mesh_iff_grill2)
    then show "A \<union> B \<notin> \<G>" using B1 by auto
  qed
  then have B5:"(\<forall>A \<in> Pow X. \<forall>B \<in> Pow X. A \<union> B \<in> \<G> \<longrightarrow> A \<in> \<G> \<or> B \<in> \<G>)" by blast
  then show ?R  using B3 by blast
next
  assume R:?R then obtain B0:"\<G> = grill (Pow X) (grill (Pow X) \<G>)" using A0 double_grill21[of \<G> X] by auto
  let ?F="grill (Pow X) \<G>"
  have B1:"is_pfilter (Pow X) ?F"
  proof(rule is_pfilterI1)
    show "is_filter (Pow X) ?F"
    proof(rule is_filterI1)
      show "?F \<noteq> {}"  by (metis "11391" A0 A2 Pow_bottom R empty_iff)
      show "?F \<subseteq> Pow X" by simp
      show "is_dir ?F (\<lambda>x y. y \<subseteq> x)"
      proof(rule is_dirI1)
        fix a b assume amem:"a \<in> ?F" and bmem:"b \<in> ?F" 
        then obtain B2:"is_ord_cl (Pow X) ?F (\<subseteq>)" and B3:"a \<in> Pow X"   and B4:"b \<in> Pow X" by (meson A0 grill_space grill_upcl subset_eq)  
        then obtain B5:"(X-a) \<notin> \<G>" and B6:"(X-b) \<notin> \<G>"   by (meson "11393" A0 R amem bmem) 
        then obtain B7:"(X-a) \<union> (X-b) \<notin> \<G>"   using R by blast
        then obtain B8:"(X-((X-a) \<union> (X-b))) \<in> grill (Pow X) \<G>" by (meson "11391" A0 Diff_subset PowI R le_supI)
        then obtain B9:"a \<inter> b \<in> ?F"  by (metis B3 B4 Diff_Diff_Int Diff_Un PowD inf.absorb2)
        then show "\<exists>c \<in> ?F. c \<subseteq> a \<and> c \<subseteq> b"   by (meson Int_lower2 inf_le1)
      qed
      show "is_ord_cl (Pow X) ?F (\<subseteq>)" using A0 grill_upcl by blast
  qed
  show "?F \<noteq> (Pow X)"
  by (metis A0 A1 Pow_bottom R bot.extremum_uniqueI grill_anti2 grill_space is_ord_cl_empty)
  qed
  then show ?L using B0 pfilters_on_iff by blast
qed

lemma maybe_tho:
  assumes A0:"is_lattice X" and A1:"is_greatest X top" and A2:"is_filter X F"
  shows "F = Sup (filters_on X) {(lorc f X)|f. f \<in>F}"
proof-
  from A0 A1 obtain B0:"is_clattice (filters_on X)" and B1:"compactly_generated (filters_on X)" 
    using lattice_filters_complete[of X top] filters_on_lattice_compactgen[of X top] lattD1 by blast
  have B2:"F= Sup (filters_on X) {k \<in> compact_elements (filters_on X). k \<le> F}" 
    using compact_dense[of "filters_on X" F]  using A2 B0 B1 filters_on_iff by auto
  have B3:"\<And>f. f \<in> compact_elements (filters_on X) \<Longrightarrow> f \<in> {lorc x X|x. x \<in> X}"
  proof-
    fix f assume "f \<in> compact_elements (filters_on X) " 
      then obtain "is_filter X f" unfolding compact_elements_def    by (simp add: compact_element_memD2 compact_elements_def filters_onE) 
    then obtain x where "lorc x X = f"  using A0 A1 principal_filters_compact[of X top f]
    using \<open>(f::'a::order set) \<in> compact_elements (filters_on (X::'a::order set))\<close> compact_elements_mem_iff1 filters_on_iff lattD1 by blast
    then show  "f \<in> {lorc x X|x. x \<in> X}"
    using A0 A1 \<open>(f::'a::order set) \<in> compact_elements (filters_on (X::'a::order set))\<close> \<open>Posets27.is_filter (X::'a::order set) (f::'a::order set)\<close> compact_element_memD1 filters_onI lattD1 principal_filters_compact by fastforce
  qed
  have B4:"\<And>f.  f \<in> {lorc x X|x. x \<in> X} \<Longrightarrow> f \<in> compact_elements (filters_on X) "
     using A0 A1 principal_filters_compact[of X top]  compact_elements_mem_iff1 lorc_filter2 by fastforce
  have B5:" {lorc x X|x. x \<in> X} =  compact_elements (filters_on X)"  using B3 B4 by blast
  have B7:"\<And>z. \<lbrakk>z \<in> X; lorc z X \<le> F\<rbrakk> \<Longrightarrow> z \<in> F" by (simp add: in_mono lorc_memI1)  
  have B8:"\<And>z. \<lbrakk>z \<in> X; z \<in> F\<rbrakk> \<Longrightarrow> lorc z X \<le> F "  using A2 is_filterE1 is_ord_clE lorcD12 lorc_subset1 by fastforce
  have B9:"{lorc x X|x. x \<in> X}  \<subseteq> Pow X" using lorcD1 by blast
  have B10:"{k \<in>{lorc x X|x. x \<in> X}. k \<le> F}  \<subseteq> Pow X"   using B9 by blast
  have B11:"{k \<in>{lorc x X|x. x \<in> X}. k \<le> F} \<subseteq> {lorc x X|x. x \<in> F}" using  B7 B8 B9 B10 by(auto) 
  have B12:"F \<subseteq> X"  by (simp add: A2 is_filterE1)
  have B13:" {lorc x X|x. x \<in> F} \<subseteq> {k \<in>{lorc x X|x. x \<in> X}. k \<le> F} " using B7 B8 B9 B10 B12  by fastforce
  have B14:"{lorc x X|x. x \<in> F} = {k \<in>{lorc x X|x. x \<in> X}. k \<le> F}" using B11 B13 by blast
  have B15:"F= Sup (filters_on X) {k \<in>{lorc x X|x. x \<in> X}. k \<le> F}"  using B2 B5 by presburger
  also have B16:"... = Sup (filters_on X)  {(lorc f X)|f. f \<in>F}" using B14 by auto
  finally show ?thesis
  by simp
qed

lemma filter_on_set_ne:
  "\<F> \<in> pfilters_on (Pow X) \<Longrightarrow> {} \<notin> \<F>"
  using pfilters_onE sets_pfilter_emp by blast

lemma filter_mem_mesh:
  "\<lbrakk>\<F> \<in> pfilters_on (Pow X); A \<in> \<F>\<rbrakk> \<Longrightarrow> {A}#\<F>"
  unfolding mesh_def  using filter_on_set_ne pfilters_onE sets_pfilter_dir by fastforce

  
definition ClN::"('a \<times> 'a set) set \<Rightarrow> 'a set \<Rightarrow> ('a set \<times> 'a) set" where
  "ClN N X \<equiv> {(B, x). B \<in> Pow X \<and> x \<in> X \<and> {B}#( N``{x})}"

definition NCl:: "('a set \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a set) set" where 
  "NCl Cl X \<equiv> {(x, A). A \<in> Pow X \<and> x \<in> X \<and> {A}#(converse Cl)``{x}}"

definition NAdh::"('a set set \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a set) set" where
  "NAdh Adh X \<equiv> {(x, A). A \<in> Pow X \<and> x \<in> X \<and> (\<forall>\<E> \<in> pfilters_on (Pow X). (\<E>, x) \<in> Adh \<longrightarrow> {A}#\<E>)}"

definition AdhN::"('a \<times> 'a set) set \<Rightarrow> 'a set \<Rightarrow> ('a set set \<times> 'a) set" where
  "AdhN N X \<equiv> {(\<E>, x). \<E> \<in> pfilters_on (Pow X) \<and> x \<in> X \<and> (\<forall>A. A \<in>  Pow X \<and> (x, A) \<in> N \<longrightarrow> {A}#\<E>)}"

definition AdhCl::"('a set \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> ('a set set \<times> 'a) set" where
  "AdhCl Cl X \<equiv> {(\<F>, x). \<F> \<in>  pfilters_on (Pow X) \<and> x \<in> X \<and> (\<forall>A. A \<in>  Pow X \<and> A \<in> \<F> \<longrightarrow> (A, x) \<in> Cl)}"

definition ClAdh::"('a set set \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow>('a set \<times> 'a) set " where
  "ClAdh Adh X \<equiv> {(A, x). A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F> \<in> pfilters_on (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> Adh)}"

definition NLim::"('a set set \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a set) set" where
  "NLim Lim X \<equiv> {(x, A). A \<in> Pow X \<and> x \<in> X \<and> (\<forall>\<E>. \<E> \<in> pfilters_on (Pow X) \<and> (\<E>, x) \<in> Lim \<longrightarrow>A \<in> \<E>)}"

definition LimN::"('a \<times> 'a set) set \<Rightarrow> 'a set \<Rightarrow> ('a set set \<times> 'a) set" where
  "LimN N X \<equiv> {(\<E>, x). \<E> \<in> pfilters_on( Pow X) \<and> x \<in> X \<and> (\<forall>A \<in>  Pow X. (x, A) \<in> N \<longrightarrow> A \<in> \<E>)}"

definition LimCl::"('a set \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> ('a set set \<times> 'a) set" where
  "LimCl Cl X \<equiv> {(\<F>, x). \<F> \<in>  pfilters_on (Pow X) \<and> x \<in> X \<and> (\<forall>A. A \<in>  Pow X \<and> {A}#\<F> \<longrightarrow> (A, x) \<in> Cl)}"

definition ClLim::"('a set set \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow>('a set \<times> 'a) set " where
  "ClLim Lim X \<equiv> {(A, x). A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F> \<in> pfilters_on (Pow X). {A} # \<F> \<and> (\<F>, x) \<in> Lim)}"

definition AdhLim::"('a set set \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow>('a set set \<times> 'a) set" where
  "AdhLim Lim X \<equiv> {(\<F>, x). \<F> \<in> (pfilters_on (Pow X))\<and>  x \<in> X \<and> (\<exists>\<G> \<in> pfilters_on (Pow X). \<G> # \<F> \<and> (\<G>, x) \<in> Lim)}"

definition LimAdh::"('a set set \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow>('a set set \<times> 'a) set" where
  "LimAdh Adh X \<equiv> {(\<F>, x). \<F> \<in> (pfilters_on (Pow X))\<and>  x \<in> X \<and> (\<forall>\<G>. \<G> \<in> pfilters_on (Pow X) \<and> \<G> # \<F>  \<longrightarrow> (\<G>, x) \<in> Adh)}"



lemma Cl_to_Nhoods1:
  assumes A0:"x \<in> X" 
  shows "(NCl Cl X)``{x} = (grill (Pow X) ((converse Cl)``{x}))"
  unfolding NCl_def grill_def using assms by auto

lemma Cl_to_Nhoods2:
    assumes A0:"x \<in> X" 
    shows "(converse (ClN N X))``{x} = grill (Pow X) (N``{x})"
    unfolding ClN_def grill_def using assms by auto
  
lemma Nhoods_to_Adh0:
  assumes A0:"\<E> \<in> pfilters_on (Pow X)" and A1:"x \<in> X" and A2:"\<And>x V. (x, V) \<in> N \<Longrightarrow> x \<in> X \<and> V \<in> Pow X"
  shows "x \<in> (AdhN N X)``{\<E>} \<longleftrightarrow> (N``{x})#\<E> " 
  unfolding AdhN_def mesh_def using assms by auto

lemma Nhoods_to_Adh1a: 
  assumes A0:"x \<in> X" and A1:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in>pfilters_on (Pow X)" and A2:"Adh \<noteq> {}"
  shows "(NAdh Adh X)``{x} \<subseteq> \<Inter>{grill (Pow X) \<E>|\<E>. (\<E>, x) \<in> Adh}"
  unfolding NAdh_def grill_def mesh_def using assms by blast
  
lemma Nhoods_to_Adh1b: 
  assumes A0:"x \<in> X" and A1:"A \<in> Pow X" and A2:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in> pfilters_on (Pow X)" and A3:"Adh \<noteq> {}" and
          A4:"(x, A) \<in> (NAdh Adh X)"
  shows " (\<And>\<E>. \<lbrakk>\<E> \<in> Pow (Pow X); (\<E>, x) \<in> Adh\<rbrakk> \<Longrightarrow> {A}#\<E>)"
  unfolding NAdh_def mesh_def using assms by(auto,metis (no_types, lifting) A2 CollectD NAdh_def case_prodD mesh_singleE) 

  
lemma Nhoods_to_Adh1c: 
  assumes A0:"x \<in> X" and A1:"A \<in> Pow X" and A2:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in> Pow (Pow X)" and A3:"Adh \<noteq> {}" and
          A4:"(\<And>\<E>. \<lbrakk>\<E> \<in> Pow (Pow X); (\<E>, x) \<in> Adh\<rbrakk> \<Longrightarrow> {A}#\<E>)"
  shows "(x, A) \<in> (NAdh Adh X)"
  unfolding NAdh_def mesh_def using assms by(simp add:mesh_def)

lemma Nhoods_to_Adh1d: 
  assumes A0:"x \<in> X" and A1:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in> pfilters_on (Pow X)" and A2:"Adh \<noteq> {}"
  shows "\<And>E.  \<lbrakk>E \<in> Pow X; E \<notin> (NAdh Adh X)``{x}\<rbrakk> \<Longrightarrow> E \<notin>  \<Inter>{grill (Pow X) \<E>|\<E>. (\<E>, x) \<in> Adh}"
  unfolding NAdh_def grill_def mesh_def using assms by(auto, smt (verit, ccfv_SIG) mem_Collect_eq)

lemma Nhoods_to_Adh1: 
  assumes A0:"x \<in> X" and A1:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in>pfilters_on(Pow X)" and A2:"Adh \<noteq> {}" and A3:"(converse Adh)``{x} \<noteq> {}"
  shows "(NAdh Adh X)``{x} = \<Inter>{grill (Pow X) \<E>|\<E>. (\<E>, x) \<in> Adh}" (is "?L = ?R")
proof
  show "?L \<subseteq> ?R" using assms Nhoods_to_Adh1a[of x X Adh] by auto
next
  show "?R \<subseteq> ?L"
  proof-
    from assms obtain B0:"{grill (Pow X) \<E>|\<E>. (\<E>, x) \<in> Adh} \<noteq> {}" by blast
    from assms B0 grill_space obtain B1:"{grill (Pow X) \<E>|\<E>. (\<E>, x) \<in> Adh} \<subseteq> (Pow (Pow X))"  by blast
    then obtain B2:"(\<Inter>{grill (Pow X) \<E>|\<E>. (\<E>, x) \<in> Adh}) \<subseteq> (Pow X)" using B0 by auto
    also obtain B3:"(NAdh Adh X)``{x} \<subseteq> Pow X" unfolding NAdh_def using assms by auto
    then show ?thesis using B2 Nhoods_to_Adh1d[of x X Adh] assms   by (meson subset_eq)
  qed
qed
 
lemma Nhoods_to_Lim0:
  assumes A0:"\<E> \<in>pfilters_on (Pow X)" and A1:"x \<in> X" and A2:"\<And>x V. (x, V) \<in> N \<Longrightarrow> x \<in> X \<and> V \<in> Pow X"
  shows "x \<in> (LimN N X)``{\<E>} \<longleftrightarrow> (N``{x}) \<subseteq> \<E> " 
  unfolding LimN_def mesh_def using assms by auto


lemma Nhoods_to_Lim1: 
  assumes A0:"x \<in> X" and A1:"\<And>x \<E>. (\<E>, x) \<in>Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> pfilters_on (Pow X)" and A2:"Lim \<noteq> {}" and A3:"(converse Lim)``{x} \<noteq> {}"
  shows "(NLim Lim X)``{x} = (\<Inter>{\<E>. (\<E>, x) \<in> Lim})" (is "?L = ?R")
proof 
  show "?L \<subseteq> ?R" unfolding NLim_def using assms by(auto)
next
  show "?R \<subseteq> ?L" 
  proof-
    have B0:"\<And>A. \<lbrakk>A \<in> Pow X; A \<notin> ?L\<rbrakk> \<Longrightarrow> A \<notin> ?R" unfolding NLim_def using assms by auto
    have B1:"?L \<subseteq> Pow X" unfolding NLim_def using assms by(auto)
    obtain ne:"{\<E>. (\<E>, x) \<in> Lim} \<noteq> {}" using A3 by blast
    then obtain B2:"?R \<subseteq> Pow X" using A1 pfilters_on_iff sets_pfilter_sub by fastforce 
    from B1 B2 B0 show ?thesis   by (meson subset_eq)
    qed
qed



lemma Nhoods_to_Lim1_via_cl: 
  assumes A0:"x \<in> X" and 
          A1:"\<And>x \<E>. (\<E>, x) \<in>Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> pfilters_on (Pow X)" and 
          A2:"Lim \<noteq> {}" and 
          A3:"(converse Lim)``{x} \<noteq> {}"
  shows "\<And>V. \<lbrakk>V \<in> Pow X\<rbrakk> \<Longrightarrow> (x, V) \<in> (NLim Lim X) \<longleftrightarrow> (X-V, x) \<notin> (ClLim Lim X) "
proof-
  fix V assume vmem:"V \<in> Pow X"
  have lfil:"\<And>\<F>. \<F> \<in> converse (Lim)``{x} \<Longrightarrow>  \<F>  \<in> Pow (Pow X) \<and> is_ord_cl (Pow X)  \<F> (\<subseteq>)" using A0 A1 by (simp add:  PowI pfilters_on_iff sets_pfilter2_upc sets_pfilter_sub)
  have B0:"(x, V) \<in> (NLim Lim X) \<longleftrightarrow> (\<forall>\<F> \<in> converse (Lim)``{x}. V \<in> \<F>)" unfolding NLim_def using A0 vmem A1 by blast
  also have B1:"...                   \<longleftrightarrow> (\<forall>\<F> \<in> converse (Lim)``{x}. (X-(X-V)) \<in> \<F>)" using double_diff vmem by fastforce
  also have B2:"...                   \<longleftrightarrow> \<not>(\<exists>\<F> \<in> converse (Lim)``{x}. (X-(X-V)) \<notin> \<F>)"  by blast
  also have B3:"...                   \<longleftrightarrow> \<not>(\<exists>\<F> \<in> converse (Lim)``{x}. (X-(X-(X-V))) \<in> grill (Pow X) \<F>)"    using "11394" lfil by(simp add:"11391")
  also have B4:"...                   \<longleftrightarrow> \<not>(\<exists>\<F> \<in> converse (Lim)``{x}. (X-V) \<in> grill (Pow X) \<F>)" by (simp add: double_diff)  
  also have B5:"...                   \<longleftrightarrow> \<not>(\<exists>\<F> \<in> converse (Lim)``{x}. {(X-V)}#\<F>)" by (simp add: grill_def) 
  also have B6:"...                   \<longleftrightarrow> (X-V, x) \<notin> (ClLim Lim X)" unfolding ClLim_def using A0 A1 vmem by blast
  finally show "(x, V) \<in> (NLim Lim X) \<longleftrightarrow> (X-V, x) \<notin> (ClLim Lim X)" by blast
qed


lemma Cl_to_Adh1:
  assumes A0:"\<And>A x. (A, x) \<in> Cl \<Longrightarrow> A \<in> Pow X \<and> x \<in> X" and A1:"\<F> \<in> pfilters_on (Pow X)"
  shows "(AdhCl Cl X)``{\<F>} = \<Inter>{Cl``{A}|A. A \<in> \<F>}"
  unfolding AdhCl_def using assms apply(auto)
  apply (meson PowD pfilters_onE sets_pfilter_sub subsetD)
  apply (metis Image_singleton_iff ex_in_conv pfilters_onE sets_pfilter_nem)
  by blast

lemma Cl_to_Adh2:
  assumes A0:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (Pow X))"  and A1:"A \<in> Pow X"
  shows "(ClAdh Adh X)``{A} = \<Union>{Adh``{\<F>}|\<F>. \<F> \<in> pfilters_on (Pow X) \<and> A \<in> \<F>}"
  unfolding ClAdh_def using assms by(auto)
   
  
lemma Cl_to_Lim1:
  assumes A0:"\<And>A x. (A, x) \<in> Cl \<Longrightarrow> A \<in> Pow X \<and> x \<in> X" and A1:"\<F> \<in> pfilters_on (Pow X)"
  shows "(LimCl Cl X)``{\<F>} = \<Inter>{Cl``{A}|A. A \<in> Pow X \<and> {A}#\<F>}"
  unfolding LimCl_def mesh_def using assms apply(auto)
  apply (metis (full_types) ImageE Pow_iff mesh_def pfilter_mesh2 pfilters_onE sets_pfilter_sub subsetD subset_refl)
  by blast 
    
  
lemma Cl_to_Lim2:
  assumes A0:"\<And>x \<E>. (\<E>, x) \<in> Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (Pow X))"  and A1:"A \<in> Pow X"
  shows "(ClLim Lim X)``{A} = \<Union>{Lim``{\<F>}|\<F>. \<F> \<in> pfilters_on (Pow X) \<and> {A}#\<F>}"
  unfolding ClLim_def using assms by(auto)

lemma Adh_to_Lim1:
  assumes A0:"\<And>x \<E>. (\<E>, x) \<in> Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (Pow X))"  and A1:"\<F> \<in> pfilters_on (Pow X)"
  shows "(AdhLim Lim X)``{\<F>} = \<Union>{Lim``{\<G>}|\<G>. \<G> \<in>  pfilters_on (Pow X) \<and> \<G>#\<F>}"
  unfolding AdhLim_def using assms by(auto)


lemma Adh_to_Lim2:
  assumes A0:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (Pow X))"  and A1:"\<F> \<in> pfilters_on (Pow X)"
  shows "(LimAdh Adh X)``{\<F>} = \<Inter>{Adh``{\<G>}|\<G>. \<G> \<in>  pfilters_on (Pow X) \<and> \<G>#\<F>}"
  unfolding LimAdh_def using assms by(auto, metis Image_singleton_iff PowD Pow_top pfilter_mesh2)

lemma cl_nh_mono1:
  assumes is_cl:"\<And>A x. (A, x) \<in> Cl \<Longrightarrow> A \<in> Pow X \<and> x \<in> X"  and  iso:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> Cl``{A} \<subseteq> Cl``{B}" 
  shows "\<And>x A. \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow> (A, x) \<in> (ClN (NCl Cl X) X) \<longleftrightarrow> (A, x) \<in> Cl"
proof-
  fix x A assume xmem:"x \<in> X" and amem:"A \<in> Pow X"
  have B0:"(NCl Cl X)``{x} = (grill (Pow X) ((converse Cl)``{x}))"  by (simp add: Cl_to_Nhoods1 xmem)
  have B1:"(converse (ClN (NCl Cl X) X))``{x} = grill (Pow X) ((NCl Cl X)``{x})" by (simp add:Cl_to_Nhoods2 xmem)
  have B2:"(converse (ClN (NCl Cl X) X))``{x} = grill (Pow X) ((grill (Pow X) ((converse Cl)``{x})))"  by (simp add: B1 Cl_to_Nhoods1 xmem)
  have B3:"\<And>A1 A2. \<lbrakk>A2 \<in> Pow X; A1 \<in> ((converse Cl)``{x}); A1 \<subseteq> A2\<rbrakk> \<Longrightarrow> A2 \<in> ((converse Cl)``{x})"
  proof-
    fix A1 A2 assume B30:"A2 \<in> Pow X" and B31:"A1 \<in> ((converse Cl)``{x})" and B32:"A1 \<subseteq> A2"
    from B31 is_cl obtain B33:"(A1, x) \<in> Cl" and B34:"A1 \<in> Pow X"   by blast
    then obtain B35:"Cl``{A1} \<subseteq> Cl``{A2}" using iso  B34 B32 B30  by force 
    then obtain "(A2, x) \<in> Cl"  using  B33    by blast
    then show "A2 \<in> ((converse Cl)``{x})" by simp
  qed
  then obtain B4:"is_ord_cl (Pow X) ((converse Cl)``{x}) (\<subseteq>)" by (metis is_ord_clI) 
  have B5:"grill (Pow X) ((grill (Pow X) ((converse Cl)``{x}))) = (converse Cl)``{x}" 
    using double_grill2 xmem  by (metis B4 Image_singleton_iff Pow_iff converseD is_cl subsetI)
  have B6:"(x, A) \<in> (converse (ClN (NCl Cl X) X)) \<longleftrightarrow> (x, A) \<in> converse Cl"  using B2 B5 by blast
  then show "(A, x) \<in> (ClN (NCl Cl X) X) \<longleftrightarrow> (A, x) \<in> Cl" by simp
qed

lemma cl_nh_mono2:
  assumes is_nh:"\<And>x V. (x, V) \<in> N \<Longrightarrow> x \<in> X \<and> V \<in> Pow X"  and  upcl:"\<And>x A B. \<lbrakk>(x, A) \<in> N ; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow>(x, B) \<in> N" 
  shows "\<And>x A. \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow> (x, A) \<in> (NCl (ClN N X) X) \<longleftrightarrow> (x, A) \<in> N"
proof-
  fix x A assume xmem:"x \<in> X" and amem:"A \<in> Pow X"
  have ordcl:"is_ord_cl (Pow X) (N``{x}) (\<subseteq>)" using upcl xmem amem is_nh  by (metis Image_singleton_iff is_ord_clI)
  have B0:"(converse (ClN N X))``{x} = grill (Pow X) (N``{x})"  by (simp add: Cl_to_Nhoods2 xmem)
  have B1:"(NCl (ClN N X) X)``{x} = grill (Pow X) ((converse (ClN N X))``{x})" by (simp add: Cl_to_Nhoods1 xmem)
  also have B2:"...               = grill (Pow X) (grill (Pow X) (N``{x}))"   using B1 B0 by auto 
  also have B3:"...               = N``{x}" using ordcl double_grill2  by (metis Image_singleton_iff Pow_iff is_nh subsetI)
  finally show "(x, A) \<in> (NCl (ClN N X) X) \<longleftrightarrow> (x, A) \<in> N"  by blast
qed

lemma nh_lim_prtp1:
  assumes is_prtp:"\<And>x. x \<in> X \<Longrightarrow> (N``{x}) \<in> pfilters_on (Pow X)" 
  shows "\<And>x A. \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow> (x, A) \<in> NLim (LimN N X) X \<longleftrightarrow> (x, A) \<in> N"
proof-
  fix x A assume xmem:"x \<in> X" and amem:"A \<in> Pow X"
  show "(x, A) \<in> NLim (LimN N X) X \<longleftrightarrow> (x, A) \<in> N" (is "?L \<longleftrightarrow> ?R")
  proof
    assume L:?L then show ?R unfolding NLim_def LimN_def using xmem amem is_prtp by auto
  next
    assume R:?R then show ?L unfolding NLim_def LimN_def using xmem amem is_prtp by auto
  qed
qed

lemma nh_lim_prtp2:
  assumes centered:"\<And>x. x \<in> X \<Longrightarrow> (lorc {x} (Pow X), x) \<in> Lim" and
          upclosed:"\<And>\<G> \<F> x. \<lbrakk>\<G> \<in> pfilters_on (Pow X); (\<F>, x) \<in> Lim;  \<F> \<subseteq> \<G>\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> Lim" and
          vicinity:"\<And>x. x \<in> X \<Longrightarrow> (\<Inter>{\<F>. (\<F>, x) \<in> Lim}, x) \<in> Lim " and  
          is_limit:"\<And>x \<E>. (\<E>, x) \<in> Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (Pow X))" 
  shows "\<And>\<F> x. \<lbrakk>\<F> \<in> pfilters_on (Pow X); x \<in> X\<rbrakk> \<Longrightarrow>(\<F>, x) \<in> LimN (NLim Lim X) X \<longleftrightarrow> (\<F>, x) \<in> Lim"
proof-
  fix \<F> x assume pfil:"\<F> \<in> pfilters_on (Pow X)" and xmem:"x \<in> X" 
  show "(\<F>, x) \<in> LimN (NLim Lim X) X \<longleftrightarrow> (\<F>, x) \<in> Lim" (is "?L \<longleftrightarrow> ?R")
  proof
    assume L:"(\<F>, x) \<in> LimN (NLim Lim X) X"
    from vicinity xmem obtain smallest:"(\<Inter>{\<F>. (\<F>, x) \<in> Lim}, x) \<in> Lim" by auto
    from L have B0:"(\<And>A. \<lbrakk>A \<in>  Pow X; (x, A) \<in> (NLim Lim X)\<rbrakk> \<Longrightarrow> A \<in> \<F>)" unfolding LimN_def by(auto)
    have B1:"\<Inter>{\<F>. (\<F>, x) \<in> Lim} = (NLim Lim X)``{x}"
      unfolding NLim_def using is_limit vicinity pfil B0 xmem centered by(auto, meson Pow_iff lorcD11 subsetD)
    also have B2:"... \<subseteq> \<F>" unfolding NLim_def using B1 B0 L is_limit  by blast
    finally show "(\<F>, x) \<in> Lim" using upclosed smallest pfil   by blast 
  next
    assume R:"(\<F>, x) \<in> Lim" then show "?L" unfolding LimN_def NLim_def using pfil xmem by auto
  qed
qed


lemma lorc_pfilter:
  assumes A0:"x \<in> X" and A1:"\<not>(is_least X x)"
  shows "is_pfilter X (lorc x X)"
proof(rule is_pfilterI1)
  show "is_filter X (lorc x X)"  by (simp add: A0 lorc_filter)
  show "(lorc x X) \<noteq> X"  by (metis A0 A1 leastI3 lorcD12)
qed


lemma lorc_set_pfilter:
  assumes A0:"A \<in> Pow X" and A1:"A \<noteq> {}" 
  shows "is_pfilter (Pow X) (lorc A (Pow X))"
  using lorc_pfilter[of A "Pow X"] A0 A1 least_unique pwr_least by blast


lemma adh_nh_mono2:
  assumes is_nh:"\<And>x V. (x, V) \<in> N \<Longrightarrow> x \<in> X \<and> V \<in> Pow X \<and> V \<noteq> {}"  and 
          upcl:"\<And>x A B. \<lbrakk>(x, A) \<in> N ; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow>(x, B) \<in> N" and
          ntr:"\<And>x. x \<in> X \<Longrightarrow> N``{x} \<noteq> {}"
  shows "\<And>x A. \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow> (x, A) \<in> (NAdh (AdhN N X) X) \<longleftrightarrow> (x, A) \<in> N"
proof-
  fix x A assume xmem:"x \<in> X" and amem:"A \<in> Pow X" 
  have "(x, A) \<in> (NAdh (AdhN N X) X) \<longleftrightarrow> (\<forall>\<F> \<in> pfilters_on (Pow X). (\<F>, x) \<in> (AdhN N X) \<longrightarrow> {A}#\<F>)"
    unfolding NAdh_def using amem xmem by blast
  also have "... \<longleftrightarrow>  (\<forall>\<F> \<in> pfilters_on (Pow X). (\<forall>V \<in> Pow X. (x, V) \<in> N \<longrightarrow> {V}#\<F>) \<longrightarrow> {A}#\<F>)"
    unfolding AdhN_def using amem xmem by auto
  also have "... \<longleftrightarrow> (\<forall>\<F> \<in> pfilters_on (Pow X). (N``{x})#\<F> \<longrightarrow> {A}#\<F>)"
    by (metis Image_singleton_iff is_nh mesh_def singletonD singletonI)
  finally have P0:"(x, A) \<in> (NAdh (AdhN N X) X) \<longleftrightarrow> (\<forall>\<F> \<in> pfilters_on (Pow X). (N``{x})#\<F> \<longrightarrow> {A}#\<F>)"  by blast
  show "(x, A) \<in> (NAdh (AdhN N X) X) \<longleftrightarrow> (x, A) \<in> N" (is "?L \<longleftrightarrow> ?R")
  proof
    assume R:?R 
    have B0:"\<And>\<F>. \<lbrakk>\<F> \<in> pfilters_on (Pow X); (\<F>, x) \<in> (AdhN N X)\<rbrakk> \<Longrightarrow> {A}#\<F>"
    proof-
      fix \<F> assume fmem:"\<F> \<in> pfilters_on (Pow X)" and fadh:"(\<F>, x) \<in> (AdhN N X)"
      then obtain "\<And>V. \<lbrakk>V \<in> Pow X; (x, V) \<in> N\<rbrakk> \<Longrightarrow> {V}#\<F>" unfolding AdhN_def using xmem by blast
      then show"{A}#\<F>" using R xmem amem by blast
    qed
    then show ?L unfolding NAdh_def using amem xmem by blast
  next
    assume L:?L 
    have B0:"\<not>(?R) \<Longrightarrow> \<not>(?L)"
    proof-
      assume negr:"\<not>(?R)"
      then obtain B1:"\<And>V. \<lbrakk>V \<in> Pow X; (x, V) \<in> N\<rbrakk> \<Longrightarrow> \<not> (V \<subseteq> A)" using upcl amem by blast
      then obtain B2:"{(X-A)}#(N``{x}) " by (meson Image_singleton_iff amem disj_sub is_nh mesh_singleI) 
      then have B3:"(lorc (X-A) (Pow X))#(N``{x})"
        unfolding mesh_def lorc_def by fastforce
      have B4:"\<not>((lorc (X-A) (Pow X))#{A})" 
        unfolding mesh_def lorc_def using Int_Diff by auto    
      obtain B5:"(X-A) \<in> Pow X" and B6:"(X-A) \<noteq> {}"  by (metis B2 Diff_disjoint Diff_empty Diff_subset Pow_iff ex_in_conv mesh_singleE ntr xmem) 
      then obtain B7:"(lorc (X-A) (Pow X)) \<in> pfilters_on (Pow X)" using lorc_set_pfilter pfilters_onI by metis
      from B7 B3 B4 have B8:"\<not>(\<forall>\<F> \<in> pfilters_on (Pow X). (N``{x})#\<F> \<longrightarrow> {A}#\<F>)" using mesh_sym by blast  
      then show "\<not>(?L)" using P0 by blast
    qed
    then show ?R using L by fastforce
  qed
qed
  

lemma adh_cl_mono1:
  assumes is_cl:"\<And>A x. (A, x) \<in> Cl \<Longrightarrow> A \<in> Pow X \<and> x \<in> X"  and  
          cl_emp:"Cl``{{}} = {}" and
          is_iso:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> Cl``{A} \<subseteq> Cl``{B}" 
  shows "\<And>x A. \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow> (A, x) \<in> (ClAdh (AdhCl Cl X) X) \<longleftrightarrow> (A, x) \<in> Cl"
proof-
  fix x A assume xmem:"x \<in> X" and amem:"A \<in> Pow X" 
  show "(A, x) \<in> (ClAdh (AdhCl Cl X) X) \<longleftrightarrow> (A, x) \<in> Cl"  (is "?L \<longleftrightarrow> ?R")
  proof
    assume L:?L
    then obtain \<F> where f1:"\<F> \<in> pfilters_on (Pow X)" and f2:"A \<in> \<F>" and f3:"(\<F>, x) \<in> AdhCl Cl X" 
      unfolding ClAdh_def using xmem amem L  by blast
    have f4:"\<And>B. B \<in> \<F> \<Longrightarrow> B \<in> Pow X"  using f1 pfilters_on_iff sets_pfilter_sub by blast
    have f5:"\<And>B. B \<in> \<F> \<Longrightarrow> (B, x) \<in> Cl" using f3 unfolding AdhCl_def using xmem f1 f4  by fastforce
    then show ?R using f2  by auto
  next
    assume R:?R
    let ?F="lorc A (Pow X)"
    have B0:"?F \<in> pfilters_on (Pow X)"  by (metis Image_singleton_iff R amem cl_emp equals0D lorc_set_pfilter pfilters_on_iff)
    have B1:"\<And>B. B \<in> ?F \<Longrightarrow> (B, x) \<in> Cl"  by (meson Image_singleton_iff R amem is_iso lorc_mem_iff1 subset_iff)
    have B2:"(?F, x) \<in>  (AdhCl Cl X)"  by (simp add: AdhCl_def B0 B1 xmem)
    have B3:"A \<in> ?F"  by (meson amem lorc_memI1)
    have B4:"(\<exists>\<F> \<in> pfilters_on (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> (AdhCl Cl X))"  using B0 B2 B3 by blast
    show ?L using B4 xmem amem unfolding ClAdh_def by blast
  qed
qed


lemma cl_lim_prtp2:
  assumes centered:"\<And>x. x \<in> X \<Longrightarrow> (lorc {x} (Pow X), x) \<in> Lim" and
          upclosed:"\<And>\<G> \<F> x. \<lbrakk>\<G> \<in> pfilters_on (Pow X); (\<F>, x) \<in> Lim;  \<F> \<subseteq> \<G>\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> Lim" and
          vicinity:"\<And>x. x \<in> X \<Longrightarrow> (\<Inter>{\<F>. (\<F>, x) \<in> Lim}, x) \<in> Lim " and  
          is_limit:"\<And>x \<E>. (\<E>, x) \<in> Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (Pow X))" 
  shows "\<And>\<F> x. \<lbrakk>\<F> \<in> pfilters_on (Pow X); x \<in> X\<rbrakk> \<Longrightarrow> (\<F>, x) \<in> Lim \<longleftrightarrow> (\<F>, x) \<in> LimCl (ClLim Lim X) X"
proof-
  fix \<F> x assume pfil:"\<F> \<in> pfilters_on (Pow X)" and xmem:"x \<in> X" 
  show "(\<F>, x) \<in> Lim \<longleftrightarrow> (\<F>, x) \<in> LimCl (ClLim Lim X) X" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L
  have L0:"\<And>A. \<lbrakk>A \<in> Pow X; {A}#\<F>\<rbrakk> \<Longrightarrow> (\<exists>\<G> \<in>  pfilters_on (Pow X). (\<G>, x) \<in> Lim \<and> {A}#\<G>)"
  proof-
    fix A assume amem:"A \<in> Pow X" and amesh:"{A}#\<F>"
    obtain is_pfil:"is_pfilter (Pow X) \<F>" and amesh_unfold:"\<forall>B \<in> \<F>. A \<inter> B \<noteq> {}" using amesh mesh_singleE pfil pfilters_on_iff by blast
    define \<H> where  "\<H> \<equiv> {E \<in> Pow X. \<exists>B \<in> \<F>. A \<inter> B \<subseteq> E}" 
    then obtain hpfil:"is_pfilter (Pow X) \<H>" and fsub:"\<F>\<subseteq> \<H>" 
      using is_pfil amesh_unfold amem finer_proper_filter[of X \<F> A]   by (simp add: Int_commute)
    obtain gmem:"\<H> \<in> pfilters_on (Pow X)" and rassum:"(\<F>, x) \<in> Lim"  and fsubh:"\<F> \<subseteq> \<H>"  using L fsub hpfil pfilters_onI by blast
    then obtain hlim:"(\<H>, x) \<in> Lim" using upclosed  by blast
    also obtain hmesh:"{A}#\<H>" unfolding \<H>_def mesh_def  using amesh_unfold by fastforce
    then show "(\<exists>\<G> \<in>  pfilters_on (Pow X). (\<G>, x) \<in> Lim \<and> {A}#\<G>)"   using gmem hlim by blast
  qed
  then show ?R unfolding LimCl_def ClLim_def using pfil xmem by (smt (verit, best) CollectI case_prodI)
next
  assume R:?R
  then obtain R0:"\<And>F. \<lbrakk>F \<in> Pow X; {F}#\<F>\<rbrakk> \<Longrightarrow>  (\<exists>\<G> \<in>  pfilters_on (Pow X). (\<G>, x) \<in> Lim \<and> {F}#\<G>)" 
    unfolding LimCl_def ClLim_def using pfil xmem by blast
  have R1:"\<And>F. \<lbrakk>F \<in> Pow X; {F}#\<F>\<rbrakk> \<Longrightarrow>  (\<exists>\<G> \<in>  pfilters_on (Pow X). (\<G>, x) \<in> Lim \<and> F \<in> \<G>)"
  proof-
    fix F assume fmem:"F \<in> Pow X" and fmesh:"{F}#\<F>" 
    then obtain \<G> where gfil:"\<G> \<in> pfilters_on (Pow X)" and gx:"(\<G>, x) \<in> Lim" and fg:"{F}#\<G>"  using R0 by auto
    then obtain is_pfil:"is_pfilter (Pow X) \<G>"  and fmesh_unfold:"\<forall>B \<in> \<G>. F \<inter> B \<noteq> {}" using fmesh mesh_singleE pfil pfilters_on_iff by blast
    define \<H> where  "\<H> \<equiv> {E \<in> Pow X. \<exists>B \<in>  \<G>. F \<inter> B \<subseteq> E}" 
    then obtain hpfil:"is_pfilter (Pow X) \<H>" and gsub:" \<G>\<subseteq> \<H>"
      using is_pfil fmesh_unfold fmem finer_proper_filter[of X  \<G> F] by (simp add: Int_commute)
    obtain hmem:"\<H> \<in> pfilters_on (Pow X)"   by (simp add: hpfil pfilters_onI) 
    obtain fmem2:"F \<in> \<H>"   using \<H>_def fmem is_pfil sets_pfilter_nem by fastforce
    obtain hlim:"(\<H>, x) \<in> Lim" using gsub hmem gx upclosed   by blast
    then show "(\<exists>\<G> \<in>  pfilters_on (Pow X). (\<G>, x) \<in> Lim \<and> F \<in>\<G>)" using hmem fmem2
    by blast
  qed
  let ?N="\<Inter>{\<F>. (\<F>, x) \<in> Lim}"
  have R2:"?N \<subseteq>\<F>"
  proof(rule ccontr)
    assume contr1:"\<not>(?N \<subseteq> \<F>)" then obtain F where f1:"F \<in> ?N" and f2:"F \<notin> \<F>" by blast
    from pfil obtain f3:"\<F>  \<in> Pow (Pow X)" and  f4:"is_ord_cl (Pow X)  \<F> (\<subseteq>)" by (simp add: pfilters_on_iff sets_pfilter2_upc sets_pfilter_sub)
    from f2 f3 f4 obtain "(X-F) \<in> grill (Pow X) \<F>"  by (metis "11391" InterE centered f1 lorcD1 mem_Collect_eq xmem) 
    then obtain "{X-F}#\<F>" by (simp add: grill_def)
    then obtain \<G> where gfil:"\<G> \<in> pfilters_on (Pow X)" and gx:"(\<G>, x) \<in> Lim" and fg:"(X-F) \<in> \<G>" by (meson Diff_subset PowI R1)
    from f1 have "F \<in> \<G>"  using gx by blast
    then obtain "{} \<in> \<G>"  by (metis Diff_disjoint fg gfil pfilters_onE sets_pfilter_dir)
    then show False
    using gfil pfilters_onE sets_pfilter_emp by blast
  qed
  then show ?L
  using pfil upclosed vicinity xmem by blast
qed
qed

lemma ccl_mnono:
  assumes is_cl:"\<And>A x. (A, x) \<in> Cl \<Longrightarrow> A \<in> Pow X \<and> x \<in> X"  and  
          CCl1:"Cl``{{}} = {}" and
          CCl2:"\<And>A. A \<in> Pow X \<Longrightarrow> A \<subseteq> Cl``{A}" and
          CCl3:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X\<rbrakk> \<Longrightarrow> Cl``{A \<union> B}=Cl``{A} \<union> Cl``{B}"
  shows "\<And>A B. \<lbrakk>A\<in> Pow X; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> Cl``{A}\<subseteq>Cl``{B}"
proof-
  fix A B assume A0:"A \<in> Pow X" and B0:"B \<in> Pow X" and AB:"A \<subseteq> B"
  then obtain B1:"(B-A) \<in> Pow X" and B2:"B=(B-A)\<union>A"   by blast
  then have "Cl``{B}=Cl``{B-A}\<union>Cl``{A}" using A0 CCl3[of "(B-A)" "A"] by presburger
  also have "... \<supseteq> Cl``{A}"  by blast
  finally show " Cl``{A}\<subseteq>Cl``{B}"  by blast
qed

lemma prtp_lim_cl1:
  assumes centered:"\<And>x. x \<in> X \<Longrightarrow> (lorc {x} (Pow X), x) \<in> Lim" and
          upclosed:"\<And>\<G> \<F> x. \<lbrakk>\<G> \<in> pfilters_on (Pow X); (\<F>, x) \<in> Lim;  \<F> \<subseteq> \<G>\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> Lim" and
          vicinity:"\<And>x. x \<in> X \<Longrightarrow> (\<Inter>{\<F>. (\<F>, x) \<in> Lim}, x) \<in> Lim " and  
          is_limit:"\<And>x \<E>. (\<E>, x) \<in> Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (Pow X))" 
  shows prtp_lim_cleq:"(ClLim Lim X) = {(A, x). A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F> \<in> pfilters_on (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> Lim)}" and
        prtp_lim_ccl0:"(ClLim Lim X)``{{}}={}" and
        prtp_lim_ccl1:"\<And>A. A \<in> Pow X \<Longrightarrow> A \<subseteq>(ClLim Lim X)``{A}" and
        prtp_lim_ccl2:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X\<rbrakk> \<Longrightarrow> (ClLim Lim X)``{A \<union> B}=(ClLim Lim X)``{A} \<union> (ClLim Lim X)``{B}"
proof-
  show Q0:"(ClLim Lim X) = {(A, x). A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F> \<in> pfilters_on (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> Lim)}"
  proof-
     have P0:"\<And>A x. \<lbrakk>A \<in> Pow X; x \<in> X\<rbrakk> \<Longrightarrow> (A, x) \<in> (ClLim Lim X) \<longleftrightarrow>  (\<exists>\<F> \<in> pfilters_on (Pow X). {A}#\<F> \<and> (\<F>, x) \<in> Lim)" unfolding ClLim_def  by blast
     then have P1:"\<And>A x. \<lbrakk>A \<in> Pow X; x \<in> X\<rbrakk> \<Longrightarrow> (A, x) \<in> (ClLim Lim X) \<longleftrightarrow>  (\<exists>\<F> \<in> pfilters_on (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> Lim)"
     proof-
      fix A x assume A0:"A \<in> Pow X" and x0:"x \<in> X" 
      show "(A, x) \<in> (ClLim Lim X) \<longleftrightarrow>  (\<exists>\<F> \<in> pfilters_on (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> Lim)" (is "?L \<longleftrightarrow> ?R")
      proof
        assume L:?L then obtain \<F> where f1:"\<F> \<in> pfilters_on (Pow X)" and f2:"{A}#\<F>"  and F3:"(\<F>, x) \<in> Lim" using P0 A0 x0 by blast
        then obtain is_pfil:"is_pfilter (Pow X) \<F>"  and fmesh_unfold:"\<forall>B \<in> \<F>. A \<inter> B \<noteq> {}" using f2 mesh_singleE f1 pfilters_on_iff by blast
        define \<H> where  "\<H> \<equiv> {E \<in> Pow X. \<exists>B \<in> \<F>. A \<inter> B \<subseteq> E}" 
        then obtain hpfil:"is_pfilter (Pow X) \<H>" and gsub:"\<F>\<subseteq> \<H>"  using is_pfil fmesh_unfold A0 finer_proper_filter[of X \<F> A] by (simp add: Int_commute)
        obtain hmem:"\<H> \<in> pfilters_on (Pow X)"   by (simp add: hpfil pfilters_onI) 
        obtain fmem2:"A \<in> \<H>"   using \<H>_def A0 is_pfil sets_pfilter_nem by fastforce
        obtain hlim:"(\<H>, x) \<in> Lim" using gsub hmem F3 upclosed  by blast
        then show "?R" using hmem fmem2 by auto
      next
        assume R:?R  then obtain \<F> where f1:"\<F> \<in> pfilters_on (Pow X)" and f2:"A \<in>\<F>"  and F3:"(\<F>, x) \<in> Lim" using P0 A0 x0 by blast
        also obtain f4:"{A}#\<F>"  by (meson f1 f2 mesh_def mesh_singleI pfilter_mesh2 subsetI)
        then show ?L  using A0 F3 P0 f1 x0 by auto
      qed
    qed
    from P1 have  P2:"\<And>A x. (A, x) \<in> (ClLim Lim X) \<Longrightarrow>  (\<exists>\<F> \<in> pfilters_on (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> Lim)" by (metis (no_types, lifting) ClLim_def CollectD case_prodD)
    from P1  have P3: "\<And>A x.   (\<exists>\<F> \<in> pfilters_on (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> Lim) \<Longrightarrow> (A, x) \<in> (ClLim Lim X)"  by (meson P1 in_mono is_limit pfilters_onE sets_pfilter_sub) 
    from P2 P3 show ?thesis  by (smt (verit) ClLim_def Collect_cong Pair_inject case_prodE case_prodI2 mem_Collect_eq) 
  qed
  show Q1:"(ClLim Lim X)``{{}}={}"
  proof-
    have P0:"\<And>x. x \<in> X \<Longrightarrow> ({}, x) \<notin> (ClLim Lim X)" using CollectD Q0 filter_on_set_ne by auto 
    then show ?thesis  by (simp add: Q0)
  qed
  show Q2:"\<And>A. A \<in> Pow X \<Longrightarrow> A \<subseteq>(ClLim Lim X)``{A}"
  proof-
    fix A assume amem:"A \<in> Pow X"
    have "\<And>x. x \<in> A \<Longrightarrow> x \<in> (ClLim Lim X)``{A}"
    proof-
      fix x assume xa:"x \<in> A"
      then obtain B0:"(lorc {x} (Pow X)) \<in> pfilters_on (Pow X)" and B1:"{A}#(lorc {x} (Pow X))" and B2:"(lorc {x} (Pow X), x) \<in> Lim"
      by (metis (no_types, opaque_lifting) Pow_iff amem bot.extremum centered filter_mem_mesh insert_subset is_limit lorcI1 mk_disjoint_insert)
      then show "x \<in> (ClLim Lim X)``{A}" unfolding ClLim_def   using Image_singleton_iff amem case_prodI is_limit by auto 
    qed
    then show "A \<subseteq>(ClLim Lim X)``{A}" by blast
  qed
  show Q3:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X\<rbrakk> \<Longrightarrow> (ClLim Lim X)``{A \<union> B}=(ClLim Lim X)``{A} \<union> (ClLim Lim X)``{B}"
  proof-
    fix A B assume amem:"A \<in> Pow X" and bmem:"B \<in> Pow X"
    show "(ClLim Lim X)``{A \<union> B} = (ClLim Lim X)``{A} \<union> (ClLim Lim X)``{B}" (is "?lhs = ?rhs")
    proof
      show "?lhs \<subseteq> ?rhs"
      proof
        fix x assume L:"x \<in> ?lhs"
        obtain G where B2:"G \<in> pfilters_on (Pow X)" and  B3:"(G, x) \<in> Lim \<and> A \<union> B \<in> G" using ClLim_def L  Q0 by auto 
        have B4:"x \<notin> (ClLim Lim X)``{A} \<Longrightarrow> x \<in> (ClLim Lim X)``{B}"
        proof-
          assume A5:"x \<notin> (ClLim Lim X)``{A}"
          then obtain B5:"A \<notin> G"   using B2 B3 ClLim_def L Q0 by auto
          have B6:"\<forall>g \<in> G. g \<inter> (X-A) \<noteq> {}"   by (meson B2 B5 PowD amem pfilters_onE pfilters_sets_comp3) 
          have B7:"is_pfilter (Pow X) G"   by (simp add: B2 pfilters_onE)
          have B8:"(X-A) \<in> Pow X"    by simp
          define H where "H \<equiv> {E \<in> Pow X. \<exists>g \<in> G. (X-A) \<inter> g \<subseteq> E}" 
          obtain B9:"is_pfilter (Pow X) H"  using finer_proper_filter[of X G "(X-A)"] B6 B7 B8 H_def by blast
          obtain B10:"G \<subseteq> H"  using finer_proper_filter[of X G "(X-A)"] B6 B7 B8 H_def by blast
          have B11:"(X - A) \<inter> (A \<union> B) \<subseteq> B"   by blast
          have B12:"(X - A) \<inter> (A \<union> B) \<in> H"      using B3 H_def by blast
          have B13:"B \<in> H"  using B12 B9 bmem sets_pfilter_upcl by blast 
          have B14a:"H \<in> pfilters_on (Pow X) \<and>  (G, x) \<in> Lim \<and> G \<subseteq> H"    by (simp add: B10 B3 B9 pfilters_on_iff)
          then have B14:"(H, x) \<in> Lim"  using upclosed by blast 
          show "x \<in> (ClLim Lim X)``{B}"  using B13 B14 B14a ClLim_def Q0  bmem is_limit by fastforce
        qed
        have B15:"x \<in>  (ClLim Lim X)``{A} \<or> x \<in>  (ClLim Lim X)``{B}"  using B4 by blast
        then show "x \<in>  (ClLim Lim X)``{A} \<union>  (ClLim Lim X)``{B}" by simp
      qed
    next
      show "?rhs \<subseteq> ?lhs"
      proof
        fix x assume R:"x \<in> ?rhs"
        then obtain B0:"x \<in>  (ClLim Lim X)``{A} \<or> x \<in>  (ClLim Lim X)``{B}" by auto
        then obtain G where B1:"G \<in> pfilters_on (Pow X)" and B2:"(G, x) \<in> Lim \<and> (A \<in> G \<or>  B \<in> G)"  
          using ClLim_def Q0 Image_Collect_case_prod mem_Collect_eq singletonD by auto 
        then obtain B3:"A \<union> B \<in> G" using   is_ord_clE pfilters_onE sets_pfilter2_upc amem bmem by fastforce
        then have B4:"G \<in>  pfilters_on (Pow X) \<and> (G, x) \<in> Lim\<and> (A \<union> B) \<in> G" by (simp add: B1 B2)
        then obtain B5:"\<exists>G1 \<in> pfilters_on (Pow X). (G1, x) \<in> Lim \<and> (A \<union>B ) \<in> G1" by blast
        also obtain "x \<in> X" using B0 ClLim_def Q0 by blast
        then show "x \<in> ?lhs" using ClLim_def Q0  calculation Pow_iff Un_subset_iff amem bmem by auto
      qed
    qed
  qed
qed
      
lemma cl_lim_prtp2b:
  assumes is_cl:"\<And>A x. (A, x) \<in> Cl \<Longrightarrow> A \<in> Pow X \<and> x \<in> X"  and  
          CCl1:"Cl``{{}} = {}" and
          CCl2:"\<And>A. A \<in> Pow X \<Longrightarrow> A \<subseteq> Cl``{A}" and
          CCl3:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X\<rbrakk> \<Longrightarrow> Cl``{A \<union> B}=Cl``{A} \<union> Cl``{B}"
  shows "\<And>A x. \<lbrakk>A \<in> (Pow X); x \<in> X\<rbrakk> \<Longrightarrow> (A, x) \<in> Cl \<longleftrightarrow> (\<forall>V \<in> Pow X. (X-V, x) \<notin> Cl \<longrightarrow> V \<inter> A \<noteq> {})"
proof-
  fix A x assume A0:"A\<in>(Pow X)" and A1:"x\<in>X"
  show "(A, x) \<in> Cl \<longleftrightarrow> (\<forall>V \<in> Pow X. (X-V, x) \<notin> Cl \<longrightarrow> V \<inter> A \<noteq> {})" (is "?L \<longleftrightarrow> ?R")
  proof
    assume L:?L 
    also have contrp:"\<not>(?R) \<Longrightarrow> \<not>(?L)"
    proof-
      assume nQ:"\<not>(?R)" then obtain V where V0:"V \<in> Pow X" and V1:"(X-V, x)\<notin>Cl" and V2:"V \<inter> A = {}" by blast
      then obtain "A \<subseteq> (X-V)"  using A0 by blast 
      then obtain "Cl``{A} \<subseteq> Cl``{(X-V)}"   by (metis A0 CCl3 Diff_subset Pow_iff subset_Un_eq)
      then obtain "x \<notin> Cl``{A}" using V1 by blast
      then show "\<not>(?L)"   by force
    qed
    then show ?R  using calculation by blast
  next
    assume R:?R then show ?L using A0 A1 is_cl CCl1 CCl2 CCl3 apply(auto)
    by (metis (no_types, lifting) Diff_Diff_Int Diff_disjoint Pow_iff inf.absorb_iff2)
  qed
qed

  


  

lemma cl_lim_prtp2:
  assumes is_cl:"\<And>A x. (A, x) \<in> Cl \<Longrightarrow> A \<in> Pow X \<and> x \<in> X"  and  
          CCl1:"Cl``{{}} = {}" and
          CCl2:"\<And>A. A \<in> Pow X \<Longrightarrow> A \<subseteq> Cl``{A}" and
          CCl3:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X\<rbrakk> \<Longrightarrow> Cl``{A \<union> B}=Cl``{A} \<union> Cl``{B}"
  shows "\<And>A x. \<lbrakk>A \<in> (Pow X); x \<in> X\<rbrakk> \<Longrightarrow> (A, x) \<in> (ClLim (LimCl Cl X) X) \<longleftrightarrow> (A, x) \<in> Cl"
proof-
  have CCl4:"\<And>A B. \<lbrakk>A\<in> Pow X; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> Cl``{A}\<subseteq>Cl``{B}" using is_cl CCl1 CCl2 CCl3 ccl_mnono[of Cl]  by presburger
  fix A x assume A0:"A \<in> Pow X" and x0:"x \<in> X"
  show "(A, x) \<in> (ClLim (LimCl Cl X) X) \<longleftrightarrow> (A, x) \<in> Cl" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L
  then show ?R unfolding ClLim_def LimCl_def using L is_cl CCl1 CCl2 CCl3 CCl4 A0 x0 by(auto)
next
  assume R:?R
  show ?L
  

(*

definition LimCl::"('a set \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> ('a set set \<times> 'a) set" where
  "LimCl Cl X \<equiv> {(\<F>, x). \<F> \<in>  pfilters_on (Pow X) \<and> x \<in> X \<and> (\<forall>A. A \<in>  Pow X \<and> {A}#\<F> \<longrightarrow> (A, x) \<in> Cl)}"

definition ClLim::"('a set set \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow>('a set \<times> 'a) set " where
  "ClLim Lim X \<equiv> {(A, x). A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F> \<in> pfilters_on (Pow X). {A} # \<F> \<and> (\<F>, x) \<in> Lim)}"
*)

(*
abbreviation is_conv where
  "is_conv R X \<equiv> R \<subseteq> {(F, x). F \<in> pfilters_on (Pow X) \<and> x \<in> X}" 

abbreviation centered_conv where
  "centered_conv R X \<equiv> (\<forall>x. x \<in> X \<longrightarrow> (lorc {x} (Pow X), x) \<in> R)"

abbreviation iso_conv where
  "iso_conv R X \<equiv> (\<forall>x \<in> X. \<forall>F \<in> pfilters_on (Pow X). \<forall>G \<in> pfilters_on (Pow X). (F, x) \<in> R \<and> F \<subseteq> G \<longrightarrow> (G, x)\<in>R)"

abbreviation nhood where
  "nhood R X \<equiv> \<lambda>x. (\<Inter>{F. (F, x) \<in> R})"

abbreviation onep_conv where
  "onep_conv R X \<equiv> (\<forall>x \<in> X. (nhood R X x, x) \<in> R)"

abbreviation is_prtop where
  "is_prtop R X \<equiv> is_conv R X \<and> centered_conv R X \<and> iso_conv R X \<and> onep_conv R X"

abbreviation finer_pfilters where
  "finer_pfilters X F \<equiv> {G \<in> pfilters_on X. F \<subseteq> G}"

abbreviation ufilters_on where
  "ufilters_on X F \<equiv> {U. is_maximal (pfilters_on X) U}"

abbreviation finer_ufilters where
  "finer_ufilters X F \<equiv> {U. is_maximal (pfilters_on X) U \<and> F \<subseteq> U}"

lemma adherence_equalities:
  assumes sub:"A \<subseteq> X" and c1:"is_conv q X" and iso:"iso_conv q X"
  defines "Adh \<equiv> (\<lambda>A. {x \<in> X. \<exists>G \<in> pfilters_on (Pow X). (G, x) \<in> q \<and> A \<in> G})"
  shows adh1:"Adh A = {x \<in> X. \<exists>F \<in> pfilters_on (Pow X). (F, x) \<in> q \<and> F#{A}}" and
        adh2:"Adh A = {x \<in> X. \<exists>F \<in> pfilters_on (Pow X). (F, x) \<in> q \<and> A \<in> grill (Pow X) F}"
  proof(auto simp add:Adh_def)
    show adh1l:"\<And>x G. x \<in> X \<Longrightarrow> G \<in> pfilters_on (Pow X) \<Longrightarrow> (G, x) \<in> q \<Longrightarrow> A \<in> G \<Longrightarrow> \<exists>F\<in>pfilters_on (Pow X). (F, x) \<in> q \<and> F # {A}"
    proof-
      fix x G assume "x \<in> X" and g0:"G \<in> pfilters_on (Pow X)" and g2:"(G, x) \<in> q"  and  g1:"A \<in> G"
      then obtain "G # {A}"  by (metis insert_absorb mesh_iff pfilter_mesh singleton_iff subset_insertI subset_preceq)
      then show " \<exists>F::'a set set\<in>pfilters_on (Pow X). (F, x) \<in> q \<and> F # {A}" using g0 g1 g2 by blast
    qed
    show adh1r:"\<And>x F. x \<in> X \<Longrightarrow> F \<in> pfilters_on (Pow X) \<Longrightarrow> (F, x) \<in> q \<Longrightarrow> F # {A} \<Longrightarrow> \<exists>G\<in>pfilters_on (Pow X). (G, x) \<in> q \<and> A \<in> G"
    proof-
      fix x F assume a0:"x \<in> X" and a1:"F \<in> pfilters_on (Pow X) " and a2:"(F, x) \<in> q" and a3:"F # {A}"
      then obtain a3:"is_pfilter (Pow X) F" and a4:"A \<in> Pow X" and a5:"\<forall>B \<in> F. B \<inter> A \<noteq> {}"      by (simp add: mesh_iff pfilters_on_iff sub)
      define H where "H \<equiv> {E \<in> Pow X. \<exists>B \<in> F. A \<inter> B \<subseteq> E}"
      then obtain a6:"H \<in> pfilters_on (Pow X)" and a7:"F \<subseteq> H" using a3 a4 a5 finer_proper_filter[of X F A] H_def by (simp add: pfilters_onI)
      obtain a8:"A \<in> H" using H_def a3 is_pfilterE1 sets_filter_top sub by fastforce
      then show "\<exists>G\<in>pfilters_on (Pow X). (G, x) \<in> q \<and> A \<in> G" using a0 a1 a2 a6 a7 iso by blast
    qed
    show "\<And>x G. x \<in> X \<Longrightarrow> G \<in> pfilters_on (Pow X) \<Longrightarrow> (G, x) \<in> q \<Longrightarrow> A \<in> G \<Longrightarrow> \<exists>F\<in>pfilters_on (Pow X). (F, x) \<in> q \<and> A \<in> grill (Pow X) F"
      by (meson "11394" PowI pfilter_sets_comp pfilters_onE sets_pfilter2_upc sets_pfilter_sub sub)
    show "\<And>x F. x \<in> X \<Longrightarrow> F \<in> pfilters_on (Pow X) \<Longrightarrow> (F, x) \<in> q \<Longrightarrow> A \<in> grill (Pow X) F \<Longrightarrow> \<exists>G\<in>pfilters_on (Pow X). (G, x) \<in> q \<and> A \<in> G"
      by (simp add: adh1r grill_def mesh_sym)
qed

lemma maximal_filter_ext:
  assumes lat:"is_lattice X" and 
          bot:"is_least X bot" and
          pfil:"is_pfilter X F" 
  shows "\<exists>U. is_maximal (pfilters_on X) U \<and> F \<subseteq> U"
proof-
  let ?A="finer_pfilters X F"
  have sub:"?A \<subseteq> Pow X" using is_filterE1 is_pfilterE1 pfilters_onE by fastforce 
  have "F \<in> ?A" using pfil  by (simp add: pfilters_onI)
  then obtain ne:"?A \<noteq> {}" by auto
  have ind:"\<And>C. \<lbrakk>C\<noteq>{}; subset.chain ?A C\<rbrakk> \<Longrightarrow> \<Union>C \<in> ?A"
  proof-
    fix C assume nem:"C \<noteq> {}" and lin:"subset.chain ?A C" 
    have ne1:"\<And>c. c \<in> C \<Longrightarrow> is_pfilter X c" using lin pfilters_on_def chainsD2 chains_alt_def by fastforce
    have cpfil:"is_pfilter X (\<Union>C)"
      proof(rule is_pfilterI1)
        show "is_filter X (\<Union> C)"
        proof(rule is_filterI1)
        have ne2:"\<And>c. c \<in> C \<Longrightarrow> c \<noteq> {}" using is_filterE1 is_pfilterE1 ne1 by blast
        show f1:"\<Union> C \<noteq> {}"  by (simp add: ne2 nem) 
        show f2:"\<Union> C \<subseteq> X" by (simp add: Sup_le_iff is_filterE1 is_pfilterE1 ne1)
        show f3:"is_dir (\<Union> C) (\<lambda>(x::'a) y::'a. y \<le> x)"
        proof(rule is_dirI1)
          fix a b assume amem:" a \<in> \<Union> C " and bmem:"b \<in> \<Union> C" 
          then obtain Fa Fb where fa1:"Fa \<in> C" and fb1:"Fb \<in> C" and fa2:"a \<in> Fa" and fb2:"b \<in> Fb" by blast
          then obtain fa3:"is_pfilter X Fa" and fb3:"is_pfilter X Fb" and  fab:"Fa \<subseteq> Fb \<or> Fb \<subseteq> Fa"  by (meson lin ne1 subset_chain_def) 
          then obtain or:"(a \<in> Fa \<and> b \<in> Fa) \<or> (a \<in> Fb \<and> b \<in> Fb)" using fa2 fb2 by blast
          have abmem:"a \<in> X \<and> b \<in> X"  using f2 amem bmem by blast 
          then obtain c  where inf:"is_inf X {a,b} c"  using lat lattD21 by blast
          show "\<exists>c::'a\<in>\<Union> C. c \<le> a \<and> c \<le> b"
          proof(cases "a \<in> Fa \<and> b \<in> Fa")
            case True then obtain  "c \<in> Fa" using fa3 filter_finf_closed inf is_pfilter_def by blast
            then obtain "c \<in>\<Union> C" and "c \<le> a" and "c \<le> b"  using fa1 inf is_infD1121 by auto
            then show ?thesis by blast
          next
          case False then obtain  "c \<in> Fb" using fb3 filter_finf_closed inf is_pfilterE1 or by blast
            then obtain "c \<in>\<Union> C" and "c \<le> a" and "c \<le> b"  using fb1 inf is_infD1121 by fastforce
            then show ?thesis by blast
          qed
        qed
        show "is_ord_cl X (\<Union> C) (\<le>)"
        proof(rule is_ord_clI)
          fix a b assume amem:" a \<in> \<Union> C " and bmem:"b \<in>X"  and le:"a \<le> b"
          obtain Fa where famem:"Fa \<in>C" and amem2:"a \<in> Fa"   using amem by blast 
          then obtain "is_pfilter X Fa"    by (simp add: ne1) 
          then obtain "b \<in> Fa" by (meson amem2 bmem is_filterE1 is_ord_clE is_pfilterE1 le)  
          then show "b \<in> \<Union>C"  using famem  by auto
        qed
      qed
      have "\<forall>c \<in> C. is_pfilter X c" by (simp add: ne1)  
      then have "\<forall>c \<in> C. bot \<notin> c"  by (metis is_filter_def bot is_pfilter_def up_cl_bot)  
      then have "bot \<notin> \<Union>C" by blast
      then show "\<Union> C \<noteq> X"  using bot leastD11 by blast
    qed
    have finer:"F \<subseteq> (\<Union>C)" by (metis (no_types, lifting) CollectD in_mono less_eq_Sup lin nem subset_chain_def)
    then show "\<Union>C \<in> ?A" by (simp add: cpfil pfilters_on_iff)
  qed
  obtain M where maxins:"M\<in>?A" and maximp:"\<forall>a\<in>?A. M \<subseteq> a \<longrightarrow> a = M" using subset_Zorn_nonempty[of ?A] ind ne by auto
  have "is_maximal (pfilters_on X) M"
    apply(rule maximalI1)
    using maxins apply force
    by (metis (no_types, lifting) CollectD CollectI dual_order.trans maximp maxins)
  also have "F \<subseteq> M"  using maxins by blast
  then show ?thesis  using calculation by blast 
qed

lemma maximal_filter_set:
  assumes  pfil:"is_pfilter (Pow X) F" 
  shows "\<exists>U. is_maximal (pfilters_on (Pow X)) U \<and> F \<subseteq> U"
proof(rule maximal_filter_ext)
  show "is_lattice (Pow X)" by (simp add: clat_lattice pow_is_clattice)
  show "is_least (Pow X) {}"  by (simp add: pwr_least) 
  show "is_pfilter (Pow X) F" by (simp add:pfil)
qed

lemma filter_max_inter:
    assumes  pfil:"is_pfilter (Pow X) F" 
    shows "F=\<Inter>(finer_ufilters (Pow X) F)"
proof- 
  let ?U="finer_ufilters (Pow X) F"
  have c1:"?U \<subseteq> Pow (Pow X)" using maximalD1 pfilters_on_def sets_pfilter_sub by fastforce 
  have c2:"F \<subseteq> Pow X" using pfil sets_pfilter_sub by blast 
  have ne:"?U \<noteq> {}" using pfil maximal_filter_set by auto
  have L:"F \<subseteq> \<Inter>?U" by(auto)
  also have R:"\<Inter>?U \<subseteq> F"
  proof(rule ccontr)
    assume nR:"\<not>(\<Inter>?U \<subseteq> F)" then obtain A where a1:"A \<in>\<Inter>?U" and a2:"A \<notin> F" by auto
    have a3:"A \<in> Pow X"  using a1 c1 ne by auto    
    let ?Ac="X-A"
    have a4:"?Ac \<in> grill (Pow X) F"  by (meson "11391" a2 a3 c2 pfil sets_pfilter2_upc)
    have fr1:"\<forall>B \<in> F. B \<inter> ?Ac \<noteq> {}" by (metis PowD a2 a3 pfil pfilters_sets_comp3)
    have fr2:"?Ac \<in> Pow X" by simp
    define H where "H \<equiv> {E \<in> Pow X. \<exists>B \<in> F. ?Ac \<inter> B \<subseteq> E}" 
    obtain pfr1:"H \<subseteq> Pow X" and pfr2:"X \<in> H" and   pfr3:"H \<noteq> {}" and   pfr4:"is_dir H (\<lambda>x y. y \<subseteq> x)" and
           pfr5:"is_ord_cl (Pow X) H (\<subseteq>) "  and  pfr6:"{} \<notin> H" and   pfr7:"Pow X \<noteq> H" and pfr8:"is_pfilter (Pow X) H" 
            using pfilter_refinment[of X F ?Ac] H_def fr1 fr2 pfil by(auto)
    have pfr9:"F \<subseteq> H"  using H_def c2 by auto
    obtain UH where uh1:"is_maximal (pfilters_on (Pow X)) UH" and uh2:"H \<subseteq> UH" using  pfr8 maximal_filter_set[of X H] by(auto)
    also obtain uh3:"F \<subseteq> UH" using pfr9 uh2 by auto
    then have uh4:"UH \<in> ?U"  using uh1 by force
    have uh5:"?Ac \<in> UH"   using H_def uh2 fr2 pfr2 by blast 
    have uh6:"A \<notin> UH"  using uh5 maximalD1 pfilters_sets_comp2 uh1 pfilters_onE by blast
    then obtain "A \<notin> \<Inter>?U"   using uh4 by blast
    then show False using a1 by blast
  qed
  then show "F=\<Inter>(finer_ufilters (Pow X) F)" by blast
qed

lemma finer_than_vicinity:
  assumes "onep_conv q X" and "(\<F>, x) \<in> q"
  shows "nhood q X x \<subseteq> \<F>"
  by (simp add: Inter_lower assms)

lemma nhood_is_pfilter:
  assumes A0:"is_conv q X" and A1:"centered_conv q X"  and A3:"x \<in> X"
  shows "is_pfilter (Pow X) (nhood q X x)"
proof-
  let ?EF="{F. (F, x) \<in> q}"
  have B0:"\<And>F. F \<in> ?EF \<Longrightarrow> is_pfilter (Pow X) F"   using A0 pfilters_onE by fastforce
  also have B1:"?EF \<noteq> {}"   using A1 A3 by blast
  then show "is_pfilter (Pow X) (nhood q X x)"
    by (simp add: Collect_mono_iff calculation pfilters_on_def set_pfilter_inter)
qed

lemma nhood_sub:
  assumes A0:"is_conv q X" and A1:"centered_conv q X" and A2:"x \<in> X"and A3:"V \<in> (nhood q X x)"
  shows "V \<in> Pow X"
  by (metis A1 A2 A3 CollectI InterE lorcD11)

definition continuous_at:: "('a::type \<Rightarrow> 'b::type) \<Rightarrow> 'a::type set \<Rightarrow> ('a::type set set \<times> 'a::type) set \<Rightarrow> 'b::type set \<Rightarrow> ('b::type set set \<times> 'b::type) set \<Rightarrow> 'a::type \<Rightarrow> bool" where
  "continuous_at f X q Y p x \<equiv> (\<forall>\<F>.  (\<F>, x)\<in> q \<longrightarrow> ({E \<in> Pow Y. \<exists>F \<in> \<F>. f`(F) \<subseteq> E}, f x) \<in> p)"

lemma continuousD:
  "\<lbrakk>continuous_at f X q Y p x; (\<F>, x) \<in> q\<rbrakk> \<Longrightarrow>({E \<in> Pow Y. \<exists>F \<in> \<F>. f`(F) \<subseteq> E}, f x) \<in> p "
  by (simp add:continuous_at_def)

lemma continuousI:
  "(\<And>\<F>. (\<F>, x) \<in> q \<Longrightarrow> ({E \<in> Pow Y. \<exists>F \<in> \<F>. f`(F) \<subseteq> E}, f x) \<in> p) \<Longrightarrow>  continuous_at f X q Y p x"
  by (simp add:continuous_at_def)


lemma im_filter:
  assumes A0:"is_pfilter (Pow X) \<F>"  and A1:"f`X \<subseteq> Y"
  shows "is_pfilter (Pow Y) {E \<in> Pow Y. \<exists>F \<in> \<F>. f`F \<subseteq> E}"  
proof(rule is_pfilterI1)
  let ?fF="{E \<in> Pow Y. \<exists>F \<in> \<F>. f`F \<subseteq> E}"
  show "is_filter (Pow Y)?fF"
  proof(rule is_filterI1)
    show "?fF \<noteq> {}"  using A0 A1 Pow_iff image_mono in_mono sets_pfilter_nem sets_pfilter_sub by fastforce
    show ysub:"?fF \<subseteq> Pow Y" by blast
    show "is_dir ?fF (\<lambda>x y. y \<subseteq> x)"
    proof(rule is_dirI1)
      fix a b assume "a \<in> ?fF" and bmem:"b \<in> ?fF" 
      then obtain fa fb where "fa \<in> \<F>"  and "fb \<in> \<F>" and asub:"f`fa \<subseteq> a" and bsub:"f`fb \<subseteq> b" by auto
      then obtain fc where fcmem:"fc \<in> \<F>" and "fc \<subseteq> fa" and "fc \<subseteq> fb"   using sets_pfilter2_dir[of X \<F>] is_dwdir_obtain[of \<F> fa fb] A0 by blast
      then obtain "f`fc \<subseteq> f`fc" and "f`fc \<in> Pow Y" and "f`fc \<subseteq> a" and "f`fc \<subseteq> b"
      by (meson PowD PowI bmem asub bsub ysub dual_order.trans image_mono subset_eq subset_refl)
      then show "\<exists>c \<in> ?fF. c \<subseteq> a \<and> c \<subseteq> b" using fcmem by auto
    qed
    show " is_ord_cl (Pow Y) ?fF (\<subseteq>)"
    proof(rule is_ord_clI)
      fix a b assume "a \<in> ?fF" and bmem:"b \<in> Pow Y" and asb:"a \<subseteq> b "
      then show "b \<in> ?fF" using inf.order_iff by fastforce
    qed
  qed
  show "?fF \<noteq> Pow Y"
  proof-
    have ne:"{} \<notin> \<F>"  using A0 sets_pfilter_emp by blast
    then obtain "{} \<notin> ?fF"  by auto
    then show "?fF \<noteq> Pow Y"    by blast
  qed
qed


lemma cont12:
  assumes A0:"is_prtop q X" and A1:"is_prtop p Y" and 
    A2: "\<And>x. x \<in> X \<Longrightarrow> continuous_at f X q Y p x"
  shows "\<And>x. x \<in> X \<Longrightarrow> nhood p Y (f x) \<subseteq> {E \<in> Pow Y. \<exists>F \<in> nhood q X x. f`F \<subseteq> E}"
proof-
  fix x assume A3:"x \<in> X"
  from A0 A3 obtain "(nhood q X x, x) \<in> q" by auto
  then obtain "({E \<in> Pow Y. \<exists>F \<in> nhood q X x. f`F \<subseteq> E}, f x) \<in> p"   using A2 A3 continuous_at_def by fastforce 
  then show "nhood p Y (f x) \<subseteq> {E \<in> Pow Y. \<exists>F \<in> nhood q X x. f`F \<subseteq> E}" by (simp add: Inf_lower)  
qed


lemma cont21:
  assumes A0:"is_prtop q X" and A1:"is_prtop p Y" and  A1b:"f`X \<subseteq>Y" and
    A2:"\<And>x. x \<in> X \<Longrightarrow> nhood p Y (f x) \<subseteq> {E \<in> Pow Y. \<exists>F \<in> nhood q X x. f`F \<subseteq> E}" 
  shows "\<And>x. x \<in> X \<Longrightarrow> continuous_at f X q Y p x" 
proof(rule continuousI)
  fix x \<F>  assume A3:"x \<in> X" and A4:"(\<F>, x) \<in> q" 
  then obtain B0:"nhood q X x \<subseteq> \<F>" by blast
  from A2 A3 have B1:"nhood p Y (f x) \<subseteq> {E \<in> Pow Y. \<exists>F \<in> nhood q X x. f`F \<subseteq> E}" by blast
  also have B2:"... \<subseteq>{E \<in> Pow Y. \<exists>F \<in> \<F>. f`(F) \<subseteq> E} "  using B0 by auto
  then obtain B3:"nhood p Y (f x) \<subseteq> {E \<in> Pow Y. \<exists>F \<in> \<F>. f`(F) \<subseteq> E}" using calculation by auto
  obtain B4:"is_pfilter (Pow X) \<F>" by (metis A0 A4 Int_Collect case_prodD inf.orderE pfilters_onE) 
  then have B5:"{E \<in> Pow Y. \<exists>F \<in> \<F>. f`(F) \<subseteq> E} \<in> pfilters_on (Pow Y)" using A1b im_filter[of X \<F> f Y]  pfilters_onI by blast
  have B6:"(nhood p Y (f x), f x) \<in> p"  using A1 A1b A3 by blast
  then show "({E \<in> Pow Y. \<exists>F\<in>\<F>. f ` F \<subseteq> E}, f x) \<in> p" using B3 B5 B6 A1 by blast
qed

lemma cont56:
  assumes A0:"is_prtop q X" and
          A1:"is_prtop p Y" and
     A2:"\<And>V. V \<in> nhood p Y (f x) \<Longrightarrow>(vimage f V) \<in> nhood q X x"
  shows "\<And>V. V \<in> nhood p Y (f x) \<Longrightarrow> \<exists>U \<in> nhood q X x. f`U \<subseteq> V "
proof-
  fix V assume A3:"V \<in> nhood p Y (f x)"
  then obtain A4:"f`(vimage f V) \<subseteq> V"  and A5:"vimage f V \<in> nhood q X x" using A2 by blast
  then show "\<exists>U \<in> nhood q X x. f`U \<subseteq> V" by blast
qed
              

lemma cont65:
  assumes A0:"is_prtop q X" and
          A1:"is_prtop p Y" and 
          A2:"x \<in> X" and
          A3:"vimage f Y \<subseteq> X" and A3b:"f`X \<subseteq> Y" and
     A4:"\<And>V.  V \<in> nhood p Y (f x) \<Longrightarrow> \<exists>U \<in> nhood q X x. f`U \<subseteq> V "
  shows "\<And>V. V \<in> nhood p Y (f x) \<Longrightarrow>(vimage f V) \<in> nhood q X x"
proof-
  fix V assume A5:"V \<in> nhood p Y (f x)"
  then obtain U where A6:"U \<in> nhood q X x" and A7:"f`U \<subseteq> V"  using A4 by blast
  then have A8:"U \<subseteq> vimage f (f`U)" by blast
  also have A9:"... \<subseteq> vimage f V"   using A7 by auto
  then obtain A10:"U \<subseteq>  vimage f V" and A11:"U \<in> nhood q X x" using A6 by blast
  have A11:"is_pfilter (Pow X) (nhood q X x)" using nhood_is_pfilter[of q X x] A0 A2 by fastforce
  have A12:"is_pfilter (Pow Y) (nhood p Y (f x))" using nhood_is_pfilter[of p Y "f x"]  using A1 A2 A3b by fastforce 
  have A13:"V \<subseteq> Y"   by (meson A12 A5 Pow_iff is_filterE1 is_pfilterE1 subsetD)
  have A14:"( vimage f V) \<in> Pow X"  using A13 A3 by blast 
  then show "vimage f V \<in> nhood q X x"  using A10 A11 A6 sets_pfilter_upcl by blast
qed

definition adherence where
   "adherence q X \<equiv> (\<lambda>A. {x \<in> X. \<exists>G \<in> pfilters_on (Pow X). (G, x) \<in> q \<and> A \<in> G})"
abbreviation Adh where "Adh q X \<equiv> adherence q X"

lemma adherence_props1:
  assumes A0:"pretop q X"
  shows adh3:"Adh q X {} = {}" and
        adh4:"\<And>A. A \<in> Pow X \<Longrightarrow> A \<subseteq> Adh q X A" and
        adh5:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X\<rbrakk> \<Longrightarrow> Adh q X (A \<union> B) = (Adh q X A) \<union> (Adh q X B)" and
        adh6:"\<And>A. A \<in> Pow X  \<Longrightarrow> Adh q X A = {x \<in> X. \<exists>F \<in> pfilters_on (Pow X). (F, x) \<in> q \<and> F#{A}}" and
        adh7:"\<And>A. A \<in> Pow X  \<Longrightarrow> Adh q X A = {x \<in> X. \<exists>F \<in> pfilters_on (Pow X). (F, x) \<in> q \<and> A \<in> grill (Pow X) F}"
  using A0 CCL0[of q X] adherence_def[of q X] apply presburger 
  using A0 CCL1[of q X] adherence_def[of q X] apply presburger 
  using A0 CCL2[of q X] adherence_def[of q X] apply presburger 
  using A0 adh1[of _ X q] adherence_def[of q X]  apply (smt (verit, ccfv_SIG) Pow_iff)
  using A0 adh2[of _ X q] adherence_def[of q X]  by (smt (verit, ccfv_SIG) Pow_iff)

lemma adherence_iff:
  assumes A0:"pretop q X" and A1:"x \<in> X" and A2:"A \<in> Pow X"
  shows "x \<in> Adh q X A \<longleftrightarrow> (nhood q X x)#{A}" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume L:"?lhs"
  then obtain F where "F \<in> pfilters_on (Pow X)" and  ftx:"(F, x) \<in> q" and fma:"F#{A}" using adh6[of q X A] A0 A2  by (smt (verit, del_insts) mem_Collect_eq)
  then obtain "(nhood q X x) \<subseteq> F" by blast
  then show "?rhs" using fma ftx  by (simp add: mesh_iff)
next
 assume L:"?rhs" 
 then obtain A00:"is_pfilter (Pow X) (nhood q X x)" and A01:"A \<in> Pow X" and A02:"\<forall>B \<in> (nhood q X x). B \<inter> A \<noteq> {}"
 by (smt (verit) A0 A1 A2 Ball_Collect case_prodD empty_iff mem_Collect_eq mesh_iff set_pfilter_inter singletonI subsetI)
 define H where "H \<equiv> {E \<in> Pow X. \<exists>B \<in> (nhood q X x). A \<inter> B \<subseteq> E}" 
 then obtain pfr1:"H \<subseteq> Pow X" and pfr2:"A \<in> H" and pfr3:"H \<noteq> {}" and prf4:"nhood q X x \<subseteq> H"  and pfr8:"is_pfilter (Pow X) H"
 using pfilter_refinment[of X "nhood q X x" A] A00 A01 A02 H_def  by (smt (verit, ccfv_threshold) DiffE Int_lower1 Int_lower2 double_diff dual_order.refl mem_Collect_eq sets_pfilter_sub subsetI)
 then obtain "x \<in> X" and "H \<in> pfilters_on (Pow X)" and  "(H, x) \<in> q"  and "A \<in> H" by (metis A0 A00 A1 pfilters_onI)
 then show "?lhs"  by (metis (no_types, lifting) CollectI adherence_def)
qed

lemma adherence_props2:
  assumes A0:"pretop q X" and A1:"x \<in> X" and A2:"V \<in> Pow X" 
  shows "V \<notin> nhood q X x \<longleftrightarrow> x \<notin> X-(Adh q X (X-V))" and
        "V \<in> nhood q X x \<longleftrightarrow> x \<in> X-(Adh q X (X-V))" 
proof-
  show "V \<notin> nhood q X x \<longleftrightarrow> x \<notin> X-(Adh q X (X-V))"  (is "?lhs \<longleftrightarrow> ?rhs") 
  proof
      assume L:"?lhs" then obtain F where pfl:"is_pfilter (Pow X) F" and fxq:"(F, x) \<in> q" and VnF:"V \<notin> F"   by (metis A0 A1 nhood_is_pfilter)
      then obtain "F#{X-V}"  by (meson "11372" A2 mesh_sym sets_pfilter2_upc sets_pfilter_sub)
      then obtain A01:"(X-V) \<in> Pow X" and A02:"\<forall>B \<in> F. B \<inter> (X-V) \<noteq> {}"   by (simp add: mesh_def)
      define H where "H \<equiv> {E \<in> Pow X. \<exists>B \<in> F. (X-V) \<inter> B \<subseteq> E}" 
      then obtain pfr1:"H \<subseteq> Pow X" and pfr2:"(X-V) \<in> H" and prf4:"F \<subseteq> H"  and pfr8:"is_pfilter (Pow X) H"
      using pfilter_refinment[of X F "(X-V)"] A01 A02 pfl by (smt (verit) Int_lower1 Int_lower2 in_mono mem_Collect_eq sets_pfilter_sub subsetI)
      then obtain "x \<in> (Adh q X (X-V))" using adherence_def[of q X] fxq  by (metis (mono_tags, lifting) A0 A1 CollectI pfilters_onI pfl)
      then show "?rhs" by simp
   next
      assume R:"?rhs" then obtain "x \<in> (Adh q X (X-V))"   by (simp add: A1)
      then obtain F where pfil:"is_pfilter (Pow X) F" and fxq:"(F, x) \<in> q" and  "(X-V) \<in> F" using adherence_def[of q X] pfilters_on_def[of "Pow X"] by auto
      also obtain "V \<notin> F"   using calculation(3) pfil pfilter_sets_comp by blast
      then show "?lhs" using fxq by blast
  qed
  then show "V \<in> nhood q X x \<longleftrightarrow> x \<in> X-(Adh q X (X-V))" by blast
qed


lemma adherence_props3:
  assumes A0:"pretop q X" and A1:"A \<in> Pow X" and A2:"B \<in> Pow X" and A3:" A \<subseteq> B"
  shows "Adh q X A \<subseteq> Adh q X B"
proof-
  have B0:"B-A \<in> Pow X" using A2 by blast
  have B1:"Adh q X A \<subseteq>  (Adh q X A) \<union> (Adh q X (B-A))"  by blast
  also have B2:"... = Adh q X (A \<union> (B- A))" using B0 A0 A1 adh5[of q X A "B-A"] by presburger
  also have B3:"... = Adh q X B"  using A3 Diff_partition by force
  then show ?thesis
  using calculation by auto
qed

lemma cont23:
  assumes A0:"is_prtop q X" and
          A1:"is_prtop p Y" and 
          A2:"A \<in> Pow X" and 
          A3:"f`X \<subseteq> Y" and
          A4:"\<And>x. x \<in> X \<Longrightarrow> nhood p Y (f x) \<subseteq> {E \<in> Pow Y. \<exists>F \<in> nhood q X x. f`F \<subseteq> E}"
  shows "f`(Adh q X A) \<subseteq> Adh p Y (f`A)" (is "?lhs \<subseteq> ?rhs")
proof
  fix fx assume B0:"fx \<in> ?lhs" then obtain x where B1:"x \<in>Adh q X A" and B2:"fx = (f x)"  by blast
  have B1b:"x \<in> X" by (metis (no_types, lifting) B1 CollectD adherence_def)
  then obtain B3:"(nhood q X x)#{A}" using adherence_iff[of q X x A] A0 A2 B1 by blast
  let ?fF="{E \<in> Pow Y. \<exists>F \<in> nhood q X x. f`F \<subseteq> E}"
  have B4:"(?fF)#{f`A}"
  proof(rule meshI)
    fix a b assume "a \<in> ?fF" and "b \<in> {f`A}"
    then obtain F where "F \<in> nhood q X x" and ffa:"f`F \<subseteq> a" and bfa:"b=f`A"  by fastforce
    then obtain fa where "fa \<in> F \<inter> A" using B3  by (meson all_not_in_conv insertI1 mesh_iff)
    then obtain "f fa \<in> a \<inter> b"  using bfa ffa by auto
    then show "a \<inter> b \<noteq> {}" by blast
  qed
  have B5:"nhood p Y (f x) \<subseteq> {E \<in> Pow Y. \<exists>F \<in> nhood q X x. f`F \<subseteq> E}"  using A4 B1b by presburger
  then obtain "(nhood p Y (f x))#{f`A}"  by (smt (verit) B4 mesh_iff subset_iff)
  then obtain "f x \<in>  Adh p Y (f`A)"  using adherence_iff[of p Y "f x" "f`A"] A1 A3 A2 B1b by blast
  then show "fx \<in> ?rhs"  using B2 by blast
qed

lemma cont35:
  assumes A0:"is_prtop q X" and
          A1:"is_prtop p Y" and  
          A2:"f`X \<subseteq> Y" and 
          A3:"vimage f UNIV \<subseteq> X" and 
          A5:"\<And>A. A \<in> Pow X \<Longrightarrow> f`(Adh q X A) \<subseteq> Adh p Y (f`A)"
  shows      "\<And>x V. \<lbrakk>x \<in> X; V \<in> nhood p Y (f x)\<rbrakk> \<Longrightarrow>(vimage f V) \<in> nhood q X x"
proof-
  have A7:"\<And>x V. \<lbrakk>V \<in> Pow Y;x \<in> X; (vimage f V) \<notin> nhood q X x\<rbrakk> \<Longrightarrow> V \<notin> nhood p Y (f x)"
  proof-
    fix x V assume A6a:"V \<in> Pow Y" and A6b:"x \<in> X" and A6:"(vimage f V) \<notin> nhood q X x"
    then obtain B0:"(vimage f V) \<in> Pow X"  using A3 by blast 
    then obtain B1:"x \<in> Adh q X (X-(vimage f V))" using adherence_props2[of q X x] B0 A6b A0 A5 Diff_iff A6 by metis
    then obtain B2:"(f x) \<in> Adh p Y (f`(X-(vimage f V)))" using A5 B0   by (simp add: image_subset_iff)
    then obtain B3:"(f x) \<in> Adh p Y (f`(vimage f (Y-V)))"   by (metis A2 A3 image_subset_iff_subset_vimage top.extremum_uniqueI vimage_Diff vimage_UNIV)
    obtain B4:"f`(vimage f (Y-V)) \<subseteq> Y-V" and  B5:"f`(vimage f (Y-V)) \<in> Pow Y" and B6:"(Y-V) \<in> Pow Y" by blast
    then obtain B7:" Adh p Y (f`(vimage f (Y-V))) \<subseteq>  Adh p Y (Y-V)" using A1 adherence_props3[of p Y "f`(vimage f (Y-V))" "Y-V"] by fastforce
    then obtain B8:"(f x) \<in> Adh p Y (Y-V)"  using B3 by blast
    then show "V \<notin> nhood p Y (f x)" using adherence_props2[of p Y "f x"]   using A1 A2 A6b A6a by blast 
  qed
  fix x V assume A8a:"x \<in> X" and A8:"V \<in> nhood p Y (f x)" 
  obtain B0:"f x \<in> Y" and  B1:"V \<in> Pow Y" using A2 A8a  nhood_sub[of p Y "f x" V]  A1 A8 by auto
  then show "(vimage f V) \<in> nhood q X x" using A7 A8 A8a by blast
qed


lemma cont53:
  assumes A0:"is_prtop q X" and
          A1:"is_prtop p Y" and  
          A2:"f`X \<subseteq> Y" and 
          A3:"vimage f UNIV \<subseteq> X" and 
          A5:"\<And>V x. \<lbrakk>x \<in> X; V \<in> nhood p Y (f x)\<rbrakk> \<Longrightarrow>(vimage f V) \<in> nhood q X x"
  shows      "\<And>A. A \<in> Pow X \<Longrightarrow> f`(Adh q X A) \<subseteq> Adh p Y (f`A)"
proof-
  fix A assume A6:"A \<in> Pow X"
  have B0:"\<And>x. \<lbrakk>x \<in> X; (f x) \<in> (Y-Adh p Y (f`A))\<rbrakk> \<Longrightarrow> x \<notin> Adh q X A"
  proof-
    fix x assume A7:"(f x) \<in> (Y-Adh p Y (f`A))" and A7a:"x \<in> X" then obtain B01:"(f x) \<in> Y-(Adh p Y (Y-(Y-(f`A))))" by (metis A2 A6 PowD double_diff equalityD1 image_subset_iff_subset_vimage subset_trans)
    obtain B02:"(f x) \<in> Y" and B03:"Y-(f`A) \<in> Pow Y" using A2 A6  B01  by blast
    then obtain B04:"(Y-(f`A)) \<in> nhood p Y (f x)" using B01 B02 B03 A1 adherence_props2[of p Y "f x" "Y-(f`A)"] by blast
    then obtain B05:"vimage f (Y-(f`A)) \<in> nhood q X x" using A7a A5 by blast
    have B06:"vimage f (Y-(f`A)) = X - (vimage f (f`A))"   using A2 A3 by force
    also have B07:"... \<subseteq> X - A" by blast
    then obtain B08:"vimage f (Y-(f`A)) \<inter> A = {}"   by blast
    then obtain B09:"\<not> (nhood q X x)#{A} "  by (metis B05 Int_commute mesh_singleE mesh_sym)
    then show B10:"x \<notin> Adh q X A" using adherence_iff[of q X x A] A7a A6 A0 by blast
  qed
  show "f`(Adh q X A) \<subseteq> Adh p Y (f`A)" 
  using A2 A3 B0 by auto
qed

lemma cont32:
  assumes A0:"is_prtop q X" and
          A1:"is_prtop p Y" and  
          A2:"f`X \<subseteq> Y" and 
          A3:"vimage f UNIV \<subseteq> X" and 
      A4:"\<And>A. A \<in> Pow X \<Longrightarrow> f`(Adh q X A) \<subseteq> Adh p Y (f`A)"
   shows "\<And>x. x \<in> X \<Longrightarrow> nhood p Y (f x) \<subseteq> {E \<in> Pow Y. \<exists>F \<in> nhood q X x. f`F \<subseteq> E}"
proof-
  have cont5:"\<And>x V. \<lbrakk>x \<in> X; V \<in> nhood p Y (f x)\<rbrakk> \<Longrightarrow>(vimage f V) \<in> nhood q X x" using cont35[of q X p Y f] A0 A1 A2 A3 A4 by presburger
  have cont6:"\<And>x V. \<lbrakk>x \<in> X; V \<in> nhood p Y (f x)\<rbrakk> \<Longrightarrow> \<exists>U \<in> nhood q X x. f`U \<subseteq> V " using cont56[of q X p Y f] A0 A1 cont5 by presburger
  fix x assume A5:"x \<in> X"
  show "nhood p Y (f x) \<subseteq> {E \<in> Pow Y. \<exists>F \<in> nhood q X x. f`F \<subseteq> E}"  (is "?lhs \<subseteq> ?rhs")
  proof
    fix V assume A6:"V \<in> nhood p Y (f x)"
    then obtain U where "U \<in> nhood q X x" and "f`U \<subseteq> V" using cont6 A5 A6 by meson
    also obtain "V \<in> Pow Y" using nhood_sub[of p Y "f x" V] A1 A2 A5 A6 by auto
    then show "V \<in> ?rhs" using calculation by blast
  qed
qed


lemmas closure_range_iso = 
  cl_sup_eq_sup
  cl_sup_eq_sup
  cl_sup_ge_sup_cl 
  closure_induced_clr_dual 
  closure_induced_clr_id
  closure_range_is_clattice
  clr_induced_closure_dual
  extensiveI4
  isotoneI4
  idempotentI4
  extensiveD4

lemmas cech_closure_iso=
  cc_pretop_cc
  pretop_to_cc
  pretop_cl_nh
  pretop_cc_pretop
  cc_pretop_nhf

lemmas comp_dense=cmeet_dense_iff
  compact_dense

lemmas closures=
  down_closed_infin_closed
  dw_cl_is_dw_cl
  dw_cl_cl
  dw_cl_lorc   
  dwdir_upcl_is_dwdir
  fin_inf_cl_idempotent2
  fin_inf_cl_is_cl
  fne_inf_cl_idempotent0
  fne_inf_cl_is_cl
  fne_inf_cl_obtains
  fne_sup_cl_idempotent0
  fne_sup_cl_is_cl
  fne_sup_cl_obtains 
  inf_cl_idempotent2
 inf_cl_is_cl inf_cl_obtains

lemmas galois_connections=extrema_dual_gc 
  gc_extrema_dual gc_extrema_dual2 gc_polar_pair gc_reverse2 gc_reverse21  gc_to_polar1

lemmas filter_lemmas=filter_closure_eq_closure
  filter_max_inter
  filter_on_lattice_top0
  filters_on_lattice_csup
  filters_on_top_inf_semilattice_is_cinf
  finite_ind_fil15
  finite_ind_fil5
  finite_ind_fil6
  finite_ind_in

lemmas distributivity=
  fin_distr2 inf_distributiveD2 inf_distributiveI1 

lemmas irreducibility=
  fin_inf_irrD1
  fin_inf_irrI1
  fin_inf_irrI2
  fin_irr_filter_prime
  fin_sup_irrD1
  fin_sup_irrI1
  fin_sup_irrI2
  finf_closedD1
  finf_glb
  finf_lb


unused_thms
*)


end