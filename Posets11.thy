theory Posets11
  imports Main
begin
hide_const(open) List.list.Nil
no_notation List.list.Nil ("[]")  
no_notation Cons (infixr "#" 65) 
hide_type list
hide_const rev
declare [[show_consts,show_sorts,show_types]]

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

lemma ub_binary:
  "a \<le> b \<longleftrightarrow> b ub {a, b}"
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

lemma lb_binary:
  "a \<le> b \<longleftrightarrow> a lb {a, b}"
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

lemma greatestD1:
  "is_greatest A m \<Longrightarrow> (m \<in> A \<and> m ub A)"
  by (simp add: Upper_Bounds_mem_iff is_greatest_def)

lemma greatestD11:
  "is_greatest A m \<Longrightarrow> m \<in> A"
  by (simp add: greatestD1)

lemma is_greatestD12:
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

lemma greatest_ne:
  "is_greatest A m \<Longrightarrow> A \<noteq> {}"
  using greatestD11 by auto

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

lemma lb_single_least1:
  "x \<in> X \<Longrightarrow> is_greatest (Lower_Bounds X {x}) x"
  by (simp add: Lower_BoundsD1 Lower_Bounds_singleton greatestI3)

lemma lb_single_least2:
  "x \<in> X \<Longrightarrow> Greatest (Lower_Bounds X {x}) = x"
  by (simp add: greatest_equality2 lb_single_least1)

lemma greatest_exD1:
  "(\<exists>m. is_greatest A m) \<Longrightarrow> Greatest A \<in> A"
  using greatestD11 greatest_equality2 by auto

lemma greatest_exD2:
  "(\<exists>m. is_greatest A m) \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> (Greatest A))"
  using greatestD2 greatest_equality2 by blast

lemma greatest_exD3:
  "(\<exists>m. is_greatest A m) \<Longrightarrow> (Greatest A) \<in> Upper_Bounds A A"
  using greatest_equality2 is_greatest_def by blast


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

lemma ub_single_least1:
  "x \<in> X \<Longrightarrow> is_least (Upper_Bounds X {x}) x"
  by (simp add: Upper_BoundsD1 Upper_Bounds_singleton least_iff)

lemma ub_single_least2:
  "x \<in> X \<Longrightarrow> Least (Upper_Bounds X {x}) = x"
  by (simp add: least_equality2 ub_single_least1)

lemma least_exD1:
  "(\<exists>m. is_least A m) \<Longrightarrow> Least A \<in> A"
  using leastD1 least_equality2 by blast

lemma least_exD2:
  "(\<exists>m. is_least A m) \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (Least A) \<le> a)"
  using leastD2 least_equality2 by blast

lemma least_exD3:
  "(\<exists>m. is_least A m) \<Longrightarrow> (Least A) \<in> Lower_Bounds A A"
  using is_least_def least_equality2 by auto

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
  by (meson Upper_BoundsD1 greatestD11 greatestI4 is_greatestD12 is_supD11 is_supI114 subsetD)

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

lemma binary_sup_iff:
  "\<lbrakk>x1 \<in> X; x2 \<in> X\<rbrakk> \<Longrightarrow> (x1 \<le> x2 \<longleftrightarrow> is_sup X {x1, x2} x2)"
  by(auto simp add:binary_supI1 binary_supD1)

subsubsection Operator

definition Sup::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order" where
  "Sup X A \<equiv> (THE m. is_sup X A m)"

lemma sup_equality:
  "is_sup X A m \<Longrightarrow> Sup X A = m"
  by (simp add: Sup_def is_sup_unique the_equality) 

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

subsubsection Operator

definition Inf::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> 'a::order" where
  "Inf X A \<equiv> (THE m. is_inf X A m)"

lemma inf_equality:
  "is_inf X A m \<Longrightarrow> Inf X A = m"
  by (simp add: Inf_def is_inf_unique the_equality) 

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

lemma Lower_eq_inf_eq:
  "Lower_Bounds X A = Lower_Bounds X B \<Longrightarrow> (is_inf X A i \<longleftrightarrow> is_inf X B i)"
  by (simp add: is_inf_def)

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
         

subsection ClosureRanges

definition is_clr::"'a::order set \<Rightarrow> 'a::order set \<Rightarrow> bool" where
  "is_clr C X \<equiv> (C \<noteq> {}) \<and> (C \<subseteq> X) \<and> (\<forall>x. x \<in> X \<longrightarrow> (\<exists>c. is_least (Upper_Bounds C {x}) c))"

lemma clrI1:
  "\<lbrakk>C \<noteq> {}; C \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> (\<exists>c. is_least (Upper_Bounds C {x}) c)) \<rbrakk> \<Longrightarrow> is_clr C X"
  by (simp add:is_clr_def)

lemma clrI2:
  "\<lbrakk>C \<noteq> {}; C \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> (\<exists>c. is_sup C {x} c)) \<rbrakk> \<Longrightarrow> is_clr C X"
  by (simp add: is_clr_def is_sup_def)

lemma clrD1:
  "is_clr C X \<Longrightarrow> C \<noteq> {}"
  by (simp add:is_clr_def)

lemma clrD2:
  "is_clr C X \<Longrightarrow> C \<subseteq> X"
  by (simp add:is_clr_def)

lemma clrD3:
  "is_clr C X \<Longrightarrow>  (\<forall>x. x \<in> X \<longrightarrow> (\<exists>c. is_least (Upper_Bounds C {x}) c))"
  by (simp add:is_clr_def)

lemma clrD3b:
  "is_clr C X \<Longrightarrow>  (\<forall>x. x \<in> X \<longrightarrow> (\<exists>c. is_sup C {x} c))"
  by (simp add: clrD3 is_sup_def)

lemma clrD4:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> (\<exists>c. is_least (Upper_Bounds C {x}) c)"
  by (simp add:is_clr_def)

lemma clrD5:
  "is_clr C X \<Longrightarrow>  (\<forall>x. x \<in> X \<longrightarrow> ((Upper_Bounds C {x}) \<noteq> {}))"
  using clrD3 least_ne by blast

lemma clrD7:
  "is_clr C X \<Longrightarrow>  x \<in> X \<Longrightarrow> (\<exists>c. c \<in> C \<and> x \<le> c)"
  by (meson Upper_BoundsD2 clrD3 is_supD1121 is_supI1 leastD11 singletonI)

lemma is_clr_cofinal:
  "is_clr C X \<Longrightarrow> is_greatest X m \<Longrightarrow> m \<in> C"
  using clrD2 greatestD11 clrD7 is_greatestD12 ubD by fastforce

definition cl_from_clr::"'a::order set \<Rightarrow> ('a::order \<Rightarrow> 'a::order)" where
  "cl_from_clr C \<equiv> (\<lambda>x. Least (Upper_Bounds C {x}))"

lemma cl_range1:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> (cl_from_clr C) x \<in> C"
  by (metis Upper_BoundsD2 cl_from_clr_def clrD3 least_equality1 least_iff)

lemma cl_range2:
  "is_clr C X  \<Longrightarrow> (cl_from_clr C)`X \<subseteq> C"
  using cl_range1 by blast

lemma cl_range3:
  "is_clr C X  \<Longrightarrow> x \<in> C \<Longrightarrow> (cl_from_clr C) x = x"
  by (simp add: cl_from_clr_def ub_single_least2)

lemma cl_range4:
  "is_clr C X  \<Longrightarrow> (cl_from_clr C)`C = C"
  by (simp add: cl_range3)

lemma cl_range5:
  "is_clr C X  \<Longrightarrow>  (cl_from_clr C)`X = C"
  by (metis cl_range2 cl_range4 clrD2 image_mono order_antisym)

lemma cl_ext1:
  "is_clr C X \<Longrightarrow> x \<in> X \<Longrightarrow> x \<le> (cl_from_clr C) x"
  by (metis Upper_BoundsD1 cl_from_clr_def clrD3 leastD11 least_equality2 singletonI)

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
  by (meson cl_ext1 cl_lt_ub2 cl_range1 order.trans)

lemma cl_iso2:
  "is_clr C X \<Longrightarrow> is_isotone X (cl_from_clr C)"
  by (simp add: cl_iso1 is_isotone_def)

lemma cl_ide:
  "is_clr C X \<Longrightarrow> is_idempotent X (cl_from_clr C) "
  by (simp add: cl_range1 cl_range3 is_idempotent_def)

lemma cl_is_closure:
  "is_clr C X \<Longrightarrow> is_closure X (cl_from_clr C)"
  by(simp add:is_closure_def cl_ext2 cl_ide cl_iso2 cl_range5 clrD2)

lemma closure_of_in_ub:
  "is_closure X f \<Longrightarrow>x \<in> X \<Longrightarrow> (f x) \<in> (Upper_Bounds (f`X) {x})"
  by (simp add: Upper_Bounds_singleton2 closureD5)

lemma closure_of_lt_ub:
  "is_closure X f \<Longrightarrow>x \<in> X \<Longrightarrow> y \<in>  (Upper_Bounds (f`X) {x}) \<Longrightarrow> (f x) \<le> y"
  by (meson Upper_BoundsD1 Upper_BoundsD2 cl_le_cl_iff_le singleton_iff)

lemma closure_of_least_closed1:
  "is_closure X f \<Longrightarrow> x \<in> X \<Longrightarrow> is_least (Upper_Bounds (f`X) {x}) (f x)"
  by (simp add: closure_of_in_ub closure_of_lt_ub leastI3)

lemma closure_of_least_closed2:
  "is_closure X f \<Longrightarrow> x \<in> X \<Longrightarrow> Least (Upper_Bounds (f`X) {x}) =  (f x)"
  by (simp add: closure_of_in_ub closure_of_lt_ub least_equality2 least_iff)

lemma closure_induced_clr:
  "is_closure X f \<Longrightarrow> X \<noteq> {} \<Longrightarrow> is_clr (f`X) X"
  by (metis closure_of_least_closed1 empty_is_image is_closure_def is_clr_def)

lemma closure_induced_clr_id1:
  "is_closure X f \<Longrightarrow> X \<noteq> {} \<Longrightarrow> x  \<in> X \<Longrightarrow> (cl_from_clr (f`X)) x = f x"
  by (simp add: cl_from_clr_def closure_of_least_closed2)

lemma closure_induced_clr_id2:
  "is_closure X f \<Longrightarrow> X \<noteq> {} \<Longrightarrow> (\<forall>x. x  \<in> X \<longrightarrow> (cl_from_clr (f`X)) x = f x)"
  by (simp add: cl_from_clr_def closure_of_least_closed2)

lemma closure_induced_clr_dual1:
  "is_closure X f1 \<Longrightarrow> is_closure X f2 \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> f1 x \<le> f2 x) \<Longrightarrow> (f2`X) \<subseteq> (f1`X)"
  by (metis closureD11 closureD2 idempotentD3 is_closure_def subsetI)
                    
lemma clr_induced_closure_dual1:
  "is_clr C1 X \<Longrightarrow> is_clr C2 X \<Longrightarrow> C2 \<subseteq> C1 \<Longrightarrow>  x \<in> X \<Longrightarrow> ((cl_from_clr C1) x) \<le> ((cl_from_clr C2) x)"
  by (simp add: cl_ext1 cl_lt_ub2 cl_range1 subsetD)

lemma clr_induced_closure_dual2:
  "is_clr C1 X \<Longrightarrow> is_clr C2 X \<Longrightarrow> C2 \<subseteq> C1 \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> ((cl_from_clr C1) x) \<le> ((cl_from_clr C2) x))"
  by (simp add: clr_induced_closure_dual1)

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

definition is_dir::"'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "is_dir X ord \<equiv> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>c \<in> X. ord a c \<and> ord b c))"

definition is_ord_cl::"'a set \<Rightarrow> 'a set \<Rightarrow>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "is_ord_cl X A ord \<equiv> (\<forall>a b. a \<in> A \<and> b \<in> X \<and> ord a b \<longrightarrow> b \<in> A )"

lemma is_dwdirE1:
  "is_dir (X::'a::order set) (\<le>)  \<Longrightarrow> a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> (\<exists>c \<in> X. a \<le> c \<and> b \<le> c) "
  by (simp add: is_dir_def)

lemma is_updirE1:
  "is_dir (X::'a::order set) (\<ge>)  \<Longrightarrow> a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> (\<exists>c \<in> X. a \<ge> c \<and> b \<ge> c) "
  by (simp add: is_dir_def)

lemma is_ord_clE1:
  "is_ord_cl (X::'a::order set) A (\<le>)  \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> X \<Longrightarrow> a \<le> b \<Longrightarrow> b \<in> A "
  by (simp add:is_ord_cl_def)

lemma is_ord_clE2:
  "is_ord_cl (X::'a::order set) A (\<ge>)  \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> X \<Longrightarrow> b \<le> a \<Longrightarrow> b \<in> A "
  by (simp add:is_ord_cl_def)

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





end