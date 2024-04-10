theory Posets21
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

lemma int_to_ind_int:
  "(\<And>(A::'a set set). P A \<Longrightarrow> Q (\<Inter>A)) \<Longrightarrow> (\<And>(f::('b \<Rightarrow> 'a set)) (I::'b set). P(f`I) \<Longrightarrow> Q(\<Inter>i \<in> I. f i))" 
  by simp

definition Pow_ne::"'a set \<Rightarrow> 'a set set" where 
  "Pow_ne X = Pow X - {{}}"

definition Fpow_ne::"'a set \<Rightarrow> 'a set set" where 
  "Fpow_ne X = Fpow X - {{}}"

lemma pow_ne_iff1:
  "A \<in> Pow_ne X \<longleftrightarrow> A \<in> Pow X \<and> A \<noteq> {}" by (simp add: Pow_ne_def)

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
  "A \<in> Pow_ne X \<Longrightarrow> A \<noteq> {} " 
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

lemma fpow_neD2:
  "A \<in> Fpow_ne X \<Longrightarrow> A \<noteq> {} " 
  by (simp add: fpow_ne_iff2)

lemma fpow_neD3:
  "A \<in> Fpow_ne X \<Longrightarrow> finite A " 
  by (simp add: fpow_ne_iff2)

lemma fpow_ne_iso0:
  "A \<in> Fpow_ne X \<Longrightarrow> B \<in> Fpow_ne A \<Longrightarrow> B \<subseteq> X" 
  by (drule fpow_neD1)+ simp

lemma fpow_ne_bot:
  "{} \<notin> Fpow_ne X"
  by (simp add: fpow_ne_iff1)

lemma ne_subset_ne:
  "A \<subseteq> B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> B \<noteq> {}" 
  by blast

lemma fpow_neD4:
  "A \<in> Fpow_ne X  \<Longrightarrow> A \<subseteq> X \<and> finite A \<and> A \<noteq> {}"
  by (simp add: fpow_ne_iff2)


lemma leq_iff_leq_eq:
  "\<lbrakk>a \<in> X; b \<in> X; antisym_on X R; (a, a) \<in> R; (b, b) \<in> R\<rbrakk> \<Longrightarrow> (\<forall>x \<in> X. (x, a) \<in> R \<longleftrightarrow> (x, b)\<in>R) \<Longrightarrow> a =b" 
  by (simp add: antisym_onD)

lemma geq_iff_geq_eq:
  "\<lbrakk>a \<in> X; b \<in> X; antisym_on X R;(a, a) \<in> R; (b, b) \<in> R\<rbrakk> \<Longrightarrow> (\<forall>x \<in> X. (a, x) \<in> R \<longleftrightarrow> (b, x) \<in> R) \<Longrightarrow> a =b" 
  by (simp add: antisym_onD)



section Definitions
subsection Bounds
definition ub::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"  where 
  "ub R A x \<equiv> (\<forall>a. a \<in> A \<longrightarrow> (a, x) \<in> R)"

abbreviation lb where
   "lb R A x \<equiv> ub (converse R) A x"

definition ubd::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where  
  "ubd R X A \<equiv> {b \<in> X. ub R A b}"

abbreviation lbd where 
  "lbd R X A \<equiv> ubd (converse R) X A"

subsection ExtremeElements
definition is_greatest::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
   "is_greatest R A m \<equiv> m \<in> ubd R A A"

abbreviation is_least::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
   "is_least R A m \<equiv> is_greatest (converse R) A m"

definition Greatest::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a" where
  "Greatest R A \<equiv> (THE m. is_greatest R A m)"

definition Least::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a" where
  "Least R A \<equiv> (THE m. is_least R A m)"

definition is_sup::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where 
  "is_sup R X A x \<equiv> (is_least R (ubd R X A) x)"

abbreviation is_inf::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where 
  "is_inf R X A x \<equiv> is_sup (converse R) X A x"

definition Sup::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where  
  "Sup R X A \<equiv> (THE m. is_sup R X A m)"

abbreviation Inf::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where  
  "Inf R X A \<equiv> (THE m. is_sup (converse R) X A m)"

subsection Lattices
definition is_sup_semilattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_sup_semilattice R X \<equiv> (X \<noteq> {}) \<and> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>x. is_sup R X {a, b} x))"

definition is_fsup_closed::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_fsup_closed R X A \<equiv> (\<forall>a1 a2. a1 \<in> A \<and>  a2 \<in> A \<longrightarrow> Sup R X {a1, a2} \<in> A)"

abbreviation is_inf_semilattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_inf_semilattice R X \<equiv> (X \<noteq> {}) \<and> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>x. is_sup (converse R) X {a, b} x))"

abbreviation is_finf_closed::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_finf_closed R X A \<equiv> (\<forall>a1 a2. a1 \<in> A \<and>  a2 \<in> A \<longrightarrow> Sup (converse R) X {a1, a2} \<in> A)"

definition is_lattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "is_lattice R X \<equiv> ((X \<noteq> {}) \<and> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>x. is_inf R X {a, b} x) \<and>  (\<exists>x. is_sup R X {a, b} x)))"

definition sup_distributive where
  "sup_distributive R X \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. \<forall>x \<in> X. (x,Sup R X {a, b})\<in>R \<longrightarrow> (\<exists>a1 b1. a1 \<in> X \<and> b1 \<in> X \<and> (a1, a)\<in>R \<and> (b1, b)\<in>R \<and> x = Sup R X {a1, b1}))"

definition inf_distributive where
  "inf_distributive R X \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. \<forall>x \<in> X.  Inf R X {a, b} \<le> x \<longrightarrow> (\<exists>a1 b1. a1 \<in> X \<and> b1 \<in> X \<and> (a,a1)\<in>R \<and> (b,b1)\<in>R \<and> x = Inf R X {a1, b1}))"

definition distributive_lattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "distributive_lattice R X \<equiv> (is_lattice R X) \<and> (\<forall>x \<in> X. \<forall>y \<in> X. \<forall>z \<in> X. Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}})"

definition is_csup_semilattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_csup_semilattice R X \<equiv> (X \<noteq> {}) \<and> (\<forall>A. A \<subseteq> X \<and> A \<noteq> {} \<longrightarrow> (\<exists>x. is_sup R X A x))"

definition is_csup_closed::"'a rel \<Rightarrow>'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_csup_closed R X A \<equiv> (\<forall>E. E \<subseteq> A \<longrightarrow> E \<noteq>{} \<longrightarrow> Sup R X E \<in> A)"

definition is_cinf_semilattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_cinf_semilattice R X \<equiv> (X \<noteq> {}) \<and> (\<forall>A. A \<subseteq> X \<and> A \<noteq> {} \<longrightarrow> (\<exists>x. is_inf R X A x))"

definition is_cinf_closed::"'a rel \<Rightarrow>'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_cinf_closed R X A \<equiv> (\<forall>E. E \<subseteq> A \<longrightarrow> E \<noteq>{} \<longrightarrow> Inf R X E \<in> A)"

definition is_clattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_clattice R X \<equiv> (X \<noteq> {}) \<and> (\<forall>A. A \<subseteq> X \<longrightarrow> (\<exists>s. is_sup R X A s))"

definition subsemilattice_inf::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "subsemilattice_inf R X A\<equiv> (A \<subseteq> X) \<and> (\<forall>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>i \<in> A. is_inf R X {a, b} i))"

definition subsemilattice_sup::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "subsemilattice_sup R X A\<equiv> (A \<subseteq> X) \<and> (\<forall>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>i \<in> A. is_sup R X {a, b} i))"

definition sublattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "sublattice R X A\<equiv> (A \<subseteq> X) \<and> (\<forall>a b. a \<in> A \<and> b \<in> A \<longrightarrow> (\<exists>s \<in> A. is_sup R X {a, b} s) \<and> (\<exists>i \<in> A. is_inf R X {a, b} i))"


subsection SpecialSets
definition is_dir::"'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where 
  "is_dir X R \<equiv> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>c \<in> X.  (a, c) \<in> R \<and>  (b, c) \<in> R))"

definition is_ord_cl::"'a set \<Rightarrow> 'a set\<Rightarrow> 'a rel \<Rightarrow> bool" where
   "is_ord_cl X A R \<equiv> (\<forall>a b. a \<in> A \<and> b \<in> X \<and>  (a, b) \<in> R \<longrightarrow> b \<in> A )"

definition is_filter::"'a rel \<Rightarrow> 'a set\<Rightarrow> 'a set \<Rightarrow> bool" where 
  "is_filter R X F \<equiv> F \<noteq> {} \<and> F \<subseteq> X \<and> (is_dir F (converse R)) \<and> is_ord_cl X F R"

abbreviation is_ideal ::"'a rel \<Rightarrow> 'a set\<Rightarrow> 'a set \<Rightarrow> bool" where 
  "is_ideal  R X I \<equiv> is_filter (converse R) X I"

definition is_pfilter::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "is_pfilter R X A \<equiv> (is_filter R X A) \<and> X \<noteq> A"

abbreviation is_pideal::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "is_pideal R X A \<equiv> is_pfilter (converse R) X A"

definition filters_on::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "filters_on R X \<equiv> {F. is_filter R X F}"

definition pfilters_on::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "pfilters_on R X \<equiv> {F. is_pfilter R X F}"

definition filter_closure::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where 
  "filter_closure R X A \<equiv> if A={} then {Greatest R X} else {x \<in> X. \<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and> (Inf R X F,  x) \<in> R}"

definition binary_filter_sup::"'a rel \<Rightarrow> 'a set \<Rightarrow>'a set\<Rightarrow> 'a set \<Rightarrow> 'a set" where 
  "binary_filter_sup R X A B = {x \<in> X. \<exists>a \<in> A. \<exists>b \<in> B. (Inf R X {a, b}, x) \<in> R}"

definition lorc::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a set" where 
  "lorc R X a \<equiv> {y \<in> X. (a, y) \<in> R} "

abbreviation rolc where 
  "rolc R X a \<equiv> lorc (converse R) X a"

definition ord_cl_sets::"'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set set" where 
  "ord_cl_sets X R \<equiv> {A. A \<subseteq> X \<and> is_ord_cl X A R}"

definition up_cl::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where 
  "up_cl R X A = {x \<in> X. \<exists>a \<in> A. (a, x) \<in> R}"

abbreviation dw_cl::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where 
  "dw_cl R X A \<equiv> up_cl (converse R) X A"

subsection SpecialElements
definition is_compact::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where 
  "is_compact R X c \<equiv> c \<in> X \<and> (\<forall>A. A \<in> Pow_ne X \<and> (c, Sup R X A) \<in> R \<longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> (c, Sup R X A0) \<in> R))"

definition compact_elements::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set" where 
  "compact_elements R X \<equiv> {c. is_compact R X c}"

definition compactly_generated::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "compactly_generated R X \<equiv> (\<forall>x. x \<in> X \<longrightarrow> (\<exists>C \<in> Pow (compact_elements R X). is_sup R X C x))"

definition join_dense::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "join_dense R X D \<equiv> (\<forall>x \<in> X. \<exists>Dx \<in> Pow D. is_sup R X Dx x)"

abbreviation meet_dense::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "meet_dense R X D \<equiv> join_dense (converse R) X D"

definition sup_prime::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "sup_prime R X A \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. (Sup R X {a, b}) \<in> A \<longrightarrow> (a \<in> A \<or> b \<in> A))"

abbreviation inf_prime::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "inf_prime R X A \<equiv> sup_prime (converse R) X A"

definition elem_sup_prime::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where 
  "elem_sup_prime R X x \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. (x, Sup R X {a, b}) \<in> R \<longrightarrow> ((x,  a) \<in> R \<or> (x, b) \<in> R))"

abbreviation elem_inf_prime::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where 
  "elem_inf_prime R X x \<equiv> elem_sup_prime (converse R) X x"

definition fin_sup_irr::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where  
  "fin_sup_irr R X x \<equiv> (\<forall>a \<in> X. \<forall>b \<in> X. x = Sup R X {a, b} \<longrightarrow> (x = a \<or> x = b))" 

abbreviation fin_inf_irr::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where 
  "fin_inf_irr R X x \<equiv> fin_sup_irr (converse R) X x"

definition meet_reducible::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where 
  "meet_reducible R X x \<equiv> (\<exists>A \<in> Pow_ne X. x \<notin> A \<and> is_inf R X A x)"

abbreviation meet_irr where 
  "meet_irr R X x \<equiv> \<not>(meet_reducible R X x)"

subsection Functions
definition isotone::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'b rel  \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where 
  "isotone Rx X Ry f \<equiv> (\<forall>x1 \<in> X. \<forall>x2 \<in> X. (x1, x2) \<in> Rx \<longrightarrow> (f x1, f x2) \<in> Ry)"

abbreviation antitone::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'b rel  \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
   "antitone Rx X Ry f \<equiv> isotone Rx X (converse Ry) f"

definition extensive::"'a rel \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where 
  "extensive R X f \<equiv> (\<forall>x. x \<in> X \<longrightarrow> (x, f x) \<in> R)"

definition idempotent::"'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where 
  "idempotent X f \<equiv> (\<forall>x. x \<in> X \<longrightarrow> f (f x) = f x)"

definition closure::" 'a rel \<Rightarrow> 'a set  \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow>  bool" where  
  "closure R X f \<equiv> extensive R X f \<and> idempotent X f \<and> isotone R X R f \<and> (f`X \<subseteq> X)"

definition closure_cond::"'a rel \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "closure_cond R X f \<equiv> (\<forall>x1 x2. x1 \<in> X \<longrightarrow> x2 \<in> X \<longrightarrow> (x1, f x2) \<in> R \<longrightarrow> (f x1, f x2) \<in> R)"

definition closure_range::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where 
  "closure_range R X C\<equiv> C \<noteq> {} \<and> (C \<subseteq> X) \<and> (\<forall>x. x \<in> X \<longrightarrow> (\<exists>c. is_least R  (ubd R C {x}) c))"
  
abbreviation clr where 
  "clr R X C \<equiv> closure_range R X C"

definition extrema_dual::"('a \<Rightarrow> 'b) \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> 'b rel \<Rightarrow> 'b set  \<Rightarrow> bool" where
  "extrema_dual f Rx X Ry Y \<equiv>(\<forall>A. A \<subseteq> X \<longrightarrow> f (Sup Rx X A) = Inf Ry Y (f`A))"

definition dual_adj::"('a \<Rightarrow> 'b) \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> 'b rel \<Rightarrow> 'b set \<Rightarrow> ('b \<Rightarrow> 'a)" where
  "dual_adj f Rx X Ry Y \<equiv> (\<lambda>y. Sup Rx X {x \<in> X. (y,f x)\<in>Ry})"

definition rel_from_pair::"('a set \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> ('b set \<Rightarrow> 'a set) \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set" where
  "rel_from_pair f X g Y \<equiv> {(x, y). (x, y) \<in> (X \<times> Y) \<and> y \<in> f {x}}"

definition lgc_from_rel::"('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a set \<Rightarrow> 'b set)" where
  "lgc_from_rel R X Y \<equiv> (\<lambda>A. {y. y \<in> Y \<and> (\<forall>x. x \<in> A \<longrightarrow> (x, y) \<in> R)})"

definition rgc_from_rel::"('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('b set \<Rightarrow> 'a set)" where
  "rgc_from_rel R X Y \<equiv> (\<lambda>B. {x. x \<in> X \<and> (\<forall>y. y \<in> B \<longrightarrow> (x, y) \<in> R)})"

definition galois_conn::"('a \<Rightarrow> 'b) \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'b rel \<Rightarrow> 'b set \<Rightarrow> bool" where
  "galois_conn f Rx X g Ry Y \<equiv> (f`X \<subseteq> Y) \<and> (g`Y \<subseteq> X) \<and> (\<forall>x \<in> X. \<forall>y \<in> Y.  ((x,g y)\<in>Rx \<longleftrightarrow> (y,f x)\<in>Ry))"

abbreviation antisym where 
  "antisym R X \<equiv> antisym_on X R"

abbreviation trans where 
  "trans R X \<equiv> trans_on X R"

abbreviation ord where 
  "ord R X \<equiv> antisym_on X R \<and> trans R X"

definition refl::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "refl R X \<equiv> (\<forall>x. x \<in> X \<longrightarrow> (x, x) \<in> R)"

abbreviation preord where
  "preord R X \<equiv> trans R X \<and> refl R X"

abbreviation pord where
  "pord R X \<equiv> trans R X \<and> antisym_on X R \<and> refl R X"

abbreviation dual where
  "dual R \<equiv> (converse R)"

definition diag::"'a set \<Rightarrow> 'a rel" where
  "diag X \<equiv> {(x, x). x \<in> X}"

definition ord_embedding::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'b rel \<Rightarrow> ('a \<Rightarrow> 'b)  \<Rightarrow> bool" where
  "ord_embedding Rx X Ry f \<equiv> (\<forall>x1 x2. x1 \<in> X \<and> x2 \<in> X \<longrightarrow> ((x1,x2)\<in>Rx  \<longleftrightarrow> (f x1,f x2)\<in>Ry))"

definition ord_isomorphism::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'b rel \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b)  \<Rightarrow> bool" where
  "ord_isomorphism Rx X Ry Y f \<equiv> ord_embedding Rx X Ry f \<and> f`X=Y"

section Bounds
subsection UpperBoundsPredicate


lemma reflI1:
  "(\<And>x. x \<in> X \<Longrightarrow> (x,x)\<in>R) \<Longrightarrow> refl R X" 
  by(simp add:refl_def)

lemma reflD1:
  "refl R X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> (x,x)\<in>R)" 
  by(simp add:refl_def)

lemma reflD2:
  "refl R X \<Longrightarrow> x \<in> X \<Longrightarrow> (x,x) \<in>R"
  by (simp add: reflD1)

lemma reflE1:
  "refl R X \<Longrightarrow> ((\<And>x. x \<in> X \<Longrightarrow> (x,x)\<in>R) \<Longrightarrow> thesis) \<Longrightarrow> thesis" 
  by(simp add:refl_def)

lemma refl_dualI:
  "refl R X \<Longrightarrow> refl (dual R) X"
  by (simp add: refl_def)

lemma refl_dualI2:
  "refl (dual R) X \<Longrightarrow> refl R X"
  by (simp add: refl_def)

lemma refl_iff:
  "refl (dual R) X \<longleftrightarrow> refl R X"
  using refl_dualI refl_dualI2 by blast

lemma refl_dualE:
  "refl (dual R) X \<Longrightarrow> (\<And>R X. refl R X \<Longrightarrow> P) \<Longrightarrow> P"
  using refl_def by auto

lemma refl_subset:
  "refl R X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> refl R A"
  by (simp add: in_mono refl_def)

lemma refl_empty1[simp]:
  "refl {} {}"
  by (simp add: refl_def)

lemma refl_empty2[simp]:
  "refl R {}"
  by (simp add: refl_def)

lemma refl_singleton[simp]:
  "refl  {(x,x)} {x}"
  by (simp add: refl_def)

lemma refl_in:
  "(\<And>i. i \<in> I \<Longrightarrow> refl (R i) (X i)) \<Longrightarrow> refl (\<Inter>(R`I)) (\<Inter>(X`I))"
  by (simp add: refl_def)

lemma refl_un:
  "(\<And>i. i \<in> I \<Longrightarrow> refl (R i) (X i)) \<Longrightarrow> refl (\<Union>(R`I)) (\<Union>(X`I))"
  by(rule reflI1, auto dest: reflD2)

lemma ub_iff1:
  "ub R A x \<longleftrightarrow> (\<forall>a \<in> A. (a, x)\<in>R)" 
  by(auto simp add:ub_def)

lemma ubI:
  "(\<And>a. a \<in> A \<Longrightarrow> (a, x) \<in> R) \<Longrightarrow> ub R A x" 
  by (simp add:ub_def)

lemma ubI2:
  "(\<forall>a. a \<in> A \<longrightarrow> (a, x) \<in> R) \<Longrightarrow> ub R A x"
  by (simp add: ubI)

lemma ubE:
  "ub R A x \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (a, x) \<in> R)"
  by (simp add: ub_def)

lemma ub_ant2:
  "\<lbrakk>A \<subseteq> B; ub R B x\<rbrakk> \<Longrightarrow> ub R A x"
   by (simp add:ub_def subsetD)

lemma ub_iso1:
  "\<lbrakk>x \<in> A; y \<in> A; trans R A; (x, y)\<in>R; ub R A x\<rbrakk> \<Longrightarrow> ub R A y" 
  by(intro ubI, rule_tac ?A="A" and ?r="R" and ?x="a" and ?y="x" and ?z="y" in trans_onD, simp+, erule ubE, simp+)

lemma ub_iso1b:
  "\<lbrakk>x \<in> A; y \<in> A; A \<subseteq> X;trans R X; (x, y)\<in>R; ub R A x\<rbrakk> \<Longrightarrow> ub R A y" 
  using ub_iso1[of x A y R] trans_on_subset[of X R A] by blast
  
lemma ub_empty:
  "ub R {} x"
  by (simp add: ub_def)

lemma ub_singleton:
  "(x, x) \<in> R \<Longrightarrow> ub R {x} x"
  by (simp add: ub_def)

lemma ub_singletonI:
  "ub R {y} x \<Longrightarrow>(y, x) \<in> R"
  by (simp add: ubE)

lemma ub_singletonD:
  "(y, x) \<in> R \<Longrightarrow> ub R {y} x"
  by (simp add: ub_def)

lemma ub_singleton_simp:
  "ub R {y} x \<longleftrightarrow>(y, x) \<in> R"
  by (simp add: ub_def)

lemma ub_insert:
  "\<lbrakk>ub R F c; (x, c) \<in> R\<rbrakk> \<Longrightarrow> ub R (insert x F) c"
  by (simp add: ub_def)

lemma ub_binaryI:
  "(a, b) \<in> R \<Longrightarrow> (b, b) \<in> R \<Longrightarrow> ub R {a, b} b"
  by (simp add: ub_insert ub_singleton)

lemma ub_binary_iff1:
  "(a, b) \<in> R \<and> (b, b) \<in> R \<longleftrightarrow> ub R {a, b} b"
  by (simp add: ub_iff1)

lemma ub_doubleE1:
  "ub R {a, b} c \<Longrightarrow> (a, c) \<in> R"
  by (simp add: ubE)

lemma ub_doubleE2:
  "ub R {a, b} c \<Longrightarrow> (b, c) \<in> R"
  by (simp add: ubE)

lemma ub_doubleI:
  "\<lbrakk>(a, c) \<in> R; (b, c) \<in> R\<rbrakk> \<Longrightarrow> ub R {a, b} c"
  by (simp add: ub_empty ub_insert)

lemma ub_double_iff1:
  "ub R {a, b} c \<longleftrightarrow>(a, c) \<in> R \<and> (b, c) \<in> R"
  by(auto, erule ub_doubleE1, erule ub_doubleE2, erule ub_doubleI, simp)

lemma ub_unionI:
  "\<lbrakk>ub R A x; ub R B x\<rbrakk> \<Longrightarrow> ub R (A \<union> B) x"
  by (simp add: ub_def)


lemma ub_unI:
  "(\<And>A. A \<in> S \<Longrightarrow> ub R A x) \<Longrightarrow> ub R (\<Union>S) x"
  by (simp add: ub_iff1)

lemma ub_unD:
  "ub R (\<Union>S) x \<Longrightarrow> A \<in> S \<Longrightarrow> ub R A x"
  using ub_ant2[of A "\<Union>S" R x] by blast

lemma ub_imageI:
  "(\<And>a. a \<in> A \<Longrightarrow> (f a, x) \<in> R) \<Longrightarrow> ub R (f`A) x"
  using image_p[of A "\<lambda>a. (a, x) \<in> R" f]
  by(simp add:ub_def image_p[of A "\<lambda>a. (a, x) \<in> R" f])

lemma fbdE1:
  "ub R (f`I) b \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> (f i, b) \<in> R)"
   by(auto intro:ubE)

lemma fbdI1:
  "(\<And>i. i \<in> I \<Longrightarrow> (f i, b) \<in> R) \<Longrightarrow> ub R (f`I) b"
  by (simp add: ub_imageI)


subsection UpperBoundsSet


lemma ubdI:
  "\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> (a, b)\<in>R); b \<in> X\<rbrakk> \<Longrightarrow> b \<in> ubd R X A"
   by(simp add: ubd_def ubI)

lemma fubdI1:
  "\<lbrakk>(\<And>i. i \<in> I \<Longrightarrow> (f i, b) \<in> R); b \<in> X\<rbrakk> \<Longrightarrow> b \<in> ubd R X (f`I)"
  by (simp add: ubd_def fbdI1)

lemma ubdI2:
  "\<lbrakk>ub R A b; b \<in> X\<rbrakk> \<Longrightarrow> b \<in> ubd R X A"
  by (simp add: ubdI ub_def) 

lemma fubdI2:
  "\<lbrakk>ub R (f`I) b; b \<in> X\<rbrakk> \<Longrightarrow> b \<in> ubd R X (f`I)"
  by (simp add: ubdI2)

lemma ubdD1:
  "\<lbrakk>b \<in> ubd R X A; x \<in> A\<rbrakk> \<Longrightarrow> (x, b)\<in>R"
  by (simp add: ubd_def ub_def)

lemma ubdD2:
  "b \<in> ubd R  X A \<Longrightarrow> b \<in> X"
  by (simp add: ubd_def)

lemma ubdD3:
  "b \<in> ubd R  X A \<Longrightarrow> ub R A b"
  by (simp add: ubd_def)

lemma ubd_mem_iff:
  "b \<in> ubd R  X A \<longleftrightarrow> (b \<in> X \<and> ub R A b)" 
   by(simp add: ubd_def)

lemma ubd_mem_iff2:
  "b \<in> ubd R  X A \<longleftrightarrow> (b \<in> X \<and> (\<forall>a. a \<in> A \<longrightarrow>  (a, b)\<in>R))"
  by (simp add: ubd_mem_iff ub_def)

lemma ubd_mem_iff3:
  "b \<in> ubd R  X A \<longleftrightarrow> (b \<in> X \<and> (\<forall>a \<in> A. (a, b)\<in>R))"
  by (simp add: ubd_mem_iff ub_iff1)

lemma ubd_sub:
  "ubd R  X A \<subseteq> X"
   by(simp add: ubd_def)

lemma ubd_ant1:
  "A \<subseteq> B \<Longrightarrow> ubd R  X B \<subseteq> ubd R  X A"
  by (simp add: ubd_mem_iff subset_iff ub_ant2) 

lemma ubd_ant1b:
  "\<lbrakk>A \<subseteq> B; b \<in> ubd R  X B\<rbrakk> \<Longrightarrow> b \<in> ubd R  X A"
  using ubd_ant1 by blast

lemma ubd_iso2:
  "Y \<subseteq> X \<Longrightarrow> ubd R  Y A \<subseteq> ubd R  X A" 
  by (simp add:subset_iff ubd_def)

lemma ubd_iso2b:
  "\<lbrakk>Y \<subseteq> X; x \<in> ubd R  Y A \<rbrakk> \<Longrightarrow> x \<in> ubd R  X A"
  by (simp add: ubd_mem_iff in_mono)

lemma ubd_emptyI:
  "x \<in> X \<Longrightarrow> x \<in> ubd R  X {}"
  by (simp add: ubd_mem_iff3)

lemma ubd_empty:
  "ubd R  X {} = X"
   by(simp add: set_eq_iff ubd_mem_iff ub_def)

lemma ubd_singleton:
  "x \<in> X \<Longrightarrow> (x, x) \<in> R \<Longrightarrow> x \<in> ubd R  X {x}"
  by (simp add: ubd_def ub_singleton)

lemma ubd_singleton2:
  "\<lbrakk>x \<in> X; (y, x)\<in>R \<rbrakk> \<Longrightarrow>  x \<in> ubd R  X {y}"
  by (simp add: ub_singletonD ubdI2)

lemma ubd_singleton_iff:
  "x \<in> ubd R  X {y} \<longleftrightarrow> (x \<in> X \<and> (y, x)\<in>R)"
  by (simp add: ubd_mem_iff ub_singleton_simp)

lemma ubd_mem_insert:
  "\<lbrakk>c \<in> ubd R X F; (x, c) \<in> R\<rbrakk> \<Longrightarrow> c \<in> ubd R  X (insert x F)"
  by (simp add: ubd_mem_iff ub_insert)

lemma ubd_mem_doubleE1:
  "c \<in> ubd R  X {a, b} \<Longrightarrow> (a, c)\<in>R"
  by (simp add: ubdD1)

lemma ubd_mem_doubleE2:
  "c \<in> ubd R  X {a, b} \<Longrightarrow> (b, c)\<in>R"
  by (simp add: ubdD1)

lemma ubd_mem_doubleI:
  "\<lbrakk>(a, c)\<in>R; (b, c)\<in>R; c \<in> X\<rbrakk> \<Longrightarrow> c \<in> ubd R  X {a, b}"
  by (simp add: ubd_empty ubd_mem_insert)

lemma ubd_mem_singleE:
  "x \<in> ubd R  X {a}\<Longrightarrow> (a, x) \<in> R"
  by (simp add: ubdD1)

lemma ubd_mem_double:
  "c \<in> X \<Longrightarrow> c \<in> ubd R  X {a, b} \<longleftrightarrow> (a, c)\<in>R \<and> (b, c)\<in>R"
  by (simp add: ubd_mem_iff ub_double_iff1)


lemma upbd_neE3:
  "ubd R  X {a} \<noteq> {} \<Longrightarrow> (\<exists>x \<in> X. (a, x) \<in> R)"
  by (meson equals0I ubd_singleton_iff)

lemma ubd_mem_unionI:
  "\<lbrakk>x \<in> ubd R  X A; x \<in> ubd R  X B\<rbrakk> \<Longrightarrow> x \<in> ubd R  X (A \<union> B)"
  by (simp add: ubd_mem_iff ub_unionI)


lemma ubd_unI:
  "x \<in> X \<Longrightarrow> (\<And>A. A \<in> S \<Longrightarrow> x \<in> ubd R  X A) \<Longrightarrow> x \<in> ubd R  X (\<Union>S)"
  by (simp add: ubd_mem_iff3)

lemma ubd_unD:
  "x \<in> X \<Longrightarrow> x \<in> ubd R  X (\<Union>S) \<Longrightarrow> A \<in> S \<Longrightarrow> x \<in> ubd R  X A"
  using ubd_ant1b[of A "\<Union>S" x R X] by blast

lemma ubd_imageI:
  "x \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (f a, x)\<in>R) \<Longrightarrow> x \<in> ubd R  X (f`A)"
  by (simp add: ub_imageI ubdI2)

lemma ubd_eqI1:
  "(\<And>x. x \<in> X \<Longrightarrow> ub R A x \<Longrightarrow>ub R B x) \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow>ub R B x \<Longrightarrow> ub R A x) \<Longrightarrow> ubd R  X A = ubd R  X B"
  by(auto simp add:set_eq_iff ubd_mem_iff)

lemma ubd_double1:
  " (a, b)\<in>R \<Longrightarrow>  ubd R  X {a, b} \<subseteq> ubd R  X {b}"
  by (simp add: ubd_ant1)



lemma ubd_double2:
  "\<lbrakk>(a, b)\<in>R; a \<in>X; b \<in> X; trans R X\<rbrakk> \<Longrightarrow>  ubd R X {b} \<subseteq> ubd R  X {a, b}"
  by(auto simp add:ubd_def,meson trans_onD ub_insert ub_singletonI)

subsection Composition

lemma lubd_comp1:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> lbd R X (ubd R X A)"
  by (simp add: in_mono subsetI ubd_mem_iff3)

lemma lubd_comp1b:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> ((\<lambda>E. lbd R X E) \<circ> (\<lambda>E. ubd R X E)) A"
  by (simp add: lubd_comp1)

lemma ulbd_comp1:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> ubd R X (lbd R X A)"
  by (simp add: in_mono subsetI ubd_mem_iff3)

lemma ulbd_comp1b:
  "A \<subseteq> X \<Longrightarrow> A \<subseteq> ((\<lambda>E. ubd R X E) \<circ> (\<lambda>E. lbd R X E)) A"
  by (simp add: ulbd_comp1)

lemma lubd_comp2:
  "A \<subseteq> B \<Longrightarrow> lbd R X (ubd R X A) \<subseteq> lbd R X (ubd R  X B)"
  by (simp add: ubd_ant1)

lemma lubd_comp2b:
  "A \<subseteq> B \<Longrightarrow> ((\<lambda>E. lbd R X E) \<circ> (\<lambda>E. ubd R  X E)) A  \<subseteq> ((\<lambda>E. lbd R X E) \<circ> (\<lambda>E. ubd R  X E)) B"
  by (simp add:  ubd_ant1)

lemma ulbd_comp2:
  "A \<subseteq> B  \<Longrightarrow> ubd R  X (lbd R X A) \<subseteq> ubd R  X (lbd R X B)"
  by (simp add:  ubd_ant1)

lemma ulbd_comp2b:
  "A \<subseteq> B \<Longrightarrow> ((\<lambda>E. ubd R  X E) \<circ> (\<lambda>E. lbd R X E)) A  \<subseteq> ((\<lambda>E. ubd R  X E) \<circ> (\<lambda>E. lbd R X E)) B"
  by (simp add:  ubd_ant1)

lemma lubd_comp3:
  "lbd R X (ubd R  X A) = lbd R X (ubd R  X (lbd R X (ubd R  X A)))"
  by (simp add: lubd_comp1 subset_antisym ubd_ant1 ubd_sub ulbd_comp1)

lemma lubd_comp3b:
  " ((\<lambda>E. lbd R X E) \<circ> (\<lambda>E. ubd R  X E)) A  = ((\<lambda>E. lbd R X E) \<circ> (\<lambda>E. ubd R  X E) \<circ> (\<lambda>E. lbd R X E) \<circ> (\<lambda>E. ubd R  X E)) A"
  using lubd_comp3 by force

lemma ulbd_comp3:
  "ubd R  X (lbd R X A) = ubd R  X (lbd R X (ubd R  X (lbd R X A)))"
  by (simp add: lubd_comp1 subset_antisym ubd_ant1 ubd_sub ulbd_comp1)

lemma ulbd_comp3b:
  "((\<lambda>E. ubd R  X E) \<circ> (\<lambda>E. lbd R X E)) A  = ((\<lambda>E. ubd R  X E) \<circ> (\<lambda>E. lbd R X E) \<circ> (\<lambda>E. ubd R  X E) \<circ> (\<lambda>E. lbd R X E)) A"
  using ulbd_comp3 by force


section AbsoluteExtrema
subsection GreatestPredicate

lemma greatestI1:
  "m \<in> ubd R A A \<Longrightarrow> is_greatest R A m" 
  by (simp add: is_greatest_def)

lemma greatestI2:
  "\<lbrakk>ub R A m; m \<in> A\<rbrakk> \<Longrightarrow> is_greatest R A m"
  by (simp add: ubd_mem_iff is_greatest_def)

lemma greatestI3:
  "\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> (a, m) \<in> R); m \<in> A\<rbrakk> \<Longrightarrow> is_greatest R A m"
  by (simp add: ubI greatestI2)

lemma greatestI4:
  "\<lbrakk>m \<in> ubd R  X A; A \<subseteq> X; m \<in> A\<rbrakk> \<Longrightarrow> is_greatest R A m"
  by (simp add: ubdD3 greatestI2)

lemma greatestD1:
  "is_greatest R A m \<Longrightarrow> (m \<in> A \<and> ub R A m)"
  by (simp add: ubd_mem_iff is_greatest_def)

lemma greatestD11:
  "is_greatest R A m \<Longrightarrow> m \<in> A"
  by (simp add: greatestD1)

lemma greatestD12:
  "is_greatest R A m \<Longrightarrow> ub R A m"
  by (simp add: greatestD1)

lemma greatestD13:
  "is_greatest R A m \<Longrightarrow> m \<in> ubd R A A"
  by (simp add: is_greatest_def)

lemma greatestD14:
  "is_greatest R A m \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (a, m) \<in> R)"
  by (simp add: is_greatest_def ubdD1)

lemma greatestD15:
  "is_greatest R A m \<Longrightarrow>  B \<subseteq> A \<Longrightarrow> m \<in> B \<Longrightarrow> is_greatest R B m"
  by(rule greatestI1,simp add: greatestD1 ub_ant2 ubdI2)

lemma greatestD2:
  "\<lbrakk>is_greatest R A m; a \<in> A\<rbrakk> \<Longrightarrow> (a, m) \<in>R"
  by (simp add: is_greatest_def ubdD1) 

lemma greatest_iff:
  "is_greatest R A m \<longleftrightarrow> (m \<in> A \<and> (\<forall>a. a \<in> A \<longrightarrow> (a, m)\<in>R))"
  by (simp add: ubd_mem_iff is_greatest_def ub_def)

lemma greatest_unique:
  "\<lbrakk>antisym_on A R; is_greatest R A m1; is_greatest R A m2\<rbrakk> \<Longrightarrow> m1 =m2"
  by (simp add: antisym_onD greatest_iff)

lemma is_greatest_iso2:
  "A \<subseteq> B \<Longrightarrow> is_greatest R A ma \<Longrightarrow> is_greatest R B mb \<Longrightarrow> (ma, mb)\<in>R"
  by (simp add: greatestD1 greatestD2 subset_iff)

lemma greatest_singleton:
  "(x, x) \<in> R \<Longrightarrow> is_greatest R {x} x"
  by (simp add: greatestI2 ub_singleton)


lemma is_greatest_singleton2:
  "refl R X \<Longrightarrow> x \<in> X \<Longrightarrow> is_greatest R {x} x"
  by (simp add: greatest_singleton reflD2)

lemma singleton_ex_greatest:
  "refl R X \<Longrightarrow> x \<in> X  \<Longrightarrow> (\<exists>m. is_greatest R {x} m)"
  using is_greatest_singleton2  by fastforce

lemma singleton_ex_greatest2:
  "(x, x) \<in> R \<Longrightarrow> (\<exists>m. is_greatest R {x} m)"
  by (meson greatest_singleton)

lemma greatest_insert1:
  "\<lbrakk>(x, x) \<in> R; ub R A x\<rbrakk> \<Longrightarrow> is_greatest R (insert x A) x"
  by (simp add: greatestI2 ub_insert)

lemma is_greatest_insert1b:
  "\<lbrakk>refl R X; x \<in> X; ub R A x\<rbrakk> \<Longrightarrow> is_greatest R (insert x A) x"
  by (simp add: greatest_insert1 reflD2)

lemma greatest_insert2:
  "is_greatest R A m \<Longrightarrow> (x, m)\<in>R \<Longrightarrow> is_greatest R (insert x A) m"
  by (simp add: greatestD11 greatestI2 greatestD12 ub_insert)

lemma greatest_insert3:
  "\<lbrakk>trans R X; A \<subseteq> X; x \<in> X; (x,x)\<in>R\<rbrakk> \<Longrightarrow>is_greatest R A m \<Longrightarrow> (m, x)\<in>R \<Longrightarrow> is_greatest R (insert x A) x"
  by(rule greatestI2, meson greatestD11 greatestD2 in_mono trans_onD ubI ub_insert, blast) 
                
lemma is_greatest_insert3b:
  "\<lbrakk>trans R X; A \<subseteq> X; x \<in> X; refl R X\<rbrakk> \<Longrightarrow>is_greatest R A m \<Longrightarrow> (m, x)\<in>R \<Longrightarrow> is_greatest R (insert x A) x"
  by (simp add: greatest_insert3 reflD2)

lemma greatest_insert4:
  "is_least R A m \<Longrightarrow> (m, x)\<in> R \<Longrightarrow> is_least R (insert x A) m"
  by (simp add: greatestD11 greatestI2 greatestD12 ub_insert)

lemma lb_single_greatest1:
  "\<lbrakk>x \<in> X; (x, x) \<in> R\<rbrakk> \<Longrightarrow> is_greatest R (lbd R X {x}) x"
  by (simp add: greatest_iff ubd_singleton_iff)

lemma lb_single_greatest1b:
  "\<lbrakk>x \<in> X; refl R X\<rbrakk> \<Longrightarrow> is_greatest R (lbd R X {x}) x"
  by (simp add: lb_single_greatest1 reflD2)

subsection GreatestOperator

lemma greatest_equality:
  "\<lbrakk>antisym_on A R; (\<And>a. a \<in> A \<Longrightarrow> (a, m)\<in>R); m \<in> A\<rbrakk> \<Longrightarrow> Greatest R A = m"
  by (simp add: Greatest_def greatestI3 greatest_unique the_equality) 

lemma greatest_equality11:
  "\<lbrakk>antisym_on A R; (\<And>a. a \<in> A \<Longrightarrow> (a, m)\<in>R); m \<in> A\<rbrakk> \<Longrightarrow> is_greatest R A (Greatest R A)"
  by (metis greatestI3 greatest_equality)

lemma greatest_equality2:
  "\<lbrakk>antisym_on A R; is_greatest R A m\<rbrakk> \<Longrightarrow> Greatest R A = m"
  by (simp add: greatest_equality greatest_iff)

lemma greatest_equality21:
  "\<lbrakk>antisym_on A R; is_greatest R A m\<rbrakk> \<Longrightarrow> is_greatest R A (Greatest R A )"
  by (simp add: greatest_equality2)

lemma greatest_equality5:
  "\<lbrakk>antisym_on X R; A \<subseteq> X;is_greatest R A m\<rbrakk> \<Longrightarrow> Greatest R A = m"
  by (simp add: antisym_on_subset greatest_equality2)            

lemma greatest_equality51:
  "\<lbrakk>antisym_on X R; A \<subseteq> X;is_greatest R A m\<rbrakk> \<Longrightarrow> is_greatest R A (Greatest R A)"
  by (simp add: antisym_on_subset greatest_equality2)

lemma greatest_equality3:
  "\<lbrakk>antisym_on A R;m \<in> ubd R A A\<rbrakk> \<Longrightarrow> Greatest R A = m"
  by (simp add: greatest_equality2 is_greatest_def)

lemma greatest_equality31:
  "\<lbrakk>antisym_on A R;m \<in> ubd R A A\<rbrakk> \<Longrightarrow> is_greatest R A (Greatest R A)"
  by (simp add: greatestI1 greatest_equality3)

lemma lb_single_greatest2:
  "\<lbrakk>(x, x) \<in> R; antisym_on X R; x \<in> X\<rbrakk> \<Longrightarrow> Greatest R (lbd R X {x}) = x"
  by(erule greatest_equality5,simp add: ubd_sub,simp add: lb_single_greatest1)

lemma greatest_exD0:
  "(\<exists>m. is_greatest R A m) \<Longrightarrow> A \<noteq> {}"
  using greatestD11 by force

lemma greatest_exD1:
  "\<lbrakk>antisym_on A R; (\<exists>m. is_greatest R A m)\<rbrakk> \<Longrightarrow> Greatest R A \<in> A"
  by (metis greatestD11 greatest_equality2)


lemma greatest_exD11:
  "\<lbrakk>antisym_on A R; (\<exists>m. is_greatest R A m)\<rbrakk> \<Longrightarrow> is_greatest R A (Greatest R A)"
  by (meson greatest_equality21)


lemma greatest_exD12:
  "\<lbrakk>antisym_on X R; A \<subseteq> X;(\<exists>m. is_greatest R A m)\<rbrakk> \<Longrightarrow> is_greatest R A (Greatest R A)"
  by (metis greatest_equality51)

lemma greatest_exD2:
  "\<lbrakk>antisym_on A R; (\<exists>m. is_greatest R A m)\<rbrakk> \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (a, (Greatest R A)) \<in> R)"
  by (metis greatestD2 greatest_equality2)

lemma greatest_exD3:
  "\<lbrakk>antisym_on A R; (\<exists>m. is_greatest R A m)\<rbrakk> \<Longrightarrow> (Greatest R A) \<in> ubd R A A"
  by (simp add: greatest_exD1 greatest_exD2 ubd_mem_iff3)

lemma greatest_exD4:
  "\<lbrakk>antisym_on A R; (\<exists>m. is_greatest R A m)\<rbrakk> \<Longrightarrow>  ub R A (Greatest R A)"
  by (metis greatestD12 greatest_equality2)

lemma greatest_exD5:
  "\<lbrakk>antisym_on B R; A \<subseteq> B; (\<exists>m. is_greatest R A m); (\<exists>m. is_greatest R B m)\<rbrakk> \<Longrightarrow> (Greatest R A, Greatest R B) \<in> R"
  by (metis antisym_on_subset greatest_equality2 is_greatest_iso2)

lemma greatest_exD5b:
  "\<lbrakk>antisym_on B R; A \<subseteq> B; is_greatest R A m\<rbrakk> \<Longrightarrow> Greatest R A = m "
  by (meson antisym_on_subset greatest_equality2)

lemma greatest_exD1b:
  "\<lbrakk>antisym_on A R; is_greatest R A m\<rbrakk> \<Longrightarrow>  Greatest R A = m"
  by (simp add: greatest_equality2)

lemma greatest_singleton2:
  "(x, x) \<in> R  \<Longrightarrow> Greatest R {x} = x"
  by (simp add: antisym_on_def greatest_equality2 greatest_singleton)

lemma greatest_insert1b:
  "\<lbrakk>antisym_on X R; A \<subseteq> X; x \<in> X; (x, x) \<in> R; ub R A x\<rbrakk> \<Longrightarrow> Greatest R (insert x A) = x"
  by (simp add: greatest_equality5 greatest_insert1)

lemma greatest_insert2b:
  "\<lbrakk>antisym_on X R; A \<subseteq> X; x \<in> X; is_greatest R A m\<rbrakk> \<Longrightarrow> (x, m)\<in>R \<Longrightarrow> Greatest R (insert x A) = m"
  by (simp add: greatest_equality5 greatest_insert2)

lemma greatest_insert3b:
  "\<lbrakk>ord R X; A \<subseteq> X; x \<in> X; (x,x) \<in>R;is_greatest R A m\<rbrakk> \<Longrightarrow> (m, x)\<in>R \<Longrightarrow> Greatest R (insert x A) =  x"
  by(rule greatest_equality2,simp add: antisym_on_def subset_iff,auto intro:greatest_insert3)

lemma greatest_ub:
  "\<lbrakk>antisym_on X R; A \<subseteq> X; is_greatest R A m\<rbrakk> \<Longrightarrow> ubd R A A = {m}"
  by(rule set_eqI, auto,metis antisym_on_subset greatest_equality3 greatest_exD5b, simp add: is_greatest_def)

section Extrema
subsection Suprema

lemma is_supI1:
  "is_least R (ubd R X A) x \<Longrightarrow> is_sup R X A x"
  by (simp add: is_sup_def) 

lemma is_supD1:
  "is_sup R X A x \<Longrightarrow> (is_least R (ubd R  X A) x)"
  by (simp add: is_sup_def)

lemma is_supI2:
  "x \<in> lbd R (ubd R  X A) (ubd R  X A) \<Longrightarrow> is_sup R X A x"
  by (simp add: is_greatest_def is_supI1)

lemma is_supD2:
  "is_sup R X A x \<Longrightarrow> x \<in> lbd R (ubd R X A) (ubd R  X A)"
  by (simp add: is_greatest_def is_sup_def)

lemma is_supI3:
  "\<lbrakk>lb R (ubd R X A) x; x \<in> (ubd R X A)\<rbrakk> \<Longrightarrow> is_sup R X A x"
  by (simp add: greatestI2 is_supI1)

lemma is_supD31:
  "is_sup R X A x \<Longrightarrow> lb R (ubd R  X A) x"
  by (simp add: greatestD12 is_supD1)

lemma is_supD32:
  "is_sup R X A x \<Longrightarrow> x \<in> (ubd R X A)"
  by (simp add: greatest_iff is_sup_def)

lemma is_supI4:
  "\<lbrakk>lb R (ubd R  X A) x; x \<in> X; ub R A x\<rbrakk> \<Longrightarrow> is_sup R X A x"
  by (simp add: is_supI3 ubdI2)

lemma is_supE1:
  "is_sup R X A x \<Longrightarrow> x \<in> X" 
  by (simp add:is_supD32[of R X A x] ubdD2[of x R X A])

lemma is_supI5:
  "\<lbrakk>(\<And>a. a \<in> (ubd R  X A) \<Longrightarrow> (x, a) \<in> R); x \<in> (ubd R X A)\<rbrakk> \<Longrightarrow> is_sup R X A x"
  by (simp add: is_supI1 greatestI3)

lemma is_supI6:
  "\<lbrakk>x \<in> X; ub R A x; (\<And>a. a \<in> (ubd R X A) \<Longrightarrow> (x, a) \<in> R)\<rbrakk> \<Longrightarrow> is_sup R X A x"
  by (simp add: is_supI5 ubdI2)

lemma is_supI7:
  "\<lbrakk>x \<in> X; ub R A x; (\<And>a. a \<in> X \<Longrightarrow> ub R A a \<Longrightarrow> (x, a) \<in> R)\<rbrakk> \<Longrightarrow> is_sup R X A x"
  by (simp add: is_supI4 ub_def ubd_mem_iff)

lemma is_supI8:
  "\<lbrakk>x \<in> X; (x, x) \<in> R; (\<And>z. z \<in> ubd R X A \<longleftrightarrow> (x, z) \<in> R)\<rbrakk> \<Longrightarrow> is_sup R X A x"
  by (simp add: is_supI1 greatest_iff)

lemma is_supI9:
  "\<lbrakk>x \<in> X; (x, x) \<in> R; (\<forall>z \<in> X. (x, z) \<in> R \<longleftrightarrow> (ub R A z))\<rbrakk> \<Longrightarrow> is_sup R X A x"
  by (simp add: is_supI7)

lemma is_supI10:
  "\<lbrakk>x \<in> X; (\<And>a. a \<in> A \<Longrightarrow> (a, x) \<in> R); (\<And>a. a \<in> X \<Longrightarrow> ub R A a \<Longrightarrow> (x, a) \<in> R)\<rbrakk> \<Longrightarrow> is_sup R X A x"
  by (simp add: is_supI4 ub_def ubd_mem_iff)

lemma is_supI11:
  "\<lbrakk>x \<in> X; (\<And>a. a \<in> A \<Longrightarrow> (a, x) \<in> R); (\<And>b. b \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (a, b) \<in> R)\<Longrightarrow> (x, b) \<in> R)\<rbrakk> \<Longrightarrow> is_sup R X A x"
  by (simp add: is_supI4 ub_def ubd_mem_iff)

lemma is_supE2:
  "is_sup R X A x \<Longrightarrow> ub R A x" 
  by(simp add:  ubdD3[of x R X A] is_supD32[of R X A x])            

lemma is_supE3:
  "\<lbrakk>is_sup R X A x; y \<in> ubd R X A\<rbrakk> \<Longrightarrow> (x, y)\<in>R "
  using is_supD2 ubdD1 by fastforce
                     
lemma is_supE4:
  "\<lbrakk>is_sup R X A x; y \<in> X; ub R A y\<rbrakk> \<Longrightarrow> (x, y)\<in>R "
  by (simp add: ubd_mem_iff is_supE3)
 
lemma is_supE5a:
  "\<lbrakk>trans R X; (x, x) \<in> R; A \<subseteq> X;is_sup R X A x; z \<in> X;  (x, z) \<in> R\<rbrakk> \<Longrightarrow> ub R A z"
  by(rule ubI,meson in_mono is_supD32 is_supE1 trans_onD ubdD1)
       
lemma is_supE5:
  "\<lbrakk>trans R X; (x, x) \<in> R; A \<subseteq> X;is_sup R X A x; z \<in> X;  (x, z) \<in> R\<rbrakk> \<Longrightarrow> z \<in> ubd R X A"
  by(rule ubdI2,simp add: is_supE5a, blast)

lemma is_supD1121:
  "\<lbrakk>is_sup R X A x; a \<in> A \<rbrakk> \<Longrightarrow> (a, x) \<in> R"
  by (meson is_supE2 ubE)

lemma is_supE6:
  "\<lbrakk>trans R X; A \<subseteq> X; z \<in> X; is_sup R X A x; (x, z) \<in> R\<rbrakk> \<Longrightarrow> ub R A z"
  by (meson is_supE1 is_supE2 is_supE4 is_supE5 ubd_mem_iff)

lemma is_supE7:
  "\<lbrakk>trans R X; A \<subseteq> X; z \<in> X;is_sup R X A x;  (x, z) \<in> R; a \<in> A\<rbrakk> \<Longrightarrow> (a, z) \<in> R"
  by (meson is_supE6 ubE)

lemma is_supD41:
  "\<lbrakk>trans R X; A \<subseteq> X; z \<in> X;is_sup R X A x\<rbrakk> \<Longrightarrow> (\<And>z. z \<in> X \<Longrightarrow> (x, z) \<in> R \<Longrightarrow> ub R A z)"
  by (simp add: is_supE6)

lemma is_supD42:
  "\<lbrakk>trans R X; A \<subseteq> X; z \<in> X;is_sup R X A x\<rbrakk> \<Longrightarrow> (\<And>z. z \<in> X \<Longrightarrow> ub R A z \<Longrightarrow>  (x, z) \<in> R)"
  by (simp add: is_supE4)

lemma is_supD5:
  "\<lbrakk>trans R X; A \<subseteq> X;is_sup R X A x\<rbrakk> \<Longrightarrow> (\<forall>z \<in> X. (x, z) \<in> R \<longleftrightarrow> (ub R A z))"
  by (meson is_supD41 is_supD42)

lemma is_sup_iff1:
  "\<lbrakk>trans R X;x \<in> X; A \<subseteq> X; (x,x)\<in>R; (\<forall>a. a \<in> A \<longrightarrow> (a,  a) \<in> R)\<rbrakk> \<Longrightarrow> ((\<forall>z \<in> X. (x, z) \<in> R \<longleftrightarrow> (ub R A z)) \<longleftrightarrow> is_sup R X A x)"
  by (meson is_supD5 is_supI9)

lemma sup_iff2:
  "\<lbrakk>trans R X; A \<subseteq> X; (s,s)\<in>R; (\<forall>a. a \<in> A \<longrightarrow> (a,  a) \<in> R)\<rbrakk> \<Longrightarrow> is_sup R X A s \<longleftrightarrow>  s \<in> X \<and> (\<forall>z \<in> X.  (s, z) \<in> R \<longleftrightarrow> z \<in> ubd R X A)"
  by (meson dual_order.refl is_supE1 is_supE3 is_supE5 is_supI5 ubdD2)

lemma sup_iff3:
  "is_sup R X A s \<longleftrightarrow> is_least R (ubd R X A) s" 
  by(simp add:is_sup_def)

lemma is_sup_unique:
  "\<lbrakk>antisym_on X R; is_sup R X A m1;  is_sup R X A m2\<rbrakk> \<Longrightarrow> m1 = m2"
  by (simp add: antisym_on_def is_supD32 is_supE1 is_supE3)

lemma is_sup_iso1:
  "A \<subseteq> B \<Longrightarrow> is_sup R X A ma \<Longrightarrow> is_sup R X B mb \<Longrightarrow> (ma, mb)\<in>R "
  by (simp add: is_supE1 is_supE2 is_supE4 ub_ant2)

lemma is_sup_iso2:
  "A \<subseteq> Y \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> is_sup R Y A my \<Longrightarrow> is_sup R X A mx \<Longrightarrow> (mx, my) \<in> R"
  by (simp add: in_mono is_supE1 is_supE2 is_supE4)

lemma sup_maxI1:
  "is_sup R X A x \<Longrightarrow> x \<in> A \<Longrightarrow> (is_greatest R A x)"
  by (simp add: greatestI2 is_supE2)

lemma sup_maxE1:
  "(is_greatest R A x) \<Longrightarrow> x \<in> X \<Longrightarrow> is_sup R X A x"
  by (simp add: greatestD11 greatestD12 is_supI6 ubdD1)

lemma sup_maxE2:
  "(is_greatest R A x) \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_sup R X A x"
  by (simp add: greatestD11 in_mono sup_maxE1)

lemma sup_max_eq:
  "A \<subseteq> X \<Longrightarrow> (is_sup R X A x \<and> x \<in> A) \<longleftrightarrow> (is_greatest R A x)"
  by (metis greatestD11 sup_maxE2 sup_maxI1)

lemma sup_max_eq2:
  "(is_sup R A A x) \<longleftrightarrow> (is_greatest R A x)"
  by (meson dual_order.refl is_supE1 sup_maxE2 sup_maxI1)

lemma sup_in_subset:
  "A \<subseteq> B \<Longrightarrow>  B \<subseteq> X \<Longrightarrow> is_sup R X A s \<Longrightarrow> s \<in> B \<Longrightarrow> is_sup R B A s"
  by (meson is_supE2 is_supE3 is_supI6 ubd_iso2b)

lemma sup_singleton:
  "s \<in> X \<Longrightarrow> (s, s) \<in> R \<Longrightarrow> is_sup R X {s} s"
  by (simp add: greatest_singleton sup_maxE1)

lemma sup_emptyI:
  "is_least R X i \<Longrightarrow> is_sup R X {} i"
  by (simp add: is_sup_def ubd_empty)

lemma sup_emptyD:
  "is_sup R X {} i \<Longrightarrow> is_least R X i "
  by (simp add: is_sup_def ubd_empty)

lemma sup_empty:
  "is_sup R X {} i \<longleftrightarrow> (is_least R X i)"
  by (simp add: ubd_empty is_sup_def)

lemma binary_supI1:
  "\<lbrakk>a \<in> X; b \<in> X; (a, b)\<in>R; (b, b) \<in> R\<rbrakk> \<Longrightarrow> is_sup R X {a, b} b"
  by (simp add: greatest_insert2 greatest_singleton sup_maxE1)

lemma binary_supI2:
  "\<lbrakk>a \<in> X; b \<in> X; (b, a) \<in> R; (a,a) \<in> R\<rbrakk> \<Longrightarrow> is_sup R X {a, b} a"
  by (simp add: greatest_insert1 sup_maxE1 ub_singleton_simp)

lemma binary_supD21:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X;s \<in> X; is_sup R X {a, b} s; (c, a) \<in> R; trans R X\<rbrakk> \<Longrightarrow>  (c, s) \<in> R"
  by (meson insertI1 is_supD1121 trans_onD)

lemma binary_supD22:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X;s \<in> X;is_sup R X {a, b} s; trans R X; (c ,b) \<in> R\<rbrakk> \<Longrightarrow>  (c, s) \<in> R"
  by (simp add: binary_supD21 insert_commute)

lemma binary_supD31:
  "\<lbrakk>a \<in> X; b \<in> X; s \<in> X; is_sup R X {a, b} s\<rbrakk>  \<Longrightarrow>  (a, s) \<in> R"
  by (simp add: is_supD1121)

lemma binary_supD32:
  "\<lbrakk>a \<in> X; b \<in> X; s \<in> X; is_sup R X {a, b} s\<rbrakk>  \<Longrightarrow>  (b, s) \<in> R"
  by (simp add: is_supD1121)


lemma sup_insert1:
  "\<lbrakk>ub R A x; x \<in> X; (x, x) \<in> R\<rbrakk> \<Longrightarrow> is_sup R X (insert x A) x"
  by (simp add: greatest_insert1 sup_maxE1)

lemma sup_insertE1:
  "\<And>a. is_sup R X A m \<Longrightarrow> (x, m) \<in> R \<Longrightarrow> a \<in> insert x A \<Longrightarrow> (a, m) \<in> R"
  by(auto, simp add: is_supD1121)

lemma sup_insert2:
  "\<lbrakk>is_sup R X A m; (x, m)\<in>R\<rbrakk> \<Longrightarrow> is_sup R X (insert x A) m"
  by(rule is_supI10,simp add: is_supE1,simp add: sup_insertE1,simp add: is_supE4 ub_def) 

lemma sup_insert3:
  "\<lbrakk>A \<subseteq> X; trans R X;is_sup R X A m; (x, x) \<in> R;(m, x)\<in>R; x \<in> X\<rbrakk> \<Longrightarrow> is_sup R X (insert x A) x"
  by (simp add: is_supD41 sup_insert1)

lemma sup_insert61:
  "\<lbrakk>trans R X;A \<subseteq> X; is_sup R X A s1; is_sup R X {s1, x} s2\<rbrakk> \<Longrightarrow> ub R A s2"
  by (meson insertI1 is_supD1121 is_supD5 is_supE1)

lemma sup_insert62:
  "\<lbrakk>trans R X;A \<subseteq> X;is_sup R X A s1; is_sup R X {s1, x} s2\<rbrakk> \<Longrightarrow> s2 \<in> ubd R  X A"
  by (simp add: is_supE1 sup_insert61 ubd_mem_iff)

lemma sup_insert7:
  "\<lbrakk>trans R X;A \<subseteq> X;is_sup R X A s1; is_sup R X {s1, x} s2; u \<in> ubd R  X (insert x A)\<rbrakk> \<Longrightarrow>  (s2, u) \<in> R"
  by (simp add: ubd_mem_iff2 is_supE3)

lemma ub_eq_sup_eq:
  "(\<And>x. ub R A x \<longleftrightarrow> ub R B x) \<Longrightarrow> (is_sup R X A s \<longleftrightarrow> is_sup R X B s)"
  by (meson is_supE1 is_supE2 is_supE4 is_supI7)

lemma Upper_eq_sup_eq:
  "ubd R  X A = ubd R  X B \<Longrightarrow> (is_sup R X A s \<longleftrightarrow> is_sup R X B s)"
  by (simp add: is_sup_def)

lemma Upper_eq_sup_eq2:
  "\<lbrakk>is_sup R X A s1;  ubd R X A=ubd R X B\<rbrakk> \<Longrightarrow> is_sup R X B s1"
  by (simp add: is_sup_def)

lemma Upper_eq_sup_eq3:
  "\<lbrakk>is_sup R X A s1;  is_sup R X B s2;ubd R X A=ubd R X B; antisym R X\<rbrakk> \<Longrightarrow> s1=s2"
  by(drule_tac ?R="R" and ?X="X" and ?A="A" and ?s1.0="s1" and ?B="B" in Upper_eq_sup_eq2,simp,simp add: is_sup_unique)

lemma sup_equality:
  "\<lbrakk>is_sup R X A m; antisym_on X R\<rbrakk> \<Longrightarrow> Sup R X A = m"
  by (simp add: Sup_def is_sup_unique the_equality) 

lemma sup_equality2:
  "\<lbrakk>antisym R X; A \<subseteq> X; (\<exists>m. is_sup R X A m)\<rbrakk> \<Longrightarrow> is_sup R X A (Sup R X A)"
  by (metis sup_equality)

lemma inf_equality:
  "\<lbrakk>is_inf R X A m; antisym_on X R\<rbrakk> \<Longrightarrow> Inf R X A = m"
  by (simp add: Upper_eq_sup_eq3 the_equality)

lemma inf_equality2:
  "\<lbrakk>antisym R X; A \<subseteq> X; (\<exists>m. is_inf R X A m)\<rbrakk> \<Longrightarrow> is_inf R X A (Inf R X A)"
  using inf_equality by fastforce

lemma sup_exI:
  "\<lbrakk>antisym_on X R; A \<subseteq> X; (\<exists>s. is_sup R X A s); (\<And>s. is_sup R X A s \<Longrightarrow> P s)\<rbrakk> \<Longrightarrow> P (Sup R X A)"
  using sup_equality  by metis

lemma set_eqI:
  "(\<And>x. x \<in> ubd R X A \<Longrightarrow> x \<in> ubd R X B) \<Longrightarrow> (\<And>x. x \<in> ubd R X B \<Longrightarrow> x \<in> ubd R X A) \<Longrightarrow> ubd R X A = ubd R X B"
  by blast

lemma sup_unc_ubd_eq:
  "\<lbrakk>trans R X; A \<subseteq> X; B \<subseteq> X; is_sup R X A s1; is_sup R X B s2\<rbrakk> \<Longrightarrow> ubd R X (A \<union> B) = ubd R X {s1, s2}"
   by(rule set_eqI,simp add: is_supE3 ubd_mem_iff3, simp add:is_supE6 ub_unionI ubd_mem_doubleE1 ubd_mem_doubleE2 ubd_mem_iff)

lemma sup_unc:
  "\<lbrakk>trans R X; A \<subseteq> X; B \<subseteq> X; antisym_on X R;is_sup R X (A \<union> B) s; is_sup R X A s1; is_sup R X B s2; is_sup R X {s1, s2} s3\<rbrakk> \<Longrightarrow> s=s3"
  by(erule_tac ?R="R" and ?X="X"  and ?A="A \<union> B" and ?B="{s1, s2}" in Upper_eq_sup_eq3, simp, simp add: sup_unc_ubd_eq)


lemma sup_families1:
  assumes A0:"I \<noteq> {}" and A1:"\<forall>i. i \<in> I \<longrightarrow> is_sup R X (A i) (s i)" and A2:"trans R X" and A3:"\<forall>i. i \<in> I \<longrightarrow> A i \<subseteq> X"
  shows "is_sup R X (\<Union>(A`I)) t \<longleftrightarrow> is_sup R X (s`I) t"
proof(rule Upper_eq_sup_eq)
  show "ubd R X (\<Union> (A ` I)) = ubd R X (s ` I)" (is "?L = ?R")
  proof
    show "?L \<subseteq> ?R"
    proof
      fix u assume L:"u \<in> ?L"  show "u \<in> ?R" 
    by(rule ubd_imageI,auto intro:L ubdD2,metis A1 L Sup_le_iff imageI is_supE4 order_refl ubdD2 ubdD3 ubd_ant1b)
    qed
    next show "?R \<subseteq> ?L"
    proof
      fix u assume R:"u \<in> ?R" show "u \<in> ?L" 
      apply(rule ubd_unI, meson R ubdD2)  using A1 A2 A3 R fbdE1 ubdD2 ubdD3   by (metis (full_types) image_iff is_supD5 ubdI2)
    qed
  qed
qed   

lemma sup_families1b:
  "\<lbrakk>trans R X; antisym_on X R; (\<And>Ai. Ai \<in> A \<Longrightarrow> Ai \<subseteq> X); A \<noteq> {}; (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_sup R X Ai si); x \<in> X\<rbrakk> \<Longrightarrow> ub R (Sup R X ` A) x \<Longrightarrow> ub R (\<Union> A) x"  
  by (metis fbdE1 is_supD41 sup_equality ub_unI)
lemma sup_families2b:
  "\<lbrakk>trans R X; antisym_on X R; (\<And>Ai. Ai \<in> A \<Longrightarrow> Ai \<subseteq> X); A \<noteq> {}; (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_sup R X Ai si); x \<in> X; ub R (\<Union>A) x\<rbrakk>   \<Longrightarrow>  ub R ((Sup R X) ` A) x" 
  by (metis is_supD5 sup_equality ub_imageI ub_unD)
lemma sup_families:
  "\<lbrakk>trans R X; antisym_on X R; (\<And>Ai. Ai \<in> A \<Longrightarrow> Ai \<subseteq> X); A \<noteq> {}; (\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_sup R X Ai si)\<rbrakk> \<Longrightarrow>(is_sup R X ((\<lambda>Ai. Sup R X Ai)`A) s) \<longleftrightarrow> (is_sup R X (\<Union>A) s)"  
  by(rule Upper_eq_sup_eq, rule ubd_eqI1,simp add: sup_families1b,simp add: sup_families2b) 

lemma sup_finite:
  assumes A0:"\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> \<exists>b \<in> X. is_sup R  X {a1, a2} b" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X" and
          A4:"trans R X" and
          A5:"antisym_on X R"
  shows "\<exists>b \<in> X. is_sup R X A b"
  using A1 A2 A3 
proof (induct A rule: finite_ne_induct)
  case (singleton x)
  then show ?case using A0 by force
next
  case (insert x F)
  obtain s1 where B0:"s1 \<in> X" "is_sup R X F s1"
    using insert.hyps(4) insert.prems by blast
  obtain s2 where B2:"s2 \<in> X" "is_sup R X {s1, x} s2"
    by (meson A0 B0(1) insert.prems insert_subset)
  have B3:"is_sup R X (insert x F) s2"
  proof(rule is_supI5)
    show "\<And>a. a \<in> ubd R X (insert x F)  \<Longrightarrow> (s2, a) \<in> R"   by (meson A4 B0(2) B2(2) insert.prems insert_subset sup_insert7) 
    show "s2 \<in> ubd R X (insert x F)" by (metis A4 B0(1) B0(2) B2(1) B2(2) binary_supD32 insert.prems insert_subset sup_insert62 ubd_mem_insert)
  qed
  then show ?case
    using B2(1) by blast
qed

lemma bsup_finite:
  assumes A0: "\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> is_sup R X {a1, a2} (Sup R X {a1, a2})" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X" and 
          A4:"trans R X" and
          A5:"antisym_on X R"
  shows "is_sup R X A (Sup R X A)"
  using A1 A2 A3 
proof (induct A rule: finite_ne_induct)
  case (singleton x)
  then show ?case using A0 by force
next
  case (insert x F)
  obtain s1 where B0:"is_sup R X F s1"
    using insert.hyps(4) insert.prems by blast
  have B1:"s1 \<in> X" by (meson B0 is_supE1)
  obtain s2 where B2:"is_sup R X {s1, x} s2"
    using A0 B1 insert.prems by auto
  have B3:"s2 \<in> ubd R  X (insert x F)"
    by (meson A4 B0 B2 insert.prems insertCI insert_subset is_supD1121 sup_insert62 ubd_mem_insert)
  have B4:"\<And>u. u \<in> ubd R  X (insert x F) \<longrightarrow> (s2, u) \<in> R"
    by (meson A4 B0 B2 insert.prems insert_subset sup_insert7)
  have B3:"is_sup R X (insert x F) s2"
    by (simp add: B3 B4 is_supI5)
  then show ?case
    by (simp add: A5 sup_equality)
qed

lemma bsup_commute:
  "is_sup R X {a, b} c \<longleftrightarrow> is_sup R X {b, a } c "
  by (simp add: insert_commute)

lemma bsup_commute2:
  "a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> Sup R X {a, b} =  Sup R X  {b, a}"
  by (simp add: insert_commute)

lemma bsup_idem1:
  "\<lbrakk>(a, a) \<in> R; a\<in> X; antisym_on X R\<rbrakk> \<Longrightarrow> Sup R X {a, a} = a"
  by (simp add: sup_equality sup_singleton)

lemma sup_singleton2:
  "\<lbrakk>(a, a) \<in> R; a\<in> X; antisym_on X R\<rbrakk> \<Longrightarrow> Sup R X {a} = a"
  using bsup_idem1 by auto

lemma sup_ge1:
  "\<lbrakk>trans R X; c \<in> X; a \<in> X;b \<in> X; (c, a) \<in> R; is_sup R X {a, b} s\<rbrakk>  \<Longrightarrow> (c, s) \<in> R " 
  by (meson binary_supD31 is_supE1 trans_onD) 

lemma sup_ge2:
  "\<lbrakk>trans R X; c \<in> X; a \<in> X;b \<in> X; (c, b) \<in> R; is_sup R X {a, b} s\<rbrakk>  \<Longrightarrow> (c, s) \<in> R " 
  by (meson binary_supD32 is_supE1 trans_onD)

lemma sup_ge3:
  "\<lbrakk>trans R X; c \<in> X; a \<in> X;b \<in> X; (b, c) \<in> R; (a, c) \<in> R;is_sup R X {a, b} s\<rbrakk>  \<Longrightarrow> (s, c) \<in> R " 
  by (simp add: is_supE4 ub_insert ub_singleton_simp)

lemma sup_ge4:
  "\<lbrakk>trans R X; x \<in> X; y \<in> X;z \<in> X; (x, y) \<in> R; is_sup R X {y, z} syz; is_sup R X {x, z} sxz\<rbrakk>  \<Longrightarrow> (sxz, syz) \<in> R " 
  by (metis sup_ge1 binary_supD32 is_supE1 sup_ge3)

lemma sup_ge5:
  "\<lbrakk>trans R X;is_sup R X {x1, x2} sx; is_sup R X {y1, y2} sy; x1 \<in> X; x2 \<in> X; y1 \<in> X; y2 \<in>X;(x1,y1) \<in> R; (x2, y2) \<in> R\<rbrakk> \<Longrightarrow>(sx, sy) \<in> R"
  by (metis sup_ge1 sup_ge2 is_supE1 sup_ge3)

lemma ge_sup_iff:
  "\<lbrakk>trans R X; is_sup R X {a, b} s; a \<in> X; b \<in> X; c \<in> X\<rbrakk>  \<Longrightarrow> ((s, c) \<in> R \<longleftrightarrow> (a, c) \<in> R \<and> (b, c) \<in> R)"
  by (meson binary_supD31 binary_supD32 is_supE1 sup_ge3 trans_onD)

lemma sup_assoc1:
  "\<lbrakk>trans R X; antisym_on X R; is_sup R X {a, b} sab; is_sup R X {sab, c} sab_c; is_sup R X {b, c} sbc; is_sup R X {a, sbc} sbc_a;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> sbc_a = sab_c" 
  apply(erule antisym_onD, simp add:is_supE1, simp add:is_supE1)
  apply (metis sup_ge1 binary_supD31 binary_supD32 is_supE1 sup_ge3)
  by (meson ge_sup_iff is_supE1 is_supE2 ub_double_iff1)

lemma sup_assoc2:
  "\<lbrakk>trans R X; antisym_on X R; is_sup R X {b, c} sbc; is_sup R X {a, sbc} sbc_a; is_sup R X {a, c} sac; is_sup R X {b, sac} sac_b;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> sac_b = sbc_a" 
  by (meson bsup_commute sup_assoc1)

lemma sup_idem2:
  "\<lbrakk>a \<in> X; b \<in> X; is_sup R X {a, b} s\<rbrakk> \<Longrightarrow> is_sup R X {a, s} s"  
  by (simp add: binary_supD31 binary_supI1 is_supE1 is_supE2 is_supE4)

lemma sup_idem3:
  "\<lbrakk>a \<in> X; b \<in> X; is_sup R X {a, b} s\<rbrakk> \<Longrightarrow> is_sup R X {b, s} s" 
  by (simp add: bsup_commute sup_idem2)

lemma sup_upper_bounds:
  "\<lbrakk>is_sup R X A s; trans R X; A \<subseteq> X\<rbrakk> \<Longrightarrow>  ubd R X {s} = ubd R X A" 
  by (meson is_supD41 is_supE4 ub_singletonD ub_singletonI ubd_eqI1)

lemma ge_sup1:
  "\<lbrakk>antisym R X; a \<in> X; b \<in> X; (a, b)\<in>R;(b,b)\<in>R\<rbrakk> \<Longrightarrow>  Sup R X {a, b} = b"
  by (simp add: binary_supI1 sup_equality)

lemma ge_sup2:
  "\<lbrakk>antisym R X;a \<in> X; b \<in> X;(b, a)\<in>R;(a,a)\<in>R\<rbrakk> \<Longrightarrow> Sup R X {a, b} = a"
  by (simp add: binary_supI2 sup_equality)

subsection Duality

lemma sup_imp_inf_ub:
  "is_sup R X A s \<Longrightarrow>  is_inf R X (ubd R X A) s"
  by (simp add: is_supD1 sup_maxE2 ubd_sub)
  
lemma sup_if_inf_ub:
  "A \<subseteq> X \<Longrightarrow> is_inf R X (ubd R  X A) s \<Longrightarrow>  is_sup R X A s"
  by (metis converse_converse is_supD31 is_supE1 is_supE2 is_supI4 lubd_comp1 ub_ant2)
  
lemma inf_imp_sup_lb:
  "is_inf R X A s \<Longrightarrow>  is_sup R X (lbd R X A) s"
  using sup_imp_inf_ub by fastforce
  
lemma inf_if_sup_lb:
  "A \<subseteq> X \<Longrightarrow> is_sup R X (lbd R X A) s \<Longrightarrow>  is_inf R X A s"
  by (simp add: sup_if_inf_ub)


subsection Misc
definition pwr where "pwr X \<equiv> {(A, B). A \<subseteq> X \<and> B \<subseteq> X \<and> A \<subseteq> B}"

lemma pwr_memI:
  "A \<subseteq> B \<Longrightarrow> B \<subseteq> X \<Longrightarrow> (A, B) \<in> pwr X"
  by (simp add: pwr_def) 

lemma pwr_memD:
  "(A, B) \<in> pwr X \<Longrightarrow> A \<subseteq> B \<and> B \<subseteq> X"
  by (simp add: pwr_def) 

lemma pwr_mem_iff:
  "(A, B) \<in> pwr X \<longleftrightarrow> (A \<subseteq> B) \<and> (B \<subseteq> X)"
  by(rule iffI, simp add:pwr_memD, simp add:pwr_memI)

lemma powsimp1:
  "A \<subseteq> Pow X \<Longrightarrow> a \<in> A \<Longrightarrow> a \<subseteq> X"
  by auto

lemma powrel1[intro?]:
  "antisym_on (Pow X) (pwr X)"  
  by(auto simp add:antisym_on_def pwr_def)

lemma powrel2[intro?]:
  "trans_on (Pow X) (pwr X)"  
  by(auto simp add:trans_on_def pwr_def)

lemma powrel3[intro?]:
  "refl_on (Pow X) (pwr X)"  
  by(auto simp add:refl_on_def pwr_def)

lemma powrel4a:
  "A \<subseteq> Pow X \<Longrightarrow> a \<in> Pow X \<Longrightarrow> lb (pwr X) A a \<Longrightarrow> a \<subseteq> X \<inter> \<Inter> A"
  by (metis Inf_greatest PowD converse_iff le_inf_iff pwr_memD ub_def)

lemma powrel4:
  "A \<subseteq> Pow X \<Longrightarrow> is_inf (pwr X) (Pow X) A (X \<inter>(\<Inter>A))" 
  apply(rule is_supI10, simp)
  apply(rule converseI)
  apply(rule pwr_memI)
  apply (simp add: Inter_lower le_infI2, simp add:powsimp1)
  apply(rule converseI)
  apply(rule pwr_memI)
  apply (metis powrel4a)
  by blast

lemma powrel5[intro?]:
  "A \<subseteq> Pow X \<Longrightarrow> is_sup (pwr X) (Pow X) A (\<Union>A)" 
  by(auto simp add:is_sup_def is_greatest_def ubd_def ub_def pwr_def)

lemma powrel6:
  "C \<subseteq> Pow X \<Longrightarrow> antisym_on C (pwr X)" 
   by (meson antisym_on_subset powrel1)

lemma powrel7:
  "C \<subseteq> Pow X \<Longrightarrow> trans_on C (pwr X)"  
  by (meson powrel2 trans_on_subset)  

lemma powrel8:
  "(x, y) \<in> pwr X \<Longrightarrow> x \<subseteq> y"  
  by (simp add: pwr_def) 

lemma powrel9:
  "\<lbrakk>A \<subseteq> C; C\<subseteq> Pow X\<rbrakk> \<Longrightarrow> is_sup (pwr X) (Pow X) A (\<Union>A)"
  by(auto simp add:is_sup_def is_greatest_def ubd_def ub_def pwr_def)

lemma powrel4b:
  "A \<subseteq> Pow X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> is_inf (pwr X) (Pow X) A (\<Inter>A)"
  by (metis Inf_lower2 Int_absorb1 equals0I powrel4 powsimp1) 

lemma uni_sup_fam:
  "\<lbrakk>S \<subseteq> Pow X; A \<subseteq> S; \<Union>A \<in> S\<rbrakk> \<Longrightarrow> is_sup (pwr (\<Union>S)) S A (\<Union>A) "
  by (meson powrel9 subset_Pow_Union sup_in_subset)

lemma uni_inf_fam:
  "\<lbrakk>S \<subseteq> Pow X; A \<subseteq> S; \<Inter>A \<in> S\<rbrakk> \<Longrightarrow> is_inf (pwr (\<Union>S)) S A (\<Inter>A) "
  by (metis Union_upper inf.absorb_iff2 le_supE powrel4 subset_Pow_Union subset_Un_eq sup_in_subset)

lemma binf_powrrel:
  "\<lbrakk>A \<in> Pow X; B \<in> Pow X\<rbrakk> \<Longrightarrow> is_inf (pwr X) (Pow X) {A, B} (A \<inter> B)"
  by(rule is_supI1,metis Inf_insert Inter_empty empty_not_insert empty_subsetI inf_top.right_neutral insert_subsetI is_supD1 powrel4b)

lemma lattice_id6:
  "\<lbrakk>trans R X; A \<subseteq> X; B \<subseteq> X; is_sup R X A s; is_inf R X B i\<rbrakk> \<Longrightarrow> (s, i) \<in> R \<Longrightarrow> (\<forall>a \<in> A. \<forall>b \<in> B. (a, b)\<in>R) "
  by (meson converse.cases in_mono is_supD1121 is_supE1 trans_onD)

lemma lattice_id7:
  "\<lbrakk>A \<subseteq> lbd R X B; is_sup R X A s; is_inf R X B i\<rbrakk> \<Longrightarrow> (s,i) \<in> R "
  using inf_imp_sup_lb is_sup_iso1  by metis

lemma lattice_id8:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> X; is_sup R X A s; is_inf R X B i;(\<forall>a \<in> A. \<forall>b \<in> B. (a, b)\<in>R)\<rbrakk> \<Longrightarrow> (s, i) \<in> R"
  by (meson converse_iff in_mono is_supE1 is_supE4 ubI)
  

lemma lattice_id9:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> X; is_sup R X A s; is_inf R X B i;(\<forall>a \<in> A. lb R B a)\<rbrakk> \<Longrightarrow> (s, i) \<in> R"
  using is_supD42 is_supE1 is_supD5 ubI lattice_id8 ubE by fastforce 

lemma least_inf:
  "\<lbrakk>antisym_on X R; is_least R X bot\<rbrakk> \<Longrightarrow> x \<in> X \<Longrightarrow> Inf R X {x, bot} = bot"
  by (metis Sup_def antisym_on_converse binary_supI1 greatestD1 greatestD2 sup_equality)

lemma least_sup:
  "\<lbrakk>antisym_on X R;is_least R X bot; (x,x)\<in> R\<rbrakk> \<Longrightarrow> x \<in> X \<Longrightarrow> Sup R X {x, bot} = x"
  by (meson binary_supI2 converseD greatestD11 greatestD2 sup_equality)

lemma greatest_inf:
  "\<lbrakk>antisym_on X R; is_greatest R X top; (x,x)\<in>R\<rbrakk> \<Longrightarrow> x \<in> X \<Longrightarrow> Inf R X {x, top} = x"
  by (metis Sup_def antisym_on_converse converseI converse_converse least_sup)


lemma greatest_sup:
  "\<lbrakk>antisym_on X R; is_greatest R X top\<rbrakk> \<Longrightarrow> x \<in> X \<Longrightarrow> Sup R X {x, top} = top"
  by (simp add: binary_supI1 greatestD11 greatestD2 sup_equality)



subsection MinimaMaxima

definition is_maximal::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_maximal R A x \<equiv> (x \<in> A) \<and> (\<forall>a. a \<in> A \<and> (x, a) \<in> R \<longrightarrow> a =x)"

definition is_minimal::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_minimal R A x \<equiv> (x \<in> A) \<and> (\<forall>a. a \<in> A \<and> (a, x) \<in> R\<longrightarrow> a = x)"

lemma maximalD1:
  "is_maximal R A x \<Longrightarrow> x \<in> A"
  by(simp add:is_maximal_def)

lemma maximalD2:
  "is_maximal R A x \<Longrightarrow>(\<forall>a. a \<in> A \<and> (x, a) \<in> R \<longrightarrow> a =x)"
  by(simp add:is_maximal_def)

lemma maximalD3:
  "is_maximal R A x \<Longrightarrow> a \<in> A \<Longrightarrow> (x, a) \<in> R \<Longrightarrow> a = x"
  by(simp add:is_maximal_def)

lemma maximalD4:
  "\<lbrakk>antisym R X; is_maximal R A x\<rbrakk> \<Longrightarrow> \<not>(\<exists>a \<in> A. (x,a)\<in>R \<and> x \<noteq> a)"
  by (metis maximalD3)


lemma maximalI1:
  "\<lbrakk>x \<in> A; (\<And>a. \<lbrakk>a \<in> A; (x, a) \<in> R\<rbrakk> \<Longrightarrow> a = x)\<rbrakk> \<Longrightarrow> is_maximal R A x"
  by(simp add:is_maximal_def)

subsection SupSemilattices


lemma ssupD2:
  "\<lbrakk>is_sup_semilattice R X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup R X {a, b} x) "
  by (simp add: is_sup_semilattice_def)

lemma ssupD3:
  "\<lbrakk>antisym_on X R; is_sup_semilattice R X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> is_sup R X {a, b} (Sup R X {a, b}) "
  using ssupD2 sup_equality by metis

lemma ssupD4:
  "\<lbrakk>antisym_on X R;is_sup_semilattice R X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow>  (Sup R X {a, b}) \<in> X"
  by (metis is_supE1 ssupD3) 

lemma bsup_geI1:
  "\<lbrakk>ord R X; is_sup_semilattice R X; a \<in> X; b \<in> X; c \<in> X; (c, a) \<in> R\<rbrakk>  \<Longrightarrow> (c, Sup R X {a, b}) \<in> R"
  by (simp add: binary_supD21 ssupD3 ssupD4)

lemma bsup_geI2:
  "\<lbrakk>ord R X;is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X; (c, b)\<in>R\<rbrakk>  \<Longrightarrow> (c, Sup R X {a, b}) \<in> R"
  by (simp add: binary_supD22 ssupD3 ssupD4)

lemma bsup_geI3:
  "\<lbrakk>ord R X; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X; (a, c) \<in> R; (b, c)\<in>R\<rbrakk> \<Longrightarrow> (Sup R X {a, b}, c) \<in> R"
  by (meson ssupD3 sup_ge3)

lemma bsup_rev:
  "\<lbrakk>ord R X; is_sup_semilattice R X; a \<in> X; b \<in> X; c \<in> X; (Sup R X {a, b}, c) \<in> R\<rbrakk>  \<Longrightarrow> (a, c)\<in>R \<and> (b, c)\<in>R"
  by (meson ge_sup_iff ssupD3)

lemma bsup_iff:
  "\<lbrakk>ord R X; is_sup_semilattice R X; a \<in> X; b \<in> X; c \<in> X\<rbrakk>  \<Longrightarrow> ((Sup R X {a, b}, c) \<in> R \<longleftrightarrow> (a, c)\<in>R \<and> (b, c)\<in>R)"
  using bsup_rev[of X R] bsup_geI3[of X R] by metis


lemma bsupI:
  "\<lbrakk>ord R X; is_sup_semilattice R X; (\<And>s. is_sup R X {a, b} s \<Longrightarrow> P s); a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> P (Sup R X {a, b})"
  by (metis is_sup_semilattice_def sup_equality)

lemma bsup_commute1:
  "\<lbrakk>ord R X; is_sup_semilattice R X; a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> Sup R X {a, b} = Sup R X {b, a}"
  by (simp add: insert_commute)

lemma bsup_assoc1:
  "\<lbrakk>ord R X; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Sup R X {a, b}, c} =Sup R X {a, Sup R X {b, c}}"
  proof-
    assume A:"ord R X" "is_sup_semilattice R X" "a \<in> X" "b \<in> X" "c \<in> X"
    obtain B0:"Sup R X {b, c} \<in> X" and B1:"(Sup R X {a, b}) \<in> X" by(simp add: A ssupD4)
    have B2:"(c, Sup R X {b, c}) \<in> R" by (meson A B0 binary_supD32 ssupD3)
    have B3:"(Sup R X {Sup R X {a, b}, c}, Sup R X {a, Sup R X {b, c}}) \<in> R"   by (metis A binary_supD32 bsup_commute1 bsup_geI2 bsup_geI3 ssupD3 ssupD4)
    also have B4:"(Sup R X {a, Sup R X {b, c}}, Sup R X {Sup R X {a, b}, c}) \<in> R"   by (metis A binary_supD31 binary_supD32 bsup_geI3 bsup_rev ssupD3 ssupD4)
    then show "Sup R X {Sup R X {a, b}, c}=Sup R X {a, Sup R X {b, c}}" by (meson A B0 B1 antisym_onD calculation ssupD4) 
qed

lemma binf_assoc1:
  "\<lbrakk>ord R X; is_inf_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf R X {Inf R X {a, b}, c} =Inf R X {a, Inf R X {b, c}}"
  using bsup_assoc1[of X "converse R" a b c]  by (simp add: Sup_def is_sup_semilattice_def)

lemma bsup_assoc11:
  "\<lbrakk>ord R X; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {c, Sup R X {a, b}} =Sup R X {a, Sup R X {b, c}}"
  by (metis bsup_assoc1 bsup_commute1)

lemma bsup_assoc14:
  "\<lbrakk>ord R X; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Sup R X {b, a}, c} =Sup R X {Sup R X {b, c},a}"
  by (metis bsup_assoc1 bsup_commute1)

lemma bsup_assoc15:
  "\<lbrakk>ord R X; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Sup R X {b, a}, c} =Sup R X {Sup R X {c,b},a}"
  by (metis bsup_assoc1 bsup_commute1)

lemma bsup_assoc2:
  "\<lbrakk>ord R X; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {a, Sup R X {b, c}} = Sup R X {b, Sup R X {a, c}}"
  by (metis bsup_assoc1 doubleton_eq_iff)

lemma binf_assoc2a:
  "\<lbrakk>ord R X; is_inf_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf R X {Inf R X {b, c},a} = Inf R X {b, Inf R X {a, c}}"
  by (metis binf_assoc1 doubleton_eq_iff)

lemma binf_assoc2b:
  "\<lbrakk>ord R X; is_inf_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf R X {Inf R X {b, c},a} = Inf R X {Inf R X {a, c},b}"
  by (metis binf_assoc1 doubleton_eq_iff)

lemma binf_assoc2c:
  "\<lbrakk>ord R X; is_inf_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf R X {a, Inf R X {b, c}} = Inf R X {Inf R X {a, c},b}"
  by (metis binf_assoc1 doubleton_eq_iff)

lemma binf_assoc2d:
  "\<lbrakk>ord R X; is_inf_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf R X {Inf R X {a, b}, c} = Inf R X {a, Inf R X {b, c}}"
  by (metis binf_assoc1 doubleton_eq_iff)

lemma bsup_idem2:
  "\<lbrakk>ord R X;is_sup_semilattice R X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow>  Sup R X {a, Sup R X {a, b}} =  Sup R X {a, b}"
  by (simp add: bsupI sup_equality sup_idem2)


lemma bsup_ge1:
  "\<lbrakk>antisym_on X R; is_sup_semilattice R X; a \<in> X;  b \<in> X; (b,b)\<in>R; (a, b)\<in>R\<rbrakk> \<Longrightarrow>  Sup R X {a, b} = b"
  by (simp add: binary_supI1 sup_equality)

lemma bsup_ge2:
  "\<lbrakk>antisym_on X R; is_sup_semilattice R X; a \<in> X;  b \<in> X; (a,a)\<in>R; (b, a)\<in>R\<rbrakk> \<Longrightarrow>  Sup R X {a, b} = a"
  by (simp add: binary_supI2 sup_equality)

lemma ge_bsup1:
  "\<lbrakk>antisym_on X R;is_sup_semilattice R X; a \<in> X; b \<in> X; Sup R X {a, b} = b\<rbrakk> \<Longrightarrow> (a, b)\<in>R"
  by (metis binary_supD31 ssupD3)

lemma ge_bsup2:
  "\<lbrakk>antisym_on X R;is_sup_semilattice R X; a \<in> X; b \<in> X; Sup R X {a, b} = a\<rbrakk> \<Longrightarrow>  (b, a)\<in>R"
  by (simp add: bsup_commute2 ge_bsup1)

lemma bsup_finite2:
  "\<lbrakk>ord R X; is_sup_semilattice R X; A \<subseteq> X;A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow>  is_sup R X A (Sup R X A)"
  by (simp add: bsup_finite ssupD3)

lemma fsup_geI1:
  "\<lbrakk>ord R X; is_sup_semilattice R X;  A \<subseteq> X;A \<noteq> {}; finite A; a \<in> A\<rbrakk> \<Longrightarrow> (a, Sup R X A) \<in>R"
  using is_supD1121[of R X A "Sup R X A" a]  bsup_finite2[of X R A] by blast

lemma fsup_ub:
  "\<lbrakk>ord R X; is_sup_semilattice R X;  A \<subseteq> X;A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow> ub R A (Sup R X A)"
  using is_supD32[of R X A "Sup R X A"] bsup_finite2[of X R A]   by (simp add: ubdD3)

lemma fsup_lub:
  "\<lbrakk>ord R X;is_sup_semilattice R X;  A \<subseteq> X;A \<noteq> {}; finite A; b \<in> ubd R X A\<rbrakk> \<Longrightarrow> (Sup R X A, b) \<in> R"
  using is_supE3[of R X A "Sup R X A" b] bsup_finite2[of X R  A] by fastforce

lemma fsup_lub2:
  "\<lbrakk>ord R X;is_sup_semilattice R X;  A \<subseteq> X;A \<noteq> {}; finite A; b \<in> X; ub R A b\<rbrakk> \<Longrightarrow>(Sup R X A, b) \<in> R"
  by (simp add: fsup_lub ubdI2)

lemma fsup_lub3:
  "\<lbrakk>ord R X; is_sup_semilattice R X;  A \<in> Fpow_ne X; b \<in> ubd R X A\<rbrakk> \<Longrightarrow> (Sup R X A, b) \<in> R"
  by (simp add: fpow_ne_iff2 fsup_lub)
lemma fsup_closedD1:
  "\<lbrakk>ord R X; is_fsup_closed R X A\<rbrakk> \<Longrightarrow> (\<And>a1 a2. a1 \<in> A \<Longrightarrow> a2 \<in> A \<Longrightarrow> Sup R X {a1, a2} \<in> A)"
  by (simp add: is_fsup_closed_def)

lemma finite_sup_closed2:
  assumes A0: " (\<And>a1 a2. a1 \<in> A \<Longrightarrow> a2 \<in> A \<Longrightarrow> Sup R X {a1, a2} \<in> A)" and 
          A1: "finite E" and
          A2: "E \<noteq> {}" and
          A3: "E \<subseteq> A" and
          A4: "A \<subseteq> X" and
          A5: "is_sup_semilattice R X" and 
          A6:"antisym_on X R" and 
          A7:"trans R X"
  shows "Sup R X E \<in> A"
  using A1 A2 A3 A4 A5
proof (induct E rule: finite_ne_induct)
  case (singleton x)
  then show ?case
    using A0 by fastforce
next
  case (insert x F)
  obtain s where A6: "is_sup R X F s"
    by (meson A4 A5 A6 A7 bsup_finite2 insert.hyps(1) insert.hyps(2) insert.prems(1) insert_subset subset_trans)
  have B0: "s \<in> A"
    by (metis A4 A5 A6 assms(7) insert.hyps(4) insert.prems(1) insert_subset sup_equality)
  have B1: "x \<in> A"
    using insert.prems(1) by auto
  obtain t where A7: "is_sup R X {x, s} t"
    by (meson A4 A5 A6 B1 in_mono is_supE1 ssupD2)
  have B2: "t \<in> A"
    by (metis A0 A7 B0 B1 assms(7) sup_equality)
  have B3: "t \<in> ubd R  X (insert x F)"
    by (metis A4 A6 A7 B2 assms(8) insert.prems(1) insert_commute insert_subset is_supE2 subset_iff sup_insert61 ub_double_iff1 ubd_mem_iff ubd_mem_insert)
  have B4: "\<And>y. y \<in> ubd R X (insert x F) \<longrightarrow> (t, y)\<in>R"
    by (meson A4 A6 A7 assms(8) bsup_commute insert.prems(1) insert_subset subset_trans sup_insert7)
  have B5: "is_sup R X (insert x F) t"
    by (simp add: B3 B4 is_supI5)
  then show ?case
    by (simp add: B2 assms(7) sup_equality)
qed

lemma sup_semilattice_fsup_closed:
  "\<lbrakk>ord R X;is_fsup_closed R X A; A \<subseteq> X; E \<subseteq> A; finite E; E \<noteq> {}; is_sup_semilattice R X\<rbrakk> \<Longrightarrow> Sup R X E \<in> A "
  by (metis finite_sup_closed2 is_fsup_closed_def)

lemma sup_semilattice_fsup:
  "\<lbrakk>ord R X;is_sup_semilattice R X; A \<in> Fpow_ne X\<rbrakk> \<Longrightarrow> is_sup R X A (Sup R X A)"
  by (simp add: bsup_finite2 fpow_ne_iff2)

lemma fsupI:
  "\<lbrakk>ord R X; is_sup_semilattice R X; (\<And>s E. is_sup R X E s \<Longrightarrow> P s); F \<in> Fpow_ne X\<rbrakk> \<Longrightarrow> P (Sup R X F)"
  using sup_semilattice_fsup by blast

lemma sup_semilattice_fsup_props0:
  "\<lbrakk>ord R X; is_sup_semilattice R X;a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {a, b, c}  \<in> X"
  by(erule fsupI,simp add:is_supE1,simp add: is_supE1,simp add: fpow_ne_iff2)

lemma sup_assoc_ubd1:
  "\<lbrakk>trans R X; a \<in>X; b \<in> X; c \<in> X; is_sup R X {b, c} s; x \<in> ubd R  X {a, s}\<rbrakk> \<Longrightarrow> x \<in> ubd R  X {a, b, c}"
  by (metis ge_sup_iff ub_double_iff1 ubd_mem_iff ubd_mem_insert)


lemma finite_inf_closed2:
  assumes A0: "\<And>a1 a2. a1 \<in> A \<Longrightarrow> a2 \<in> A \<Longrightarrow>  Inf R X {a1, a2} \<in> A" and 
          A1:"finite E" and
          A2:"E \<noteq> {}" and
          A3:"E \<subseteq> A" and
          A4:"A \<subseteq> X" and
          A5:"is_inf_semilattice R X" and 
          A6:"antisym R X" and 
          A7:"trans R X"
  shows "Inf R X E \<in> A"
  using A1 A2 A3 A4 A5
proof (induct E rule: finite_ne_induct)
  case (singleton x)  then show ?case    using A0 by fastforce
next
  case (insert x F)
  obtain i where A8:"is_inf R X F i"    by (metis A4 A5 A6 A7 antisym_on_converse bsup_finite2 insert.hyps(1) insert.hyps(2) insert.prems(1) insert_subset is_sup_semilattice_def subset_trans trans_on_converse)
  have B0:"i \<in> A" by (metis A4 A5 A6 A8 Sup_def antisym_on_converse insert.hyps(4) insert.prems(1) insert_subset sup_equality)
  have B1:"x \<in> A" using insert.prems(1) by auto
  obtain t where A9:"is_inf R X {x, i} t" by (meson A4 A5 A8 dual_order.trans insert.prems(1) insert_subset is_supE1 ssupD2)
  have B2:"t \<in> A" by (metis A0 A6 A9 B0 B1 antisym_on_converse sup_equality the_equality)  
  have B3:"t \<in> (lbd R X (insert x F))"  by (meson A4 A7 A8 A9 bsup_commute insert.prems(1) insertCI insert_subset is_supD1121 subset_trans sup_insert62 trans_on_converse ubd_mem_insert)
  have B4:"\<And>y. y \<in> (lbd R X (insert x F)) \<longrightarrow> (y,t)\<in>R"  by (meson A4 A7 A8 A9 bsup_commute converse_iff insert.prems(1) insert_subset subset_trans sup_insert7 trans_on_converse)
  have B5:"is_inf R X (insert x F) t"  by (simp add: B3 B4 is_supI5)
  then show ?case   by (metis B2 A6 Sup_def antisym_on_converse sup_equality)
qed


subsection Lattices

lemma lattI1:
  "\<lbrakk>X \<noteq> {}; (\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  (\<exists>x. is_inf R X {a, b} x) \<and>  (\<exists>x. is_sup R X {a, b} x))\<rbrakk> \<Longrightarrow> is_lattice R X"
  by (simp add: is_lattice_def)

lemma lattI2:
  "\<lbrakk>is_inf_semilattice R X; is_sup_semilattice R X\<rbrakk> \<Longrightarrow> is_lattice R X"
  by (simp add: is_sup_semilattice_def lattI1)

lemma lattI3:
  "is_inf_semilattice R X \<and> is_sup_semilattice R X \<Longrightarrow> is_lattice R X"
  by (simp add: lattI2)

lemma lattD1:
  "is_lattice R X \<Longrightarrow> X \<noteq> {}"
  by (simp add: is_lattice_def)

lemma lattD21:
  "\<lbrakk>is_lattice R X;  a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  (\<exists>x. is_inf R X {a, b} x) "
  by (simp add: is_lattice_def)

lemma lattD22:
  "\<lbrakk>is_lattice R X;  a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  (\<exists>x. is_sup R X {a, b} x) "
  by (simp add: is_lattice_def)

lemma lattD32:
  "\<lbrakk>antisym_on X R;is_lattice R X;  a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  is_sup R X {a, b} (Sup R X {a, b}) "
  by (metis lattD22 sup_equality)

lemma lattD31:
  "\<lbrakk>antisym_on X R; is_lattice R X;  a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  is_inf R X {a, b} (Inf R X {a, b})"
  by (metis Sup_def antisym_on_converse lattD21 sup_equality)

lemma lattD41:
  "is_lattice R X \<Longrightarrow> is_inf_semilattice R X"
  by (simp add: is_sup_semilattice_def is_lattice_def)

lemma lattD42:
  "is_lattice R X \<Longrightarrow> is_sup_semilattice R X"
  by (simp add: is_sup_semilattice_def is_lattice_def)

lemma lattD4:
  "is_lattice R X \<Longrightarrow> is_sup_semilattice R X \<and> is_inf_semilattice R X"
  by (simp add: is_sup_semilattice_def is_lattice_def)

lemma lattD5:
  "\<lbrakk>antisym_on X R; is_lattice R X; x \<in> X; y \<in> X; Sup R X {x, y} = y\<rbrakk> \<Longrightarrow> (x, y)\<in>R"
  by (simp add: ge_bsup1 lattD42)

lemma latt_iff:
  "is_lattice R X \<longleftrightarrow> (is_inf_semilattice R X) \<and> (is_sup_semilattice R X)"
  by(rule iffI,simp add:lattD4,simp add:lattI3)

lemma latt_ge_iff1:
  "\<lbrakk>ord R X; is_lattice R X; (y,y)\<in>R;x \<in>X; y \<in> X\<rbrakk> \<Longrightarrow> ((x, y)\<in>R \<longleftrightarrow> Sup R X {x, y} = y)"
  by (auto simp add: bsup_ge1 lattD42 lattD5)

lemma latt_ge_iff2:
  "\<lbrakk>ord R X;is_lattice R X; (x,x)\<in>R;x \<in>X; y \<in> X\<rbrakk> \<Longrightarrow> ((y, x)\<in>R \<longleftrightarrow> Sup R X {x, y} = x)"
  by (simp add: bsup_commute2 latt_ge_iff1)

lemma lattice_absorb1:
  "\<lbrakk>ord R X;is_lattice R X; (x,x)\<in>R;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Sup R X {x, Inf R X {x, y}} = x"
  by (meson binary_supD31 bsup_ge2 converseD is_supE1 lattD31 lattD42)

lemma lattice_absorb13:
  "\<lbrakk>ord R X;is_lattice R X; (x,x)\<in>R;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Sup R X {x, Inf R X {y,x}} = x"
  by (simp add: insert_commute lattice_absorb1)

lemma lattice_absorb12:
  "\<lbrakk>ord R X;is_lattice R X; (x,x)\<in>R;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Inf R X {x, y},x} = x"
  by (simp add: insert_commute lattice_absorb1)

lemma lattice_absorb14:
  "\<lbrakk>ord R X;is_lattice R X; (x,x)\<in>R;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Inf R X {y,x},x} = x"
  by (simp add: insert_commute lattice_absorb1)

lemma lattice_absorb15:
  "\<lbrakk>ord R X;is_lattice R X; (x,x)\<in>R;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Inf R X {x,y},x} = x"
  by (simp add: insert_commute lattice_absorb1)

lemma lattice_absorb2:
  "\<lbrakk>ord R X; is_lattice R X; (x,x)\<in>R;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Inf R X {x,Sup R X {x, y}} = x"
  by (meson antisym_on_converse binary_supD31 binary_supI2 converse_iff is_sup_unique lattD31 lattD32 lattD42 ssupD4)

lemma lattice_absorb21:
  "\<lbrakk>ord R X; is_lattice R X; (x,x)\<in>R;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Inf R X {Sup R X {x, y},x} = x"
  by (simp add: insert_commute lattice_absorb2)

lemma lattice_absorb22:
  "\<lbrakk>ord R X; is_lattice R X; (x,x)\<in>R;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Inf R X {x,Sup R X {y,x}} = x"
  by (simp add: insert_commute lattice_absorb2)

lemma lattice_absorb23:
  "\<lbrakk>ord R X; is_lattice R X; (x,x)\<in>R;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Inf R X {Sup R X {y,x},x} = x"
  by (simp add: insert_commute lattice_absorb2)

lemma distrib_sup_le: 
  "\<lbrakk>ord R X;is_lattice R X;x \<in>X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> (Sup R X {x, Inf R X {y, z}}, Inf R X {Sup R X {x, y}, Sup R X {x, z}})\<in>R"
  by (smt (verit, del_insts) binary_supD31 binary_supD32 converse_iff is_supE1 lattD31 lattD32 sup_ge3 sup_ge5 trans_on_converse)

lemma distrib_inf_le: 
  "\<lbrakk>ord R X;is_lattice R X; x \<in>X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> (Sup R X {Inf R X {x, y}, Inf R X {x, z}}, Inf R X {x, Sup R X {y, z}}) \<in> R"
  by (smt (verit, del_insts) binary_supD31 binary_supD32 converse_iff is_supE1 lattD31 lattD32 sup_ge3 sup_ge5 trans_on_converse)

lemma mod_sup_le:
  "\<lbrakk>ord R X; is_lattice R X; x \<in> X; y \<in> X; z \<in> X; (x, z)\<in>R\<rbrakk> \<Longrightarrow> (Sup R X {x, Inf R X {y, z}}, Inf R X {Sup R X {x, y}, z})\<in>R"
  by (smt (verit, del_insts) binary_supD31 binary_supD32 converse_iff is_supE1 lattD31 lattD32 sup_ge3 sup_ge4 trans_on_converse)
subsection DistributiveLattices

lemma distribD1:
  assumes A0:"is_lattice R X" and
          A1:"ord R X" and 
          A2:"refl R X" and
          A3:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}" and
          A4:" x \<in> X \<and> y \<in> X \<and> z \<in> X"
  shows "Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
proof-
  obtain A5:"is_sup_semilattice R X" and A6:"is_inf_semilattice R X" using A0 lattD4 by blast
  obtain A7:"Inf R X {y, z} \<in> X" and A8:"Inf R X {x, z} \<in> X" and A9:"Sup R X {x, y} \<in> X"  by (meson A0 A1 A4 A5 is_supE1 lattD31 ssupD4)
  have B0:"Sup R X {x, Inf R X {y, z}} = Sup R X {Sup R X {x, Inf R X {x, z}}, Inf R X {y, z}}"  (*x \<or> (x \<and> z) = ((x \<or> (x \<and> z) \<or> (z \<and> y)))*)
    by (metis A0 A1 A2 A4 lattice_absorb1 reflD1)
  have B1:"... = Sup R X {x, Sup R X {Inf R X {z, x}, Inf R X {z, y}}}" (* x \<or> ((z \<and> x) \<or> (z \<and> y)) *)
    using bsup_assoc14[of X R "Inf R X {x, z}" x "Inf R X {y, z}"]
    by (metis A1 A4 A5 A7 A8 bsup_assoc15 doubleton_eq_iff)
  have B2:"... = Sup R X {x, Inf R X {z, Sup R X {x, y}}}" (*x \<or> (z \<and> (x \<or> y))*)
    by (simp add: A3 A4) 
  have B3:"... = Sup R X {Inf R X {Sup R X {x, y}, x}, Inf R X {Sup R X {x, y}, z}}"
    by (metis A0 A1 A2 A4 lattice_absorb21[of X R x y] doubleton_eq_iff refl_def)
  have B4:"... = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
    by (simp add: A3 A4 A9)
  show ?thesis
    by (simp add: B0 B1 B2 B3 B4)
qed


lemma distribD2:
  assumes A0:"is_lattice R X" and
          A1:"ord R X" and 
          A2:"refl R X" and
          A3: "\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}" and
          A4: "x \<in> X \<and> y \<in> X \<and> z \<in> X"
  shows "Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}"
proof-
  obtain A5:"is_sup_semilattice R X" and A6:"is_inf_semilattice R X" using A0 lattD4 by blast
  obtain A7:"Sup R X {z, y} \<in> X" and A8:"Sup R X {x, z} \<in> X" and A9:"Inf R X {x, y} \<in> X" by (meson A0 A1 A4 A5 is_supE1 lattD31 ssupD4) 
  have B0:"Inf R X {x, Sup R X {y, z}} = Inf R X {Inf R X {x, Sup R X {x, z}}, Sup R X {y, z}}"(*x \<and> (x \<or> z) = ((x \<and> (x \<or> z)) \<and> (z \<or> y)))*)
    by (metis A0 A1 A2 A4 lattice_absorb2 reflE1)  
  have B1:"... = Inf R X {Inf R X {x, Sup R X {z, x}}, Sup R X {z, y}}" (*(x \<and> (z \<or> x)) \<and> (z \<or> y)*)
    by (simp add: insert_commute)
  have B2:"... = Inf R X {x, Inf R X {Sup R X {z, x}, Sup R X {z, y}}}" (* x \<and> ((z \<or> x) \<or> (z \<or> y)) *)
    using binf_assoc2d[of X R x "Sup R X {z, x}" "Sup R X {z, y}"]  by (simp add: A1 A4 A5 A6 ssupD4)
  have B3:"... = Inf R X {x, Sup R X {z, Inf R X {x, y}}}" (*x \<and> (z \<or> (x \<and> y))*)
    by (simp add: A3 A4) 
  have B4:"... = Inf R X {Sup R X {Inf R X {x, y}, x}, Sup R X {Inf R X {x, y}, z}}" (* ((x \<and> y) \<or> x) \<and> ((x \<and> y) \<or> z) *)
    by (metis A0 A1 A2 A4 lattice_absorb15[of X R x y] doubleton_eq_iff refl_def)
  have B5:"... = Sup R X {Inf R X {x, y}, Inf R X {x, z}}"
    by (simp add: A3 A4 A9)
  show ?thesis
    by (simp add: B0 B1 B2 B3 B4 B5)
qed


lemma distribD3:
  assumes A0:"is_lattice R X" and
          A1:"ord R X" and 
          A2:"refl R X" and
          A3:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> (Inf R X {Sup R X {x, y}, Sup R X {x, z}}, Sup R X {x, Inf R X {y, z}})\<in>R"
  shows      "\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
proof-
  fix x y z assume A4:"x\<in>X""y\<in>X""z\<in>X"
  let ?a="Sup R X {x, Inf R X {y, z}}" let ?b="Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
  obtain A5:"?a\<in>X" and A6:"?b\<in>X"  by (meson A0 A1 A4(1) A4(2) A4(3) is_supE1 lattD31 lattD42 ssupD4)
  have B0:"(?a, ?b)\<in>R"   by (simp add: A0 A1 A4(1) A4(2) A4(3) distrib_sup_le) 
  also have B1:"(?b, ?a)\<in>R" by (simp add: A3 A4(1) A4(2) A4(3)) 
  then show "?a=?b" by (meson A1 A5 A6 antisym_onD calculation)
qed

lemma distribD4:
  assumes A0:"is_lattice R X" and
          A1:"ord R X" and 
          A2:"refl R X" and
          A3:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> (Inf R X {x, Sup R X {y, z}}, Sup R X {Inf R X {x, y}, Inf R X {x, z}})\<in>R"
  shows      "\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}"
proof-
  fix x y z assume A4:"x\<in>X""y\<in>X""z\<in>X"
  let ?a="Inf R X {x, Sup R X {y, z}}" let ?b="Sup R X {Inf R X {x, y}, Inf R X {x, z}}"
  obtain A5:"?a\<in>X" and A6:"?b\<in>X"  by (meson A0 A1 A4(1) A4(2) A4(3) is_supE1 lattD31 lattD42 ssupD4)
  have B0:"(?a, ?b)\<in>R"  using A3 A4(1) A4(2) A4(3) by presburger
  also have B1:"(?b, ?a)\<in>R" by (simp add: A0 A1 A4(1) A4(2) A4(3) distrib_inf_le)
  then show "Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}" by (meson A1 A5 A6 antisym_onD calculation)
qed


lemma distI3:
  assumes A0:"is_lattice R X" and
          A1:"ord R X" and 
          A2:"refl R X" and
          A3:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> (Inf R X {x, Sup R X {y, z}}, Sup R X {Inf R X {x, y}, Inf R X {x, z}})\<in>R" 
  shows      "\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow>  Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
proof-
  have B0:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}"
    by (metis A0 A1 A3 distrib_inf_le antisym_on_def is_supE1 lattD31 lattD42 ssupD4)
  then show B1:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}" 
  proof-
     fix x y z assume A4:"x \<in> X" "y \<in> X" "z \<in> X"
     then show "Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
      by(simp add: A0 A1 A2 A3 A4 B0 distribD1[of R X x y z])
  qed
qed




lemma distr_latticeI1:
  "\<lbrakk>ord R X; refl R X; is_lattice R X; (\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> (Inf R X {Sup R X {x, y}, Sup R X {x, z}}, Sup R X {x, Inf R X {y, z}})\<in>R)\<rbrakk> \<Longrightarrow> distributive_lattice R X"
  by(simp add:distributive_lattice_def distribD3)

lemma distr_latticeI2:
  "\<lbrakk>ord R X; refl R X; is_lattice R X; (\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> (Inf R X {x, Sup R X {y, z}}, Sup R X {Inf R X {x, y}, Inf R X {x, z}})\<in>R)\<rbrakk> \<Longrightarrow> distributive_lattice R X"
  by(simp add:distributive_lattice_def distI3)


lemma distr_latticeD1:
  "\<lbrakk>distributive_lattice R X; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow>  Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}} "
  by (simp add: distributive_lattice_def insert_commute)

lemma distr_latticeD2:
  "\<lbrakk>distributive_lattice R X; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow>  Sup R X {Inf R X {y, z}, x} = Inf R X {Sup R X {y, x}, Sup R X {z, x}}"
  by (simp add: distributive_lattice_def insert_commute)
 
lemma distr_latticeD3:
  "\<lbrakk>ord R X; refl R X; distributive_lattice R X; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow>  Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}"
  using distribD2 distributive_lattice_def by fastforce
 
lemma distr_latticeD4:
  "\<lbrakk>ord R X; refl R X; distributive_lattice R X; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow>  Inf R X {Sup R X {y, z}, x} = Sup R X {Inf R X {y, x}, Inf R X {z, x}}"
  by (simp add: distr_latticeD3 insert_commute)


lemma lattice_ne_inf_le_sup:
  "\<lbrakk>trans R X; A \<subseteq> X; A \<noteq> {}; is_inf R X A i; is_sup R X A s\<rbrakk> \<Longrightarrow> (i, s) \<in> R"
  by (meson converse_iff equals0I in_mono is_supD1121 is_supE1 trans_on_def)

lemma lattice_in_inf_le_sup:
  "\<lbrakk>trans R X; A \<subseteq> X; B \<subseteq> X; A \<inter> B \<noteq> {}; is_inf R X A i; is_sup R X B s\<rbrakk> \<Longrightarrow> (i, s)\<in>R"
proof-
  assume A0:"trans R X" "A \<subseteq> X" "B \<subseteq> X" "A \<inter> B \<noteq> {}" "is_inf R X A i"  "is_sup R X B s"
  obtain x where B0:"x \<in> A \<inter> B"   using A0(4) by blast
  obtain B1:"x \<in> X"using A0(2) B0 by blast
  then obtain B2:"(i, x)\<in>R" and B3:"(x,s)\<in>R"  using A0(5) A0(6) B0 is_supD1121 by fastforce
  then show "(i,s)\<in>R" by (meson A0(1) A0(5) A0(6) B1 is_supE1 trans_onD)
qed

lemma lattice_id0:
  "\<lbrakk>ord R X; is_lattice R X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> lb R {Sup R X {x, y}, Sup R X {y, z}, Sup R X {x, z}} (Inf R X {x, y})"
  apply(rule ubI)
  apply(auto)
  apply (metis binary_supD31 bsup_geI1 converseD is_supE1 lattD31 lattD42)
  apply (metis binary_supD32 bsup_geI1 converseD is_supE1 lattD31 lattD42)
  by (metis binary_supD31 bsup_geI1 converseD is_supE1 lattD31 lattD42)

lemma lattice_id1:
  "\<lbrakk>ord R X; is_lattice R X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow>  lb R {Sup R X {x, y}, Sup R X {y, z}, Sup R X {x, z}} (Inf R X {y, z})"
  apply(rule ubI)
  apply(auto)
  apply (metis binary_supD31 bsup_geI2 converseD is_supE1 lattD31 lattD42)
  apply (metis binary_supD32 bsup_geI2 converseD is_supE1 lattD31 lattD42)
  by (metis binary_supD32 bsup_geI2 converseD is_supE1 lattD31 lattD42)
  

lemma lattice_id2:
  "\<lbrakk>ord R X; is_lattice R X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> lb R {Sup R X {x, y}, Sup R X {y, z}, Sup R X {x, z}} ( Inf R X {x, z})"
  using lattice_id0[of X R x z y]  by (simp add: insert_commute)

lemma lattice_id3:
  "\<lbrakk>ord R X;is_lattice R X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> ub R {Inf R X {x, y}, Inf R X {y, z}, Inf R X {x, z}} (Sup R X {x, y})"
  apply(rule ubI)
  apply(auto)
  apply (metis binary_supD31 bsup_geI1 converseD is_supE1 lattD31 lattD42)
  apply (metis binary_supD31 bsup_geI2 converseD is_supE1 lattD31 lattD42)
  by (metis binary_supD31 bsup_geI1 converseD is_supE1 lattD31 lattD42)

lemma lattice_id4:
  "\<lbrakk>ord R X;is_lattice R X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow>  ub R {Inf R X {x, y}, Inf R X {y, z}, Inf R X {x, z}} (Sup R X {y, z})"
  apply(rule ubI)
  apply(auto)
  apply (metis binary_supD32 bsup_geI1 converseD is_supE1 lattD31 lattD42)
  apply (metis binary_supD31 bsup_geI1 converseD is_supE1 lattD31 lattD42)
  by (metis binary_supD32 bsup_geI2 converseD is_supE1 lattD31 lattD42)


lemma lattice_id5:
  "\<lbrakk>ord R X;is_lattice R X; x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow>  ub R {Inf R X {x, y}, Inf R X {y, z}, Inf R X {x, z}} (Sup R X {x, z})"
  using lattice_id3[of X R x z y] by (simp add: insert_commute)
lemma distr_latticeD5:
  "distributive_lattice R X \<Longrightarrow> is_lattice R X" 
  by (simp add: distributive_lattice_def)

lemma distrib_I3:
  "\<lbrakk>ord R X;distributive_lattice R X;refl R X;x\<in>X;y\<in>X;z\<in>X ;Inf R X {x, z} = Inf R X {y, z}; Sup R X {x, z}=Sup R X {y, z}\<rbrakk> \<Longrightarrow> x=y"
proof-
  assume A0:"ord R X" "distributive_lattice R X" "refl R X" "x\<in>X" "y\<in>X"  "z\<in>X"  " Inf R X {x, z} = Inf R X {y, z}" " Sup R X {x, z}=Sup R X {y, z}"
  obtain A1:"is_lattice R X" and A2:"(x,x)\<in>R"  by (metis A0(2) A0(3) A0(4) distr_latticeD5 reflE1) 
  then have B0:"x = Inf R X {x, Sup R X {x, z}}" using A1 A0(1,3,4,6) lattice_absorb2[of X R x z] by simp
  also have B1:"... = Inf R X {x, Sup R X {y, z}}"  by (simp add: A0(8))
  also have B2:"... = Sup R X {Inf R X {x, y}, Inf R X {x, z}}" using A0(1-6) distr_latticeD3[of X R x y z] by fastforce
  also have B3:"... = Sup R X {Inf R X {y, x}, Inf R X {y, z}}"   by (simp add: A0(7) insert_commute) 
  also have B4:"... = Inf R X {y, Sup R X {x, z}}"   by (simp add: A0(1-6) distr_latticeD3)
  also have B5:"... = Inf R X {y, Sup R X {y, z}}"   by (simp add: A0(8))
  also have B6:"... = y"   by (meson A0(1) A0(3) A0(5) A0(6) A1 lattice_absorb2 refl_def)
  then show "x=y"   by (simp add: calculation)
qed

subsection CompleteLattices

lemma csupD2:
  "\<lbrakk>ord R X; is_csup_semilattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup R X A x)"
  by (simp add: is_csup_semilattice_def)
lemma csupD4:
  "\<lbrakk>ord R X; is_csup_semilattice R X;  A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_sup R X A (Sup R X A)"
  by (metis csupD2 sup_equality)
lemma csupD50:
  "\<lbrakk>ord R X; is_csup_semilattice R X;  A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (Sup R X A) \<in> X"
  by (metis csupD4 is_supE1)

lemma csupD51:
  "\<lbrakk>ord R X; is_csup_semilattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> ub R A (Sup R X A)"
  by (meson csupD4 is_supE2)


 lemma csupD61:
  "\<lbrakk>ord R X; is_csup_semilattice R X;  A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> b \<in> ubd R X A \<Longrightarrow> (Sup R X A, b) \<in> R "
  by (meson csupD4 is_supD5 ubdD2 ubdD3)   


lemma cinfD2:
  "\<lbrakk>ord R X; is_cinf_semilattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_inf R X A x)"
  by (simp add: is_cinf_semilattice_def)

lemma clatD21:
  "\<lbrakk>ord R X; is_clattice R X; A \<subseteq> X\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup R X A x)"
  by (simp add: is_clattice_def)

lemma clatD22:
  "\<lbrakk>ord R X; is_clattice R X; A \<subseteq> X\<rbrakk> \<Longrightarrow> (\<exists>x. is_inf R X A x)"
  by (meson clatD21 inf_if_sup_lb ubd_sub)

lemma clatD1:
  "is_clattice R X \<Longrightarrow> is_csup_semilattice R X"
  by (simp add: is_clattice_def is_csup_semilattice_def)

lemma clatD2:
  "is_clattice R X \<Longrightarrow> is_cinf_semilattice R X"
  by (metis inf_if_sup_lb is_cinf_semilattice_def is_clattice_def ubd_sub)

lemma csupD3:
  "is_csup_semilattice R X \<Longrightarrow> (\<exists>x. is_greatest R X x)"
  by (metis is_csup_semilattice_def order_refl sup_max_eq2)

lemma cinfD4:
  "\<lbrakk>ord R X; is_cinf_semilattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_inf R X A (Inf R X A)"
  by (metis antisym_on_converse cinfD2 is_sup_unique the1I2)

lemma clatD41:
  "\<lbrakk>ord R X; is_clattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_sup R X A (Sup R X A)"
  by (simp add: clatD21 sup_exI)

lemma cinfD50:
  "\<lbrakk>ord R X; is_cinf_semilattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (Inf R X A) \<in> X"
  by (meson cinfD4 is_supE1)


lemma cinfD61:
  "\<lbrakk>ord R X; is_cinf_semilattice R X;  A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> b \<in> lbd R X A \<Longrightarrow> (b, Inf R X A) \<in> R "
  by (metis cinfD4 converseD is_supE3)

lemma cinfD62:
  "\<lbrakk>ord R X; is_cinf_semilattice R X;  A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> b \<in> X \<Longrightarrow> lb R A b \<Longrightarrow>  (b,Inf R X A)\<in>R"
  by (simp add: cinfD61 ubdI2)

lemma csup_inf:
  "\<lbrakk>ord R X; is_csup_semilattice R X; A \<subseteq> X; lbd R X A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_inf R X A x)"
  by (meson ubd_sub csupD2 inf_if_sup_lb)


lemma csup_fsup:
  "is_csup_semilattice R X \<Longrightarrow> is_sup_semilattice R X"
  by (simp add: is_csup_semilattice_def is_sup_semilattice_def)

lemma cinf_sinf:
  "is_cinf_semilattice R X \<Longrightarrow> is_inf_semilattice R X"
  by (simp add: is_cinf_semilattice_def is_sup_semilattice_def)

lemma clatD31:
  "\<lbrakk>ord R X; is_clattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Sup R X A \<in> X"
  by (simp add: clatD1 csupD50)

lemma clatD32:
  "\<lbrakk>ord R X; is_clattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Inf R X A \<in> X"
  by (simp add: clatD2 cinfD50)
lemma clat_lattice:
  "is_clattice R X \<Longrightarrow> is_lattice R X"
  using cinf_sinf clatD1 clatD2 csup_fsup is_lattice_def ssupD2 by fastforce

lemma sup_iso1b:
  "\<lbrakk>ord R X; is_csup_semilattice R X; A \<noteq> {}; A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> (Sup R X A, Sup R X B)\<in>R"
  by (metis csupD4 dual_order.trans is_sup_iso1 ne_subset_ne)

lemma sup_iso1:
  "\<lbrakk>ord R X;is_clattice R X; A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> (Sup R X A, Sup R X B)\<in>R"
  by (metis clatD21 dual_order.trans is_sup_iso1 sup_equality)

lemma sup_iso2:
  "\<lbrakk>ord R X;is_clattice R X; is_clattice R Y;A \<subseteq> Y; Y \<subseteq> X; Y \<noteq> {}\<rbrakk> \<Longrightarrow> (Sup R X A, Sup R Y A)\<in>R"
  by (smt (verit, ccfv_SIG) antisym_on_subset clatD21 is_sup_iso2 subset_trans sup_equality trans_on_subset)

lemma inf_anti1:
  "\<lbrakk>ord R X; is_clattice R X; A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> (Inf R X B, Inf R X A)\<in>R"
  by (smt (verit, ccfv_SIG) antisym_on_converse clatD22 converseD is_sup_iso1 is_sup_unique subset_trans the_equality)

lemma pow_is_clattice2:
  "is_inf (pwr X) (Pow X) {} X"
  by (metis Union_Pow_eq empty_subsetI inf_if_sup_lb powrel5 subset_Pow_Union ubd_empty)

lemma pow_is_clattice:
  "is_clattice (pwr X) (Pow X)"
  by (meson Pow_not_empty is_clattice_def powrel5)

section Functions
subsection Isotonicity

lemma isotoneI1:
  "(\<And>x1 x2. x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> (x1, x2) \<in> Rx \<Longrightarrow> (f x1, f x2) \<in> Ry) \<Longrightarrow> isotone Rx X Ry f" 
  by (simp add: isotone_def)

lemma isotoneD1:
  "isotone Rx X Ry f \<Longrightarrow> x1 \<in> X \<Longrightarrow> x2 \<in> X \<Longrightarrow> (x1, x2) \<in> Rx \<Longrightarrow> (f x1, f x2) \<in> Ry" 
  by (simp add: isotone_def)

lemma isotoneD2:
  "isotone Rx X Ry f \<Longrightarrow> A \<subseteq> X \<Longrightarrow> isotone Rx A Ry f"  
  by (simp add: isotone_def subset_iff) 

lemma isotone_emp:
  "isotone Rx {} Ry f"
   by(blast intro:isotoneI1)

lemma isotoneD31: 
  "\<lbrakk>isotone R X Ry f; ub R A b; A \<subseteq> X; b \<in> X \<rbrakk> \<Longrightarrow> ub Ry (f`A) (f b)" 
   by (simp add: isotone_def subsetD ubE ub_imageI)

lemma isotoneD32: 
  "\<lbrakk>isotone R X Ry f; lb R A b; A \<subseteq> X; b \<in> X \<rbrakk> \<Longrightarrow> lb Ry (f`A) (f b)"
  by (meson converse.cases converseI isotoneD1 subsetD ubE ub_imageI) 


lemma isotoneD41: 
   "\<lbrakk>isotone R X Ry f; b \<in>ubd R X A; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f b) \<in> ubd Ry (f`X) (f`A)"
   by (simp add: isotoneD31 ubd_mem_iff)

lemma isotoneD42: 
   "\<lbrakk>isotone R X Ry f; b \<in>lbd R X A; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f b) \<in> lbd Ry (f`X) (f`A)"
   by (simp add: isotoneD32 ubd_mem_iff)

lemma isotoneD51:
   "\<lbrakk>isotone R  X Ry f; is_greatest R A x; A \<subseteq> X\<rbrakk> \<Longrightarrow> is_greatest Ry (f`A) (f x)"
    by (meson greatestD11 greatestD12 greatestI2 image_eqI isotoneD31 isotoneD2 order_refl) 

lemma isotoneD52:
   "\<lbrakk>isotone R  X Ry f; is_least R A x; A \<subseteq> X\<rbrakk> \<Longrightarrow> is_least Ry (f`A) (f x)"
  by (meson is_greatest_def isotoneD2 isotoneD42 order_refl)

lemma isotoneD61:
  "\<lbrakk>isotone R  X Ry f; is_sup R X A x; A \<subseteq> X\<rbrakk> \<Longrightarrow> ub Ry (f`A) (f x)" 
  by (simp add: is_supE1 is_supE2 isotoneD31) 

lemma isotoneD62:
  "\<lbrakk>isotone R  X Ry f; is_inf R X A x; A \<subseteq> X\<rbrakk> \<Longrightarrow> lb Ry (f`A) (f x)"
  by (simp add: is_supE1 is_supE2 isotoneD32) 

subsection Extensivity

lemma extensiveI1:
  "(\<And>x. x \<in> X \<Longrightarrow> (x, f x) \<in> R) \<Longrightarrow> extensive R X f" 
  by (simp add:extensive_def)

lemma extensiveD1:
  "extensive R X f \<Longrightarrow> x \<in> X \<Longrightarrow> (x, f x) \<in> R" 
  by (simp add:extensive_def)

lemma extensive_sub:
  "extensive R X f \<Longrightarrow> A \<subseteq> X \<Longrightarrow> extensive R A f" 
  by (simp add: extensive_def in_mono) 

lemma extensive_emp:
  "extensive R {} f"  
  by (simp add: extensive_def) 

lemma extensiveD2:
  "\<lbrakk>trans R X; (f`X) \<subseteq> X; extensive R X f; ub R (f`X) b; b \<in> X\<rbrakk> \<Longrightarrow> ub R X b"
proof(rule ubI)
  fix a assume A0:"trans R X " "f`X \<subseteq> X"  "extensive R X f" "ub R (f`X) b" "b \<in> X" "a\<in>X"
  then have "(a, f a)\<in>R"  by (simp add: extensiveD1)
  also have "(f a, b)\<in>R" by(meson A0 fbdE1)
  then show "(a,b)\<in>R" using A0(1) trans_onD[of X R a "f a" b]
    using A0(2) A0(5) A0(6) calculation by blast
qed
    
lemma extensiveD3:
  "\<lbrakk>trans R X;(f`X) \<subseteq> X;extensive R X f; x \<in> X; y \<in> X; (x, y)\<in>R\<rbrakk> \<Longrightarrow> (x,f y)\<in>R"
  using extensiveD1[of R X f y] trans_onD[of X R x y "f y"] by blast

lemma extensiveD4:
  "\<lbrakk>trans R X; extensive R X f; (f`X) \<subseteq> X; x1 \<in> X;x2 \<in> X; (f x2) \<in> X;  (f x1, f x2)\<in>R\<rbrakk> \<Longrightarrow> (x1, (f x2))\<in>R"
  using extensiveD1[of R X f x1] trans_onD[of X R x1 "f x1" "f x2"] by blast

lemma extensive_ub:
  "trans R X \<Longrightarrow> extensive R X f \<Longrightarrow> f ` X \<subseteq> X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> b \<in> ubd R X (f ` A) \<Longrightarrow> a \<in> A \<Longrightarrow> (a, b) \<in> R"
proof-
  fix a assume A0:"trans R X" "extensive R X f" "f`X \<subseteq> X" "A \<subseteq> X" " b \<in> ubd R X (f ` A)" "a \<in> A"
    then have "(a, f a)\<in>R" by (metis extensiveD1 in_mono)  
    also have "(f a, b)\<in>R"  by (meson A0(5) A0(6) fbdE1 ubdD3) 
    then show "(a,b)\<in>R" using A0(1) trans_onD[of X R a "f a" b]
      by (metis A0(3) A0(4) A0(5) A0(6) calculation image_subset_iff in_mono ubdD2)
qed
  

lemma extensive_ub_imp0:
  "trans R X \<Longrightarrow> extensive R X f \<Longrightarrow> f ` X \<subseteq> X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> b \<in> ubd R (f ` X) (f ` A) \<Longrightarrow> ub R A b"
  apply(rule ubI)
  proof-
    fix a assume A0:"trans R X" "extensive R X f" "f`X \<subseteq> X" "A \<subseteq> X" " b \<in> ubd R (f ` X) (f ` A)" "a \<in> A"
    then have "(a, f a)\<in>R" by (metis extensiveD1 in_mono)  
    also have "(f a, b)\<in>R"  by (meson A0(5) A0(6) fbdE1 ubdD3) 
    then show "(a,b)\<in>R" using A0(1) trans_onD[of X R a "f a" b]
      by (metis A0(3) A0(4) A0(5) A0(6) calculation image_subset_iff in_mono ubdD2)
qed

lemma extensive_ub_imp:
  "\<lbrakk>trans R X; extensive R X f ; (f`X \<subseteq> X); A \<subseteq> X ; b \<in> ubd R (f`X) (f`A) \<rbrakk> \<Longrightarrow> b \<in> ubd R X A"
  apply(rule ubdI2,simp add: extensive_ub_imp0)
  using ubd_mem_iff2 by fastforce

lemma extensive_ub_imp2:
  "\<lbrakk>trans R X;extensive R X f; (f`X \<subseteq> X); A \<subseteq> X; b \<in> ubd R X (f`A)\<rbrakk> \<Longrightarrow> b \<in> ubd R X A"
  by(rule ubdI,simp add: extensive_ub,simp add: ubd_mem_iff2)

lemma is_iso_extD1:
  "\<lbrakk>isotone R X R f;  extensive R X f;  (f`X \<subseteq> X);  x \<in> X\<rbrakk> \<Longrightarrow> (f x, f (f x))\<in>R"
  by (simp add: extensive_def image_subset_iff)

lemma is_iso_sup:
  "isotone R X R f \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_sup R X A x \<Longrightarrow> is_sup R (f`X) (f`A) y  \<Longrightarrow> (y, f x)\<in>R"
  by (simp add: is_supE1 is_supE4 isotoneD61)

lemma is_iso_inf:
  "isotone R X R f \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_inf R A X x \<Longrightarrow> is_inf R (f`X) (f`A) y  \<Longrightarrow> (f x, y)\<in>R"
  by (meson converseD in_mono is_supE1 is_supE2 isotoneD32 order_refl ubE)
subsection Idempotency

lemma idempotentD1:
  "\<lbrakk>idempotent X f; x \<in> X \<rbrakk> \<Longrightarrow>  f (f x) = f x"
  by (simp add: idempotent_def)

lemma idempotentD3:
  "\<lbrakk>idempotent X f; y \<in> f`X \<rbrakk> \<Longrightarrow>  f y = y"
  by (auto simp add: idempotent_def)

lemma iso_idemD1:
  "\<lbrakk>(x,x)\<in>R;isotone R X R f; idempotent X f; x \<in> X\<rbrakk> \<Longrightarrow> (f x, f (f x))\<in>R"
  by (simp add: idempotentD1 isotoneD1)

lemma iso_idemD2:
  "\<lbrakk>isotone R X R f; idempotent X f;  x1 \<in> X;x2 \<in> X; (f x2) \<in> X;  (x1,f x2)\<in>R\<rbrakk> \<Longrightarrow> (f x1,f x2)\<in>R"
   using idempotentD1[of X  f x2] isotoneD1[of R X R f x1 "f x2"] by presburger 
lemma iso_idemD3:
  "\<lbrakk>isotone R X R f; idempotent X f; f`X \<subseteq> X; x1 \<in> X;x2 \<in> X;   (x1,f x2)\<in>R\<rbrakk> \<Longrightarrow> (f x1,f x2)\<in>R"
  by (simp add: image_subset_iff iso_idemD2)
lemma idemp_iff:
  "idempotent X f \<longleftrightarrow> (\<forall>x \<in> X. (f \<circ> f) x = f x)"
  using idempotent_def by auto
lemma idempotentI2:
  "\<lbrakk>antisym R X; extensive R X f; isotone R X R f;  f`X \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> (f (f x), f x)\<in>R)\<rbrakk> \<Longrightarrow> idempotent X f"
  by (simp add: antisym_onD idempotent_def image_subset_iff is_iso_extD1)

lemma idempotent_isotoneD1:
  "\<lbrakk>idempotent X f; isotone R X R f;  f`X \<subseteq> X;  y \<in> f`X;  x \<in> X; (x, y)\<in>R\<rbrakk> \<Longrightarrow> (f x, y)\<in>R"
   using rev_subsetD[of "y" "f`X" "X"] isotoneD1[of R "X" R "f" "x" "y"] idempotentD3[of "X" "f" "y"] by simp

lemma isotoneI2:
  "\<lbrakk>refl R X; trans R X;extensive R X f; f`X \<subseteq> X; closure_cond R X f\<rbrakk> \<Longrightarrow> isotone R X R f"
  by (simp add: closure_cond_def extensiveD3 isotone_def)

lemma idempotentI3:
  "\<lbrakk>antisym R X;extensive R X f;  f`X \<subseteq> X; closure_cond R X f\<rbrakk> \<Longrightarrow> idempotent X f"
  by (simp add: antisym_onD closure_cond_def extensive_def idempotent_def image_subset_iff)

subsection Closures 

lemma closureI3:
  "\<lbrakk>trans R X; refl R X; antisym R X;extensive R X f; f`X \<subseteq> X;  closure_cond R X f\<rbrakk> \<Longrightarrow> closure R X f"
  by (simp add: closure_def idempotentI3 isotoneI2)
lemma closureD1:
  "\<lbrakk>closure R X f;  x \<in> X\<rbrakk> \<Longrightarrow> f x \<in> X"
  by (simp add: image_subset_iff closure_def)
lemma closureD2:
  "\<lbrakk>closure R X f;  y \<in> f`X\<rbrakk> \<Longrightarrow> y \<in> X"
  by(simp add: closure_def[of R X f] subsetD[of "f`X" X y])

lemma closureD3:
  "closure R X f \<Longrightarrow> closure_cond R X f"
  by(simp add:closure_cond_def[of R X f] closure_def[of R X f] iso_idemD3[of R X f])
lemma closureD4:
  "\<lbrakk>closure R X f; x \<in> X; y \<in> X; (x, y)\<in>R\<rbrakk> \<Longrightarrow> (f x,f y)\<in>R"
  by (simp add: closure_def isotone_def)

lemma closureD5:
  "\<lbrakk>closure R X f; x \<in> X\<rbrakk> \<Longrightarrow> (x,f x)\<in>R"
  by(simp add:closure_def extensive_def)

lemma closureD7:
  "\<lbrakk>closure R X f; x \<in> X;  y \<in> (f`X) ;  (x, y)\<in>R\<rbrakk> \<Longrightarrow> (f x, y)\<in>R"
  by (meson closure_def idempotent_isotoneD1)
lemma closureD8:
  "\<lbrakk>trans R X; closure R X f;  x \<in> X;  y \<in> (f`X) ;  (f x, y)\<in>R\<rbrakk> \<Longrightarrow>  (x, y)\<in>R"
  by (meson closureD1 closureD2 closureD5 trans_onD)
lemma closureD9:
  "\<lbrakk>closure R X f;  y \<in> f`X\<rbrakk>  \<Longrightarrow> (f y,y)\<in>R"
  by (metis closureD2 closureD5 closure_def idempotentD3)
lemma closureD10:
  "\<lbrakk>antisym R X;closure R X f;  x \<in> X;  (f x,x)\<in>R\<rbrakk> \<Longrightarrow> x = f x"
  by (simp add: antisym_onD closureD1 closureD5)

lemma closureD11:
  "\<lbrakk>antisym R X;closure R X f;  x \<in> X; (f x,x)\<in>R\<rbrakk> \<Longrightarrow> x \<in> f `X"
  using closureD10 by fastforce 

lemma cl_sup_eq_sup_cl1:
  "\<lbrakk>closure R X f; is_sup R X A s; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f s) \<in> ubd R  (f`X) (f`A)"
  by (meson closure_def is_supD32 isotoneD41)


lemma cl_sup_eq_sup_cl2:
  "\<lbrakk>trans R X;closure R X f;  is_sup R X A s; b \<in> ubd R (f`X) (f`A); A \<subseteq> X\<rbrakk> \<Longrightarrow> (s, b)\<in>R"
  by (meson closure_def converse.cases extensive_ub_imp is_supD2 ubdD1)

lemma cl_sup_eq_sup_cl3:
  "\<lbrakk>trans R X;closure R X f; is_sup R X A s; b \<in> ubd R (f`X) (f`A);A \<subseteq> X\<rbrakk> \<Longrightarrow> (f s, b)\<in>R"
  by (meson cl_sup_eq_sup_cl2 closureD7 is_supE1 ubd_mem_iff)

lemma cl_sup_eq_sup:
  "\<lbrakk>trans R X;closure R X f;  is_sup R X A s;A \<subseteq> X\<rbrakk> \<Longrightarrow> is_sup R (f`X) (f`A) (f s)"
  by (simp add: cl_sup_eq_sup_cl1 cl_sup_eq_sup_cl3 is_supI5)

lemma cl_sup_ge_sup_cl11:
  "\<lbrakk>trans R X;closure R X f; is_sup R X A s1; is_sup R X (f`A) s2; A \<subseteq> X\<rbrakk> \<Longrightarrow> (s1, s2)\<in>R"
  by (meson extensive_ub_imp2 closure_def is_supD32 is_supE3)

lemma cl_sup_ge_sup_cl2:
  "\<lbrakk>trans R X;closure R X f;  is_sup R X A s1;  is_sup R X (f`A) s2; A \<subseteq>  X\<rbrakk> \<Longrightarrow> (s2, f s1)\<in>R"
  by (meson closureD1 closure_def is_supE1 is_supE2 is_supE4 isotoneD31)

lemma cl_sup_ge_sup_cl3:
  "\<lbrakk>closure R X f;  is_sup R X A s1;  is_sup R X (f`A) s2; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f s2, f s1)\<in>R"
  by (meson closureD1 closure_def is_supE1 is_supE4 iso_idemD3 isotoneD61)

lemma cl_sup_ge_sup_cl4:
  "\<lbrakk>trans R X;closure R X f; is_sup R X A s1;  is_sup R X (f`A) s2; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f s1, f s2)\<in>R"
  by (simp add: cl_sup_ge_sup_cl11 closureD4 is_supE1)

lemma cl_sup_ge_sup_cl:
  "\<lbrakk>antisym R X;trans R X;closure R X f; is_sup R X A s1;  is_sup R X (f`A) s2; A \<subseteq> X\<rbrakk> \<Longrightarrow> f s1  = f s2"
  by (simp add: antisym_on_def cl_sup_ge_sup_cl3 cl_sup_ge_sup_cl4 closureD1 is_supE1)

subsection ClosureRanges
lemma clrI1:
  "\<lbrakk>C \<noteq> {}; C \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> (\<exists>c. is_least R (ubd R C {x}) c)) \<rbrakk> \<Longrightarrow> clr R X C"
  by (simp add:closure_range_def)
lemma clrD2:
  "clr R X C \<Longrightarrow> C \<subseteq> X"
  by (simp add:closure_range_def)

lemma clrD2b:
  "clr R X C \<Longrightarrow> x \<in> C \<Longrightarrow>x \<in> X"
  by(drule clrD2,simp add:subsetD)
lemma clrD3:
  "clr R X C \<Longrightarrow>  (\<And>x. x \<in> X \<Longrightarrow> (\<exists>c. is_least R (ubd R  C {x}) c))"
  by (simp add:closure_range_def)

lemma clrD4:
  "clr R X C \<Longrightarrow> x \<in> X \<Longrightarrow> (\<exists>c. is_least R (ubd R  C {x}) c)"
  by (simp add:closure_range_def)

lemma clrD5:
  "clr R X C \<Longrightarrow>  (\<And>x. x \<in> X  \<Longrightarrow> ((ubd R  C {x}) \<noteq> {}))"
  by (metis clrD3 greatest_exD0)
lemma clrD6:
  "clr R X C \<Longrightarrow>  x \<in> X \<Longrightarrow> (ubd R C {x}) \<noteq> {}"
  by (simp add: clrD5)

lemma clrD7:
  "clr R X C \<Longrightarrow>  x \<in> X \<Longrightarrow> (\<exists>c \<in> C.  (x, c)\<in>R)"
  by (simp add: clrD6 upbd_neE3)

lemma is_clr_cofinal1:
  "clr R X C \<Longrightarrow> is_greatest R X m \<Longrightarrow> (\<exists>c \<in> C.  (m, c)\<in>R)"
  by (simp add: clrD7 greatestD11)

lemma is_clr_cofinal2:
  "antisym R X \<Longrightarrow> clr R X C \<Longrightarrow> is_greatest R X m \<Longrightarrow> c \<in> C \<Longrightarrow> (m, c)\<in>R \<Longrightarrow> m =c"
  by (simp add: antisym_onD clrD2b greatestD11 greatestD2)

lemma is_clr_cofinal:
  "antisym R X\<Longrightarrow>clr R X C \<Longrightarrow> is_greatest R X m \<Longrightarrow> m \<in> C"
  by (metis is_clr_cofinal1 is_clr_cofinal2)

definition cl_from_clr::"'a rel \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "cl_from_clr R C \<equiv> (\<lambda>x. Least R  (ubd R  C {x}))"

lemma clr_equality:
  "\<lbrakk>antisym R X; clr R X C;is_least R (ubd R  C {x}) c\<rbrakk> \<Longrightarrow> cl_from_clr R C x = c"
  by (metis Greatest_def Least_def antisym_on_converse antisym_on_subset cl_from_clr_def clrD2 greatest_equality2 ubd_sub)

lemma cl_range1:
  assumes A0:"antisym R X" and A1:"clr R X C" and A2:"x \<in> X" 
  shows "(cl_from_clr R C) x \<in> C"
proof-
  obtain c where A3:"is_least R (ubd R  C {x}) c"
    by (meson A1 A2 clrD4)
  then have "(cl_from_clr R C) x = c"
    by (meson A0 A1 clr_equality)
  also have "c \<in> C"
    by (meson A3 greatestD11 ubdD2)
  finally show "(cl_from_clr R C) x \<in> C" by simp
qed

lemma cl_range2:
  "antisym R X \<Longrightarrow> clr R X C  \<Longrightarrow> (cl_from_clr R C)`X \<subseteq> C"
  by (simp add: cl_range1 image_subset_iff)

lemma cl_range3:
  "refl R C \<Longrightarrow> antisym R X \<Longrightarrow> clr R X C  \<Longrightarrow> x \<in> C \<Longrightarrow> (cl_from_clr R C) x = x"
  by (simp add: clr_equality greatest_iff reflD1 ubdD1 ubd_singleton)

lemma cl_range31:
  "refl R X \<Longrightarrow> antisym R X \<Longrightarrow> clr R X C  \<Longrightarrow> x \<in> C \<Longrightarrow> (cl_from_clr R C) x = x"
  by (simp add: cl_range3 clrD2b refl_def)

lemma cl_range4:
  "refl R C \<Longrightarrow> antisym R X \<Longrightarrow> clr R X C  \<Longrightarrow> (cl_from_clr R C)`C = C"
  by (simp add: cl_range3)

lemma cl_range5:
  "refl R C \<Longrightarrow> antisym R X  \<Longrightarrow> clr R X C \<Longrightarrow> x \<in> C  \<Longrightarrow> x \<in>  cl_from_clr R C ` X"
  by (metis cl_range3 clrD2b rev_image_eqI)

lemma clr_induced_closure_id:
  "\<lbrakk>refl R C; antisym R X ; clr R X C\<rbrakk>  \<Longrightarrow>  (cl_from_clr R C)`X = C"
   by (rule order_antisym, auto simp add: cl_range2 cl_range5)

lemma cl_ext1:
  "\<lbrakk>refl R C; antisym R X ;clr R X C\<rbrakk> \<Longrightarrow> x \<in> X \<Longrightarrow> (x, (cl_from_clr R C) x)\<in>R"
  by (metis clrD4 clr_equality greatestD11 ubd_mem_singleE)

lemma cl_ext2:
  "\<lbrakk>refl R C; antisym R X ;clr R X C\<rbrakk>\<Longrightarrow> extensive R X (cl_from_clr R C)"
  by (simp add: cl_ext1 extensive_def)

lemma cl_lt_ub1:
  "\<lbrakk>refl R C; antisym R X; clr R X C; x \<in> X; c \<in> ubd R C {x}\<rbrakk> \<Longrightarrow> ((cl_from_clr R C) x, c)\<in>R"
  by (metis clrD3 clr_equality is_supE3 is_supI1)

lemma cl_lt_ub2:
  "\<lbrakk>refl R C; antisym R X; clr R X C; x \<in> X; c \<in> C; (x,c)\<in>R\<rbrakk> \<Longrightarrow> ((cl_from_clr R C) x, c)\<in>R"
  by (simp add: ubd_singleton2 cl_lt_ub1)

lemma cl_iso1:
  "\<lbrakk>refl R C; antisym R X;trans R X;clr R X C; x \<in> X;y \<in> X; (x, y)\<in>R\<rbrakk>\<Longrightarrow> ((cl_from_clr R C) x, (cl_from_clr R C) y)\<in>R"
  by (simp add: cl_ext2 cl_lt_ub2 cl_range1 clrD2 clr_induced_closure_id extensiveD3)

lemma cl_iso2:
  "\<lbrakk>refl R C; antisym R X;trans R X;clr R X C\<rbrakk> \<Longrightarrow> isotone R X R (cl_from_clr R C)"
  by (simp add: cl_iso1 isotone_def)

lemma cl_ide:
  "\<lbrakk>refl R C; antisym R X;clr R X C\<rbrakk> \<Longrightarrow> idempotent X (cl_from_clr R C) "
  by (simp add: cl_range1 cl_range3 idempotent_def)

lemma cl_is_closure:
  "\<lbrakk>refl R C; antisym R X;trans R X;clr R X C\<rbrakk> \<Longrightarrow> closure R X (cl_from_clr R C)"
  by(simp add:closure_def cl_ext2 cl_ide cl_iso2 clr_induced_closure_id clrD2)

lemma closure_of_in_ub:
  "closure R X f \<Longrightarrow>x \<in> X \<Longrightarrow> (f x) \<in> (ubd R  (f`X) {x})"
  by (simp add: ubd_singleton2 closureD5)

lemma closure_of_lt_ub:
  "closure R X f \<Longrightarrow>x \<in> X \<Longrightarrow> y \<in>  (ubd R (f`X) {x}) \<Longrightarrow> ((f x), y)\<in>R"
  by (simp add: closureD7 ubd_singleton_iff)

lemma closure_of_least_closed1:
  "closure R X f \<Longrightarrow> x \<in> X \<Longrightarrow> is_least R (ubd R  (f`X) {x}) (f x)"
  by (simp add: closure_of_in_ub closure_of_lt_ub greatestI3)

lemma closure_of_least_closed2:
  assumes A0:"antisym R X"  and A1:"closure R X f" and A2:"x \<in> X"
 shows "Least R (ubd R  (f`X) {x}) =  (f x)"
proof-
  obtain B0:"antisym R (f`X)"  by (meson A0 A1 antisym_on_subset closure_def)
  have B1:"is_least R (ubd R  (f`X) {x}) (f x)"  by (simp add: A1 A2 closure_of_least_closed1)
  then show "Least R (ubd R  (f`X) {x}) =  (f x)"
    by (metis B0 Greatest_def Least_def antisym_on_converse antisym_on_subset greatest_equality2 ubd_sub)
qed

lemma closure_induced_clr:
  "\<lbrakk>antisym R X; closure R X f; X \<noteq> {}\<rbrakk> \<Longrightarrow> clr R X (f`X)"
  by (meson closure_def closure_of_least_closed1 clrI1 image_is_empty)

lemma closure_induced_clr_id:
  "\<lbrakk>antisym R X; closure R X f; X \<noteq> {};x\<in>X\<rbrakk>  \<Longrightarrow> (cl_from_clr R (f`X)) x = f x"
  by (simp add: cl_from_clr_def closure_of_least_closed2)

lemma closure_induced_clr_dual:
  "\<lbrakk>antisym R X; closure R X f1; closure R X f2; (\<And>x. x \<in> X \<Longrightarrow> (f1 x,f2 x)\<in>R)\<rbrakk> \<Longrightarrow> (f2`X) \<subseteq> (f1`X)"
  by (metis closureD11 closureD2 idempotentD3 closure_def subsetI)
                    
lemma clr_induced_closure_dual:
  "\<lbrakk>refl R C; antisym R X;clr R X C1; clr R X C2; C2 \<subseteq> C1; x \<in> X\<rbrakk> \<Longrightarrow> (((cl_from_clr R C1) x),((cl_from_clr R C2) x))\<in>R"
  by (metis clrD4 clr_equality converseD greatest_iff ubd_iso2b)
lemma extensiveI4:
  "refl R X \<Longrightarrow> (\<And>A s. A \<subseteq> X \<Longrightarrow> is_sup R X A s \<Longrightarrow> (s,f s)\<in>R) \<Longrightarrow>  f`X \<subseteq> X \<Longrightarrow> extensive R X f"
proof(rule extensiveI1)
  fix x assume A0:"refl R X" "(\<And>A s. A \<subseteq> X \<Longrightarrow> is_sup R X A s \<Longrightarrow> (s,f s)\<in>R) " " f`X \<subseteq> X" "x \<in> X"
  have B0:"is_sup R X {x} x" by (metis A0(1) A0(4) reflE1 sup_singleton)
  have B1:"{x} \<subseteq> X"   by (simp add: A0(4))
  show "(x, f x) \<in> R"  using A0(2) B0 B1 by blast
qed
lemma idempotentI4:
  "\<lbrakk>refl R X; antisym R X; (\<And>A s1 s2. A \<subseteq> X \<Longrightarrow> is_sup R X A s1 \<Longrightarrow> is_sup R X (f`A) s2 \<Longrightarrow> f s1 = f s2);  f`X \<subseteq> X\<rbrakk> \<Longrightarrow> idempotent X f"
  unfolding idempotent_def apply(auto)
proof-
  fix x assume A0:"refl R X" "antisym R X" "(\<And>A s1 s2. A \<subseteq> X \<Longrightarrow> is_sup R X A s1 \<Longrightarrow> is_sup R X (f`A) s2 \<Longrightarrow> f s1 = f s2)" "f`X \<subseteq> X" "x \<in> X "
  have B0:"is_sup R X {x} x"   by (meson A0(1) A0(5) reflE1 sup_singleton)
  have B1:"is_sup R X (f`{x}) (f x)"   by (metis A0(1) A0(4) A0(5) image_empty image_insert image_subset_iff reflE1 sup_singleton)
  have B2:"{x} \<subseteq> X"  by (simp add: A0(5))
  show "f (f x) = f x"
    by (metis A0(3) B0 B1 B2)
qed


lemma isotoneI4:
  assumes A0:"(\<And>A s. \<lbrakk>A \<subseteq> X; is_sup R X A s\<rbrakk> \<Longrightarrow> is_sup R (f`X) (f`A) (f s))" and A1:"f`X \<subseteq>X " and A2:"refl R X"
  shows "isotone R X R f"
proof- 
  have P:"\<And>x1 x2. \<lbrakk>x1 \<in> X;x2 \<in> X; (x1, x2)\<in>R\<rbrakk> \<Longrightarrow> (f x1,f x2)\<in>R"
    proof-
      fix x1 x2 assume A2:"x1 \<in> X""x2 \<in> X" "(x1,x2)\<in>R"
      have B01:"is_sup R X {x1, x2} x2"   by (meson A2(1) A2(2) A2(3) assms(3) binary_supI1 reflD1)
      have B02:"is_sup R (f`X) (f`{x1, x2}) (f x2)"  by (meson A2 B01 assms(1) empty_subsetI insert_subset)
      show "(f x1, f x2)\<in>R"   using B02 is_supD1121 by fastforce
    qed
  show ?thesis
    by (simp add: P isotoneI1)
qed

lemma clrD8:
  "\<lbrakk>refl R X; antisym R X; clr R X C; A \<subseteq> C ; is_inf R X A i\<rbrakk> \<Longrightarrow> (cl_from_clr R C) i \<in> lbd R X A"
  by (smt (verit, ccfv_threshold) cl_lt_ub2 cl_range1 clrD2b converseD converseI is_supD1121 is_supE1 refl_def subsetD ubd_mem_iff3)
lemma clrD9:
  "\<lbrakk>refl R X; antisym R X; clr R X C; A \<subseteq> C ; is_inf R X A i\<rbrakk>  \<Longrightarrow> ((cl_from_clr R C) i,i)\<in>R"
  by (metis clrD8 converse.simps is_supE3)
lemma clrD10:
  "\<lbrakk>refl R X; antisym R X; clr R X C; A \<subseteq> C ; is_inf R X A i\<rbrakk>\<Longrightarrow> (cl_from_clr R C) i = i"
  by (meson antisym_on_def cl_ext2 cl_range1 clrD2b clrD9 extensiveD1 is_supE1 refl_def)
lemma clrD11:
  "\<lbrakk>refl R X; antisym R X; clr R X C; A \<subseteq> C ; is_inf R X A i\<rbrakk> \<Longrightarrow>  i \<in> C"
  by (metis cl_range1 clrD10 is_supE1)

lemma moore_clI1:
  "C \<subseteq> Pow X \<Longrightarrow> (\<And>E. E \<subseteq> C \<Longrightarrow> (X \<inter> (\<Inter>E)) \<in> C) \<Longrightarrow> x \<in> Pow X \<Longrightarrow> is_least (pwr X) (ubd (pwr X) C {x})  (X \<inter> (\<Inter>(ubd (pwr X) C {x}))) "
  by(auto simp add:closure_range_def is_greatest_def ubd_def  ub_def pwr_def)

lemma moore_clI2:
  "C \<subseteq> Pow X \<Longrightarrow> (\<And>E. E \<subseteq> C \<Longrightarrow> (X \<inter> (\<Inter>E)) \<in> C) \<Longrightarrow> clr (pwr X) (Pow X) C"
  by (metis empty_iff empty_subsetI closure_range_def moore_clI1)

lemma moore_clI3:
  "C \<subseteq> Pow X \<Longrightarrow> X \<in> C \<Longrightarrow> (\<And>E. E \<subseteq> C \<Longrightarrow> E \<noteq> {} \<Longrightarrow> (\<Inter>E) \<in> C) \<Longrightarrow> clr (pwr X ) (Pow X) C"
  by (metis Inf_insert insert_not_empty insert_subsetI moore_clI2)

lemma clr_cinf_semilattice1:
  assumes A0:"clr R X C" and A1:"is_cinf_semilattice R X" and A2:"antisym R X" and A3:"refl R X" and A4:"trans R X"
  shows "\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_inf R C A x \<and> is_inf R X A x)"
proof-
  let ?f="(cl_from_clr R C)"
  fix A assume P0:"A \<subseteq> C" and P1:"A \<noteq> {}"
  then have B0:"A \<subseteq> X"   using A0 clrD2 by blast
  then obtain m where B1:"is_inf R X A m"  by (meson A1 P1 is_cinf_semilattice_def)
  then have B2:"\<And>a. a \<in> A \<Longrightarrow> (?f m, a)\<in>R"
  proof-
    fix a assume P2:"a \<in> A" 
    then have B20:"a \<in> C" using P0 by auto
    have B21:"(m, a)\<in>R"   using B1 P2 is_supE2 ubE by fastforce
    then have B22:"(?f m, ?f a)\<in>R"  by (metis A0 A2 A3 B1 B20 P0 cl_range31 clrD10)
    also have B23:"?f a = a"  by (meson A0 A2 A3 B20 cl_range31)
    finally show "(?f m, a)\<in>R" by simp
  qed
  have B3:"?f m \<in> lbd R X A" by (simp add: A0 A2 A3 B1 P0 clrD8)
  have B4:"?f m \<in> lbd R C A"  by (metis A0 A2 A3 B1 P0 cl_range31 clrD11 is_supE2 ubdI2)
  have B5:"(?f m, m) \<in> R"  by (meson A0 A2 A3 B1 P0 clrD9)
  also have B5:"(m, ?f m)\<in> R"using A0 A2 A3 B1 P0 calculation clrD10 by fastforce
  then have B6:"?f m = m" by (metis A0 A2 A3 B1 P0 clrD10)
  have B7:"is_inf R C A m"  by (meson A0 A2 A3 B1 P0 closure_range_def clrD11 sup_in_subset)
  show "(\<exists>x. is_inf R C A x \<and> is_inf R X A x)"
    using B1 B7 by blast
qed

lemma clr_clattice1:
  assumes A0:"clr R X C" and A1:"is_clattice R X" and A2:"antisym R X" and A3:"refl R X" and A4:"trans R X"
  shows "\<And>A. A \<subseteq> C \<Longrightarrow> (\<exists>x. is_sup R C A x \<and> is_inf R X (ubd R C A) x)"
proof-
  fix A assume A2:"A \<subseteq> C" then have B0:"A \<subseteq> X"   using A0 clrD2 by blast
  also have B1:"ubd R C A \<subseteq> X" by (meson A0 clrD2 dual_order.trans ubd_sub)
  then obtain x where B2:"is_inf R X (ubd R C A) x"  using A1 A4 assms(3) clatD22 by blast
  then have B1:"is_sup R C A x"   by (metis A0 A2 A3 assms(3) clrD11 clrD2 converse_converse inf_if_sup_lb sup_in_subset ubd_sub)
  then show "(\<exists>x. is_sup R C A x \<and> is_inf R X (ubd R C A) x)"  using B2 by auto
qed



lemma clr_is_clattice:
  "\<lbrakk>clr R X C; is_clattice R X; antisym R X; trans R X; refl R X\<rbrakk> \<Longrightarrow> is_clattice R C"
  by (metis clr_clattice1 is_clattice_def closure_range_def)

lemma closure_range_is_clattice:
  "\<lbrakk>closure R X f; is_clattice R X; antisym R X; trans R X; refl R X\<rbrakk> \<Longrightarrow> is_clattice R (f`X)"
  using closure_induced_clr clr_is_clattice is_clattice_def by blast

section Subsets
subsection Directedness

lemma is_dirI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>c \<in> X.  (a, c) \<in> R \<and>  (b, c) \<in> R)) \<Longrightarrow> is_dir X R"
  by (simp add: is_dir_def)

lemma is_dirE1:
  "is_dir X R \<Longrightarrow> a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> (\<exists>c \<in> X. (a, c)\<in>R \<and> (b, c)\<in>R)"
  by (simp add: is_dir_def)

lemma is_dirD1:
  "is_dir X R \<Longrightarrow> a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> (\<exists>c \<in> X. ub R {a,b} c)"
  by (simp add: is_dirE1 ub_double_iff1)

lemma is_dir_empty:
   "is_dir {} R"
  using is_dir_def by auto

lemma is_dir_singleton:
  "(x,x)\<in>R \<Longrightarrow> is_dir {x} R"
  by (metis is_dirI1 singletonD)

lemma is_dir_singleton2:
  "refl R X \<Longrightarrow> x \<in> X \<Longrightarrow> is_dir {x} R"
  by (simp add: is_dir_singleton reflD1)


lemma updir_finite1:
  assumes A0: "\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow>  (\<exists>c \<in> X. (a1,c)\<in>R \<and> (a2,c)\<in>R)" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X" and 
          A4:"trans R X" 
  shows " (\<exists>c \<in> X. \<forall>a. a \<in> A \<longrightarrow> (a, c)\<in>R)"
  using A1 A2 A3 
proof (induct A rule: finite_ne_induct)
  case (singleton x) then show ?case  using A0 by auto
next
  case (insert x F) obtain c1 where P0:"c1 \<in> X" and P1:"(\<forall>a. a\<in>F\<longrightarrow>(a,c1)\<in>R)" using insert.hyps(4) insert.prems by blast
  then obtain c2 where P2:"c2\<in>X" and P3:"(c1, c2) \<in> R \<and> (x, c2) \<in> R"   by (meson A0 insert.prems insert_subset)
  then have P4:"\<And>a. a \<in> (insert x F)\<Longrightarrow>(a, c2) \<in> R"
  proof-
    fix a assume P5:"a\<in>(insert x F)"
    show "(a,c2)\<in>R"
    proof(cases "a=x")
      case True then show ?thesis   by (simp add: P3)
    next
      case False  then show ?thesis  by (meson A4 P0 P1 P2 P3 P5 in_mono insert.prems insertE trans_onD)
    qed
  qed
  then show ?case  using P2 by blast
qed
  
lemma updir_finite2:
  "\<lbrakk>is_dir X R;A \<subseteq> X;trans R X;finite A;A \<noteq> {}\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. ub R A c)"
  by (metis is_dir_def ubI updir_finite1)

lemma updir_finite_obtain:
  assumes "is_dir X R" and "A \<in> Fpow_ne X" and "trans R X"
  obtains c where "c \<in> X \<and> ub R A c"
  by (metis assms(1) assms(2) assms(3) fpow_ne_iff2 updir_finite2)

lemma updir_finite3:
  "(\<And>A. \<lbrakk>A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. ub R A c)) \<Longrightarrow> is_dir X R"
proof(rule is_dirI1)
  fix a b assume A0:"(\<And>A. \<lbrakk>A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (\<exists>c \<in> X. ub R A c))" and A1:"a \<in> X" and A2:"b \<in> X"
  then obtain B0:"{a,b} \<subseteq> X" and B1:"finite {a,b}" and B2:"{a,b} \<noteq> {}" by blast
  then obtain c where B3:"c \<in> X" and B4:"ub R {a,b} c"  by (meson A0)
  then have B4:"(a, c) \<in> R \<and> (b, c) \<in> R"  by (simp add: ub_double_iff1)
  then show "\<exists>c\<in>X. (a, c) \<in> R \<and> (b, c) \<in> R"  using B3 by auto
qed

lemma is_dirI2:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>i. is_sup R X {a, b} s)) \<Longrightarrow> is_dir X R"
  by (metis binary_supD32 is_dir_def is_supE1)

lemma is_dirI4:
  "\<lbrakk>antisym R X;refl R X;trans R X;is_sup_semilattice R X; A \<subseteq> X; (\<And>a b. \<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> (Sup R X {a, b} \<in> A))\<rbrakk> \<Longrightarrow> is_dir A R"
proof(rule is_dirI1)
  fix a b assume A0:"antisym R X" and A1:"refl R X" and A2:"trans R X" and A3:"is_sup_semilattice R X" and A4:"A \<subseteq> X" and
                 A5:"(\<And>a b. \<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> (Sup R X {a, b} \<in> A))"  and A6:"a \<in> A" and A7:"b \<in> A"
  let ?c="Sup R X {a,b}"
  have B0:"?c \<in> A \<and> (a,?c)\<in>R \<and> (b,?c)\<in>R"    by (meson A0 A1 A2 A3 A4 A5 A6 A7 bsup_geI1 bsup_geI2 reflE1 subset_eq)
  then show "\<exists>c::'a\<in>A. (a, c) \<in> R \<and> (b, c) \<in> R" by blast
qed
lemma is_dirI5:
  "\<lbrakk>antisym R X;refl R X;trans R X;is_sup_semilattice R X; A \<subseteq> X; is_fsup_closed R X A\<rbrakk> \<Longrightarrow> is_dir A R"
  by (simp add: is_dirI4 is_fsup_closed_def)

subsection OrderClosure
lemma is_ord_clE1:
  "is_ord_cl X A R  \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> X \<Longrightarrow> (a, b)\<in>R \<Longrightarrow> b \<in> A "
   by (simp add:is_ord_cl_def)

lemma is_ord_clI1:
  "(\<And>a b. \<lbrakk>a \<in> A; b \<in> X; (a,b)\<in>R\<rbrakk> \<Longrightarrow> b \<in> A ) \<Longrightarrow> is_ord_cl X A R"
  by (auto simp add:is_ord_cl_def)

lemma is_ord_empty:
  "is_ord_cl X {} R "
  by (simp add: is_ord_cl_def)
lemma is_ord_cl_space:
  "is_ord_cl X X R "
  by (simp add: is_ord_cl_def)

lemma is_ord_cl_comp1:
  "is_ord_cl X A R \<Longrightarrow> is_ord_cl X (X-A) (converse R)"
  by(auto simp add:is_ord_cl_def)

lemma is_ord_cl_comp2:
  "A \<subseteq> X \<Longrightarrow> is_ord_cl X (X-A) (converse R) \<Longrightarrow> is_ord_cl X A R"
  by(auto simp add:is_ord_cl_def)

lemma is_ord_cl_un:
  "A \<in> (Pow (Pow X)) \<Longrightarrow> (\<And>Ai. Ai \<in> A \<Longrightarrow> is_ord_cl X Ai R) \<Longrightarrow>  is_ord_cl X (\<Union>A) R "
  apply(simp add:is_ord_cl_def) by metis

lemma is_ord_cl_in:
  "A \<in> (Pow (Pow X)) \<Longrightarrow> (\<And>Ai. Ai \<in> A \<Longrightarrow> is_ord_cl X Ai R) \<Longrightarrow>  is_ord_cl X (\<Inter>A) R "
  apply(simp add:is_ord_cl_def) by metis

lemma is_ord_cl_un3:
  "(f`I)\<in> (Pow (Pow X)) \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> is_ord_cl X (f i) R) \<Longrightarrow>  is_ord_cl X (\<Union>i \<in> I. f i) R "
  by (metis (mono_tags, lifting) f_inv_into_f inv_into_into is_ord_cl_un)

lemma is_ord_cl_in3:
  "(f`I)\<in> (Pow (Pow X)) \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> is_ord_cl X (f i) R) \<Longrightarrow>  is_ord_cl X (\<Inter>i \<in> I. f i) R "
  by (metis (mono_tags, lifting) f_inv_into_f inv_into_into is_ord_cl_in)
lemma ord_cl_memI1:
  "is_ord_cl X A R \<Longrightarrow> x \<in> X \<Longrightarrow> (\<exists>a. a \<in> A \<and> (a,x)\<in>R) \<Longrightarrow> x \<in> A"
  by(auto simp add:is_ord_cl_def)

lemma ord_cl_dwdir_inf:
  assumes A0:"A \<subseteq> X" and A1:"is_dir A (converse R)" and A2:"is_ord_cl X A R"
  shows "\<And>a b. \<lbrakk>a \<in> A; b \<in> A; is_inf R X {a, b} i\<rbrakk> \<Longrightarrow> i \<in> A"
proof-
  fix a b assume A3:"a \<in>A" and A4:"b\<in>A" and A5:"is_inf R X {a, b} i"
  then obtain c where B0:"c \<in> A" and B1:"(c,a)\<in>R" and B2:"(c,b)\<in>R"   by (meson A1 converse.cases is_dirE1)
  then have B3:"c \<in> lbd R X {a, b}" by (meson A0 converse_iff in_mono ubd_mem_double)
  then have B4:"(c, i) \<in> R"   by (meson A5 converseD is_supE3)
  then have B5:"(i, c)\<in>(converse R)" by simp
  also have B6:"i\<in>X"  by (meson A5 is_supE1)
  then show "i\<in>A"  by (meson A2 B0 B4 is_ord_clE1)
qed

lemma ord_cl_updir_sup:
  assumes A0:"A \<subseteq> X" and A1:"is_dir A R" and A2:"is_ord_cl X A (converse R)"
  shows "\<And>a b. \<lbrakk>a \<in> A; b \<in> A; is_sup R X {a, b} s\<rbrakk> \<Longrightarrow> s \<in> A"
  by (metis A0 A1 A2 converse_converse ord_cl_dwdir_inf)

lemma up_cl_bot:
  "\<lbrakk>is_least R X bot; A \<subseteq>X; is_ord_cl X A R; bot \<in> A\<rbrakk> \<Longrightarrow> A=X"
  by (meson converseD greatestD2 is_ord_cl_def subset_antisym subset_eq)

subsection Filters
subsection DefinitionAndBasicProps
lemma filterI1:
  "\<lbrakk> F \<noteq> {}; F \<subseteq> X; is_dir F (converse R);  is_ord_cl X F R\<rbrakk> \<Longrightarrow> is_filter R X F" 
  by (simp add: is_filter_def)

lemma idealI1:
  "\<lbrakk>F \<noteq> {}; F \<subseteq> X; is_dir F R;  is_ord_cl X F (converse R)\<rbrakk> \<Longrightarrow> is_ideal R X F" 
  by (simp add: is_filter_def)

lemma filterI2:
  "\<lbrakk>antisym R X;refl R X;trans R X;is_inf_semilattice R X; F \<noteq> {}; F \<subseteq> X; is_finf_closed R X F; is_ord_cl X F R\<rbrakk> \<Longrightarrow> is_filter R X F" 
proof-
  assume A0:"antisym R X" and A1:"refl R X" and A2 :"trans R X" and A3:"is_inf_semilattice R X" and
         A4:"F \<noteq> {}" and A5:"F \<subseteq> X" and A6:"is_finf_closed R X F" and A7:"is_ord_cl X F R"
  then obtain B0:"antisym (converse R) X" and B1:"refl (converse R) X" and B2:"trans (converse R) X" and
              B3:"is_sup_semilattice (converse R) X" and B4:"is_fsup_closed (converse R) X F"  by (simp add: is_fsup_closed_def is_sup_semilattice_def refl_def)
  then have B5:"is_dir F (converse R)" using is_dirI5[of X "(converse R)" F] using A5 by blast
  show "is_filter R X F"
    by (simp add: A4 A5 A7 B5 filterI1)
qed

lemma idealI2:
  "\<lbrakk>antisym R X;refl R X;trans R X;is_sup_semilattice R X; F \<noteq> {}; F \<subseteq> X; is_fsup_closed R X F; is_ord_cl X F (converse R)\<rbrakk> \<Longrightarrow> is_ideal R X F"
  by (simp add: idealI1 is_dirI5) 
        
lemma filterD1: 
  "is_filter R X F \<Longrightarrow> F \<noteq> {}" 
  by (simp add: is_filter_def)
lemma filterD2:
  "is_filter R X F \<Longrightarrow> F \<subseteq> X" 
  by (simp add: is_filter_def)
lemma filterD21:
  "is_filter R X F \<Longrightarrow> x \<in> F \<Longrightarrow> x \<in> X" 
  using filterD2 by blast
lemma filterD3: 
  "is_filter R X F \<Longrightarrow> (is_dir F (converse R))"
  by (simp add: is_filter_def)
lemma filterD4:
  "is_filter R X F \<Longrightarrow> (is_ord_cl X F R)" 
  by (simp add: is_filter_def)
lemma filter_greatestD1:
  "is_greatest R X m \<Longrightarrow> is_filter R X F \<Longrightarrow>  (\<exists>f. f \<in> F \<and> (f, m)\<in>R)"
  by (metis is_filter_def ex_in_conv filterD21 greatestD2)

lemma filter_greatestD2:
  "is_greatest R X m \<Longrightarrow> is_filter R X F \<Longrightarrow>  m \<in> F"
  using filterD4 greatestD11 filter_greatestD1 is_ord_clE1 by fastforce

lemma filter_finf_closed: 
  "\<lbrakk>is_filter R X F; a \<in> F;  b \<in> F;  is_inf R X {a, b} i\<rbrakk>\<Longrightarrow> i \<in> F"
  by (meson is_filter_def ord_cl_dwdir_inf)

subsection FiniteInfClosure

lemma filter_finf_closed1:
  "\<lbrakk>antisym R X; is_inf_semilattice R X; is_filter R X F; a \<in> F; b \<in> F\<rbrakk> \<Longrightarrow> Inf R X {a, b} \<in> F"
  proof-
    assume A0:"antisym R X" and A1:"is_inf_semilattice R X" and A2:"is_filter R X F" and A3:"a\<in>F" and A4:"b\<in>F"
    obtain i where B0:"is_inf R X {a,b} i"  by (meson A1 A2 A3 A4 filterD21)
    have B1:"i \<in> F"
      by (meson A2 A3 A4 B0 filter_finf_closed)
    show "Inf R X {a, b} \<in> F"
      by (metis A0 B0 B1 antisym_on_converse sup_equality the_equality)
qed

lemma filter_finf_closed3:
  "\<lbrakk>antisym R X; trans R X; is_inf_semilattice R X; is_filter R X F; A \<subseteq> F; A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow> Inf R X A \<in> F"
  by (simp add: is_filter_def filter_finf_closed1 finite_inf_closed2)

lemma filter_finf_closed4:
  "\<lbrakk>antisym R X; trans R X;is_inf_semilattice R X; is_filter R X F; A \<in> Fpow_ne F\<rbrakk> \<Longrightarrow> Inf R X A \<in> F"
  by (simp add: filter_finf_closed3 fpow_ne_iff2)

lemma min_filter1:
  "(top,top)\<in>R \<Longrightarrow> antisym R X \<Longrightarrow> is_greatest R X top \<Longrightarrow> is_filter R X {top}"
  by (simp add: is_filter_def antisym_onD greatest_iff is_dir_singleton is_ord_cl_def)

lemma min_filter1b:
  "refl R X \<Longrightarrow> antisym R X \<Longrightarrow> is_greatest R X top \<Longrightarrow> is_filter R X {top}"
  by (simp add: is_filter_def antisym_onD greatest_iff is_dir_singleton is_ord_cl_def)

lemma min_filter2:
  "\<lbrakk>is_greatest R X top; is_filter R X F\<rbrakk> \<Longrightarrow>{top} \<subseteq> F"
  by (simp add: filter_greatestD2)

lemma inf_dwdir:
  "\<lbrakk>is_inf_semilattice R X\<rbrakk> \<Longrightarrow> is_dir X (converse R)"
  by (metis binary_supD31 binary_supD32 is_dirI1 is_supE1)

lemma filters_max0:
  "is_inf_semilattice R X \<Longrightarrow> is_filter R X X"
  by (simp add: is_filter_def inf_dwdir is_ord_cl_def)
lemma filters_max1:
  "is_cinf_semilattice R X \<Longrightarrow>is_filter R X X"
  by (simp add: cinf_sinf filters_max0)

section SetOfFilters

lemma filters_on_iff:
  "F \<in> filters_on R X \<longleftrightarrow> is_filter R X F"
  by (simp add: filters_on_def)

lemma filters_is_clr1:
  "(filters_on R X) \<subseteq> Pow X"
  using filterD2 filters_on_iff by fastforce

lemma filters_is_clr1b:
  "is_inf_semilattice R X \<Longrightarrow> X \<in> filters_on R X"
  by (simp add: filters_max0 filters_on_iff)

lemma filter_inter_upcl:
  "(\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F) \<Longrightarrow> is_ord_cl X (\<Inter>EF) R"
  by (meson Inter_iff filterD4 is_ord_cl_def)

lemma filter_pow_memD:
  "EF \<in> Pow(filters_on R X) \<Longrightarrow> (\<And>F. F \<in> EF \<Longrightarrow> is_filter R X F)"
  using filters_on_iff by auto 

lemma is_pfilterD1: 
  "is_pfilter R X A \<Longrightarrow> is_filter R X A" 
  by(simp add:is_pfilter_def)

lemma is_pfilterD2:
  "is_pfilter R X A \<Longrightarrow>  X \<noteq> A"
  by(simp add:is_pfilter_def)

lemma is_pfilterD3:
  "is_pfilter R X A \<Longrightarrow>  A \<subseteq> X"
  using filterD2 is_pfilter_def by blast

lemma is_pfilterD4:
  "\<lbrakk>is_least R X bot; is_pfilter R X A\<rbrakk> \<Longrightarrow> bot \<notin> A"
  by (metis filterD4 is_pfilterD3 is_pfilter_def up_cl_bot)

lemma is_pfilterI1:
  "\<lbrakk>is_filter R X A; X \<noteq> A\<rbrakk> \<Longrightarrow> is_pfilter R X A"
  by(simp add:is_pfilter_def)

lemma is_pfilterI2:
  "\<lbrakk>is_least R X bot; bot \<notin> A; is_filter R X A\<rbrakk> \<Longrightarrow> is_pfilter R X A"
  by (metis greatestD11 is_pfilterI1)

lemma pfilters_memD0:
  "F \<in> pfilters_on R X \<Longrightarrow> is_pfilter R X F"
  by (simp add:pfilters_on_def)

lemma pfilters_memD1:
  "F \<in> pfilters_on R X \<Longrightarrow> is_filter R X F"
  by (simp add:pfilters_on_def is_pfilterD1)

lemma pfilters_memD2:
  "F \<in> pfilters_on R X \<Longrightarrow> F \<noteq> X"
  using is_pfilterD2 pfilters_memD0 by blast

lemma pfilters_memD3:
  "F \<in> pfilters_on R X  \<Longrightarrow> F \<subseteq> X"
  by (simp add:pfilters_on_def is_pfilterD3)

lemma pfilters_memI:
  "is_pfilter R X F \<Longrightarrow> F \<in> pfilters_on R X"
  by (simp add: pfilters_on_def)

lemma maximal_pfiltersD1:
  "is_maximal (pwr X) (pfilters_on R X) F \<Longrightarrow> H \<in> pfilters_on R X \<Longrightarrow> F \<subseteq> H \<Longrightarrow> F=H  "
  by (metis maximalD3 pfilters_memD3 pwr_mem_iff)

lemma maximal_pfiltersI1:
  "\<lbrakk>F \<in> pfilters_on R X; (\<And>H. \<lbrakk>H  \<in> pfilters_on R X; F \<subseteq> H\<rbrakk> \<Longrightarrow> F =H)\<rbrakk> \<Longrightarrow>  is_maximal (pwr X) (pfilters_on R X) F "
  by (metis maximalI1 pwr_mem_iff)

lemma maximal_pfiltersI2:
  "\<lbrakk>F \<in> pfilters_on R X; (\<And>H. \<lbrakk>H  \<in> pfilters_on R X; F \<subseteq> H\<rbrakk> \<Longrightarrow> F \<supseteq> H)\<rbrakk> \<Longrightarrow>  is_maximal (pwr X) (pfilters_on R X) F "
  by (metis maximal_pfiltersI1 subset_antisym)


subsection IntersectionOfFilters
subsubsection Upclosed

lemma filter_inter_upcl2:
  "EF \<in> Pow (filters_on R X) \<Longrightarrow> is_ord_cl X (\<Inter>EF) R"
  by (simp add: filter_inter_upcl filter_pow_memD)
subsubsection Nonempty

lemma filter_inter_ne:
  "\<lbrakk>(\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F);is_greatest R X top\<rbrakk> \<Longrightarrow> (\<Inter>EF) \<noteq> {}"
  by (metis InterI empty_iff filter_greatestD2)

lemma filter_inter_ne2:
  "\<lbrakk>EF \<in> Pow (filters_on R X);is_greatest R X top\<rbrakk> \<Longrightarrow> (\<Inter>EF) \<noteq> {}"
  by (simp add: filter_inter_ne filters_on_iff subset_iff)

lemma filter_inter_sub1:
  "\<lbrakk>EF \<in> Pow_ne (filters_on R X); x \<in> \<Inter>EF\<rbrakk> \<Longrightarrow> x \<in> X"
  by (metis Inter_iff ex_in_conv filterD2 filters_on_iff in_mono pow_ne_iff2)

lemma filter_inter_sub2:
  "\<lbrakk>EF \<in> Pow_ne (filters_on R X)\<rbrakk> \<Longrightarrow> \<Inter>EF \<subseteq> X"
  by (simp add: filter_inter_sub1 subset_iff)
subsubsection InfimaClosed

lemma filter_inter_double:
  "\<lbrakk>antisym R X; is_inf_semilattice R X; EF \<in> Pow_ne (filters_on R X); x \<in> \<Inter>EF; y \<in> \<Inter>EF; F \<in> EF\<rbrakk> \<Longrightarrow> Inf R X {x, y} \<in> F "
  by (metis (full_types) InterD filter_finf_closed1 filter_pow_memD pow_ne_iff1)

lemma filter_inter_inf:
  "\<lbrakk>antisym R X;is_inf_semilattice R X; EF \<in> Pow_ne (filters_on R X); x \<in> \<Inter>EF; y \<in> \<Inter>EF\<rbrakk> \<Longrightarrow> Inf R X {x, y} \<in> \<Inter>EF "
  by (simp add: filter_inter_double)

lemma filter_inter_dwdir3:
  "\<lbrakk>antisym R X;is_inf_semilattice R X; EF \<in> Pow_ne (filters_on R X)\<rbrakk> \<Longrightarrow>is_dir (\<Inter>EF) (converse R)"
proof-
  assume A0:"antisym R X" and A1:"is_inf_semilattice R X" and A2:"EF \<in> Pow_ne (filters_on R X)"
  have B0:"\<And>a b. \<lbrakk>a \<in> \<Inter> EF; b \<in> \<Inter> EF\<rbrakk> \<Longrightarrow> \<exists>c\<in>\<Inter> EF. (a, c) \<in> (converse R) \<and> (b, c) \<in>(converse R)"
  proof-
    fix a b assume P0:"a \<in> \<Inter> EF" and P1:"b \<in> \<Inter> EF"
    then obtain B01:"Inf R X {a,b} \<in> \<Inter>EF" and B02:"(a, Inf R X {a,b}) \<in> (converse R)" and B03:"(b, Inf R X {a,b}) \<in>(converse R)"
      by (metis A0 A1 A2 Sup_def antisym_on_converse binary_supD31 binary_supD32 filter_inter_inf filter_inter_sub1 is_sup_semilattice_def ssupD3)
    then show "\<exists>c\<in>\<Inter> EF. (a, c) \<in> (converse R) \<and> (b, c) \<in>(converse R)" by auto
  qed
  show "is_dir (\<Inter>EF) (converse R)"   using B0 is_dirI1 by blast
qed

lemma filter_inter_dir2:
  "\<lbrakk>antisym R X;is_inf_semilattice R X; is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> is_dir (\<Inter>{F1, F2}) (converse R)"
  by(erule filter_inter_dwdir3, simp,simp add: filters_on_iff pow_neI)

subsubsection ClosedUnderIntersection

lemma filter_inter_closed1:
  "\<lbrakk>antisym R X;is_inf_semilattice R X; EF \<in> Pow_ne (filters_on R X); is_greatest R X top\<rbrakk> \<Longrightarrow>  is_filter R X (\<Inter>EF)"
  by (metis is_filter_def filter_inter_dwdir3 filter_inter_ne filter_inter_sub2 filter_inter_upcl filter_pow_memD pow_ne_iff1)

lemma filter_inter_closed2:
  "\<lbrakk>antisym R X;is_inf_semilattice R X;is_greatest R X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> (\<And>E. \<lbrakk>E \<subseteq> (filters_on R X); E \<noteq> {}\<rbrakk> \<Longrightarrow> (\<Inter>E) \<in> (filters_on R X))"
  by (simp add: filter_inter_closed1 filters_on_iff pow_neI)

subsection FilterMembership

lemma filter_memI:
  "\<lbrakk>is_filter R X F; x \<in> X\<rbrakk> \<Longrightarrow>y \<in> F \<Longrightarrow> (y, x)\<in>R \<Longrightarrow> x \<in> F"
  by (meson filterD4 is_ord_clE1) 
lemma filter_bsup_memI1: 
  "\<lbrakk>antisym R X; is_sup_semilattice R X; x \<in> F; is_filter R X F; y \<in> X\<rbrakk> \<Longrightarrow> Sup R X {x, y} \<in> F"
  by (meson binary_supD31 filterD21 filterD4 is_ord_clE1 ssupD3 ssupD4) 

lemma filter_bsup_memI2:
   "\<lbrakk>antisym R X; is_sup_semilattice R X; x \<in> F; is_filter R X F; y \<in> X\<rbrakk> \<Longrightarrow> Sup R X {y, x} \<in> F" 
   by (simp add: filter_bsup_memI1 insert_commute)

lemma filter_ex_elem: 
  "\<lbrakk>is_filter R X F\<rbrakk> \<Longrightarrow> \<exists>f. f \<in> F" 
  by (simp add: ex_in_conv filterD1)

lemma filter_is_clr:
  "\<lbrakk>antisym R X;is_inf_semilattice R X;is_greatest R X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> clr (pwr X) (Pow X) (filters_on R X)"
  by (simp add: cinf_sinf filter_inter_closed2 filters_is_clr1 filters_is_clr1b moore_clI3)

lemma filter_closure_of_empty1:
  "\<lbrakk>(top,top)\<in>R; antisym R X;is_inf_semilattice R X;is_greatest R X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> is_least (pwr X) (ubd  (pwr X) (filters_on R X) {{}}) {top}"
proof-
  assume A0:"(top,top)\<in>R" and A1:"antisym R X" and A2:"is_inf_semilattice R X" and A3:"is_greatest R X top" and
         A4:"X \<noteq> {}"
  show " is_least (pwr X) (ubd  (pwr X) (filters_on R X) {{}}) {top}"
  apply(rule greatestI3)
    apply (metis A3 converseI filter_greatestD2 filters_on_iff insert_subsetI pwr_mem_iff ubdD2 ubd_mem_singleE)
    by (metis A0 A1 A3 filters_is_clr1 filters_on_iff min_filter1 powsimp1 pwr_memI subset_insertI ubd_singleton_iff)
qed


lemma filter_closure_of_empty1b:
  "\<lbrakk>refl R X; antisym R X;is_inf_semilattice R X;is_greatest R X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> is_least (pwr X) (ubd  (pwr X) (filters_on R X) {{}}) {top}"
  by (simp add: filter_closure_of_empty1 greatestD11 greatestD2)

lemma filter_closure_of_empty2:
  "\<lbrakk>(top,top)\<in>R; antisym R X;is_inf_semilattice R X;is_greatest R X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> (cl_from_clr (pwr X) (filters_on R X)) {} = {top}"
  by (metis clr_equality filter_closure_of_empty1 filter_is_clr powrel1)

lemma filter_closure_iff:
  "A \<noteq> {} \<Longrightarrow> x \<in> filter_closure R X A  \<longleftrightarrow> (x \<in> X \<and> ( \<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and> (Inf R X F, x)\<in>R))"
  by (simp add: filter_closure_def)

lemma filter_closure_memI1:
  "(x \<in> X \<and> ( \<exists>F. F \<subseteq> A \<and> finite F \<and> F \<noteq> {} \<and> (Inf R X F, x)\<in>R)) \<Longrightarrow> x \<in> filter_closure R X A"
  by (metis filter_closure_iff ne_subset_ne)

lemma filter_closure_memI2:
  "(x \<in> X \<and>  F \<subseteq> A \<and> finite F \<and> F \<noteq> {} \<and> (Inf R X F, x)\<in>R) \<Longrightarrow> x \<in> filter_closure R X A"
  by (metis filter_closure_iff ne_subset_ne)

lemma filter_closure_memD1:
  "\<lbrakk>A \<noteq> {}; x \<in> filter_closure R X A\<rbrakk> \<Longrightarrow> ( \<exists>F. F \<subseteq> A \<and> finite F \<and> F \<noteq> {} \<and> (Inf R X F, x)\<in>R)"
  by (simp add: filter_closure_iff)

lemma filter_closure_ne_simp:
  "A \<noteq> {} \<Longrightarrow> filter_closure R X A = {x \<in> X. \<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and>(Inf R X F ,x)\<in>R}"
  by (simp add: filter_closure_def)

lemma filter_closure_singleton:
  "\<lbrakk>(a,a)\<in>R;antisym R X;A \<subseteq> X; a \<in> A\<rbrakk> \<Longrightarrow> a \<in> filter_closure R X A"
  apply(rule_tac ?F="{a}"  in filter_closure_memI2, simp)
  by (metis Sup_def antisym_on_converse converse_iff in_mono sup_equality sup_singleton)

lemma filter_closure_singletonb:
  "\<lbrakk>refl R X;antisym R X;A \<subseteq> X; a \<in> A\<rbrakk> \<Longrightarrow> a \<in> filter_closure R X A"
  by (simp add: filter_closure_singleton reflD1 subsetD)

lemma filter_closure_obtains:
  assumes "A \<noteq> {}" and "x \<in> filter_closure R X A"
  obtains Fx where "Fx \<subseteq> A \<and> finite Fx \<and> Fx \<noteq> {}  \<and> (Inf R X Fx, x)\<in>R"
  by (meson assms filter_closure_iff)

lemma filter_closure_empty:
  "antisym R X \<Longrightarrow> is_greatest R X top \<Longrightarrow> filter_closure R X {} = {top}"
  by (simp add: filter_closure_def greatest_equality2)

lemma filter_closure_ne:
  "\<lbrakk>antisym R X;refl R X;X \<noteq> {}; A \<subseteq> X\<rbrakk> \<Longrightarrow> filter_closure R X A \<noteq> {}"
  by (metis (no_types, lifting) empty_iff filter_closure_def filter_closure_singleton in_mono insert_not_empty ne_subset_ne reflD1 subset_emptyI)

lemma filter_closure_superset:
  "\<lbrakk>antisym R X;refl R X;X \<noteq> {}; A \<subseteq> X\<rbrakk> \<Longrightarrow> A \<subseteq> filter_closure R X A"
  by (meson filter_closure_singleton in_mono reflD1 subsetI)

lemma ne_filter_cl1:
  "\<lbrakk>trans R X;antisym R X;refl R X;A \<subseteq> X; A \<noteq> {};is_inf_semilattice R X\<rbrakk> \<Longrightarrow> is_ord_cl X (filter_closure R X A) R"
proof-
  assume A0:"trans R X" and A1:"antisym R X" and A2:"refl R X" and A3:"A \<subseteq> X" and A4:"A \<noteq> {}" and A5:"is_inf_semilattice R X" 
  have B0:"\<And>a b. \<lbrakk>a \<in>  filter_closure R X A; b \<in> X; (a,b)\<in>R\<rbrakk> \<Longrightarrow> b \<in>  filter_closure R X A"
  proof-
    fix a b assume P0:"a \<in> filter_closure R X A" and P1:"b \<in> X" and P2:"(a,b)\<in>R"
    obtain F where B01:"F \<subseteq> A" and B02:"finite F" and B03:"F \<noteq> {}" and B04:"(Inf R X F,a)\<in>R"   by (meson A4 P0 filter_closure_memD1)
    also have B05:"Inf R X F \<in> X" by (meson A0 A1 A3 A5 B01 B02 B03 filter_finf_closed3 filters_max0 subset_trans)
    then have B06:"(Inf R X F, b) \<in>R"
      by (meson A0 A4 B04 P0 P1 P2 filter_closure_iff trans_onD)
    then have B01:"\<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and> (Inf R X F,  b) \<in> R"   using B01 B02 B03 by blast
    then show "b \<in>  filter_closure R X A"
      by (simp add: P1 filter_closure_memI1)
  qed
  show "is_ord_cl X (filter_closure R X A) R"  using B0 is_ord_clI1 by blast
qed


lemma filter_cl0:
  "\<lbrakk>refl R X;antisym R X;A \<subseteq> X\<rbrakk> \<Longrightarrow> A \<subseteq> filter_closure R X A"
  by (simp add: filter_closure_singletonb subsetI)

lemma filter_cl1:
  "\<lbrakk>refl R X;antisym R X;trans R X;is_inf_semilattice R X; is_greatest R X top;A \<subseteq> X\<rbrakk> \<Longrightarrow> is_ord_cl X (filter_closure R X A) R"
  by (metis filterD4 filter_closure_empty min_filter1b ne_filter_cl1)

lemma filter_cl_empty:
  "\<lbrakk>antisym R X;is_greatest R X top; (top,top)\<in>R\<rbrakk> \<Longrightarrow> is_dir (filter_closure R X {}) (converse R)"
  by (simp add: filter_closure_empty is_dir_singleton)

lemma filter_cl_emptyb:
  "\<lbrakk>antisym R X;is_greatest R X top; refl R X\<rbrakk> \<Longrightarrow> is_dir (filter_closure R X {}) (converse R)"
  by (simp add: filter_cl_empty greatest_iff)


lemma filter_cl2a:
  assumes csinf:"is_inf_semilattice R X" and 
          A0:"A \<subseteq> X" and
          A1:"A \<noteq> {}" and 
          A2:"antisym R X" and
          A3:"refl R X" and 
          A4:"trans R X"
  shows "is_dir (filter_closure R X A) (converse R)"
proof-
  have B0:"\<And>a b. \<lbrakk>a \<in> filter_closure R X A; b \<in> filter_closure R X A\<rbrakk> \<Longrightarrow> (\<exists>c\<in>filter_closure R X A. (c, a)\<in>R \<and> (c,b)\<in>R)"
  proof-
    fix a b assume P0:"a \<in> filter_closure R X A"  and P1:"b \<in> filter_closure R X A" then
    obtain Fa Fb where B01:"Fa \<subseteq> A" and B02:"finite Fa" and B03:"Fa \<noteq> {}" and B04:"(Inf R X Fa, a)\<in>R" and 
                       B05:"Fb \<subseteq> A" and B06:"finite Fb" and B07:"Fb \<noteq> {}" and B08:"(Inf R X Fb, b)\<in>R" 
    by (meson A1 assms(3) filter_closure_obtains)
    then obtain B01b:"Fa \<subseteq> X" and B015b:"Fb \<subseteq> X" using A0 by blast
    let ?Fab="Fa \<union> Fb"
    obtain B09:"?Fab \<subseteq> A" and B10:"finite ?Fab" and B11:"?Fab \<noteq> {}"   by (simp add: B01 B02 B03 B05 B06)
    then have B12:"?Fab \<subseteq> X"  using A0 by auto
    also have B13:"Inf R X (?Fab) \<in>  (filter_closure R X A)"   by (metis A2 A3 A4 B09 B10 B11 calculation csinf filter_closure_memI1 filter_finf_closed3 filters_max0 reflD1)
    obtain B14:"Fa \<subseteq> ?Fab" and B15:"Fb \<subseteq> ?Fab" by simp
    have B16:"is_inf R X Fa (Inf R X Fa)"
      by (metis A0 A2 A4 B01 B02 B03 Sup_def antisym_on_converse bsup_finite2 csinf is_sup_semilattice_def subset_trans trans_on_converse)
    have B17:"is_inf R X Fb (Inf R X Fb)"
      by (metis A2 A4 B015b B06 B07 Sup_def antisym_on_converse bsup_finite2 csinf is_sup_semilattice_def trans_on_converse)
    have B18:"(Inf R X ?Fab, Inf R X Fa)\<in>R"
      by (metis A2 A4 B10 B11 B12 B14 B16 Sup_def antisym_on_converse bsup_finite2 converseD csinf is_sup_iso1 is_sup_semilattice_def trans_on_converse) 
     have B19:"(Inf R X ?Fab, Inf R X Fb)\<in>R"
      by (metis A2 A4 B10 B11 B15 B17 Sup_def antisym_on_converse bsup_finite2 calculation converseD csinf is_sup_iso1 is_sup_semilattice_def trans_on_converse)
    have B20:"Inf R X ?Fab \<in> X"
      by (meson A1 B13 filter_closure_iff)
    then obtain B21:"(Inf R X ?Fab, a) \<in> R" and B22:"(Inf R X ?Fab, b)\<in>R" by (meson A4 B18 B19 B20 B04 B08  A1 B16 B17 P0 P1 filter_closure_iff is_supE1 trans_onD) 
    then show "(\<exists>c\<in>filter_closure R X A. (c,a)\<in>R \<and> (c, b)\<in>R)"   using B13 B21 B22 by blast
  qed
  show ?thesis by (simp add: B0 is_dirI1)
qed


lemma filter_cl2:
  assumes toped:"is_greatest R X top" and
          csinf:"is_inf_semilattice R X" and 
          A0:"A \<subseteq> X" and 
          A1:"antisym R X" and
          A2:"refl R X" and 
          A3:"trans R X"
  shows "is_dir (filter_closure R X A) (converse R)"
proof(cases "A={}")
  case True  then show ?thesis  by (meson A1 A2 filter_cl_emptyb toped)
next
  case False  then show ?thesis
    by (simp add: A0 A1 A2 A3 csinf filter_cl2a)
qed

lemma filter_cl_range:
  "\<lbrakk>antisym R X; refl R X; is_greatest R X top;A \<subseteq> X\<rbrakk> \<Longrightarrow> (filter_closure R X A) \<subseteq> X"
  by (metis filterD2 filter_closure_empty filter_closure_iff min_filter1b subset_eq)

lemma filter_cl3a:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_filter R X (filter_closure R X A)"
  by (metis is_filter_def filter_cl2a filter_closure_iff filter_closure_ne ne_filter_cl1 subsetI)

lemma filter_cl3:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_greatest R X top; is_inf_semilattice R X; A \<subseteq> X\<rbrakk> \<Longrightarrow> is_filter R X (filter_closure R X A)"
  by (simp add: filterI1 filter_cl1 filter_cl2 filter_cl_range filter_closure_ne is_sup_semilattice_def)

lemma filter_cl_least1a:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X; is_filter R X F; A \<noteq> {};A \<subseteq> F; x \<in> (filter_closure R X A)\<rbrakk> \<Longrightarrow> \<exists>Fx. Fx \<in> Fpow_ne A \<and> (Inf R X Fx, x)\<in>R \<and> Inf R X Fx \<in> F"
  by (smt (verit) filter_closure_iff filter_finf_closed3 fpow_ne_iff2 subset_trans)

lemma filter_cl_least1b:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X; is_filter R X F; A \<noteq> {};A \<subseteq> F; x \<in> (filter_closure R X A)\<rbrakk> \<Longrightarrow> x \<in> F"
  by (smt (verit, ccfv_SIG) filterD4 filter_cl_least1a filter_closure_iff is_ord_clE1)

lemma filter_cl_least1:
  assumes A0:"is_greatest R X top" and 
          A1:" is_inf_semilattice R X" and
          A2:"is_filter R X F" and
          A3:"A \<subseteq> F" and 
          A4:"x \<in>  (filter_closure R X A)" and
          A5:"antisym R X" and
          A6:"trans R X" and
          A7:"refl R X"
  shows " x \<in>F"
proof(cases "A={}")
  case True then show ?thesis
    using A0 A2 A4 A5 filter_closure_empty min_filter2 by fastforce
next
  case False  then show ?thesis by (meson A1 A2 A3 A4 A5 A6 A7 filter_cl_least1b) 
qed


lemma filter_cl_least2a:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X; is_filter R X F; A \<subseteq> F; A \<noteq> {}\<rbrakk> \<Longrightarrow> (filter_closure R X A) \<subseteq> F"
  using filter_cl_least1b by (metis subsetI) 

lemma filter_cl_least2:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_greatest R X top; is_inf_semilattice R X; is_filter R X F; A \<subseteq> F\<rbrakk> \<Longrightarrow> (filter_closure R X A) \<subseteq> F"
  using filter_cl_least1 by (metis subsetI) 

lemma filter_cl_is_ub_ne:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (filter_closure R X A) \<in>  (ubd (pwr X) (filters_on R X) {A})"
  by (metis filterD2 filter_cl0 filter_cl3a filters_on_iff pwr_memI ubd_singleton_iff)
lemma filter_cl_is_ub:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_greatest R X top; is_inf_semilattice R X;A \<subseteq> X\<rbrakk> \<Longrightarrow> (filter_closure R X A) \<in>  (ubd (pwr X)  (filters_on R X) {A})"
  by (metis (no_types, lifting) filter_cl_is_ub_ne filter_closure_empty filter_closure_of_empty1b greatestD11)

lemma filter_cl_lt_ub_ne:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;A \<subseteq> X; A \<noteq> {};F \<in>  (ubd (pwr X) (filters_on R X) {A})\<rbrakk> \<Longrightarrow> ((filter_closure R X A), F)\<in>(pwr X)"
  by (metis filter_cl_least1b filters_on_iff pwr_memD pwr_memI subsetI ubd_singleton_iff)
  
lemma filter_cl_lt_ub:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_greatest R X top; is_inf_semilattice R X;A \<subseteq> X\<rbrakk>  \<Longrightarrow> F \<in>  (ubd (pwr X)  (filters_on R X) {A}) \<Longrightarrow> ((filter_closure R X A), F)\<in>(pwr X)"
  by (metis (no_types, opaque_lifting) filter_cl_lt_ub_ne filter_closure_empty filter_greatestD2 filters_on_iff insert_subsetI pwr_mem_iff ubd_singleton_iff)

lemma filter_cl_is_lub_ne:
  "\<lbrakk>antisym R X;trans R X; refl R X;A \<noteq> {}; is_inf_semilattice R X;A \<subseteq> X\<rbrakk> \<Longrightarrow>  is_inf (pwr X) (Pow X) (ubd (pwr X) (filters_on R X) {A}) (filter_closure R X A)"
  by (smt (verit, best) filter_cl_is_ub_ne filter_cl_lt_ub_ne filters_is_clr1 is_supD1 is_supI5 sup_maxE1 ubdD2 ubd_iso2b)

lemma filter_cl_is_lub:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_greatest R X top; is_inf_semilattice R X;A \<subseteq> X\<rbrakk> \<Longrightarrow>  is_inf (pwr X) (Pow X) (ubd (pwr X) (filters_on R X) {A}) (filter_closure R X A) "
  by (metis (no_types, lifting) PowI filter_cl_is_lub_ne filter_cl_range filter_closure_empty filter_closure_of_empty1b sup_maxE1)
lemma filter_cl_is_lub_ne2:
  "\<lbrakk>antisym R X;trans R X; refl R X;A \<noteq> {}; is_inf_semilattice R X;A \<subseteq> X\<rbrakk> \<Longrightarrow>  is_least (pwr X) (ubd (pwr X) (filters_on R X) {A}) (filter_closure R X A)"
  by (metis filter_cl_is_lub_ne filter_cl_is_ub_ne sup_maxI1)
lemma filter_cl_is_lcl:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_greatest R X top; is_inf_semilattice R X;A \<subseteq> X\<rbrakk> \<Longrightarrow>  is_least (pwr X) (ubd (pwr X) (filters_on R X) {A}) (filter_closure R X A) "
  by (metis filter_cl_is_lub filter_cl_is_ub sup_maxI1)

lemma filter_closure_eq_closure:                                      
  "\<lbrakk>antisym R X;trans R X; refl R X;is_greatest R X top; is_inf_semilattice R X;A \<subseteq> X;A \<subseteq> X\<rbrakk>  \<Longrightarrow> filter_closure R X A = (cl_from_clr (pwr X) (filters_on R X)) A "
  by (metis clr_equality filter_cl_is_lcl filter_is_clr powrel1)


lemma filter_closure_of_filters1:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;A \<subseteq> filters_on R X\<rbrakk> \<Longrightarrow> F \<in> A \<Longrightarrow> F \<subseteq> (filter_closure R X (\<Union>A))"
  by (metis Union_Pow_eq Union_mono Union_upper filter_cl0 filters_is_clr1 order.trans)

lemma filter_closure_of_filters2_ne:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;A \<subseteq> filters_on R X; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (filter_closure R X (\<Union>A)) \<in>filters_on R X"
  by (metis all_not_in_conv cSup_least empty_Union_conv filterD1 filterD2 filter_cl3a filters_on_iff in_mono)

lemma filter_closure_of_filters2:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;A \<subseteq> filters_on R X;is_greatest R X top\<rbrakk> \<Longrightarrow>  (filter_closure R X (\<Union>A)) \<in>filters_on R X"
  by (metis Union_empty filter_closure_empty filter_closure_of_filters2_ne filters_on_iff min_filter1b)

lemma filter_closure_of_filters3_ne:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_inf_semilattice R X;A \<subseteq> filters_on R X; A \<noteq> {}\<rbrakk> \<Longrightarrow>  (filter_closure R X (\<Union>A)) \<in> ubd (pwr X) (filters_on R X) A"
  by (smt (verit, ccfv_SIG) filter_closure_of_filters1 filter_closure_of_filters2_ne filters_is_clr1 powsimp1 pwr_memI ubdI)

lemma filter_closure_of_filters3:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;A \<subseteq> filters_on R X; is_greatest R X top\<rbrakk> \<Longrightarrow>  (filter_closure R X (\<Union>A)) \<in>ubd (pwr X)  (filters_on R X) A"
  by (metis filter_closure_of_filters2 filter_closure_of_filters3_ne ubd_emptyI)

lemma filter_closure_of_filters4:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;A \<subseteq> filters_on R X;is_greatest R X top; G \<in> ubd (pwr X) (filters_on R X) A\<rbrakk> \<Longrightarrow> (filter_closure R X (\<Union>A)) \<subseteq> G"
  by (metis Sup_le_iff filter_cl_least2 filters_on_iff powrel8 ubd_mem_iff2)

lemma filter_closure_of_filters5:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;A \<subseteq> filters_on R X; is_greatest R X top\<rbrakk> \<Longrightarrow> is_sup (pwr X) (filters_on R X) A (filter_closure R X (\<Union>A))"
  by (smt (verit, ccfv_SIG) filter_closure_of_filters3 filter_closure_of_filters4 filters_is_clr1 in_mono is_supI5 powsimp1 pwr_memI ubd_sub)

lemma filters_on_lattice_inf01:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> z \<in> F1 \<inter> F2 \<Longrightarrow> \<exists>f1 f2. f1 \<in> F1 \<and> f2 \<in> F2 \<and> z = Sup R X {f1, f2}"
  by (metis IntE bsup_idem1 filterD21 reflD1)

lemma pfilters_on_lattice_inf01:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; is_pfilter R X F1; is_pfilter R X F2\<rbrakk> \<Longrightarrow> z \<in> F1 \<inter> F2 \<Longrightarrow> \<exists>f1 f2. f1 \<in> F1 \<and> f2 \<in> F2 \<and> z = Sup R X {f1, f2}"
  by (meson filters_on_lattice_inf01 is_pfilterD1)

lemma filters_on_lattice_inf02:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> f1 \<in> F1 \<and> f2 \<in> F2 \<and> z = Sup R X {f1, f2} \<Longrightarrow> z \<in> F1 \<inter> F2 "
  by (simp add: filterD21 filter_bsup_memI1 filter_bsup_memI2 latt_iff)
  

lemma pfilters_on_lattice_inf02:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_pfilter R X F1; is_pfilter R X F2\<rbrakk> \<Longrightarrow> f1 \<in> F1 \<and> f2 \<in> F2 \<and> z = Sup R X {f1, f2} \<Longrightarrow> z \<in> F1 \<inter> F2 "
  by (meson filters_on_lattice_inf02 is_pfilterD1)

lemma filters_on_lattice_inf03:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> f1 \<in> F1 \<Longrightarrow> f2 \<in> F2  \<Longrightarrow> Sup R X {f1, f2} \<in> F1 \<inter> F2 "
  by (meson filters_on_lattice_inf02)

lemma pfilters_on_lattice_inf03:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_pfilter R X F1; is_pfilter R X F2\<rbrakk> \<Longrightarrow> f1 \<in> F1 \<Longrightarrow> f2 \<in> F2  \<Longrightarrow> Sup R X {f1, f2} \<in> F1 \<inter> F2 "
  by (meson pfilters_on_lattice_inf02)

lemma filter_on_lattice_sup01: 
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_filter R X F; x \<in> X; y \<in> F\<rbrakk> \<Longrightarrow> Sup R X {x, y} \<in> F" 
   by (simp add: filter_bsup_memI2 lattD42)


lemma pfilter_on_lattice_sup01: 
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_pfilter R X F; x \<in> X; y \<in> F\<rbrakk> \<Longrightarrow> Sup R X {x, y} \<in> F "
  by (simp add: filter_on_lattice_sup01 is_pfilterD1)


lemma filter_on_lattice_top0:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X\<rbrakk> \<Longrightarrow> is_filter R X {x} \<Longrightarrow> a \<in> X \<Longrightarrow> (a, x) \<in> R"
  by (meson filterD2 filter_on_lattice_sup01 lattD5 singleton_iff subset_iff)

lemma pfilter_on_lattice_top0:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X\<rbrakk> \<Longrightarrow> is_pfilter R X {x} \<Longrightarrow> a \<in> X \<Longrightarrow> (a, x) \<in> R"
  by (simp add: filter_on_lattice_top0 is_pfilterD1)

lemma filter_on_lattice_top:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X;  is_filter R X {x}\<rbrakk> \<Longrightarrow>  is_greatest R X x"
  by(rule greatestI1, rule ubdI, simp add: filter_on_lattice_top0, simp add:filterD21)

lemma pfilter_on_lattice_top:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X;  is_pfilter R X {x}\<rbrakk> \<Longrightarrow>  is_greatest R X x"
  by (simp add: filter_on_lattice_top is_pfilterD1)

lemma filter_on_lattice_eq:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X;is_lattice R X; is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> (F1 \<inter> F2) = {y. (\<exists>f1 \<in> F1. \<exists>f2 \<in> F2. y = Sup R X {f1, f2})}"
  apply(auto simp add:set_eq_iff)
  apply (metis bsup_idem1 filterD21 reflD1)
  apply (simp add: filterD21 filter_bsup_memI1 lattD42)
  by (simp add: filterD21 filter_on_lattice_sup01)

lemma pfilter_on_lattice_eq:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X;is_lattice R X; is_pfilter R X F1; is_pfilter R X F2\<rbrakk> \<Longrightarrow> (F1 \<inter> F2) = {y. (\<exists>f1 \<in> F1. \<exists>f2 \<in> F2. y = Sup R X {f1, f2})}"
  by (simp add: filter_on_lattice_eq is_pfilterD1)

lemma filter_inter_dir3:
  assumes "antisym R X" "trans R X" "refl R X"  "is_inf_semilattice R X" "is_filter R X F1" "is_filter R X F2"
  shows "is_dir (F1 \<inter> F2) (converse R)"
  using assms filter_inter_dir2 by auto

lemma filters_on_lattice_inf2b:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X;is_lattice R X; is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> is_dir (F1 \<inter> F2) (converse R)"
  using filter_inter_dir3 lattD4 by blast

lemma pfilters_on_lattice_inf2b:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X;is_lattice R X; is_pfilter R X F1; is_pfilter R X F2\<rbrakk> \<Longrightarrow> is_dir (F1 \<inter> F2) (converse R)"
  by (simp add: filters_on_lattice_inf2b is_pfilterD1)

lemma filters_upcl:
  "\<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> is_ord_cl X (F1 \<inter> F2) (R)"
  by (smt (verit, ccfv_threshold) Int_iff filter_memI is_ord_clI1) 

lemma pfilters_upcl:
  "\<lbrakk>is_pfilter R X F1; is_pfilter R X F2\<rbrakk> \<Longrightarrow> is_ord_cl X (F1 \<inter> F2) (R)" 
  by (simp add: filters_upcl is_pfilterD1)

lemma filter_on_lattice_inf4b:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<noteq> {}"
  by (metis empty_iff equals0I filterD1 filters_on_lattice_inf02)

lemma pfilter_on_lattice_inf4b:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_pfilter R X F1; is_pfilter R X F2\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<noteq> {}"
  by (simp add: filter_on_lattice_inf4b is_pfilterD1)

lemma filters_on_lattice_inf5b:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> is_filter R X (F1 \<inter> F2)"
  by (meson filterD2 filterI1 filter_on_lattice_inf4b filters_on_lattice_inf2b filters_upcl inf.coboundedI2) 

lemma pfilters_on_lattice_inf5b:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_pfilter R X F1; is_pfilter R X F2\<rbrakk> \<Longrightarrow> is_pfilter R X (F1 \<inter> F2)"
  by (metis Int_left_absorb filters_on_lattice_inf5b inf.orderE is_pfilterD3 is_pfilter_def)

lemma filters_on_lattice_inf6b:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<in> (lbd (pwr X) (filters_on R X) {F1, F2})"
  by (simp add: filterD2 filters_on_iff filters_on_lattice_inf5b pwr_memI ubd_mem_double)

lemma pfilters_on_lattice_inf6b:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_pfilter R X F1; is_pfilter R X F2\<rbrakk> \<Longrightarrow> F1 \<inter> F2 \<in> (lbd (pwr X) (pfilters_on R X) {F1, F2})"
  by (simp add: is_pfilterD3 pfilters_memI pfilters_on_lattice_inf5b pwr_mem_iff ubd_mem_double)

lemma filters_on_lattice_inf7b:
  "\<lbrakk>is_filter R X F1; is_filter R X F2; G \<in> (lbd (pwr X) (filters_on R X) {F1, F2})\<rbrakk>  \<Longrightarrow>  G \<subseteq>  (F1 \<inter> F2)"
  by (simp add: pwr_mem_iff ubd_mem_iff2)

lemma pfilters_on_lattice_inf7b:
  "\<lbrakk>is_pfilter R X F1; is_pfilter R X F2; G \<in> (lbd (pwr X) (pfilters_on R X) {F1, F2})\<rbrakk>  \<Longrightarrow>  G \<subseteq>  (F1 \<inter> F2)"
  by (metis Int_subset_iff converse_iff pwr_mem_iff ubd_mem_doubleE1 ubd_mem_doubleE2)

lemma filters_on_lattice_inf8b:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X;  is_filter R X F1; is_filter R X F2\<rbrakk>\<Longrightarrow> is_inf (pwr X) (filters_on R X) {F1, F2} (F1 \<inter> F2)"
  by (smt (verit, ccfv_threshold) converseI filterD2 filters_on_lattice_inf6b filters_on_lattice_inf7b inf.absorb_iff2 inf.bounded_iff is_supI5 pwr_mem_iff)

lemma pfilters_on_lattice_inf8b:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_pfilter R X F1; is_pfilter R X F2\<rbrakk>\<Longrightarrow> is_inf (pwr X) (pfilters_on R X) {F1, F2} (F1 \<inter> F2)"
  by (metis converseI is_pfilterD3 is_supI5 pfilters_on_lattice_inf5b pfilters_on_lattice_inf6b pfilters_on_lattice_inf7b pwr_mem_iff)
  

lemma filters_on_lattice_inf_semilattice1:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X\<rbrakk> \<Longrightarrow> is_inf_semilattice (pwr X) (filters_on R X)"
  by (metis empty_iff filters_is_clr1b filters_on_iff filters_on_lattice_inf8b lattD41)
  

lemma filters_on_lattice_sup1b:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; (\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> is_ord_cl X (filter_closure R X (\<Union>EF)) R"
  by (metis Sup_least all_not_in_conv empty_Union_conv filterD1 filterD2 lattD41 ne_filter_cl1)

lemma filters_on_lattice_sup2a:
  assumes A01:"antisym R X" and A02:"trans R X" and A03:"refl R X" and 
          A0:"is_lattice R X" and A1:"(\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F)" and A2:"EF \<noteq> {}" and
          A3: "a \<in> (filter_closure R X (\<Union>EF))" and  A4:"b \<in> (filter_closure R X (\<Union>EF))"
  shows "(\<exists>c \<in> (filter_closure R X (\<Union>EF)).  (c,a)\<in>R \<and>  (c, b)\<in>R)"
proof-
  let ?A="(\<Union>EF)"
    obtain Fa Fb where B01:"Fa \<subseteq> ?A" and B02:"finite Fa" and B03:"Fa \<noteq> {}" and B04:"(Inf R X Fa, a)\<in>R" and 
                       B05:"Fb \<subseteq> ?A" and B06:"finite Fb" and B07:"Fb \<noteq> {}" and B08:"(Inf R X Fb, b)\<in>R"
      by (metis A1 A2 A3 A4 Pow_empty filterD1 filter_closure_obtains insertI1 subset_Pow_Union subset_singletonD) 
    then obtain B01b:"Fa \<subseteq> X" and B015b:"Fb \<subseteq> X"  by (meson A1 Sup_least dual_order.trans filterD21 subsetI)
    let ?Fab="Fa \<union> Fb"
    obtain B09:"?Fab \<subseteq> ?A" and B10:"finite ?Fab" and B11:"?Fab \<noteq> {}"   by (simp add: B01 B02 B03 B05 B06)
    then have B12:"?Fab \<subseteq> X"   by (simp add: B015b B01b) 
    also have B13:"Inf R X (?Fab) \<in>  (filter_closure R X ?A)"       by (metis A0 A01 A02 A03 B09 B10 B11 calculation filter_closure_memI1 filter_finf_closed3 filters_max0 latt_iff reflD1) 
    obtain B14:"Fa \<subseteq> ?Fab" and B15:"Fb \<subseteq> ?Fab" by simp
    have B16:"is_inf R X Fa (Inf R X Fa)"
      by (metis A0 A01 A02 B01b B02 B03 Sup_def antisym_on_converse bsup_finite2 is_sup_semilattice_def latt_iff trans_on_converse)
    have B17:"is_inf R X Fb (Inf R X Fb)"
      by (metis A0 A01 A02 B015b B06 B07 Sup_def antisym_on_converse bsup_finite2 is_sup_semilattice_def latt_iff trans_on_converse)
    have B18:"(Inf R X ?Fab, Inf R X Fa)\<in>R"
      by (metis A0 A01 A02 B10 B11 B14 B16 Sup_def antisym_on_converse bsup_finite2 calculation converseD is_sup_iso1 is_sup_semilattice_def latt_iff trans_on_converse)
     have B19:"(Inf R X ?Fab, Inf R X Fb)\<in>R"
       by (metis A0 A01 A02 B10 B11 B15 B17 Sup_def antisym_on_converse bsup_finite2 calculation converseD is_sup_iso1 is_sup_semilattice_def latt_iff trans_on_converse)
    have B20:"Inf R X ?Fab \<in> X"
      by (metis B09 B11 B13 empty_subsetI equalityI filter_closure_iff)  
    then obtain B21:"(Inf R X ?Fab, a) \<in> R" and B22:"(Inf R X ?Fab, b)\<in>R"
      by (smt (verit, del_insts) A02 A3 A4 B01 B03 B04 B08 B16 B17 B18 B19 filter_closure_iff is_supE1 ne_subset_ne trans_onD)
  show ?thesis using B13 B21 B22 by blast 
qed


lemma filters_on_inf_lattice_sup2b:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;is_greatest R X top;(\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F)\<rbrakk> \<Longrightarrow> is_dir (filter_closure R X (\<Union>EF)) (converse R)"
  by (metis is_filter_def Sup_le_iff filter_cl2a filter_cl_emptyb)

lemma filters_on_inf_lattice_sup2c:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;(\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir (filter_closure R X (\<Union>EF)) (converse R)"
  by (simp add: is_filter_def cSup_least filter_cl2a)


lemma filters_on_lattice_sup2b:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X;(\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir (filter_closure R X (\<Union>EF)) (converse R)"
  by (simp add: filters_on_lattice_sup2a is_dirI1)

lemma filters_on_lattice_sup3b:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X;(\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> filter_closure R X (\<Union>EF) \<noteq> {}"
  by (metis filterD1 filter_closure_of_filters2_ne filters_on_iff latt_iff subsetI)

lemma filters_on_inf_lattice_sup3b:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;is_greatest R X top; (\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F)\<rbrakk> \<Longrightarrow> filter_closure R X (\<Union>EF) \<noteq> {}"
  by (meson Sup_le_iff filterD21 filter_closure_ne subset_iff)
  
lemma filters_on_lattice_sup4b:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; (\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> is_filter R X (filter_closure R X (\<Union>EF))"
  by (simp add: is_filter_def filter_closure_iff filters_on_lattice_sup1b filters_on_lattice_sup2b filters_on_lattice_sup3b subset_iff)

lemma filters_on_inf_lattice_sup4b:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X;is_greatest R X top; (\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F)\<rbrakk> \<Longrightarrow> is_filter R X (filter_closure R X (\<Union>EF))"
  by (metis Union_empty filter_closure_empty filter_closure_of_filters2_ne filters_on_iff min_filter1b subsetI)

lemma filters_on_lattice_sup5b:
  "\<lbrakk>antisym R X;trans R X; refl R X;(\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F); EF \<noteq> {}; F \<in> EF\<rbrakk> \<Longrightarrow>  F \<subseteq> (filter_closure R X (\<Union>EF))"
  by (meson Sup_le_iff filterD2 filter_cl0)

lemma filters_on_lattice_sup6b:
  assumes A01:"antisym R X" and A02:"trans R X" and A03:"refl R X" and 
          A0:"is_lattice R X" and A1:"(\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F)" and A2:"EF \<noteq> {}" and
          A3:"is_filter R X G"  and A4:"(\<And>F. F \<in> EF \<Longrightarrow> F \<subseteq> G)"
  shows "filter_closure R X (\<Union>EF) \<subseteq> G"
proof
  fix x assume A5:"x \<in> filter_closure R X (\<Union>EF)"
  obtain Fx where  B1:"Fx \<subseteq>  (\<Union>EF) \<and> finite Fx \<and> Fx \<noteq> {} \<and> (Inf R X Fx,x)\<in>R"
    by (metis A5 Pow_empty A1 A2 filterD1 filter_closure_obtains insertI1 subset_Pow_Union subset_singletonD)
  have B2:"Fx \<subseteq> G"
    using B1(1) A4  by blast
  have B3:"Fx \<subseteq> X"
    using A3 B2 filterD2 by blast
  show "x \<in> G"
    by (metis A0 A01 A02 A03 A3 A5 B1 B2 filter_cl_least1b filter_closure_iff latt_iff ne_subset_ne subset_refl)
qed


lemma filters_on_lattice_sup7b:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; (\<forall>F. F \<in> EF \<longrightarrow> is_filter R X F); EF \<noteq> {}\<rbrakk> \<Longrightarrow> is_sup (pwr X) (filters_on R X) EF (filter_closure R X (\<Union>EF))"
  apply(rule is_supI11)
  apply (simp add: filters_on_iff filters_on_lattice_sup4b)
  apply (metis is_filter_def filters_on_lattice_sup4b filters_on_lattice_sup5b pwr_mem_iff)
  by (simp add: filterD2 filters_on_iff filters_on_lattice_sup6b pwr_mem_iff)


lemma filters_on_lattice_sup7c:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; EF \<subseteq> filters_on R X; EF \<noteq> {}\<rbrakk> \<Longrightarrow> is_sup (pwr X) (filters_on R X) EF (filter_closure R X (\<Union>EF))"
  by (simp add: filter_pow_memD filters_on_lattice_sup7b)


(*On a lattice filters form a complete sup semilattice*)

lemma filters_on_lattice_csup0:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X\<rbrakk> \<Longrightarrow>  filters_on R X \<noteq> {} "
  by (simp add: filters_on_lattice_inf_semilattice1)


lemma filters_on_lattice_csup1:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; A \<subseteq>filters_on R X; A \<noteq> {} \<rbrakk> \<Longrightarrow>   (\<exists>x::'a set. is_sup (pwr X) (filters_on R X) A x)"
proof-
  assume A0:"antisym R X" and A1:"trans R X" and A2:"refl R X" and A3:"is_lattice R X" and 
         A4:"A \<subseteq>filters_on R X" and  A5:"A \<noteq> {}"
  have B0:"is_sup (pwr X) (filters_on R X) A (filter_closure R X (\<Union>A))"
    by (simp add: A0 A1 A2 A3 A4 A5 filters_on_lattice_sup7c)
  show " (\<exists>x. is_sup (pwr X) (filters_on R X) A x)"  using B0 by blast
qed

lemma filters_on_lattice_csup:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X\<rbrakk> \<Longrightarrow> is_csup_semilattice (pwr X) (filters_on R X)"
  by (simp add: is_csup_semilattice_def filters_on_lattice_csup1 filters_on_lattice_inf_semilattice1) 

lemma filters_on_lattice_sup_semilattice1b:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> is_sup (pwr X) (filters_on R X) {F1, F2} (filter_closure R X (F1 \<union> F2))"
  by (metis Union_insert ccpo_Sup_singleton empty_not_insert filters_on_lattice_sup7b insertE singleton_iff)

lemma filters_on_top_inf_lattice_clattice:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_greatest R X top; is_inf_semilattice R X\<rbrakk> \<Longrightarrow> is_clattice (pwr X) (filters_on R X)"
  by (metis empty_iff filter_closure_of_filters5 filters_is_clr1b is_clattice_def)

lemma filters_clattice1:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_greatest R X top; is_inf_semilattice R X; EF \<subseteq> filters_on R X\<rbrakk> \<Longrightarrow> is_sup  (pwr X) (filters_on R X) EF (Sup (pwr X) (filters_on R X) EF)"
  by (metis clatD21 filters_is_clr1 filters_on_top_inf_lattice_clattice powrel6 powrel7 sup_equality)

lemma filters_clattice2:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_greatest R X top; is_inf_semilattice R X; EF \<subseteq> filters_on R X\<rbrakk> \<Longrightarrow> is_inf (pwr X) (filters_on R X) EF (Inf (pwr X) (filters_on R X) EF)"
  by (metis Sup_def antisym_on_converse antisym_on_subset clatD22 filters_is_clr1 filters_on_top_inf_lattice_clattice powrel1 powrel7 sup_equality)


lemma lattice_filter_memI:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; is_filter R X F; x \<in> F; y \<in> X\<rbrakk> \<Longrightarrow> Sup R X {x, y} \<in> F"
  by (simp add: filter_bsup_memI1 lattD42)

lemma lattice_filter_dunion1:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; D \<noteq> {}; D \<subseteq> filters_on R X; is_dir D (pwr X)\<rbrakk> \<Longrightarrow> \<Union>D \<noteq> {} "
  by (simp add: is_filter_def filters_on_iff subset_iff)

lemma lattice_filter_dunion2:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; D \<noteq> {}; D \<subseteq> filters_on R X; is_dir D (pwr X)\<rbrakk> \<Longrightarrow> is_ord_cl X (\<Union>D) (R)"
  by (metis Pow_iff filterD2 filterD4 filters_on_iff is_ord_cl_un subset_iff)

lemma lattice_filter_dunion3:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; D \<noteq> {}; D \<subseteq> filters_on R X; is_dir D (pwr X); x \<in> (\<Union>D); y \<in> (\<Union>D)\<rbrakk> 
     \<Longrightarrow> (\<exists>Dx \<in> D. \<exists>Dy \<in> D. \<exists>Dxy \<in> D. x \<in> Dx \<and> y \<in> Dy \<and>(Dx,Dxy)\<in>pwr X \<and> (Dy, Dxy)\<in>pwr X)"
  by (simp add: is_dirE1) 


lemma lattice_filter_dunion4:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; D \<noteq> {}; D \<subseteq> filters_on R X; is_dir D (pwr X); x \<in> (\<Union>D); y \<in> (\<Union>D)\<rbrakk> \<Longrightarrow> (\<exists>Dxy \<in> D. x\<in> Dxy \<and> y \<in> Dxy)"
  proof-
    assume A0:"antisym R X" and A1:"trans R X" and A2:"refl R X" and A3:"is_lattice R X" and A4:"D \<noteq> {}" and 
          A5:"D \<subseteq> filters_on R X" and A6:" is_dir D (pwr X)" and A7:"x \<in> (\<Union>D) "and A8:"y \<in> (\<Union>D) "
    obtain Dx Dy Dxy where B0:"Dx \<in> D" and B1:"Dy \<in> D" and B2:"Dxy \<in> D" and B3:"x \<in> Dx" and B4:"y \<in> Dy" and B5:" (Dx, Dxy)\<in>pwr X" and B6: "(Dy, Dxy)\<in>pwr X"
      by (metis A6 A7 A8 UnionE is_dirE1) 
    then obtain B7:"Dx \<subseteq> Dxy" and B8:"Dy \<subseteq> Dxy"   by (simp add: pwr_mem_iff)
    then obtain B9:"Dxy \<in> D" and B10:"x \<in> Dxy" and B11:"y \<in> Dxy"  using B2 B3 B4 by blast
    then show "(\<exists>Dxy \<in> D. x\<in> Dxy \<and> y \<in> Dxy)"
      by auto
qed

lemma lattice_filter_dunion5:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; D \<noteq> {}; D \<subseteq> filters_on R X; is_dir D (pwr X); x \<in> (\<Union>D); y \<in> (\<Union>D)\<rbrakk> \<Longrightarrow> (\<exists>Dxy \<in> D. Inf R X {x, y} \<in> Dxy)"
  proof-
    assume A0:"antisym R X" and A1:"trans R X" and A2:"refl R X" and A3:"is_lattice R X" and A4:"D \<noteq> {}" and 
          A5:"D \<subseteq> filters_on R X" and A6:" is_dir D (pwr X)" and A7:"x \<in> (\<Union>D) "and A8:"y \<in> (\<Union>D) "
    obtain Dxy where B0:"Dxy \<in>D" and B1:"x \<in> Dxy" and B2:"y \<in> Dxy"    by (meson A0 A1 A2 A3 A4 A5 A6 A7 A8 lattice_filter_dunion4) 
    have B3:"is_filter R X Dxy"  using A5 B0 filters_on_iff by blast
    have B4:"Inf R X {x, y} \<in> Dxy"   using A0 A3 B1 B2 B3 filter_finf_closed1 latt_iff by fastforce
    then show ?thesis
      using B0 by blast
qed

lemma lattice_filter_dunion6:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; D \<noteq> {}; D \<subseteq> filters_on R X; is_dir D (pwr X); x \<in> (\<Union>D); y \<in> (\<Union>D)\<rbrakk> \<Longrightarrow> Inf R X {x, y} \<in>  (\<Union>D)"
  by (simp add: lattice_filter_dunion5)

lemma lattice_filter_dunion7:
  "\<lbrakk>D \<noteq> {}; D \<subseteq> filters_on R X\<rbrakk> \<Longrightarrow> \<Union>D \<subseteq> X"
  by(auto simp add:filters_on_def is_filter_def)

lemma lattice_filter_dunion8:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; D \<noteq> {}; D \<subseteq> filters_on R X; is_dir D (pwr X)\<rbrakk> \<Longrightarrow> is_dir (\<Union>D) (converse R)"
  apply(rule_tac ?X="X" in  is_dirI4)
  apply simp
  apply (simp add: refl_def)
  apply simp
  apply (simp add: is_sup_semilattice_def latt_iff)
  apply (simp add: lattice_filter_dunion7)
  by (metis Sup_def lattice_filter_dunion6)

lemma lattice_filter_dunion9:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; D \<noteq> {}; D \<subseteq> filters_on R X; is_dir D (pwr X)\<rbrakk> \<Longrightarrow> is_filter R X (\<Union>D)"
  by (metis is_filter_def lattice_filter_dunion1 lattice_filter_dunion2 lattice_filter_dunion7 lattice_filter_dunion8) 


lemma lattice_filters_complete:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X;  is_greatest R X top\<rbrakk> \<Longrightarrow> is_clattice (pwr X) (filters_on R X)"
  by (simp add: filters_on_top_inf_lattice_clattice latt_iff)

lemma filters_inf_semilattice_inf:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_inf_semilattice R X; EF \<in> Pow_ne (filters_on R X); is_greatest R X top\<rbrakk> \<Longrightarrow> is_inf (pwr X) (filters_on R X) EF (\<Inter>EF)"
  apply(rule is_supI11)
  apply (simp add: filter_inter_closed1 filters_on_iff)
  apply (meson InterD converseI filters_is_clr1 pow_neD1 powsimp1 pwr_memI subset_iff)
  proof-
    fix b assume A0:"antisym R X" and A1:"trans R X" and A2:"refl R X" and A3:"is_inf_semilattice R X" and
                 A4:"EF \<in> Pow_ne (filters_on R X)" and A5:"is_greatest R X top" and A6:"b \<in> filters_on R X " and
                 A7:"(\<And>a::'a set. a \<in> EF \<Longrightarrow> (a, b) \<in> (converse (pwr X))) "
    then have B0:"(\<And>f. f \<in> EF \<Longrightarrow> b \<subseteq> f)"
      by (simp add: pwr_mem_iff)
    then have B1:"(b, \<Inter>EF ) \<in> (pwr X)"   by (meson A4 Inf_greatest filter_inter_sub2 pwr_memI)
    show "(\<Inter> EF, b) \<in> converse (pwr X)" by (simp add: B1)
qed
      

lemma filters_lattice_inf:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; F1 \<in> filters_on R X; F2 \<in> filters_on R X\<rbrakk> \<Longrightarrow> is_inf(pwr X) (filters_on R X) {F1 ,F2} (F1 \<inter> F2)"
  by (simp add: filters_on_iff filters_on_lattice_inf8b)

lemma filters_lattice_inf_op:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; F1 \<in> filters_on R X; F2 \<in> filters_on R X\<rbrakk> \<Longrightarrow>Inf (pwr X) (filters_on R X) {F1, F2} = (F1 \<inter> F2)"
  by (metis Sup_def antisym_on_converse filters_is_clr1 filters_on_iff filters_on_lattice_inf8b powrel6 sup_equality)

lemma lorcI1:
  "y \<in> X \<Longrightarrow> (a, y)\<in>R \<Longrightarrow> y \<in> lorc R X a" 
  by (simp add:lorc_def)

lemma lorcD1:
  "y \<in> lorc R X a \<Longrightarrow> y \<in> X \<and> (a, y)\<in>R"
   by (simp add:lorc_def)

lemma lorcD11:
  "y \<in> lorc R X a \<Longrightarrow> y \<in> X "
   by (simp add:lorc_def)

lemma lorcD12:
  "y \<in> lorc R X a \<Longrightarrow> (a, y)\<in>R" 
  by (simp add:lorc_def)

lemma lorcD2:"trans R X \<Longrightarrow> a \<in> X \<Longrightarrow>x \<in> X \<Longrightarrow> y \<in> lorc R X a \<Longrightarrow>  (y, x)\<in>R \<Longrightarrow> x \<in> lorc R X a"
  by (meson lorcD11 lorcD12 lorcI1 trans_onD)

lemma lorcD3:
  "a \<in> X \<Longrightarrow> trans R X \<Longrightarrow> (\<exists>b. (b,x)\<in>R \<and> b \<in> lorc R X a) \<Longrightarrow> x \<in> X \<Longrightarrow>  x \<in> lorc R X a"
  by (metis lorcD2)

lemma lorc_mem_iff1:
  "y \<in> (lorc R X a) \<longleftrightarrow> (y \<in> X \<and> (a, y)\<in>R)" 
  by (simp add:lorc_def)

lemma lorc_mem_iff2:
  "y \<in> (lorc R X a) \<longleftrightarrow> (y \<in> X \<and> ub R {a} y)" 
  by (simp add:lorc_def ub_def)

lemma lorc_eq_upbd:
  "(lorc R X a) = (ubd R  X {a})"
  by(simp add: set_eq_iff ubd_mem_iff lorc_mem_iff2)

lemma lorc_eq_upbd2:
  "A \<noteq> {} \<Longrightarrow> (\<Inter>a \<in> A. lorc R X a) = ubd R  X A"
  by(auto simp add:ubd_mem_iff2 lorc_mem_iff1)

lemma lorc_memI1:
  "refl R X \<Longrightarrow> a \<in> X \<Longrightarrow> a \<in> lorc R X a "
  by (simp add: lorcI1 reflD1)

lemma lorc_subset1:
  "(lorc R X a) \<subseteq> X"
  by (simp add: ubd_sub lorc_eq_upbd)

lemma lorc_top:
  "is_greatest R X m \<Longrightarrow> a \<in> X \<Longrightarrow> m \<in> lorc R X a"
  by (simp add: greatestD11 greatestD2 lorcI1)

lemma lorc_sup_latticeD1:
  "\<lbrakk>antisym R X;trans R X;refl R X;is_sup_semilattice R X; x \<in> X; y \<in> X\<rbrakk>\<Longrightarrow> Sup R X {x, y} \<in> (lorc R X x)"
  by (simp add: binary_supD31 lorcI1 ssupD3 ssupD4)

lemma lorc_inf_latticeD1:
  "\<lbrakk>trans R X; refl R X; antisym R X;is_least R X bot\<rbrakk> \<Longrightarrow> (lorc R X bot) = X"
  by(auto simp add: lorc_mem_iff1 greatest_iff)

lemma lorc_dual_iso:
  "\<lbrakk>a \<in> X; b \<in> X;trans R X; refl R X; antisym R X\<rbrakk> \<Longrightarrow> (lorc R X a) \<subseteq> (lorc R X b)  \<longleftrightarrow> (b, a)\<in>R"
  by (smt (verit) in_mono lorcD11 lorcD12 lorcI1 lorc_memI1 subsetI trans_onD)

lemma lorc_upclI:
  "\<lbrakk>trans R X; refl R X; antisym R X;a \<in> X\<rbrakk> \<Longrightarrow> is_ord_cl X (lorc R X a) R"
  by (simp add: is_ord_clI1 lorcD2)

lemma lorc_upclD:
  "\<lbrakk>U \<subseteq> X; is_ord_cl X U R; is_least R U x\<rbrakk> \<Longrightarrow> U = lorc R X x"
  apply (auto simp add: in_mono greatestD2 lorcI1)
  apply (meson converse_iff greatestD2 in_mono lorcI1)
  by (meson is_ord_clE1 greatestD11 lorcD1)

lemma lorc_upcl1:
  "\<lbrakk>is_greatest R X m; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> m \<in> (\<Inter>a \<in> A. lorc R X a)"
  by (simp add: greatestD11 greatestD2 in_mono lorcI1)

lemma lorc_upcl3:
  "\<lbrakk>trans R X; refl R X; antisym R X; is_greatest R X m; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow>  is_ord_cl X (\<Inter>a \<in> A. lorc R X a) R"
  apply(rule is_ord_cl_in)
  apply (simp add: image_subset_iff lorc_subset1)
  using lorc_upclI by fastforce

lemma lorc_upcl4:
  "\<lbrakk>trans R X; refl R X; antisym R X; is_greatest R X m; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> {m} \<in> ord_cl_sets X (R)"
  by (metis (no_types, lifting) is_filter_def mem_Collect_eq min_filter1b ord_cl_sets_def)

lemma lorc_moore:
  "\<lbrakk>trans R X; refl R X; antisym R X;is_greatest R X m\<rbrakk> \<Longrightarrow> clr (pwr X) (Pow X) (ord_cl_sets X (R))"  
  by(rule moore_clI3, auto simp add:ord_cl_sets_def is_ord_cl_space is_ord_cl_def,blast)

lemma lorc_is_clattice:
  "\<lbrakk>trans R X; refl R X; antisym R X;is_greatest R X m\<rbrakk> \<Longrightarrow> is_clattice (pwr X) (ord_cl_sets X R)"
  by (meson Pow_iff clr_is_clattice lorc_moore order_refl pow_is_clattice powrel1 powrel2 pwr_memI refl_def)

lemma lorc_filter:
  "\<lbrakk>trans R X; refl R X; antisym R X;x \<in> X\<rbrakk> \<Longrightarrow> is_filter R X (lorc R X x)"
  apply(auto simp add:is_filter_def)
  apply (metis empty_iff lorc_memI1)
  apply (simp add: lorc_mem_iff2)
  apply (meson converse_iff is_dirI1 lorcD12 lorc_memI1)
  by (simp add: lorc_upclI)

lemma lorc_filter2:
  "\<lbrakk>trans R X; refl R X; antisym R X;c \<in> X\<rbrakk> \<Longrightarrow>  (lorc R X c) \<in> filters_on R X"
  by (simp add: filters_on_iff lorc_filter)

lemma lorc_inter:
  "\<lbrakk>is_lattice R X; trans R X; refl R X; antisym R X;a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> (lorc R X a) \<inter> (lorc R X b) = lorc R X (Sup R X {a, b})"
  by(auto simp add: bsup_geI3 latt_iff lorc_mem_iff1 bsup_iff)
 


lemma compactI:
  "\<lbrakk>c \<in> X; (\<And>A. \<lbrakk>A \<in> Pow_ne X; (c, Sup R X A) \<in> R\<rbrakk> \<Longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> (c,Sup R X A0) \<in> R))\<rbrakk> \<Longrightarrow> is_compact R X c"  
  by(simp add:is_compact_def)

lemma compactD:
  "\<lbrakk>is_compact R X c; A \<in> Pow_ne X; (c, Sup R X A) \<in> R\<rbrakk> \<Longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> (c,Sup R X A0) \<in> R)"
   by(simp add:is_compact_def)

lemma compact_element_memD1:
  "x \<in> compact_elements R X  \<Longrightarrow> is_compact R X x" 
  by (simp add: compact_elements_def)
lemma compactD2:
  "is_compact R X x \<Longrightarrow> x \<in> X" 
  by (simp add: is_compact_def)
lemma compact_element_memD2:
  "x \<in> compact_elements R X  \<Longrightarrow> x \<in> X" 
  by (meson compactD2 compact_element_memD1) 
lemma compact_elements_sub:
  "compact_elements R X \<subseteq> X"  
  by (simp add: compact_element_memD2 subsetI) 
lemma compact_elements_mem_iff1:
   "x \<in> compact_elements R X \<longleftrightarrow> is_compact R X x" 
  by (simp add: compact_elements_def)
lemma compactly_generatedD1: 
  "compactly_generated R X \<Longrightarrow> x \<in> X \<Longrightarrow> (\<exists>C \<in> Pow (compact_elements R X). is_sup R X C x)" 
   by(simp add:compactly_generated_def)

lemma compactly_generatedI1: 
  "(\<And>x. x \<in> X \<Longrightarrow>  (\<exists>C \<in> Pow (compact_elements R X). is_sup R X C x)) \<Longrightarrow> compactly_generated R X"  
  by(simp add:compactly_generated_def)


lemma join_denseD1:
  "\<lbrakk>join_dense R X D; x \<in> X\<rbrakk> \<Longrightarrow> (\<exists>Dx \<in> Pow D. is_sup R X Dx x)" 
  by (simp add:join_dense_def)
lemma meet_denseD1:"
  \<lbrakk>meet_dense R X D; x \<in> X\<rbrakk> \<Longrightarrow> (\<exists>Dx \<in> Pow D. is_inf R X Dx x)" by (simp add:join_dense_def)


lemma cmeet_dense_iff:"\<lbrakk>D \<subseteq> X; is_clattice R X; antisym R X\<rbrakk> \<Longrightarrow> (meet_dense R X D \<longleftrightarrow> (\<forall>x \<in> X. \<exists>Dx \<in> Pow D. x = Inf R X Dx))"
  by (metis Pow_mono Sup_def antisym_on_converse inf_if_sup_lb is_clattice_def join_dense_def powsimp1 sup_equality ubd_sub)

lemma join_denseD2:"\<lbrakk>antisym R X; join_dense R X D; D \<subseteq> X\<rbrakk> \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x = Sup R X (rolc R D x))"
proof-
  assume P:"antisym R X" "join_dense R X D" "D \<subseteq> X" 
  show "(\<And>x. x \<in> X \<Longrightarrow> x = Sup R X (rolc R D x))"
  proof- 
    fix x assume P1:"x \<in> X" 
    obtain Dx where P2:"Dx \<in> Pow D" "is_sup R X Dx x" by (meson P(2) P1 join_denseD1) 
    have B0:"\<forall>d. d \<in> Dx \<longrightarrow> (d, x) \<in> R"  by (meson P2(2) is_supD1121) 
    have B1:"Dx \<subseteq> X" using P(3) P2(1) by auto 
    have B2:"Dx \<subseteq> (rolc R D x)"  using B0 P2(1) lorc_def by fastforce 
    have B3:"is_sup R X (rolc R D x) x" 
      proof(rule is_supI5)
        show "\<And>a. a \<in> ubd R X (rolc R D x) \<Longrightarrow> (x, a) \<in> R"  by (meson B2 P2(2) is_supE3 ubd_ant1b)
        show " x \<in> ubd R X (rolc R D x)" by (metis (no_types, lifting) P1 converse.cases lorc_def mem_Collect_eq ubdI) 
      qed
    show "x= Sup R X (rolc R D x)"     by (metis B3 P(1) sup_equality) 
  qed
qed

lemma join_denseI2:
  "\<lbrakk>D \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> is_sup R X (rolc R D x) x) \<rbrakk> \<Longrightarrow> join_dense R X D"  
  by (metis (no_types, lifting) Pow_iff join_dense_def lorc_def mem_Collect_eq subset_eq) 

lemma meet_denseD2:
  "\<lbrakk>antisym R X; meet_dense R X D; D \<subseteq> X\<rbrakk> \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x = Inf R X (lorc R D x))"
  by (metis Sup_def antisym_on_converse converse_converse join_denseD2) 

lemma meet_denseI2:
  "\<lbrakk>D \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> is_inf R X (lorc R D x) x) \<rbrakk> \<Longrightarrow> meet_dense R X D"
  by (simp add: join_denseI2) 
lemma compactly_generated_iff:
  "compactly_generated R X \<longleftrightarrow> join_dense R X (compact_elements R X)" 
  by(auto simp add:compactly_generated_def join_dense_def)


lemma compactD1: "\<lbrakk>antisym R X; refl R X; trans R X;is_compact R X c; A \<in> Pow_ne X; (c, Sup R X A) \<in> R; is_dir A R\<rbrakk> \<Longrightarrow> (\<exists>A0. \<exists>a. a \<in> A \<and> ub R A0 a \<and> A0 \<in> Fpow_ne A \<and> (c, Sup R X A0) \<in> R)"
proof-
  assume A0:"antisym R X" "refl R X" "trans R X" "is_compact R X c" "A \<in> Pow_ne X" "(c, Sup R X A) \<in> R" "is_dir A R"
  obtain A0 where B0:"A0 \<in> Fpow_ne A \<and> (c, Sup R X A0) \<in> R"  by (meson A0(4) A0(5) A0(6) compactD) 
  have B1:"A \<subseteq> X"
    by (simp add: A0(5) pow_neD1) 
  obtain a where B4:"a \<in> A \<and> ub R A0 a"
    by (meson A0(3) A0(7) B0 B1 trans_on_subset updir_finite_obtain)  
  show "(\<exists>A0. \<exists>a. a \<in> A \<and> ub R A0 a \<and> A0 \<in> Fpow_ne A \<and> (c, Sup R X A0) \<in> R)"
    using B0 B4 by blast
qed

lemma ccompact0:
  assumes A0:"is_sup_semilattice R X" and
          A1:"is_compact R X c" and
          A2:"A \<in> Pow_ne X" and
          A3:"(c, Sup R X A) \<in> R" and
          A4:"is_dir A R" and 
          A5:"antisym R X" and
          A6:"refl R X" and
          A7:"trans R X"
  shows "\<exists>a \<in> A. (c, a) \<in> R"
proof-
  obtain A0 a where A8:"a \<in> A \<and> ub R A0 a \<and> A0 \<in> Fpow_ne A \<and> (c, Sup R X A0) \<in> R"  by (meson A1 A2 A3 A4 A5 A6 A7 compactD1) 
  obtain B0:"A \<subseteq> X" and B1:"A \<noteq> {}" and B2:"a \<in> X"   by (metis A2 A8 empty_iff in_mono pow_neD1)
  obtain B3:"A0 \<subseteq> X" and B4:"finite A0" and B5:"A0 \<noteq> {}"  by (metis A8 B0 dual_order.trans fpow_ne_iff2)
  have B6:"a \<in> ubd R X A0"  by(rule ubdI, meson A8 ubE, simp add: B2)
  have B7:"(Sup R X A0, a) \<in> R" by (simp add: A0 A5 A7 B3 B4 B5 B6 fsup_lub)
  have B8:"(c, a) \<in> R"   by (meson A0 A1 A5 A7 A8 B2 B3 B4 B5 B7 bsup_finite2 compactD2 is_supE1 trans_onD) 
  show ?thesis   using A8 B8 by blast
qed


definition fne_sup_cl::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow>  'a set" where
  "fne_sup_cl R X A\<equiv> {x \<in> X. \<exists>F \<in> Fpow A. F \<noteq> {} \<and> is_sup R X F x}"


lemma fne_sup_cl_imp1: "x \<in> fne_sup_cl R X A \<Longrightarrow> (\<exists>F \<in> Fpow A. F \<noteq> {} \<and> is_sup R X F x)" by (simp add: fne_sup_cl_def)
lemma fne_sup_cl_obtains:  assumes "x \<in> fne_sup_cl R X A"  obtains F where "F \<in> Fpow A \<and> F \<noteq> {} \<and> is_sup R X F x"  by (meson assms fne_sup_cl_imp1)

lemma fne_sup_cl_extensive:"\<lbrakk>A \<subseteq> X; antisym R X;  refl R X;  trans R X\<rbrakk> \<Longrightarrow> A \<subseteq> fne_sup_cl R X A"
proof-
  assume A0:"A \<subseteq> X" "antisym R X" "refl R X" "trans R X"
  show "A \<subseteq> fne_sup_cl R X A"
  proof
  fix a assume A1: "a \<in> A"
  have B0: "is_sup R X {a} a"    by (meson A0(1) A0(3) A1 reflD1 subsetD sup_singleton) 
  have B2: "{a} \<in> Fpow A"  by (simp add: A1 Fpow_def)
  show "a \<in> fne_sup_cl R X A"
    apply(auto simp add:fne_sup_cl_def)
    using A0(1) A1 apply blast
    using B0 B2 by blast
  qed
qed


lemma fne_sup_cl_ext:
  "\<lbrakk>antisym R X;  refl R X;  trans R X\<rbrakk>  \<Longrightarrow> extensive (pwr X) (Pow X) (\<lambda>A. fne_sup_cl R X A)"
  apply(auto simp add:extensive_def pwr_def)
  apply (meson fne_sup_cl_imp1 is_supE1)
  using fne_sup_cl_extensive by blast

lemma fne_sup_cl_isotone:
  "\<lbrakk>antisym R X;  refl R X;  trans R X; A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> fne_sup_cl R X A \<subseteq> fne_sup_cl R X B"
  apply(auto simp add:fne_sup_cl_def) by (metis Fpow_mono empty_iff subsetD)
           

lemma fne_sup_cl_iso:
  "\<lbrakk>antisym R X;  refl R X;  trans R X\<rbrakk> \<Longrightarrow> isotone (pwr X) (Pow X) (pwr X) (\<lambda>A. fne_sup_cl R X A)"
  apply(auto simp add:isotone_def pwr_def)
  apply (meson fne_sup_cl_imp1 is_supE1)
  apply (meson fne_sup_cl_imp1 is_supE1)
  using fne_sup_cl_isotone by blast

lemma fne_sup_cl_if1:"\<lbrakk>antisym R X;  refl R X;  trans R X; x \<in> X; (\<exists>F \<in> Fpow A. F \<noteq> {} \<and>  is_sup R X F x)\<rbrakk> \<Longrightarrow> x \<in> fne_sup_cl R X A" by (simp add: fne_sup_cl_def)



lemma fne_sup_cl_idempotent0: 
  "\<lbrakk>antisym R X; refl R X; trans R X; s \<in> fne_sup_cl R X (fne_sup_cl R X A)\<rbrakk> \<Longrightarrow> (\<exists>E. E \<in> Fpow (fne_sup_cl R X A) \<and> E \<noteq> {} \<and> is_sup R X E s)"
    by (meson fne_sup_cl_imp1)
lemma fne_sup_cl_idempotent1:
   "\<lbrakk>antisym R X; refl R X; trans R X ; E \<in> Pow (fne_sup_cl R X A); E \<noteq> {}; x \<in> E\<rbrakk> \<Longrightarrow> (\<exists>Ex. Ex \<in> Fpow A \<and> Ex \<noteq> {}  \<and> is_sup R X Ex x)"
   by (meson PowD in_mono fne_sup_cl_imp1)
lemma fne_sup_cl_idempotent2: 
  "\<lbrakk>antisym R X; refl R X; trans R X\<rbrakk>  \<Longrightarrow> fne_sup_cl R X A \<subseteq> fne_sup_cl R X (fne_sup_cl R X A)"
  by (metis (no_types, lifting) fne_sup_cl_def fne_sup_cl_extensive mem_Collect_eq subsetI)  


lemma fne_sup_cl_idempotent:
  assumes A0:"antisym R X" and A1:"refl R X" and A2:"trans R X" and  A4:"A \<subseteq> X"
  shows "fne_sup_cl R X (fne_sup_cl R X A) = fne_sup_cl R X A"
proof-
  let ?L1="fne_sup_cl R X A" let ?L2="fne_sup_cl R X ?L1"
  show "?L2 = ?L1"
  proof
    show "?L1 \<subseteq>?L2"    by (simp add: assms fne_sup_cl_idempotent2)
    next
    show "?L2 \<subseteq> ?L1"
  proof
    fix s assume P0:"s \<in>?L2"
    show "s \<in> ?L1"
    proof-
      let ?P="\<lambda>E x. E \<in> Fpow A \<and> E \<noteq> {} \<and> is_sup R X E x"
      let ?f= "(\<lambda>x. SOME Ex. ?P Ex x)"
      obtain E where P1:"E \<in> Fpow ?L1 \<and> E \<noteq> {} \<and> is_sup R X E s"    by (meson P0 fne_sup_cl_imp1)
      have B0:"\<forall>x \<in> E. (\<exists>Ex. ?P Ex x)"    by (meson Fpow_subset_Pow P1 assms fne_sup_cl_idempotent1 in_mono)
      let ?fE="?f`E" let ?S="{s \<in> X. \<exists>Ai \<in> ?fE. s = Sup R X Ai}"
      have B00:"((\<lambda>Ai. Sup R X Ai)`?fE) = ?S" by(auto,metis (mono_tags, lifting) B0 A0 is_supE1 someI_ex sup_equality)
      have B1:"\<forall>x \<in> E. ?P (?f x) x"   by (metis (mono_tags, lifting) B0 tfl_some)
      have B2:"?S = E"
      proof
        show "?S \<subseteq> E"
          proof
            fix s assume B6A0:"s \<in>?S"  have B60:"\<exists>Ai \<in> ?fE. s = Sup R X Ai" using B6A0 by blast
            show "s \<in> E" using B1 B60 assms sup_equality by fastforce
          qed
        next  
        show "E \<subseteq> ?S"
          proof
            fix s assume B6A1:"s \<in> E" show "s \<in> ?S"  by (metis (no_types, lifting) B00 B1 B6A1 A0 image_eqI sup_equality)
        qed
      qed
      obtain se where B11A0:"is_sup R X E se"   using P1 by blast
      obtain ss where B11A1:"is_sup R X ?S ss"   using B11A0 B2 by auto
      have B8:"\<forall>Ai \<in> ?fE. (\<exists>si. is_sup R X Ai si)"  using B1 by blast
      have B11:"(\<And>Ai. Ai \<in> ?fE \<Longrightarrow> \<exists>ti. is_sup R X Ai ti)"   using B1 by blast
      have B12:" (\<And>Ai. Ai \<in>?fE\<Longrightarrow> Ai \<subseteq> X)"
      proof-  
        fix Ai assume B12A:"Ai \<in> ?fE"
        then have B121:"Ai \<in> Fpow A"   using B1 by blast
        then show "Ai \<subseteq> X"   using A4 Fpow_subset_Pow by auto
      qed
      have B13:"is_sup R X ((\<lambda>Ai. Sup R X Ai)`?fE) ss"     using B00 B11A1 by presburger
      have B14:"is_sup R X (\<Union>?fE) ss"
        by (metis (no_types, lifting) A0 A2 B11 B12 B13 P1 image_is_empty sup_families) 
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
        by (smt (verit, best) B0 B11A1 B14 B15 B2 Collect_cong P1 assms empty_Union_conv empty_def fne_sup_cl_if1 is_supE1 mem_Collect_eq sup_equality)
      qed
    qed
  qed
qed

lemma fne_sup_cl_ide:
  "\<lbrakk>antisym R X; refl R X; trans R X\<rbrakk> \<Longrightarrow> idempotent (Pow X) (\<lambda>A. fne_sup_cl R X A)"
  by (simp add: fne_sup_cl_idempotent idempotent_def)
lemma fne_sup_cl_range: 
  "(\<lambda>A. fne_sup_cl R X A)`(Pow X) \<subseteq> Pow X"  
  by (simp add: fne_sup_cl_def image_subset_iff)

lemma fne_sup_cl_is_cl: 
   "\<lbrakk>antisym R X; refl R X; trans R X\<rbrakk>  \<Longrightarrow> closure (pwr X) (Pow X) (\<lambda>A. fne_sup_cl R X A)"
    by (simp add: fne_sup_cl_ext fne_sup_cl_ide fne_sup_cl_iso fne_sup_cl_range closure_def)

lemma fne_sup_cl_dir:
  assumes A0:"is_sup_semilattice R X" and A1:"A \<subseteq> X" and A2:"antisym R X" and A3:"refl R X" and A4:"trans R X"
  shows  "is_dir (fne_sup_cl R X A) R"
proof-
  have B0:"\<And>a b. a \<in> fne_sup_cl R X A \<and> b \<in> fne_sup_cl R X A \<longrightarrow> (\<exists>c\<in>fne_sup_cl R X A. (a, c) \<in> R \<and> (b, c) \<in> R)"
  proof
    fix a b assume A2:"a \<in> fne_sup_cl R X A \<and> b \<in> fne_sup_cl R X A "
    obtain Ea where A3:"Ea \<in> Fpow A \<and> Ea \<noteq> {} \<and> is_sup R X Ea a"by (meson A2 fne_sup_cl_imp1)
    obtain Eb where A4:"Eb \<in> Fpow A \<and> Eb \<noteq> {} \<and> is_sup R X Eb b" by (meson A2 fne_sup_cl_imp1)
    have B1:"Ea \<union> Eb \<in> Fpow A \<and> Ea \<union> Eb \<noteq> {}"      by (metis A3 A4 Fpow_Pow_finite Int_Collect Pow_iff Un_empty Un_subset_iff finite_UnI)
    have B2:"(Ea \<union> Eb) \<subseteq> X"   by (metis A1 A3 A4 Fpow_Pow_finite Int_Collect Pow_iff dual_order.trans sup.boundedI)
    have B2b:"finite (Ea \<union> Eb)"   by (metis B1 Fpow_Pow_finite Int_Collect)
    obtain c where A5:"is_sup R X (Ea \<union> Eb) c" using A0 B1 B2 B2b assms(3) assms(5) bsup_finite2 by blast 
    have B3:"c \<in> fne_sup_cl R X A \<and> (a, c) \<in> R \<and> (b, c) \<in> R"   by (smt (verit, best) A3 A4 A5 B1 fne_sup_cl_def is_supE1 is_sup_iso1 mem_Collect_eq semilattice_sup_class.sup_ge1 sup.cobounded2) 
    show "(\<exists>c\<in>fne_sup_cl R X A. (a, c) \<in> R \<and> (b, c) \<in> R)"   using B3 by blast
  qed
  show ?thesis   by (simp add: B0 is_dirI1)
qed
  

lemma ccompact1:
  assumes A0:"is_csup_semilattice R X" and
          A1:"c \<in> X" and
          A2:"(\<And>A. \<lbrakk>A \<in> Pow_ne X; (c, Sup R X A) \<in> R; is_dir A R\<rbrakk> \<Longrightarrow> (\<exists>a \<in> A. (c, a) \<in> R))" and 
          A3:"antisym R X" and 
          A4:"refl R X" and 
          A5:"trans R X"
  shows "is_compact R X c"
proof-
  have P0:"(\<And>A. A \<in> Pow_ne X \<and> (c, Sup R X A) \<in> R \<longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> (c,Sup R X A0) \<in> R))"
  proof
    fix A assume A6:"A \<in> Pow_ne X \<and> (c, Sup R X A) \<in> R"
    let ?C="fne_sup_cl R X A"
    have B0:"is_dir ?C R"   by (simp add: A0 A3 A4 A5 A6 csup_fsup fne_sup_cl_dir pow_neD1)
    have B1:"A \<subseteq> ?C"   by (simp add: A3 A4 A5 A6 fne_sup_cl_extensive pow_neD1) 
    have B2:"A \<subseteq> X \<and> ?C \<subseteq> X"  by (simp add: A6 fne_sup_cl_def pow_neD1)  
    have B3:"(Sup R X A, Sup R X ?C) \<in> R"  by (metis A0 A3 A5 A6 B1 B2 pow_ne_iff2 sup_iso1b)
    have B4:"(c, Sup R X ?C) \<in> R"  by (metis A0 A1 A3 A5 A6 B1 B2 B3 csupD50 ne_subset_ne pow_ne_iff2 trans_onD) 
    obtain d where B4:"d \<in> ?C \<and> (c, d) \<in> R"  by (metis A2 A6 B0 B1 B2 B4 ne_subset_ne pow_ne_iff2) 
    obtain Fd where B5:"Fd \<in> Fpow_ne A \<and> Sup R X Fd = d" by (smt (verit) A3 B4 fne_sup_cl_def fpow_ne_iff1 mem_Collect_eq sup_equality) 
    have B6:"Fd \<in> Fpow_ne A \<and> (c, Sup R X Fd) \<in> R" using B4 B5 by fastforce
    show "(\<exists>A0. A0 \<in> Fpow_ne A \<and> (c, Sup R X A0) \<in> R)"   using B6 by blast
  qed
  show ?thesis by (metis A1 P0 compactI)
qed


lemma bot_compact:
  assumes A0:"antisym R X" and 
          A1:"refl R X" and 
          A2:"trans R X" and
          A3:"bot \<in> X" and
          A4:"(\<And>x. x \<in> X \<Longrightarrow> (bot, x) \<in> R)"
  shows "is_compact R X bot"
proof-
  have P0:"(\<And>A. A \<in> Pow_ne X \<and> (bot, Sup R X A) \<in> R \<longrightarrow> (\<exists>A0. A0 \<in> Fpow_ne A \<and> (bot, Sup R X A0) \<in> R))" 
    proof
      fix A assume A5:"A \<in> Pow_ne X \<and> (bot, Sup R X A) \<in> R" obtain a where A6:"a \<in> A"   using A5 pow_ne_iff2 by fastforce 
      then obtain B0:"A \<subseteq> X" and B1:"A \<noteq> {}"   using A5 pow_neD1 by blast
      have B2:"{a} \<in> Fpow_ne A \<and> (bot, Sup R X {a}) \<in> R"   using A0 A1 A4 A6 B0 finite_insert fpow_ne_iff2 ge_sup2 reflD1 by fastforce 
      show "(\<exists>A0. A0 \<in> Fpow_ne A \<and> (bot, Sup R X A0) \<in> R)"   using B2 by blast 
    qed
  show ?thesis by (simp add: A3 P0 compactI)
qed

lemma dir_set_closure_subset:
  assumes A0:"clr (pwr X) (Pow X) C" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (pwr X)  \<Longrightarrow> \<Union>D \<in> C)" and
          A3:"x \<in> X" and 
          A4:"A \<in> Pow_ne C" and
          A5:"(cl_from_clr (pwr X) C) {x} \<subseteq> Sup  (pwr X) C A" and 
          A6:"is_dir A (pwr X)"
  shows "\<exists>a \<in> A. (cl_from_clr (pwr X) C) {x} \<subseteq> a"
proof-
  let ?R="pwr X" let ?P="Pow X"
  obtain B0:"antisym ?R ?P" and B1:"refl ?R ?P" and B2:"trans ?R ?P"   by (meson powrel1 powrel2 powrel3 reflI1 refl_onD)
  let ?f="cl_from_clr ?R C"
  have B3:"C \<subseteq> Pow X"   using A0 clrD2 by blast
  have B4:"A \<subseteq> C"  by (simp add: A4 pow_neD1)   
  have B5:"\<Union>A \<in> C"   using A2 A4 A6 B4 pow_ne_bot by blast
  have B6:"is_sup ?R C A (\<Union>A)"  by (meson B3 B4 B5 powrel9 sup_in_subset) 
  have B7:"Sup ?R C A = \<Union>A"  by (simp add: B3 B6 powrel6 powrel7 sup_equality)
  have B8:"?f {x} \<in> C"  using A0 A3 cl_range1 powrel1 by fastforce
  have B9:"({x}, ?f {x}) \<in> ?R"  by (metis A0 A3 B3 PowI bot.extremum cl_ext1 insert_absorb insert_mono powrel1 powsimp1 pwr_mem_iff refl_def subset_refl)
  have B10:"{x} \<subseteq> ?f {x}"  using B9 powrel8 by blast 
  have B11:"... \<subseteq> \<Union>A"   using A5 B7 by auto 
  have B12:"{x} \<subseteq> \<Union>A"  using B10 B11 by blast
  obtain a where B13:"a \<in> A \<and> x \<in> a"   using B12 by auto  
  have B14:"({x}, a) \<in> ?R" by (meson B13 B3 B4 empty_subsetI in_mono insert_subsetI powsimp1 pwr_memI)
  have B15:"a \<in> ubd ?R C {{x}}"  by (meson B13 B14 B4 in_mono ubd_singleton_iff)
  have B16:"?f a = a"  by (meson A0 B0 B1 B13 B4 cl_range31 in_mono)
  have B17:"(?f {x}, ?f a) \<in> ?R" by (smt (verit, ccfv_SIG) A0 B0 B15 B16 B9 Pow_iff closure_range_def clr_equality converseD greatestD2 order.trans pwr_memD)
  have B18:"(?f {x}, a)\<in>?R" using B16 B17 by force
  have B19:"?f {x} \<subseteq> a"  using B18 powrel8 by blast 
  show "(\<exists>a\<in>A. ?f {x} \<subseteq> a)"  using B13 B19 by blast 
qed

      
lemma dir_set_closure_subset2:
  assumes A0:"clr (pwr X) (Pow X) C" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (pwr X)  \<Longrightarrow> \<Union>D \<in> C)" and
          A3:"x \<in> X" and 
          A4:"A \<in> Pow_ne C" and
          A5:"((cl_from_clr  (pwr X) C) {x}, Sup  (pwr X) C A) \<in> pwr X" and 
          A6:"is_dir A (pwr X)"
  shows "\<exists>a \<in> A. ((cl_from_clr (pwr X) C) {x}, a) \<in> pwr X"
proof-
  from A5 have B0:"(cl_from_clr  (pwr X) C) {x} \<subseteq> Sup  (pwr X) C A"   by (simp add: powrel8)
  obtain a where B1:"a \<in> A \<and> (cl_from_clr (pwr X) C) {x} \<subseteq> a" using dir_set_closure_subset  by (metis A0 A2 A3 A4 A6 B0) 
  have B2:"a \<subseteq> X"   by (meson A0 A4 B1 Pow_iff clrD2 in_mono pow_neD1)  
  then have "((cl_from_clr (pwr X) C) {x}, a) \<in> pwr X "   by (metis B1 PowI Pow_mono Union_Pow_eq is_supD1121 powrel5)
  then show ?thesis  using B1 by blast
qed

lemma singleton_closure_compact:
  assumes A0:"clr (pwr X) (Pow X) C" and 
          A1:"(\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C)" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk>\<Longrightarrow> is_dir D (pwr X)  \<Longrightarrow> \<Union>D \<in> C)" and
          A3:"x \<in> X"
  shows "is_compact (pwr X) C (cl_from_clr (pwr X) C {x})"
  apply(rule ccompact1) 
  using A0 clatD1 clr_is_clattice apply (metis pow_is_clattice powrel1 powrel2 powrel3 refl_def refl_onD)
  apply (meson A0 A3 Pow_iff cl_range1 empty_subsetI insert_subset powrel1)
  apply (simp add: A0 A2 A3 dir_set_closure_subset2)
  apply (meson A0 clrD2 powrel6)
  apply (meson A0 clrD2b powrel3 refl_def refl_onD)
  by (meson A0 clrD2 powrel7)

lemma closed_compgen:
  assumes A0:"clr (pwr X) (Pow X) C" and 
          A1:"(\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C)" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (pwr X) \<Longrightarrow> \<Union>D \<in> C)" and
          A3:"E \<in> C"
  shows "(\<exists>A \<in> Pow (compact_elements (pwr X) C). is_sup (pwr X) C A E)"
proof-
   let ?R="pwr X"  let ?f="cl_from_clr ?R C"
   let ?A="{y. (\<exists>x \<in> E. y= ?f {x})}"
  have B0:"is_clattice (pwr X) C"  by (meson A0 clr_is_clattice pow_is_clattice powrel1 powrel2 powrel3 refl_def refl_onD)
  have B1:"\<And>x. x \<in> X \<longrightarrow> is_compact (pwr X) C (?f {x})" by (metis A0 A1 A2 singleton_closure_compact)
  have P1:"E \<in> Pow X" using A0 A3 clrD2 by blast
  have P2:"\<forall>x. x \<in> E \<longrightarrow> {x} \<in> Pow X"  using P1 by blast 
  have P3:"?A \<subseteq> C"
  proof 
    fix y assume A9:"y \<in> ?A" 
    obtain x where P30:"x \<in> E \<and> y = ?f {x}" using A9 by blast
    show "y \<in> C"   by (metis A0 P2 P30 cl_range1 powrel1)
  qed
  have B9:"\<forall>x. x \<in> E \<longrightarrow> {x} \<subseteq> ?f {x}"  using cl_ext1[of "pwr X" C "Pow X"]  by (meson A0 P2 clrD2 powrel1 powrel8 powsimp1 pwr_memI reflI1 set_eq_subset)
  have B10:"?f E = E"  by (meson A0 A3 cl_range31 powrel1 powrel3 refl_def refl_onD)
  have B11:"\<And>x. x \<in> E \<longrightarrow> ?f {x} \<subseteq> ?f E"
    by (smt (verit, ccfv_SIG) A0 A3 B10 P2 PowD Pow_bottom Pow_iff cl_lt_ub2 clrD2 insert_subset powrel1 powrel3 pwr_mem_iff refl_def refl_on_def subset_iff)
  have B11b:"ub ?R ?A E" by (smt (verit) B10 B11 P1 Pow_iff mem_Collect_eq pwr_memI ub_def)
  have B11c:"E \<in> ubd ?R C ?A"  by (simp add: A3 B11b ubd_mem_iff)
  have B12:"E = (\<Union>x \<in> E. {x})"    by simp
  have B13:"... \<subseteq> (\<Union>x \<in> E. ?f {x})"  using B9 by blast
  have B14:"... = (\<Union>?A)"  by blast
  have B15:"... = Sup  ?R (Pow X) ?A" by (metis (no_types, lifting) A0 P3 clrD2 powrel1 powrel9 sup_equality)
  have B16:"... \<subseteq> Sup ?R C ?A" using sup_iso2  by (metis (no_types, lifting) A0 B0 P3 closure_range_def pow_is_clattice powrel1 powrel2 powrel8)
  have B17:"... \<subseteq> E"  by (smt (verit) A0 A3 B11b B12 B13 B14 P1 P3 clrD2 is_supE4 powrel6 powrel9 pwr_mem_iff set_eq_subset sup_equality sup_in_subset)
  have B18:"\<forall>x. x \<in> ?A \<longrightarrow> x \<in> compact_elements ?R C" using B1 P1 compact_elements_mem_iff1 by fastforce
  have B19:"?A \<in> Pow (compact_elements ?R C)"  using B18 by blast
  have B20:"E = Sup ?R C ?A" using B13 B15 B16 B17 by auto
  have B21:"is_sup ?R C ?A E"
    by (metis (no_types, lifting) A0 A3 B12 B13 B14 B15 B16 B20 P3 clrD2 powrel9 subset_antisym sup_in_subset)
  show "\<exists>A \<in> Pow (compact_elements ?R C). is_sup ?R C A E"   using B19 B21 by blast
qed


lemma clr_compgen1:
  assumes A0:"clr (pwr X) (Pow X) C" and 
          A1:"(\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C)" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (pwr X) \<Longrightarrow> \<Union>D \<in> C)"
  shows "compactly_generated (pwr X) C \<and> (\<forall>x. x \<in> X \<longrightarrow> is_compact (pwr X) C ((cl_from_clr (pwr X) C) {x}))"
  by (simp add: A0 A1 A2 closed_compgen compactly_generated_def singleton_closure_compact)



lemma clr_compgen2:
 "\<lbrakk>clr (pwr X) (Pow X) C; (\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C);(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (pwr X) \<Longrightarrow> \<Union>D \<in> C)\<rbrakk> \<Longrightarrow> compactly_generated (pwr X) C"
  by (simp add: clr_compgen1)

lemma filters_on_lattice_compactgen:
  "\<lbrakk>antisym R X; trans R X; refl R X;is_lattice R X; is_greatest R X top; X \<noteq> {}\<rbrakk> \<Longrightarrow> compactly_generated (pwr X) (filters_on R X)" 
  apply(rule_tac ?X="X" in clr_compgen2)
  apply (simp add: filter_is_clr lattD41)
  apply (simp add: filter_inter_closed2 lattD41)
  by (simp add: filters_on_iff lattice_filter_dunion9)



context
  fixes R::"'a rel" and X::"'a set" 
  assumes ref:"refl R X" and ant:"antisym R X" and trn:"trans R X"
begin

lemma sup_assoc_ubd1b:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X; d \<in> X; is_sup R X {a, b} s; is_sup R X {c, d} t; x \<in> ubd R X {s, t}\<rbrakk> \<Longrightarrow> x \<in> ubd R X {a, b, c, d}"
  by (metis ge_sup_iff trn ubdD2 ubd_mem_double ubd_mem_insert)

lemma sup_assoc_ubd2:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X;is_sup R X {b, c} s\<rbrakk> \<Longrightarrow> ubd R X {a, b, c} = ubd R X {a, s} "
  apply(auto)
  apply (simp add: sup_upper_bounds trn ubdD1 ubd_ant1b ubd_mem_insert)
  by (simp add: sup_assoc_ubd1 trn)

lemma sup_assoc_ubd2b:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X;d \<in> X;is_sup R X {a, b} s; is_sup R X {c, d} t\<rbrakk> \<Longrightarrow>  ubd R X {s, t} =  ubd R X {a, b, c, d}"
  by (auto, simp add:sup_assoc_ubd1b, simp add: is_supE4 ub_double_iff1 ubd_mem_iff2)

lemma sup_assoc_ubd3:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X;is_sup R X {b, c} s\<rbrakk> \<Longrightarrow> (\<forall>t. is_sup R X {a, b, c} t  \<longleftrightarrow> is_sup R X  {a, s} t) "
  by (simp add: sup_assoc_ubd2 is_sup_def)
            
lemma sup_assoc_ubd3a:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X;is_sup R X {b, c} s; is_sup R X {a, b, c} t\<rbrakk> \<Longrightarrow> is_sup R X  {a, s} t"
  by (simp add: sup_assoc_ubd2 is_sup_def)

lemma sup_assoc_ubd3b:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X;is_sup R X {b, c} s;is_sup R X  {a, s} t\<rbrakk> \<Longrightarrow>  is_sup R X {a, b, c} t"
  by (simp add: sup_assoc_ubd2 is_sup_def)

lemma sup_assoc_ubd4a:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X;d \<in> X;is_sup R X {a, b} s; is_sup R X {c, d} t; is_sup R X {a, b, c, d} r\<rbrakk> \<Longrightarrow> is_sup R X  {s, t} r"
  by (meson Upper_eq_sup_eq sup_assoc_ubd2b)

lemma sup_assoc_ubd4b:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X;d \<in> X;is_sup R X {a, b} s; is_sup R X {c, d} t; is_sup R X  {s, t} r\<rbrakk> \<Longrightarrow>  is_sup R X {a, b, c, d} r"
  by (meson Upper_eq_sup_eq sup_assoc_ubd2b)

end

context
  fixes R::"'a rel" and X::"'a set" 
  assumes ref:"refl R X" and ant:"antisym R X" and trn:"trans R X" and ssl:"is_sup_semilattice R X"
begin
lemma sup_semilattice_fsup_props1:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> is_sup R X {a, Sup R X {b, c}} (Sup R X {a, b, c})"
  by (metis ant is_supE1 ref ssl ssupD3 sup_assoc_ubd3b sup_equality trn)

lemma sup_semilattice_supf_props2:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {a, Sup R X {b, c}} = Sup R X {a, b, c}"
  by (simp add: ant sup_equality sup_semilattice_fsup_props1)

lemma sup_semilattice_fsup_props3:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X; d \<in> X\<rbrakk> \<Longrightarrow> is_sup R X {Sup R X {a, b}, Sup R X {c, d}} (Sup R X {a, b, c, d})"
proof-
  assume A0:"a \<in> X" and A1:"b \<in> X" and A2:"c \<in> X" and A3:"d \<in> X"
  let ?sabcd = "Sup R X {a, b, c, d}" let ?sab="Sup R X {a,b}" let ?scd="Sup R X {c,d}"
  let ?ab="{a,b}" let ?cd="{c,d}" let ?abcd="{a,b,c,d}"
  obtain B00:"finite ?ab" and B01:"?ab \<subseteq> X" and B02:"?ab \<noteq> {}" and
         B10:"finite ?cd" and B01:"?cd \<subseteq> X" and B02:"?cd \<noteq> {}" and
         B20:"finite ?abcd" and B21:"?abcd \<subseteq> X" and B22:"?abcd \<noteq> {}" and
         B30:"?ab \<subseteq> ?abcd" and B31:"?cd \<subseteq> ?abcd"  using A0 A1 A2 A3 by blast
  obtain B40:"?sab \<in> X" and B41:"?scd \<in> X"  by (simp add: A0 A1 A2 A3 ant ssl ssupD4)
  obtain s where B0:"is_sup R X {a,b,c,d} s"  by (meson A0 A1 A2 A3 ant is_supE1 ref ssl ssupD3 sup_assoc_ubd4b trn)
  obtain B1:"(?sab, ?sabcd)\<in>R" and B2:"(?scd, ?sabcd)\<in>R"   by (metis A0 A1 A2 A3 B0 ant bsup_iff insertCI is_supD1121 is_supE1 ssl sup_equality trn)
  obtain B3:"(a,?sab)\<in>R" and B4:"(b,?sab)\<in>R" and B5:"(c,?scd)\<in>R" and B6:"(d,?scd)\<in>R"
    by (meson A0 A1 A2 A3 ant insertCI is_supD1121 ssl ssupD3)
  show "is_sup R X {Sup R X {a, b}, Sup R X {c, d}} (Sup R X {a, b, c, d})"
    by (metis A0 A1 A2 A3 B0 ant ref ssl ssupD3 sup_assoc_ubd4a sup_equality trn)
qed

lemma sup_semilattice_fsup_props4:
  "\<lbrakk> a \<in> X; b \<in> X; c \<in> X; d \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Sup R X {a, b}, Sup R X {c, d}} = Sup R X {a, b, c, d}"
  by (simp add: ant sup_equality sup_semilattice_fsup_props3)

lemma sup_semilattice_fsup_iso:
  "\<lbrakk>is_sup_semilattice R X; A \<in> Fpow_ne X; B \<in> Fpow_ne X; A \<subseteq> B\<rbrakk> \<Longrightarrow> (Sup R X A, Sup R X B)\<in>R"
  by (meson ant is_sup_iso1 sup_semilattice_fsup trn)
end
    


context
  fixes R::"'a rel" and X::"'a set" 
  assumes ref:"refl R X" and ant:"antisym R X" and trn:"trans R X" and ssl:"is_inf_semilattice R X"
begin


lemma inf_semilattice_finf_props1:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> is_inf R X {a, Inf R X {b, c}} (Inf R X {a, b, c})"
  using sup_semilattice_fsup_props1[of "converse R" X a b c]
  by (metis Sup_def ant antisym_on_converse converseI is_sup_semilattice_def ref refl_def ssl trans_on_converse trn)

lemma inf_semilattice_finf_props2:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf R X {a, Inf R X {b, c}} = Inf R X {a, b, c}"
  using sup_semilattice_supf_props2[of "converse R" X a b c]
  by (metis Sup_def ant antisym_on_converse converseI is_sup_semilattice_def ref refl_def ssl trans_on_converse trn)

lemma inf_semilattice_finf_props3:
  "\<lbrakk>a \<in> X; b \<in> X; c \<in> X; d \<in> X\<rbrakk> \<Longrightarrow> is_inf R X {Inf R X {a, b}, Inf R X {c, d}} (Inf R X {a, b, c, d})"
  using sup_semilattice_fsup_props3[of "converse R" X a b c d]
  by (metis Sup_def ant antisym_on_converse converseI is_sup_semilattice_def ref refl_def ssl trans_on_converse trn)

lemma inf_semilattice_finf_props4:
  "\<lbrakk> a \<in> X; b \<in> X; c \<in> X; d \<in> X\<rbrakk> \<Longrightarrow> Inf R X {Inf R X {a, b}, Inf R X {c, d}} = Inf R X {a, b, c, d}"
 using sup_semilattice_fsup_props4[of "converse R" X a b c d]
 by (metis Sup_def ant antisym_on_converse converseI is_sup_semilattice_def ref refl_def ssl trans_on_converse trn)

lemma inf_semilattice_finf_props5:
  "\<lbrakk>is_inf_semilattice R X; a \<in> X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Inf R X {Inf R X {a, b}, Inf R X {a, c}} = Inf R X {a, Inf R X {b, c}}"
  by (simp add: inf_semilattice_finf_props2 inf_semilattice_finf_props4 insert_commute)

lemma inf_semilattice_finf_anti:
  "\<lbrakk>is_inf_semilattice R X; A \<in> Fpow_ne X; B \<in> Fpow_ne X; A \<subseteq> B\<rbrakk> \<Longrightarrow> (Inf R X B, Inf R X A)\<in>R"
  using sup_semilattice_fsup_iso[of "converse R" X A B]
  by (metis Sup_def ant antisym_on_converse converseD converseI is_sup_semilattice_def ref refl_def trans_on_converse trn)


end

context
  fixes R::"'a rel" and X::"'a set"
  assumes ref:"refl R X" and ant:"antisym R X" and trn:"trans R X"
begin

lemma filters_on_lattice_sup_semilattice2b:
  "is_lattice R X \<Longrightarrow> is_sup_semilattice (pwr X) (filters_on R X)"
  by (simp add: ant csup_fsup filters_on_lattice_csup ref trn)

lemma filters_on_lattice_sup_semilattice3b:
  "is_lattice R X \<Longrightarrow> EF \<subseteq> (filters_on R X) \<Longrightarrow> finite EF \<Longrightarrow> EF \<noteq> {} \<Longrightarrow> (Sup (pwr X) (filters_on R X) EF) \<in> filters_on R X"
  by (simp add: ant csupD50 filters_is_clr1 filters_on_lattice_csup powrel6 powrel7 ref trn)

lemma filters_on_lattice_csup2:
  "is_lattice R X \<Longrightarrow> EF \<subseteq> (filters_on R X) \<Longrightarrow> EF \<noteq> {} \<Longrightarrow> (Sup (pwr X) (filters_on R X) EF) \<in> filters_on R X"
  by (simp add: ant csupD50 filters_is_clr1 filters_on_lattice_csup powrel6 powrel7 ref trn)

lemma filter_bsup_memD1:
  "x \<in> binary_filter_sup R X A B \<Longrightarrow> x \<in> X"
   by (simp add:binary_filter_sup_def)

lemma filter_bsup_mem_iff:
  "x \<in> binary_filter_sup R X A B \<longleftrightarrow> (x \<in> X \<and> (\<exists>a \<in> A. \<exists>b \<in> B. (Inf R X {a, b}, x)\<in>R))"
  by (simp add:binary_filter_sup_def)

lemma binary_filter_sup_obtains:
  assumes A0:"a \<in>  (binary_filter_sup R X F1 F2)"
  obtains a1 a2 where "a1 \<in> F1 \<and> a2 \<in> F2 \<and> (Inf R X {a1, a2}, a)\<in>R"
  by (meson assms filter_bsup_mem_iff)

lemma filters_on_lattice_bsup01:
  assumes A0:"is_lattice R X" and A1:"is_filter R X  F1" and A2:"is_filter R X  F2" and A3:"a \<in> F1"
  shows "a \<in> binary_filter_sup R X F1 F2"
proof-
  obtain y where A4:"y \<in> F2"
    using A2 filter_ex_elem by blast
  have B0:"(Inf R X {a, y}, a)\<in>R"
    by (meson A0 A1 A2 A3 A4 ant converseD filterD21 insertI1 is_supD1121 lattD31)
  show "a \<in> binary_filter_sup R X F1 F2"
    by (meson A1 A3 A4 B0 filterD21 filter_bsup_mem_iff)
qed

lemma filters_on_lattice_bsup02:
  assumes A0:"is_lattice R X" and A1:"is_filter R X  F1" and A2:"is_filter R X  F2" and A3:"b \<in> F2"
  shows "b \<in> binary_filter_sup R X F1 F2"
proof-
  obtain x where A4:"x \<in> F1"
   using A1 filter_ex_elem by blast
  have B0:"(Inf R X {x, b}, b)\<in>R"
    by (meson A0 A1 A2 A3 A4 ant binary_supD32 converseD filterD21 is_supE1 lattD31)
  show "b \<in> binary_filter_sup R X F1 F2"
    by (meson A2 A3 A4 B0 filterD21 filter_bsup_mem_iff)
qed

lemma filters_on_lattice_bsup03:
  "\<lbrakk>is_lattice R X; is_filter R X  F1; is_filter R X  F2\<rbrakk> \<Longrightarrow> F1 \<subseteq> (binary_filter_sup R X F1 F2)"
  by (simp add: filters_on_lattice_bsup01 subsetI)

lemma filters_on_lattice_bsup04:
  "\<lbrakk>is_lattice R X; is_filter R X  F1; is_filter R X  F2\<rbrakk> \<Longrightarrow> F2 \<subseteq> (binary_filter_sup R X F1 F2)"
  by (simp add: filters_on_lattice_bsup02 subsetI)

lemma filters_on_lattice_bsup1b:
  "\<lbrakk>is_lattice R X; is_filter R X  F1; is_filter R X  F2\<rbrakk> \<Longrightarrow>  is_ord_cl X (binary_filter_sup R X F1 F2) R"
  by(auto simp add:binary_filter_sup_def is_ord_cl_def,meson ant filterD21 is_supE1 lattD31 trans_onD trn)

lemma tmp_inf_lemma:
  assumes "is_lattice R X"  "a \<in> X" "a1 \<in> X" "a2 \<in> X" "b1 \<in> X" "b2 \<in> X" "(Inf R X {a1, a2}, a)\<in>R" 
  shows "(Inf R X {Inf R X {a1, b1}, Inf R X {a2, b2}}, a)\<in>R"
proof-
  have B0:"Inf R X {Inf R X {a1, b1}, Inf R X {a2, b2}} = Inf R X {a1, b1, a2, b2}"
    by (metis ant assms(1) assms(3) assms(4) assms(5) assms(6) inf_semilattice_finf_props4 latt_iff ref trn)
  also have B1:"(Inf R X {a1, b1, a2, b2}, Inf R X {a1, a2})\<in>R"
    using inf_semilattice_finf_anti[of R X "{a1, a2}" "{a1, b1, a2, b2}"]
    by (smt (verit) ant assms(1) assms(3) assms(4) assms(5) assms(6) binary_supD31 calculation converseD is_supE1 lattD31 sup_ge5 trans_on_converse trn)
  also have B2:"(Inf R X {a1, a2}, a)\<in>R"
    using assms(7) by force
  show ?thesis
    by (meson B2 ant assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) calculation is_supE1 lattD31 trans_onD trn)
qed 
  

lemma filters_on_lattice_bsup2a:
  assumes A0:"is_lattice R X" and A1:"is_filter R X F1" and A2:"is_filter R X F2" and
          A3: "a \<in> (binary_filter_sup R X F1 F2)" and  A4:"b \<in> (binary_filter_sup R X F1 F2)"
  shows "(\<exists>c \<in> (binary_filter_sup R X F1 F2). (c,a)\<in>R \<and> (c, b)\<in>R)"
proof-
  obtain a1 a2 where B0:"a1 \<in> F1 \<and> a2 \<in> F2 \<and> (Inf R X {a1, a2}, a)\<in>R"
    using A3 binary_filter_sup_obtains by blast
  obtain b1 b2 where B1:"b1 \<in> F1 \<and> b2 \<in> F2 \<and> (Inf R X {b1, b2},b)\<in>R"
    using A4 binary_filter_sup_obtains by blast
  have B0b:"a \<in> X \<and> b \<in> X \<and> a1 \<in> X \<and> a2 \<in> X \<and> b1 \<in> X \<and> b2 \<in> X"
    using A1 A2 A3 A4 B0 B1 filterD2 filter_bsup_mem_iff by auto
  have B2:"(Inf R X {Inf R X {a1, b1}, Inf R X {a2, b2}},a)\<in>R"
    by (meson A0 B0 B0b tmp_inf_lemma)
  have B3:"(Inf R X {Inf R X {a1, b1}, Inf R X {a2, b2}},b)\<in>R"
    by (smt (verit) A0 B0b B1 insert_commute tmp_inf_lemma)
  obtain ab1 where P1A3:"ab1 \<in> F1 \<and> (ab1,a1)\<in>R \<and> (ab1,b1)\<in>R"
    by (meson A1 B0 B1 is_filter_def converseD is_dirE1)
  obtain ab2 where P1A4:"ab2 \<in> F2 \<and> (ab2,a2)\<in>R \<and> (ab2, b2)\<in>R"
    by (metis A2 B0 B1 is_filter_def converseD is_dirE1)
  obtain C0:"a1 \<in> X" and C1:"b1 \<in>X" and C2:"a2 \<in> X" and C3:"b2 \<in> X" and C4:"ab1 \<in> X" and C5:"ab2 \<in> X"
    by (metis A1 A2 B0b P1A3 P1A4 filterD21)
  obtain C6:"ab1 \<in> lbd R X {a1,b1}" and C7:"ab2 \<in> lbd R X {a2,b2}"
    by (simp add: C4 C5 P1A3 P1A4 ubd_mem_doubleI)
  have P1B10:"(ab1,Inf R X {a1, b1})\<in>R"
    by (meson A0 B0b C6 ant converseD is_supE3 lattD31)
  have P1B11:"(ab2,Inf R X {a2, b2})\<in>R"
     by (meson A0 B0b C7 ant converseD is_supE3 lattD31)
  have P1B1:"(ab1,Inf R X {a1, b1})\<in>R \<and> (ab2,Inf R X {a2, b2})\<in>R"
    by (simp add: P1B10 P1B11)
  have P1B2:"Inf R X {a1, b1} \<in> F1 \<and> Inf R X {a2, b2} \<in> F2"
    using A0 A1 A2 B0 B1 ant filter_finf_closed1 latt_iff by fastforce
  have P1B3:"Inf R X {Inf R X {a1, b1}, Inf R X {a2, b2}} \<in> (binary_filter_sup R X F1 F2)"
    by (meson A0 A1 A2 P1B2 ant filterD21 filter_bsup_mem_iff is_supE1 lattD31 ref reflD1)
  show "(\<exists>c \<in> (binary_filter_sup R X F1 F2).  (c,a)\<in>R \<and>  (c, b)\<in>R)"
    using B2 B3 P1B3 by blast
qed
         
lemma filters_on_lattice_bsup2b:
  "\<lbrakk>is_lattice R X; is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> is_dir (binary_filter_sup R X F1 F2) (converse R)"
  by (simp add: filters_on_lattice_bsup2a is_dirI1)

lemma filters_on_lattice_bsup3:
  "\<lbrakk>is_lattice R X; is_filter R X  F1; is_filter R X  F2\<rbrakk> \<Longrightarrow> (binary_filter_sup R X F1 F2) \<noteq> {}"
  by (metis is_filter_def filters_on_lattice_bsup04 ne_subset_ne)

lemma filters_on_lattice_bsup4:
  "\<lbrakk>is_lattice R X; is_filter R X  F1; is_filter R X  F2\<rbrakk> \<Longrightarrow> (binary_filter_sup R X F1 F2) \<in> filters_on R X"
  by (metis is_filter_def filter_bsup_mem_iff filters_on_iff filters_on_lattice_bsup1b filters_on_lattice_bsup2b filters_on_lattice_bsup3 subsetI)

lemma filters_on_lattice_bsup5:
  "\<lbrakk>is_lattice R X; is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> (binary_filter_sup R X F1 F2) \<in> ubd (pwr X) (filters_on R X) {F1, F2}"
  by (meson filterD2 filters_on_iff filters_on_lattice_bsup03 filters_on_lattice_bsup04 filters_on_lattice_bsup4 pwr_memI ubd_mem_double)

lemma filters_on_lattice_bsup6:
  assumes A0:"is_lattice R X" and A1:"is_filter R X  F1" and A2:"is_filter R X F2" and A3:"G \<in> (ubd (pwr X)  (filters_on R X) {F1, F2})"
  shows "(binary_filter_sup R X F1 F2) \<subseteq> G" (is "?L \<subseteq> ?R")
proof
  fix x assume A4:"x \<in> ?L"
  obtain a1 a2  where B0:"a1 \<in> F1 \<and> a2 \<in> F2 \<and> (Inf R X {a1, a2},x)\<in>R"
    using A4 binary_filter_sup_obtains by blast
  have B1:"a1 \<in> G \<and> a2 \<in> G"
    by (meson A3 B0 pwr_mem_iff subset_iff ubd_mem_doubleE1 ubd_mem_doubleE2)
  have B2:"Inf R X {a1, a2} \<in> G"
    by (metis A0 A3 B1 ant filter_finf_closed1 filters_on_iff latt_iff ubdD2)
  have B3:"is_filter R X  G "
    by (meson A3 filters_on_iff ubdD2)
  show "x \<in> G"
    by (meson A4 B0 B2 B3 filterD4 filter_bsup_mem_iff ord_cl_memI1)
qed

lemma filters_on_lattice_bsup7:
  "\<lbrakk>is_lattice R X; is_filter R X  F1; is_filter R X  F2\<rbrakk> \<Longrightarrow> is_sup (pwr X) (filters_on R X) {F1, F2} (binary_filter_sup R X F1 F2) "
  by (meson filters_on_lattice_bsup5 filters_on_lattice_bsup6 is_supI5 pwr_mem_iff ubd_mem_doubleE1)

lemma filters_on_lattice_bsup8:
  "\<lbrakk>is_lattice R X; is_filter R X  F1; is_filter R X  F2\<rbrakk> \<Longrightarrow> Sup (pwr X) (filters_on R X) {F1, F2} = (binary_filter_sup R X F1 F2)"
  by (simp add: filters_is_clr1 filters_on_lattice_bsup7 powrel6 sup_equality)

lemma filters_on_lattice_bsup0:
  "\<lbrakk>is_lattice R X; is_filter R X  F1; is_filter R X  F2\<rbrakk> \<Longrightarrow> (filter_closure R X (F1 \<union> F2)) = Sup (pwr X) (filters_on R X) {F1, F2}"
  using filters_on_lattice_sup_semilattice1b sup_equality
  by (metis ant filters_is_clr1 powrel6 ref trn)

lemma filters_on_lattice_bsup1:
  "\<lbrakk>is_lattice R X;  is_filter R X  F1; is_filter R X  F2; z \<in> Sup (pwr X) (filters_on R X) {F1, F2}\<rbrakk> \<Longrightarrow>(\<exists>Fx \<subseteq>(F1 \<union> F2). finite Fx \<and> Fx \<noteq> {} \<and> (Inf R X Fx,z)\<in>R)"
  by (metis filterD1 filter_closure_obtains filters_on_lattice_bsup0 sup_bot.eq_neutr_iff)

lemma filters_on_lattice_bsup2:
  assumes A0:"is_lattice R X" and A1:"is_filter R X F1" and A2:"is_filter R X F2" and
          A3:"z \<in> Sup (pwr X) (filters_on R X) {F1, F2}"
  shows "(\<exists>f1 \<in>F1. \<exists>f2 \<in> F2. (Inf R X {f1, f2},z)\<in>R)"
  by (metis A0 A1 A2 A3 filter_bsup_mem_iff filters_on_lattice_bsup8)


(*On a topped inf semilattice filters form a complete inf semilattice*)

lemma filters_on_top_inf_semilattice_is_cinf:
  "\<lbrakk>is_greatest R X top; is_inf_semilattice R X\<rbrakk> \<Longrightarrow> is_cinf_semilattice (pwr X) (filters_on R X)"
  apply(auto simp add:is_cinf_semilattice_def)
  using filters_is_clr1b apply blast
  by (metis ant antisym_on_subset clatD22 filters_is_clr1 filters_on_top_inf_lattice_clattice insert_absorb insert_not_empty powrel1 powrel7 ref trn) 

(*On a topped inf semlattice filters form a complete complete lattice*)

end

subsection UpDwClosure
subsubsection UpClosure


lemma up_cl_mem_iff:
  "x \<in> up_cl R X A \<longleftrightarrow> (x \<in> X \<and> (\<exists>a \<in> A. (a, x) \<in> R))"
  by (simp add: up_cl_def)

lemma up_cl_memD1:
  "x \<in> up_cl R X A \<Longrightarrow> x \<in> X"
  by (simp add: up_cl_def)

lemma up_cl_memD2:
  "x \<in> up_cl R X A \<Longrightarrow> \<exists>a \<in> A. (a, x) \<in> R"
  by (simp add: up_cl_def)

lemma up_cl_memI1:
  "x \<in> X \<Longrightarrow> a \<in> A \<Longrightarrow> (a, x) \<in> R \<Longrightarrow> x \<in> up_cl R X A"
  by (meson up_cl_mem_iff)

lemma up_cl_memI2:
  "x \<in> X \<Longrightarrow> (\<exists>a \<in> A. (a, x) \<in> R) \<Longrightarrow> x \<in> up_cl R X A"
  by (simp add: up_cl_mem_iff)

lemma up_cl_sub1:
  "\<lbrakk>refl R X; A \<subseteq> X; a \<in> A\<rbrakk> \<Longrightarrow> a \<in> up_cl R X A"
  by (meson in_mono reflD1 up_cl_memI2)

lemma up_cl_sub2:
  "\<lbrakk>refl R X; A \<subseteq> X; a \<in> A\<rbrakk>\<Longrightarrow> A \<subseteq>  up_cl R X A"
  by (simp add: subsetI up_cl_sub1)

lemma up_cl_sub3:
  "up_cl R X A \<subseteq> X"
  by (simp add: subsetI up_cl_memD1)

lemma up_cl_iso1:
  "A \<subseteq> B \<Longrightarrow> up_cl R X A \<subseteq> up_cl R X B"
  by (meson in_mono subsetI up_cl_memD1 up_cl_memD2 up_cl_memI1)

lemma up_cl_idem1:
  "\<lbrakk>A \<subseteq> X; trans R X;x \<in> up_cl R X (up_cl R X A)\<rbrakk> \<Longrightarrow> x \<in> up_cl R X A"
  by (smt (verit) in_mono trans_onD up_cl_mem_iff)


lemma up_cl_idem2:
  "\<lbrakk>A \<subseteq> X; trans R X\<rbrakk> \<Longrightarrow> up_cl R X (up_cl R X A) \<subseteq> up_cl R X A"
  by (simp add: subsetI up_cl_idem1)

lemma up_cl_idem3:
  "\<lbrakk>A \<subseteq> X; trans R X;refl R X\<rbrakk> \<Longrightarrow> up_cl R X (up_cl R X A) = up_cl R X A"
  by (simp add: subsetI subset_antisym up_cl_idem2 up_cl_sub1 up_cl_sub3)

lemma up_cl_singleton:
  "x \<in> up_cl R X {a}  \<longleftrightarrow> (x \<in> X \<and> (a, x) \<in> R)"
  by (simp add: up_cl_mem_iff)

lemma up_cl_lorc:
  "up_cl R X {a} = lorc R X a"
  by (simp add: lorc_mem_iff1 set_eq_iff up_cl_singleton)

lemma up_cl_ext:
  "\<lbrakk>refl R X\<rbrakk> \<Longrightarrow> extensive (pwr X) (Pow X) (\<lambda>A. up_cl R X A)"
  by (simp add: extensive_def pwr_memI subsetI up_cl_sub1 up_cl_sub3)

lemma up_cl_iso:
  "isotone (pwr X) (Pow X)  (pwr X) (\<lambda>A. up_cl R X A)"
  by (simp add: isotone_def pwr_mem_iff up_cl_iso1 up_cl_sub3)

lemma up_cl_idem:
  "\<lbrakk>trans R X;refl R X\<rbrakk> \<Longrightarrow> idempotent (Pow X) (\<lambda>A. up_cl R X A)"
  by (simp add: idempotent_def up_cl_idem3)

lemma up_cl_cl:
  "\<lbrakk>trans R X;refl R X\<rbrakk> \<Longrightarrow> closure (pwr X) (Pow X) (\<lambda>A. up_cl R X A)"
  by (simp add: image_subsetI closure_def up_cl_ext up_cl_idem up_cl_iso up_cl_sub3)

lemma up_cl_memI3:
  "\<lbrakk>trans R X; A \<subseteq> X; refl R X\<rbrakk> \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> (up_cl R X A); b \<in> X; (a, b)\<in>R\<rbrakk> \<Longrightarrow> b \<in> (up_cl R X A))"
  by (meson up_cl_idem1 up_cl_memI1)

lemma up_cl_is_up_cl:
  "\<lbrakk>trans R X; A \<subseteq> X; refl R X\<rbrakk> \<Longrightarrow> is_ord_cl X (up_cl R X A) R"
  by (simp add: is_ord_clI1 up_cl_memI3)

lemma dwdir_upcl_is_dwdir:
  assumes A0:"is_dir A (converse R)" and A1:"A \<subseteq> X" and A2:"trans R X" and A3:"refl R X"
  shows "is_dir (up_cl R X A) (converse R)"
proof-
  have B0:"\<And>a b.  \<lbrakk>a \<in> up_cl R X A; b \<in> up_cl R X A\<rbrakk> \<Longrightarrow>  (\<exists>c\<in>up_cl R X A. (c,a)\<in>R \<and> (c,b)\<in>R)"
  proof-
    fix a b assume A4:"a \<in> up_cl R X A" and A5:"b \<in> up_cl R X A" 
    obtain a1 b1 where B1:"a1 \<in> A \<and> b1 \<in> A \<and> (a1,a)\<in>R \<and> (b1,b)\<in>R"  by (meson A4 A5 up_cl_memD2)
    obtain c where B2:"c \<in> A \<and> (c,a1)\<in>R \<and> (c,b1)\<in>R" by (meson A0 B1 converseD is_dirE1) 
    have B3:"c \<in> up_cl R X A \<and> (c,a)\<in>R \<and> (c,b)\<in>R"  by (meson A1 A2 A3 A4 A5 B1 B2 trans_onD up_cl_memD1 up_cl_sub1) 
    show "\<exists>c\<in>up_cl R X A. (c,a)\<in>R \<and> (c,b)\<in>R"   using B3 by auto
  qed
  show ?thesis   by (simp add: B0 is_dirI1)
qed

lemma upcl_dwdir_is_dwdir:
  assumes A0:"is_dir (up_cl R X A) (converse R)" and A1:"A \<subseteq> X" and A2:"trans R X" and A3:"refl R X"
  shows "is_dir A (converse R)"
proof-
  have B0:" \<And>a b. \<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> (\<exists>c\<in>A. (c,a)\<in>R \<and> (c,b)\<in>R)"
  proof-
    fix a b assume A4:"a \<in> A" and A5:"b \<in> A"
    have B1:"a \<in> up_cl R X A \<and> b \<in> up_cl R X A" by (simp add: A1 A3 A4 A5 up_cl_sub1) 
    obtain c where B2:"c \<in> up_cl R X A \<and> (c,a)\<in>R \<and> (c,b)\<in>R"   by (meson A0 B1 converseD is_dirE1) 
    obtain d where B3:"d \<in> A \<and> (d,c)\<in>R" by (meson B2 up_cl_memD2) 
    have B4:"d \<in> A \<and> (d,a)\<in>R \<and> (d,b)\<in>R" by (meson A1 B1 B2 B3 assms(3) in_mono trans_onD up_cl_memD1)
    show "\<exists>c\<in>A. (c,a)\<in>R \<and> (c,b)\<in>R"    using B4 by blast
  qed
  show ?thesis   by (simp add: B0 is_dirI1)
qed

lemma leq_sup:
  "\<lbrakk>antisym R X;trans R X; refl R X; is_lattice R X; x \<in> X; y \<in>X; z \<in> X;(x, z)\<in>R; (y,z)\<in>R\<rbrakk> \<Longrightarrow> (Sup R X {x, y}, z) \<in>R"
  by (simp add: bsup_geI3 lattD42)

lemma distr_lattice_filters:
  "\<lbrakk>antisym R X;trans R X; refl R X;distributive_lattice R X\<rbrakk> \<Longrightarrow> is_lattice (pwr X) (filters_on R X)"
  by (simp add: distributive_lattice_def filters_on_lattice_inf_semilattice1 filters_on_lattice_sup_semilattice2b lattI2)
  
lemma lattice_filters_distr:
  assumes A0:"distributive_lattice R X"  and A1:"antisym R X" and A2:"refl R X" and A3:"trans R X"
  shows "distributive_lattice (pwr X) (filters_on R X)"
proof-
  let ?F="filters_on R X" let ?R="pwr X"
  have B01:"is_lattice R X"  using assms distributive_lattice_def by blast
  have B02:"is_lattice (pwr X) ?F"  by (simp add: assms distr_lattice_filters)
  have B1:" \<And>x y z. \<lbrakk>x \<in> ?F;  y \<in>?F; z \<in> ?F\<rbrakk> \<Longrightarrow> (Inf ?R ?F {Sup ?R ?F {x, y}, Sup ?R ?F {x, z}}, Sup ?R ?F {x, Inf ?R ?F {y, z}})\<in>(pwr X)"
  proof-
    fix f g h assume A4:"f \<in> ?F" and A5:"g \<in> ?F" and A6:"h \<in> ?F"
    let ?sfg="Sup ?R ?F {f, g}" and ?sfh="Sup ?R ?F {f, h}" and  ?igh="Inf ?R ?F {g, h}"
    have D0:"Inf ?R ?F {?sfg, ?sfh} \<subseteq> Sup ?R ?F {f, ?igh}"
    proof
        fix z assume A7:"z \<in> (Inf ?R ?F {?sfg, ?sfh})"
        have B2:"Inf ?R ?F {?sfg, ?sfh} =?sfg \<inter> ?sfh"
          by (simp add: A1 A2 A3 A4 A5 A6 B01 filters_lattice_inf_op filters_on_lattice_sup_semilattice3b)
        have B3:"z \<in> ?sfg \<and> z \<in> ?sfh"    using A7 B2 by blast
        obtain x1 y where B4:"x1 \<in> f \<and> y \<in> g \<and> (Inf R X {x1, y},z)\<in>R"
          by (metis A1 A2 A3 A4 A5 B01 B3 filters_on_iff filters_on_lattice_bsup2)
        obtain x2 t where B5:"x2 \<in> f \<and> t \<in> h \<and> (Inf R X {x2, t} ,z)\<in>R"
          by (metis A1 A2 A3 A4 A6 B01 B3 filters_on_iff filters_on_lattice_bsup2)
        have B450:"x1 \<in> X \<and> y \<in> X \<and> x2 \<in> X \<and> t \<in> X"
          by (meson A4 A5 A6 B4 B5 filterD21 filters_on_iff)
        have B6:"Sup R X {x1, Inf R X {x2, t}} \<in> f"
          by (meson A1 A4 B01 B4 B450 filter_bsup_memI1 filters_on_iff is_supE1 lattD31 lattD42)
        have B7:"Sup R X {y, x2} \<in> f"
          by (meson A1 A2 A3 A4 B01 B450 B5 filter_on_lattice_sup01 filters_on_iff)
        have B8:"Sup R X {y, t} \<in> g"
          by (meson A1 A2 A3 A5 B01 B4 B450 filters_on_iff lattice_filter_memI)
        have B9:"Sup R X {y, t} \<in> h"
          by (metis A1 A2 A3 A6 B01 B450 B5 filter_on_lattice_sup01 filters_on_iff)
        have B10:"Inf R X {Sup R X {x1, Inf R X {x2, t}}, Sup R X {y, x2}} \<in> f"
          by (metis A1 A4 B01 B6 B7 filter_finf_closed1 filters_on_iff latt_iff)
        have B11:"Inf R X {Sup R X {y, x2}, Sup R X {y, t}} = Sup R X {y, Inf R X {x2, t}}"
          by (simp add: B450 assms distr_latticeD1)
        have B12:"Inf R X {Sup R X {x1, Inf R X {x2, t}}, Inf R X {Sup R X {y, x2}, Sup R X {y, t}}} =
                  Inf R X {Sup R X {x1, Inf R X {x2, t}},  Sup R X {y, Inf R X {x2, t}}}"
          by (simp add: B11)
        have B13:"... = Sup R X {Inf R X {x2, t}, Inf R X {x1, y}}"
          by (smt (verit, ccfv_threshold) A0 A1 B01 B450 distr_latticeD2 insert_commute is_supE1 lattD31)
        have B14:"... = Sup R X {Inf R X {x1, y}, Inf R X {x2, t}}"
          by (simp add: insert_commute)
        have B15:"Sup R X {Inf R X {x1, y}, Inf R X {x2, t}} = Inf R X {Sup R X {x1, Inf R X {x2, t}}, Inf R X {Sup R X {y, x2}, Sup R X {y, t}}} "
          using B11 B13 B14 by presburger
        have B16:"... =  Inf R X {Inf R X {Sup R X {x1, Inf R X {x2, t}}, Sup R X {y, x2}}, Sup R X {y, t}}"
          by (metis A1 A3 B01 B450 binf_assoc2d is_supE1 lattD31 latt_iff ssupD4)
        obtain C0:"Inf R X {x1, y} \<in> X" and C1:"Inf R X {x2, t} \<in> X" and C2:"(Inf R X {x1, y},z)\<in>R" and 
               C3:"(Inf R X {x2,t},z)\<in>R"
          by (meson A1 B01 B4 B450 B5 is_supE1 lattD31)
        have B17:"(Sup R X {Inf R X {x1, y}, Inf R X {x2, t}}, z)\<in>R"
          using leq_sup[of X R "Inf R X {x1, y}" "Inf R X {x2, t}" z]
          by (meson A1 A2 A3 A4 A5 B01 B02 B3 C0 C1 C2 C3 filterD21 filters_is_clr1 filters_on_iff lattD42 powrel6 ssupD4)
        have B18:"(Inf R X {Inf R X {Sup R X {x1, Inf R X {x2, t}}, Sup R X {y, x2}}, Sup R X {y, t}},z)\<in>R"
          using B11 B13 B14 B16 B17 by presburger
        have B19:"Inf R X {Sup R X {x1, Inf R X {x2, t}}, Sup R X {y, x2}} \<in> f"
          by (simp add: B10)
        have B20:"Sup R X {y, t} \<in> Inf ?R ?F {g, h}"
          by (simp add: A1 A2 A3 A5 A6 B01 B8 B9 filters_lattice_inf_op)
        have B21:"z \<in> binary_filter_sup R X f ?igh"
          by (meson A1 A2 A3 A4 A5 B02 B18 B19 B20 B3 filterD21 filter_bsup_mem_iff filters_is_clr1 filters_on_iff lattD42 powrel6 ssupD4)
        have B22:" binary_filter_sup R X f ?igh = Sup ?R ?F {f, ?igh}"
          by (metis A1 A2 A3 A4 A5 A6 B01 filters_lattice_inf filters_lattice_inf_op filters_on_iff filters_on_lattice_bsup8 is_supE1)
        show "z \<in> Sup ?R ?F {f, ?igh}"
          using B21 B22 by blast
   qed
   have B23:"Inf ?R ?F {?sfg, ?sfh} \<subseteq> X"  by (meson A4 A5 A6 B02 distrib_sup_le filters_is_clr1 powrel6 powrel7 pwr_mem_iff)
   have B24:"Sup ?R ?F {f, ?igh} \<subseteq> X"  by (meson A4 A5 A6 B02 B23 distrib_sup_le dual_order.trans filters_is_clr1 powrel6 powrel7 pwr_memD)
   show "(Inf ?R ?F {?sfg, ?sfh}, Sup ?R ?F {f, ?igh}) \<in> ?R" by (simp add: B24 D0 pwr_mem_iff) 
  qed
  have P:" \<And>x y z. \<lbrakk>x \<in> ?F;  y \<in>?F; z \<in> ?F\<rbrakk> \<Longrightarrow> (Inf ?R ?F {Sup ?R ?F {x, y}, Sup ?R ?F {x, z}}, Sup ?R ?F {x, Inf ?R ?F {y, z}}) \<in> (pwr X)"
    using B1
    by blast
  show ?thesis
    by (smt (verit) B02 B1 distrib_sup_le distributive_lattice_def filters_is_clr1 powrel6 powrel7 powrel8 subset_antisym)
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


lemma sup_primeD1:
  "\<lbrakk>sup_prime R X A; a \<in> X; b \<in> X; Sup R X {a, b} \<in> A\<rbrakk> \<Longrightarrow> a \<in> A \<or> b \<in> A"
  by (simp add:sup_prime_def)

lemma inf_primeD1:
  "\<lbrakk>inf_prime R X A; a \<in> X; b \<in> X; Inf R X {a, b} \<in> A\<rbrakk> \<Longrightarrow> a \<in> A \<or> b \<in> A"
  by (simp add: Sup_def sup_prime_def)

lemma sup_primeI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; Sup R X {a, b} \<in> A\<rbrakk> \<Longrightarrow> (a \<in> A \<or> b \<in> A)) \<Longrightarrow> sup_prime R X A"
  by (simp add:sup_prime_def)

lemma inf_primeI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; Inf R X {a, b} \<in> A\<rbrakk> \<Longrightarrow> (a \<in> A \<or> b \<in> A)) \<Longrightarrow> inf_prime R X A"
  by (simp add:sup_prime_def Sup_def)

lemma elem_sup_primeD1:
  "\<lbrakk>elem_sup_prime R X x; a \<in> X; b \<in> X; (x, Sup R X {a, b})\<in>R\<rbrakk> \<Longrightarrow> ((x, a)\<in>R \<or> (x, b)\<in>R)"
  by(simp add:elem_sup_prime_def)

lemma elem_inf_primeD1:
  "\<lbrakk>elem_inf_prime R X x; a \<in> X; b \<in> X; (Inf R X {a, b}, x)\<in>R\<rbrakk> \<Longrightarrow> ((a,x)\<in>R \<or> (b,x)\<in>R)"
  by (simp add: Sup_def elem_sup_prime_def)
                                         
lemma elem_sup_primeI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; (x,Sup R X {a, b})\<in>R\<rbrakk> \<Longrightarrow> ((x,a)\<in>R \<or> (x, b)\<in>R)) \<Longrightarrow> elem_sup_prime R X x"
  by (simp add:elem_sup_prime_def)                    

lemma elem_inf_primeI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; (Inf R X {a, b}, x)\<in>R\<rbrakk> \<Longrightarrow> ((a,x)\<in>R \<or> (b,x)\<in>R)) \<Longrightarrow> elem_inf_prime R X x"
  by (simp add:elem_sup_prime_def Sup_def)

lemma elem_sup_primeE1:
  "\<lbrakk>x \<in> X; elem_sup_prime R X x\<rbrakk> \<Longrightarrow> sup_prime R X (lorc R X x)"
  by (metis elem_sup_prime_def lorcD12 lorcI1 sup_prime_def)       

lemma elem_inf_primeE1:
  "\<lbrakk>x \<in> X; elem_inf_prime R X x\<rbrakk> \<Longrightarrow> inf_prime R X (lorc (converse R) X x)"
  by (simp add: elem_sup_primeE1)

lemma elem_sup_primeI2:
  "\<lbrakk>x \<in> X;sup_prime R X  (lorc R X x);refl R X; trans R X; antisym R X; is_sup_semilattice R X\<rbrakk> \<Longrightarrow> elem_sup_prime R X x"
  by (metis elem_sup_prime_def lorcD12 lorcI1 ssupD4 sup_prime_def)

lemma elem_inf_primeI2:
  "\<lbrakk>x \<in> X; inf_prime R X (lorc (converse R) X x);refl R X; trans R X; antisym R X; is_inf_semilattice R X\<rbrakk> \<Longrightarrow> elem_inf_prime R X x"
  by (simp add: elem_sup_primeI2 is_sup_semilattice_def refl_def)

lemma fin_sup_irrD1:
  "\<lbrakk>fin_sup_irr R X x; a \<in> X; b \<in> X; x=Sup R X {a, b}\<rbrakk> \<Longrightarrow> (x = a \<or> x =b)"
  by (simp add:fin_sup_irr_def)

lemma fin_inf_irrD1:
  "\<lbrakk>fin_inf_irr R X x; a \<in> X; b \<in> X; x=Inf R X {a, b}\<rbrakk> \<Longrightarrow> (x = a \<or> x =b)"
  by (simp add:fin_sup_irr_def Sup_def)

lemma fin_sup_irrI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; x = Sup R X {a, b}\<rbrakk> \<Longrightarrow> x =a \<or> x =b) \<Longrightarrow> fin_sup_irr R X x"
  by (simp add: fin_sup_irr_def)

lemma fin_inf_irrI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; x = Inf R X {a, b}\<rbrakk> \<Longrightarrow> x =a \<or> x =b) \<Longrightarrow> fin_inf_irr R X x"
  by (simp add: fin_sup_irr_def Sup_def)

lemma fin_sup_irrE1:
  "\<lbrakk>antisym R X; trans R X; refl R X; distributive_lattice R X; x \<in> X; elem_sup_prime R X x\<rbrakk> \<Longrightarrow> fin_sup_irr R X x"
  by (metis antisym_onD binary_supD31 binary_supD32 distributive_lattice_def elem_sup_prime_def fin_sup_irr_def lattD42 reflD1 ssupD3)


lemma fin_inf_irrE1:
  "\<lbrakk>antisym R X; trans R X; refl R X;distributive_lattice R X; x \<in> X; elem_inf_prime R X x\<rbrakk> \<Longrightarrow> fin_inf_irr R X x"
  by (smt (verit, del_insts) bsup_ge1 bsup_ge2 distr_latticeD5 elem_inf_primeD1 fin_inf_irrI1 lattD42 lattice_absorb12 lattice_absorb13 refl_def)


lemma elem_sup_primeI3:
  assumes A0:"distributive_lattice R X" and A1:"x \<in> X" and A2: "fin_sup_irr R X x" and A3:"antisym R X" and
          A4:"trans R X" and A5:"refl R X"
  shows "elem_sup_prime R X x"
proof-
  have B0:"\<And>a b. \<lbrakk>a \<in> X; b \<in> X; (x,Sup R X {a, b})\<in>R\<rbrakk> \<Longrightarrow> ((x,a)\<in>R \<or> (x, b)\<in>R)"
  proof-
    fix a b assume P0:"a \<in> X" and P1:"b \<in> X" and P2:"(x,Sup R X {a,b})\<in>R"
    have B1:"x = Inf R X {x, Sup R X {a, b}}"
      using A0 A1 P0 P1 P2 distributive_lattice_def 
      by (metis A3 A5 antisym_on_converse binary_supI2 converseI is_supE1 lattD31 lattD32 reflD1 sup_equality)
    have B2:"... = Sup R X {Inf R X {x, a}, Inf R X {x, b}}"
      by (simp add: A0 A1 A3 A4 A5 P0 P1 distr_latticeD3)
    have B3:"x = Inf R X {x, a} \<or> x = Inf R X {x, b}"
      by (metis A0 A1 A2 A3 B1 B2 P0 P1 distr_latticeD5 fin_sup_irr_def is_supE1 lattD31)
    show "(x,a)\<in>R \<or> (x, b)\<in>R"
      by (metis A0 A1 A3 B3 P0 P1 binary_supD32 converse.simps distributive_lattice_def lattD31)
  qed
  show ?thesis
    by (simp add: B0 elem_sup_primeI1)
qed

lemma lattice_dualization:
  "\<lbrakk>is_lattice R X; antisym R X; refl R X; trans R X\<rbrakk> \<Longrightarrow> (\<And>R X. \<lbrakk>is_lattice R X; antisym R X; refl R X; trans R X\<rbrakk> \<Longrightarrow> P R X) \<Longrightarrow> P (converse R) X "
  proof-
    assume A0:"is_lattice R X" and A1:"antisym R X" and A2:"refl R X" and A3:"trans R X" and A4:"(\<And>R X. \<lbrakk>is_lattice R X; antisym R X; refl R X; trans R X\<rbrakk> \<Longrightarrow> P R X)"
    have B0:"is_lattice (converse R) X"
      by (metis A0 converse_converse lattD1 lattD21 lattD22 lattI1)
    also obtain  B1:"antisym (converse R) X" and B2:"refl (converse R) X" and B3:"trans (converse R) X"
      by (meson A1 A2 A3 antisym_on_converse converseI refl_def trans_on_converse)
    then show "P (converse R) X"
      using A4 calculation by blast
qed


lemma distributive_lattice_dualization:
  "\<lbrakk>distributive_lattice R X; antisym R X; refl R X; trans R X\<rbrakk> \<Longrightarrow> (\<And>R X. \<lbrakk>distributive_lattice R X; antisym R X; refl R X; trans R X\<rbrakk> \<Longrightarrow> P R X) \<Longrightarrow> P (converse R) X "
  proof-
    assume A0:"distributive_lattice R X" and A1:"antisym R X" and A2:"refl R X" and A3:"trans R X" and A4:"(\<And>R X. \<lbrakk>distributive_lattice R X; antisym R X; refl R X; trans R X\<rbrakk> \<Longrightarrow> P R X)"
    have B0:"is_lattice R X"  by (simp add: A0 distr_latticeD5)
    then have B1:"is_lattice (converse R) X"    by (simp add: A1 A2 A3 lattice_dualization)
    also have B2:"distributive_lattice (converse R) X"  by (smt (verit, best) A0 A1 A2 A3 Sup_def calculation converse_converse distr_latticeD3 distributive_lattice_def)
    obtain B3:"antisym (converse R) X" and B4:"refl (converse R) X" and B5:"trans (converse R) X"
      by (meson A1 A2 A3 antisym_on_converse converseI refl_def trans_on_converse)
    then show "P (converse R) X"
      using A4 B2 by blast
qed

lemma fin_irr_dualization:
  "\<lbrakk>fin_inf_irr R X x; antisym R X; trans R X; refl R X\<rbrakk> \<Longrightarrow> (\<And>R X x. \<lbrakk>fin_sup_irr R X x; antisym R X; trans R X; refl R X\<rbrakk> \<Longrightarrow> P R) \<Longrightarrow> P (converse R) "
  by (simp add: refl_def)



lemma elem_inf_primeI3:
  assumes A0:"distributive_lattice R X" and A1:"x \<in> X" and A2: "fin_inf_irr R X x" and A3:"antisym R X" and
          A4:"trans R X" and A5:"refl R X"
  shows "elem_inf_prime R X x"  
  using elem_sup_primeI3
  by (metis A0 A1 A2 A3 A4 A5 antisym_on_converse distributive_lattice_dualization trans_on_converse)
lemma sup_prime_iff:
  "\<lbrakk>distributive_lattice R X; antisym R X; refl R X; trans R X; x \<in> X\<rbrakk> \<Longrightarrow> (elem_sup_prime R X x \<longleftrightarrow> fin_sup_irr R X x)"
  using elem_sup_primeI3 fin_sup_irrE1 by auto
lemma inf_prime_iff:
  "\<lbrakk>distributive_lattice R X; antisym R X; refl R X; trans R X; x \<in> X\<rbrakk> \<Longrightarrow> (elem_inf_prime R X x \<longleftrightarrow> fin_inf_irr R X x)"
  using elem_inf_primeI3 fin_inf_irrE1 by auto


lemma fin_sup_irrI2:
  "\<lbrakk>distributive_lattice R X; antisym R X; refl R X; trans R X;x \<in> X;  sup_prime R X (lorc R X x)\<rbrakk> \<Longrightarrow> fin_sup_irr R X x"
  by (simp add: distributive_lattice_def elem_sup_primeI2 fin_sup_irrE1 lattD42)
  
lemma fin_inf_irrI2:
  "\<lbrakk>distributive_lattice R X; x \<in> X;  antisym R X; refl R X; trans R X;inf_prime R X (lorc (converse R) X x)\<rbrakk> \<Longrightarrow> fin_inf_irr R X x"
  by (simp add: distributive_lattice_dualization fin_sup_irrI2)

lemma sup_primeI4:
  "\<lbrakk>distributive_lattice R X; x \<in> X;  antisym R X; refl R X; trans R X;fin_sup_irr R X x\<rbrakk> \<Longrightarrow> sup_prime R X (lorc R X x)"
  by (simp add: elem_sup_primeE1 elem_sup_primeI3)

  lemma inf_primeI4:
  "\<lbrakk>distributive_lattice R X; x \<in> X;  antisym R X; refl R X; trans R X;fin_inf_irr R X x\<rbrakk> \<Longrightarrow> inf_prime R X (lorc (converse R) X x)"
  by (simp add: elem_inf_primeE1 elem_inf_primeI3)

lemma sup_prime_pfilterD1:
  "\<lbrakk>sup_prime R X A; is_pfilter R X A; antisym R X; refl R X; trans R X\<rbrakk> \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> X; b \<in> X;  (Sup R X {a, b}) \<in> A\<rbrakk> \<Longrightarrow> (a \<in> A \<or> b \<in> A))"
  by (simp add: sup_prime_def)

lemma sup_prime_pfilterD2:
  "\<lbrakk>is_lattice R X;  antisym R X; refl R X; trans R X;sup_prime R X A; is_pfilter R X A\<rbrakk> \<Longrightarrow> (\<And>a b.  \<lbrakk>a \<in> X; b \<in> X; (a \<in> A \<or> b \<in> A)\<rbrakk> \<Longrightarrow> (Sup R X {a, b}) \<in> A)"
  using filter_on_lattice_sup01 is_pfilterD1 lattice_filter_memI  by metis 
lemma sup_prime_pfilterD3:
  "\<lbrakk>is_lattice R X;  antisym R X; refl R X; trans R X;sup_prime R X F; is_pfilter R X F\<rbrakk> \<Longrightarrow> (\<And>F1 F2. \<lbrakk>is_filter R X  F1; is_filter R X  F2; \<not>(F1 \<subseteq> F); \<not>(F2 \<subseteq> F)\<rbrakk> \<Longrightarrow> \<not>(F1 \<inter> F2 \<subseteq> F))"
  by(auto simp add:sup_prime_def,meson filterD21 filters_on_lattice_inf02 in_mono)

lemma sup_prime_pfilterD4:
  "\<lbrakk>is_lattice R X;  antisym R X; refl R X; trans R X;sup_prime R X F; is_pfilter R X F; is_filter R X  F1; is_filter R X  F2; F1 \<inter> F2 \<subseteq> F\<rbrakk> \<Longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F"
  using sup_prime_pfilterD3 by blast

lemma lorc_sup_filter_subset:
  "\<lbrakk>is_lattice R X;  antisym R X; refl R X; trans R X; (\<And>F1 F2. \<lbrakk> is_filter R X  F1; is_filter R X  F2; F1 \<inter> F2 \<subseteq> F\<rbrakk> \<Longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F); is_filter R X F\<rbrakk> \<Longrightarrow>(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; (Sup R X {a, b}) \<in> F\<rbrakk>\<Longrightarrow> (a \<in> F \<or> b \<in> F))"
proof-
  assume A0:"is_lattice R X" and A1:"antisym R X"  and
         A2:"refl R X" and
         A3:"trans R X"and
         A4:"(\<And>F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2; F1 \<inter> F2 \<subseteq> F\<rbrakk> \<Longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F)" and
         A5:"is_filter R X F" 
  show "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; (Sup R X {a, b}) \<in> F\<rbrakk>\<Longrightarrow> (a \<in> F \<or> b \<in> F))"
  proof-
    fix a b assume A6:"a \<in> X" and A7:"b \<in> X" and A8:"(Sup R X {a, b}) \<in> F" 
    let ?F1="(lorc R X a)" let ?F2="(lorc R X b)"
    have B1:"?F1 \<inter> ?F2 \<subseteq> F" 
    proof
      fix x assume A9: "x \<in> ?F1 \<inter> ?F2"
      then obtain B10:"(a, x) \<in> R" and B11:"(b, x) \<in> R" by (simp add:lorc_mem_iff1)
      then obtain B11:"(Sup R X {a, b}, x) \<in> R"  by (metis A0 A1 A2 A3 A6 A7 A9 IntD1 leq_sup lorcD11) 
      then show "x \<in> F" using A5 A8 A9 filter_memI lorc_mem_iff2 by fastforce
    qed
    obtain B2:"is_filter R X  ?F1" and B3:"is_filter R X ?F2"     by (simp add: A1 A2 A3 A6 A7 lorc_filter)
    then obtain B4:"?F1 \<subseteq> F \<or> ?F2 \<subseteq> F"   by (simp add: A4 B1)
    then show "(a \<in> F \<or> b \<in> F)"  by (meson A2 A6 A7 in_mono lorc_memI1)
  qed
qed


lemma sup_prime_pfilterI2:
  "\<lbrakk>is_lattice R X;   antisym R X; refl R X; trans R X; (\<And>F1 F2. \<lbrakk> is_filter R X  F1; is_filter R X  F2; F1 \<inter> F2 \<subseteq> F\<rbrakk> \<Longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F); is_pfilter R X F\<rbrakk> \<Longrightarrow> sup_prime R X F"
  by (simp add: is_pfilterD1 lorc_sup_filter_subset sup_primeI1)

lemma not_prime_obtain:
  assumes A0:"is_lattice R X" and A1:"is_pfilter R X F" and A2:"\<not>(sup_prime R X F)" and A3:"antisym R X" and
          A4:"refl R X" and A5:"trans R X"
  obtains x y where "x \<in> X \<and> y \<in> X \<and> Sup R X {x, y} \<in> F \<and> x \<notin> F \<and> y \<notin> F"
  using A2 sup_prime_def by blast

lemma primefilterD1:
  "\<lbrakk>sup_prime R X A; is_pfilter R X A\<rbrakk> \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> X; b \<in> X;  (Sup R X {a, b}) \<in> A\<rbrakk> \<Longrightarrow> (a \<in> A \<or> b \<in> A))"
  by (simp add: sup_prime_def)

lemma element_filter:
  assumes A0:"is_lattice R X" and A1:"is_filter R X F" and A2:"a \<in> X" and A3:"refl R X" and
          A4:"trans R X" and A5:"antisym R X"    
  defines "G \<equiv> {x \<in> X. \<exists>y \<in> F. (Inf R X {a, y}, x)\<in>R}"
  shows "is_filter R X G"
proof-
  have B0:"G \<subseteq> X" by (simp add: G_def)
  have B1:"\<And>x1 x2. \<lbrakk>x1 \<in> G; x2 \<in> G\<rbrakk> \<Longrightarrow> Inf R X {x1, x2} \<in> G"
  proof-
    fix x1 x2 assume A6:"x1 \<in> G" and A7:"x2 \<in> G" 
    obtain B30:"x1 \<in> X" and B31:"x2 \<in> X"   using A6 A7 B0 by blast
    obtain y1 y2 where B20:"y1 \<in> F" and B21:"(Inf R X {a, y1}, x1)\<in>R" and
                       B22:"y2 \<in> F" and B23:"(Inf R X {a, y2}, x2)\<in>R"  using A6 A7 G_def by blast
    obtain B32:"y1 \<in> X" and B33:"y2 \<in> X"      by (metis A1 B20 B22 filterD21)
    have B3:"Inf R X {y1, y2} \<in> F"  by (meson A0 A1 A5 B20 B22 B32 B33 filter_finf_closed lattD31)
    obtain B34:"Inf R X {x1, x2} \<in> X" and B35:"Inf R X {a, y1} \<in> X" and B36:"Inf R X {a, y2} \<in> X"   using A2 B30 B31 B32 B33 A0   by (simp add: A5 filter_finf_closed1 filters_max0 latt_iff)
    have B4:"(Inf R X {Inf R X {a, y1}, Inf R X {a, y2}},Inf R X {x1, x2})\<in>R"
      using B34 B35 B36 B21 B23 A0  by (meson A5 B30 B31 assms(5) converseD converseI lattD31 sup_ge5 trans_on_converse)
    have B5:"Inf R X {Inf R X {a, y1}, Inf R X {a, y2}}  = Inf R X {a, Inf R X {y1, y2}}"
     using inf_semilattice_finf_props5[of R X a y1 y2] A0 B30 lattD41[of R X]  using A2 A3 A4 A5 B32 B33 by fastforce
    have B6:"(Inf R X {Inf R X {y1, y2}, a},Inf R X {x1, x2})\<in>R"
      by (metis B4 B5 insert_commute)
    have B7:"\<exists>y \<in> F. (Inf R X {a, y},Inf R X {x1, x2})\<in>R"
      using B3 B4 B5 by auto
    show "Inf R X {x1, x2} \<in> G"
      using B34 B7 G_def by blast
  qed
  have B6:"\<And>x g. \<lbrakk>g \<in> G; x \<in> X; (g, x)\<in>R\<rbrakk> \<Longrightarrow> x \<in> G"
  proof-
     fix x g assume A8:"g \<in> G" and A9:"x \<in> X" and A10:"(g,x)\<in>R"
     obtain y where B60:"y \<in> F" and B61:"(Inf R X {a, y}, g)\<in>R"  using A8 G_def by blast 
     also obtain B61:"g \<in> X"  and B62:"Inf R X {a, y} \<in> X"  by (meson A0 A1 A2 A5 A8 B0 B60 filterD21 in_mono is_supE1 lattD31) 
     then have B60:"(Inf R X {a, y}, x) \<in> R" using B61 B62 A4 A9  by (simp add: A10 calculation(2) trans_onD)
     then show "x \<in> G"
       using A9 G_def calculation(1) by blast
  qed
  
  have B7:"G \<noteq> {}"
  proof-
    obtain f where B70:"f \<in> F"  using A1 filter_ex_elem by blast
    have B71:"(Inf R X {a, f}, a) \<in>R"
      by (meson A0 A1 A2 A5 B70 converseD filterD21 insertI1 is_supD1121 lattD31)
    then have "a \<in> G"
      using A2 B70 G_def by blast
    then show ?thesis by auto
  qed
  have B8:"\<And>a b. \<lbrakk>a \<in> G; b \<in> G\<rbrakk> \<Longrightarrow>  (\<exists>c\<in>G. (c,a)\<in>R \<and> (c,b)\<in>R)"
  proof-
    fix a b assume A4:" a \<in> G" and A5:"b \<in>G"
    obtain B90:"Inf R X {a,b}\<in>G" and B91:"(Inf R X {a,b}, a)\<in>R" and B92:"(Inf R X {a,b}, b)\<in>R"
      by (meson A0 A3 A4 A5 B0 B1 assms(5) assms(6) lattD5 latt_ge_iff2 lattice_absorb1 lattice_absorb14 reflD1 subsetD)
    show "\<exists>c\<in>G. (c,a)\<in>R \<and> (c,b)\<in>R"
      using B90 B91 B92 by blast
  qed
  have B10:"is_dir G (converse R)"
    by (simp add: B8 is_dirI1)
  have B11:"is_ord_cl X F R"
    by (simp add: A1 filterD4)
  show ?thesis
    by (simp add: B0 B10 B6 B7 filterI1 is_ord_clI1)
qed  

lemma primefilterI1:
  "\<lbrakk>is_lattice R X; refl R X; trans R X; antisym R X; is_pfilter R X A; (\<forall>a b. (a \<in> A \<or> b \<in> A) \<longleftrightarrow> ((Sup R X {a, b}) \<in> A)) \<rbrakk> \<Longrightarrow> sup_prime R X A"
  by (simp add: sup_prime_def)

lemma primefilter_iff1:
  "\<lbrakk>is_lattice R X; refl R X; trans R X; antisym R X\<rbrakk> \<Longrightarrow>
   ( sup_prime R X A \<and> is_pfilter R X A) \<longleftrightarrow> (is_pfilter R X A \<and>  (\<forall>a \<in> X. \<forall>b \<in> X. (a \<in> A \<or> b \<in> A) \<longleftrightarrow> ((Sup R X {a, b}) \<in> A)))"
  by (metis sup_primeD1 sup_primeI1 sup_prime_pfilterD2)

lemma prime_filter_iff2:
  "\<lbrakk>is_lattice R X; refl R X; trans R X; antisym R X\<rbrakk> \<Longrightarrow>
    (sup_prime R X F \<and> is_pfilter R X F)  \<longleftrightarrow>  (is_pfilter R X F \<and> (\<forall>F1 F2. is_filter R X  F1 \<and> is_filter R X  F2 \<and> F1 \<inter> F2 \<subseteq> F \<longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F))"
  by (metis sup_prime_pfilterD3 sup_prime_pfilterI2)
lemma prime_filter_fin_irr1:
  "\<lbrakk>is_lattice R X; refl R X; trans R X; antisym R X; sup_prime R X F; is_pfilter R X F; G \<in> filters_on R X; H \<in> filters_on R X; G \<inter> H = F\<rbrakk> \<Longrightarrow> G=F \<or> H=F"
  by (meson filters_on_iff inf_le1 inf_le2 order_refl subset_antisym sup_prime_pfilterD4)
lemma prime_filter_fin_irr2:
  "\<lbrakk>is_lattice R X; sup_prime R X F; refl R X; trans R X; antisym R X; is_pfilter R X F; G \<in> filters_on R X; H \<in> filters_on R X; Inf (pwr X) (filters_on R X) {G, H} = F\<rbrakk> \<Longrightarrow> G=F \<or> H=F"
  by (simp add: filters_lattice_inf_op prime_filter_fin_irr1)

lemma prime_filter_irr3:
  "\<lbrakk>is_lattice R X; sup_prime R X F;refl R X; trans R X; antisym R X; is_pfilter R X F\<rbrakk> \<Longrightarrow> fin_inf_irr (pwr X) (filters_on R X) F"
  by (metis fin_sup_irr_def prime_filter_fin_irr2 Sup_def)


lemma proper_principal_prime:
  "\<lbrakk>is_pfilter R X (lorc R X a); (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; (a, Sup R X {x, y})\<in>R\<rbrakk> \<Longrightarrow> (a, x) \<in> R \<or> (a,y)\<in>R)\<rbrakk> \<Longrightarrow> sup_prime R X (lorc R X a)"
  by (metis lorcD12 lorcI1 sup_prime_def)

lemma proper_principal_prime2:
  "\<lbrakk>is_lattice R X; refl R X; trans R X; antisym R X;is_pfilter R X (lorc R X a); (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; (a, Sup R X {x, y})\<in>R\<rbrakk> \<Longrightarrow> (a, x) \<in> R \<or> (a,y)\<in>R)\<rbrakk> \<Longrightarrow> (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; a = Sup R X {x, y}\<rbrakk> \<Longrightarrow> a =x \<or> a=y)"
  by (metis ge_sup1 ge_sup2 ge_sup_iff lattD32 lattD42 refl_def ssupD4)

lemma proper_principal_fin_irr:
  "\<lbrakk>is_lattice R X; refl R X; trans R X; antisym R X;is_pfilter R X (lorc R X a); (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; (a, Sup R X {x, y})\<in>R\<rbrakk> \<Longrightarrow> (a, x) \<in> R \<or> (a,y)\<in>R)\<rbrakk> \<Longrightarrow>fin_inf_irr (pwr X) (filters_on R X) (lorc R X a)"
  by (simp add: prime_filter_irr3 proper_principal_prime)

lemma fin_irr_filter_prime:
  "\<lbrakk>distributive_lattice R X;is_pfilter R X F;refl R X; trans R X; antisym R X; fin_inf_irr (pwr X) (filters_on R X) F\<rbrakk> \<Longrightarrow> inf_prime R X F"
  by (metis distr_latticeD5 filter_on_lattice_sup01 inf_primeI1 is_pfilterD1 lattice_absorb1 reflD1)

lemma distr_lattice_maximal_prime:
  assumes A0:"distributive_lattice R X" and A1:"refl R X" and A2:"trans R X" and A3:"antisym R X" and
          A4:"is_maximal (pwr X) (pfilters_on R X) F"
  shows "sup_prime R X F"
proof-
  have B00:"is_lattice R X"   using A0 distributive_lattice_def by blast
  have B0:"is_pfilter R X F"   by (meson A4 maximalD1 pfilters_memD0) 
  have P:"\<And>a b. \<lbrakk>a \<in> X;b \<in> X; Sup R X {a, b} \<in> F;  a \<notin> F\<rbrakk> \<Longrightarrow> b \<in> F"
  proof-
    fix a b assume B0A0:"a \<in> X" and B0A1:"b \<in> X" and B0A2:"Sup R X {a,b}\<in>F" and B0A3:"a \<notin>F"
    let ?sab="Sup R X {a,b}"
    let ?Fa="binary_filter_sup R X F (lorc R X a)"
    have B1:"a \<in> ?Fa - F"   by (simp add: A1 A2 A3 B0 B00 B0A0 B0A3 filters_on_lattice_bsup02 is_pfilterD1 lorc_filter lorc_memI1)
    then have B2:"F \<subset> ?Fa"   by (metis A1 A2 A3 B0 B00 B0A0 B0A3 DiffD1 filters_on_lattice_bsup03 is_pfilterD1 lorc_filter order_less_le)
    have B3:"?Fa \<notin> pfilters_on R X" using A4 B2 maximal_pfiltersD1 by blast
    have B4:"?Fa \<in> filters_on R X"   by (simp add: A1 A2 A3 B0 B00 B0A0 filters_on_lattice_bsup4 is_pfilterD1 lorc_filter)
    have B5:"?Fa = X" by (metis B3 B4 filters_on_iff is_pfilter_def pfilters_memI)
    have B6:"b \<in> ?Fa"  by (simp add: B0A1 B5)
    obtain f c where B70:"f \<in>F" and B71:"c \<in> (lorc R X a)" and B72:"(Inf R X {f, c}, b)\<in>R" by (meson A1 A2 A3 B6 binary_filter_sup_obtains)
    let ?ifc="Inf R X {f, c}" let ?sbf="Sup R X {b,f}" let ?sbc="Sup R X {b,c}"
    obtain B73:"f \<in> X" and B74:"c \<in> X"     by (metis B2 B5 B70 B71 lorc_mem_iff2 psubsetD) 
    obtain B75:"?ifc \<in> X" and B76:"Sup R X {b, f} \<in> X" and B77:"Sup R X {b, c} \<in> X"
      by (meson A3 B00 B0A1 B73 B74 is_supE1 lattD31 lattD42 ssupD4)
    have B8:"b = Sup R X {b, ?ifc}"
      by (metis A1 A3 B00 B0A1 B72 B73 B74 ge_sup2 is_supE1 lattD31 reflD1)
    have B9:"... = Inf R X {?sbf, ?sbc}"
      by (simp add: A0 B0A1 B73 B74 distr_latticeD1)
    let ?i_sbf_sbc="Inf R X {Sup R X {b, f}, Sup R X {b, c}}" let ?sba="Sup R X {b, a}"
    have B90:"?i_sbf_sbc \<in> X"  using B0A1 B8 B9 by auto
    have B10:"?sbf \<in> F \<and> ?sbc \<in> (lorc R X a) \<and> b = ?i_sbf_sbc"  by (metis A1 A2 A3 B0 B00 B0A0 B0A1 B70 B71 B8 B9 filter_on_lattice_sup01 lorc_filter pfilter_on_lattice_sup01)
    have B11:"(a, ?sbc) \<in> R"
      by (meson B10 lorcD12)
    have B110:"b \<in> X \<and> ?sbf \<in> X \<and> ?sbc \<in> X \<and> c \<in> X \<and> a \<in> X"
      by (simp add: B0A0 B0A1 B74 B76 B77)
    let ?s_b_sbf=" Sup R X {b, ?sbf}" let ?s_b_sbc="Sup R X {b, ?sbc}"
    obtain D0:"?s_b_sbf \<in> X" and D1:"?s_b_sbc \<in> X" and B2:"?sba \<in> X"
      by (simp add: A3 B00 B110 lattD42 ssupD4)
    have B111:"(?sbf, ?s_b_sbf)\<in>R"
      by (meson A3 B00 B110 binary_supD32 is_supE1 lattD32)
    have B112:"(?sba,?s_b_sbc) \<in>R"
      by (metis A1 A2 A3 B00 B11 B110 binary_supD31 ge_sup1 lattD32 leq_sup refl_def)
    have B12:"b = Sup R X {b, Inf R X {?sbf, ?sbc}}"
      by (metis A1 A3 B0A1 B8 B9 bsup_idem1 reflD1)
    have B13:"... = Inf R X {?s_b_sbf, ?s_b_sbc}"
      by (simp add: A0 B0A1 B76 B77 distr_latticeD1)
    have B14:"(Inf R X {?sbf, ?sba}, Inf R X {?s_b_sbf, ?s_b_sbc}) \<in>R"
      by (meson A2 A3 B00 B111 B112 B2 B76 D0 D1 converseD converseI lattD31 sup_ge5 trans_on_converse)    
    have B15:"Inf R X {?sbf, ?sba} \<in> F"
      by (metis A3 B0 B00 B0A2 B10 \<open>\<And>thesis::bool. (\<lbrakk>(f::'a::type) \<in> (X::'a::type set); (c::'a::type) \<in> X\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> doubleton_eq_iff emptyE filter_finf_closed1 is_pfilterD1 lattD31)
    have B16:"(Inf R X {?sbf, ?sba}, b)\<in>R"
      using B12 B13 B14 by presburger
    show "b \<in> F"
      by (meson B0 B110 B15 B16 filter_memI is_pfilterD1)
  qed
  show ?thesis
    by (meson P sup_primeI1)
qed


lemma sinfD4:
  "\<lbrakk>refl R X; antisym R X; trans R X; is_inf_semilattice R X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> (Inf R X {a, b}) \<in> X"
  by (simp add: filter_finf_closed1 filters_max0)

lemma tmp0:
  "\<lbrakk>refl R X; antisym R X; trans R X;a1 \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>{Inf R X {b, a}|a. a \<in> {a1}} = {Inf R X {b, a1}}"
   by auto
lemma tmp1:
  "\<lbrakk>refl R X; antisym R X; trans R X;a1 \<in> X; a2 \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>{Inf R X {b, a}|a. a \<in> {a1, a2}} = {Inf R X {b, a1}, Inf R X {b, a2}}" 
  by auto
lemma tmp2:
  "\<lbrakk>refl R X; antisym R X; trans R X;A \<subseteq> X; finite A; A \<noteq> {}; b \<in> X\<rbrakk> \<Longrightarrow>{Inf R X {b, a}|a. a \<in>A} = (\<lambda>a. Inf R X {b, a})`A" 
  by auto
lemma tmp3:"\<lbrakk>refl R X; antisym R X; trans R X;a1 \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>{Sup R X {b, a}|a. a \<in> {a1}} = {Sup R X {b, a1}}" by auto
lemma tmp4:"\<lbrakk>refl R X; antisym R X; trans R X;a1 \<in> X; a2 \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>{Sup  R X {b, a}|a. a \<in> {a1, a2}} = {Sup R X {b, a1}, Sup R X {b, a2}}" by auto
lemma tmp5:"\<lbrakk>refl R X; antisym R X; trans R X;A \<subseteq> X; finite A; A \<noteq> {}; b \<in> X\<rbrakk> \<Longrightarrow>{Sup R X {b, a}|a. a \<in>A} = (\<lambda>a. Sup R X {b, a})`A" by auto


lemma distr_eq_tmp0:"\<lbrakk>refl R X; antisym R X; trans R X;is_lattice R X; a1 \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> Inf R X {b, (Sup R X {a1})} = Sup R X {Inf R X {b, a}|a. a \<in> {a1}}" 
  proof-
    fix a1 b assume C0:"refl R X" and C1:"antisym R X" and C2:"trans R X" and A0:"is_lattice R X" and A1:"a1 \<in> X" and A2:"b \<in>X"
    have B0:"Sup R X {a1} = a1" using  C1 C2 C0 A1  refl_def sup_singleton2 by metis 
    also have B1:"{Inf R X {b, a}|a. a \<in> {a1}} = {Inf R X {b, a1}}"   by auto
    then show "Inf R X {b, (Sup R X {a1})} = Sup R X {Inf R X {b, a}|a. a \<in> {a1}}"  by (metis (no_types, lifting) A0 A1 A2 C1 is_supE1 lattD31 C0 reflD1 sup_singleton2)
qed


lemma distr_eq_tmp1:"\<lbrakk>refl R X; antisym R X; trans R X;distributive_lattice R X; a1 \<in> X; a2 \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> Inf R X {b, Sup R X {a1, a2}} = Sup R X {Inf R X {b, a}|a. a \<in> {a1, a2}}" using distr_latticeD3 tmp1
  proof-
    fix a1 a2 b assume C0:"refl R X" and C1:"antisym R X" and C2:"trans R X" and 
                        A0:"distributive_lattice R X" and A1:"a1 \<in> X" and A2:"a2 \<in>X" and "b \<in> X"
    obtain B0:"is_lattice R X" and B1:"Sup R X {a1, a2} \<in> X" and B2:"Inf R X {b, a1} \<in> X" and B3:"Inf R X {b, a2}\<in>X"
      by (meson A0 A1 A2 \<open>(b::'a::type) \<in> (X::'a::type set)\<close> C1 distr_latticeD5 is_supE1 lattD31 lattD4 ssupD4)
    obtain B1:"{Inf R X {b, a}|a. a \<in> {a1, a2}} = {Inf R X {b, a1}, Inf R X {b, a2}}" by blast
    then show "Inf R X {b, Sup R X {a1, a2}} = Sup R X {Inf R X {b, a}|a. a \<in> {a1, a2}}"
      by (simp add: A0 A1 A2 \<open>(b::'a::type) \<in> (X::'a::type set)\<close> C1 distr_latticeD3 C0 C2)
qed


lemma distr_eq_tmp2:"\<lbrakk>refl R X; antisym R X; trans R X;is_lattice R X; a1 \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> Sup R X{b, (Inf R X {a1})} = Inf R X {Sup R X {b, a}|a. a \<in> {a1}}"
proof-
    fix a1 b assume C0:"refl R X" and C1:"antisym R X" and C2:"trans R X" and 
                     A0:"is_lattice R X" and A1:"a1 \<in> X" and A2:"b \<in>X"
    have B0:"Inf R X {a1} = a1" using  C1 C2 A1 by (metis Sup_def antisym_on_converse converseI C0 reflE1 sup_singleton2) 
    also have B1:"{Sup R X {b, a}|a. a \<in> {a1}} = {Sup R X {b, a1}}"    by auto
    then show "Sup R X {b, (Inf R X {a1})} = Inf R X {Sup R X {b, a}|a. a \<in> {a1}}"    by (metis (no_types, lifting) A0 A1 A2 C1 bsup_commute2 calculation insert_absorb2 lattD32 lattD42 lattice_absorb2 C0 refl_def ssupD4 sup_equality sup_idem2 C2)
qed

lemma distr_eq_tmp3:"\<lbrakk>refl R X; antisym R X; trans R X;distributive_lattice R X; a1 \<in> X; a2 \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> 
      Sup R X {b, (Inf R X {a1, a2})} = Inf R X {Sup R X {b, a}|a. a \<in> {a1, a2}}" 
      using distr_latticeD1 tmp4 by fastforce

lemma l_sup_closed:
  "\<lbrakk>refl R X; antisym R X; trans R X;is_lattice R X;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Sup R X {x, y} \<in> X" 
  by (simp add: lattD42 ssupD4) 

lemma l_inf_closed:
  "\<lbrakk>refl R X; antisym R X; trans R X;is_lattice R X;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Inf R X {x, y} \<in> X" by (simp add: lattD41 sinfD4)

lemma l_finsup:
  "\<lbrakk>refl R X; antisym R X; trans R X;is_lattice R X; A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>s. is_sup R X A s" 
  using  bsup_finite2 lattD42 by blast

lemma l_fininf:
  "\<lbrakk>refl R X; antisym R X; trans R X;is_lattice R X; A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>s. is_inf R X A s" 
   by (simp add: l_finsup  lattice_dualization) 

lemma s_finsup:
  "\<lbrakk>refl R X; antisym R X; trans R X;is_sup_semilattice R X; A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>s. is_sup R X A s"
  by (meson fpow_ne_iff2 sup_semilattice_fsup) 
 
lemma s_fininf:"\<lbrakk>refl R X; antisym R X; trans R X;is_inf_semilattice R X; A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>s. is_inf R X A s" 
   by (metis antisym_on_converse is_supE1 sup_finite trans_on_converse) 



lemma sup_insert9: 
  "\<lbrakk>trans R Y;A \<subseteq> Y;is_sup R Y A s1; is_sup R Y {s1, x} s2\<rbrakk> \<Longrightarrow>  s2 \<in> (ubd R Y (insert x A))"
   by (simp add: is_supD1121 sup_insert62 ubd_mem_insert)
lemma inf_insert9:
   "\<lbrakk>trans R Y;A \<subseteq> Y;is_inf R Y A s1; is_inf R Y {s1, x} s2\<rbrakk> \<Longrightarrow>  s2 \<in> (lbd R Y (insert x A))" 
   by (simp add: sup_insert9) 


lemma sup_ubd: 
  "\<lbrakk>trans R Y; F \<subseteq> Y;is_sup R Y F s; is_sup R Y {x, s} t\<rbrakk> \<Longrightarrow> is_sup R Y (insert x F) t"
   by (meson bsup_commute is_supI5 sup_insert7 sup_insert9) 

lemma inf_lbd: 
  "\<lbrakk>trans R Y; F \<subseteq> Y;is_inf R Y F s; is_inf R Y {x, s} t\<rbrakk> \<Longrightarrow> is_inf R Y (insert x F) t" 
   by (simp add: sup_ubd) 
lemma sup_ex:
  "\<lbrakk>antisym R X; refl R X; trans R Y;is_lattice R X;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> is_sup R X {x, y} (Sup R X {x, y})"
   by (simp add: lattD32)
lemma ssup_ex:
  "\<lbrakk>antisym R X; refl R X; trans R Y;is_sup_semilattice R X;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> is_sup R X {x, y} (Sup R X {x, y})"
   by (simp add: ssupD3)


lemma fsup_insert:
  "\<lbrakk>antisym R X; refl R X; trans R X; is_lattice R X; finite F; F \<subseteq> X; F \<noteq> {}; x \<in> X\<rbrakk> \<Longrightarrow> Sup R X {x, (Sup R X F)} = Sup R X (insert x F)"
  by (smt (verit, best) bsup_finite2 finite.intros(2) insert_not_empty insert_subset is_supE1 is_sup_unique lattD42 ssupD3 sup_ubd)  
lemma finf_insert:
  "\<lbrakk>antisym R X; refl R X; trans R X; is_lattice R X; finite F; F \<subseteq> X; F \<noteq> {}; x \<in> X\<rbrakk> \<Longrightarrow> Inf R X {x, (Inf R X F)} = Inf R X (insert x F)"
  by (metis Sup_def antisym_on_converse fsup_insert lattice_dualization trans_on_converse) 

lemma distr_finite2:
  assumes A0:"b \<in> X" and
          A1: "\<And>a1 a2. \<lbrakk>a1 \<in> X; a2 \<in> X\<rbrakk> \<Longrightarrow> Inf R X {b, (Sup R X {a1, a2})} = Sup R X {Inf R X {b, a}|a. a \<in> {a1, a2}}" and 
          A2:"finite A" and
          A3:"A \<noteq> {}" and
          A4:"A \<subseteq> X" and
          A5:"distributive_lattice R X" and 
          A6:"refl R X" and
          A7:"trans R X" and
          A8:"antisym R X"          
  shows "Inf R X {b, (Sup R X A)} = Sup R X {Inf R X {b, a}|a. a \<in> A}"
  using A2 A3 A4 A1 A0
proof (induct A rule: finite_ne_induct)
  case (singleton x) then show ?case using A5 by fastforce 
next
  case (insert x F)
  obtain P0:"x \<in> X" and P1:"F \<subseteq> X" and P2:"finite F" and P3:"F \<noteq> {}"
    using insert.hyps(1,2) insert.prems(1) by blast
  have L:"is_lattice R X"  by (simp add: A5 distr_latticeD5) 
  let ?ba="{Inf R X {b, a} |a::'a. a \<in> F}" and ?xba="{Inf R X {b, a}|a. a \<in> (insert x F)}"
  let ?s="Sup R X F" and ?sba="Sup R X ?ba" and ?sxba="Sup R X ?xba"
  have P4:"?ba \<subseteq> X" using L A0 P1 l_inf_closed A6 A7 A8 by (smt (verit, ccfv_threshold) mem_Collect_eq subset_iff)
  have P5:"?xba \<subseteq> X" using L A0 P0 P1 l_inf_closed A6 A7 A8  by (smt (verit, ccfv_threshold) insert.prems(1) mem_Collect_eq subset_iff) 
  have P6:"finite ?ba" using P2 by force
  have P7:"finite ?xba"  by (simp add: insert.hyps(1))
  have P8:"?xba = {Inf R X {b, x}} \<union> ?ba" by (auto)
  have P9:"Inf R X {b, x} \<in> X"   by (simp add: A0 A6 A7 A8 L P0 l_inf_closed)
  have P10:"?ba \<noteq> {}"  using P3 by blast
  have P11:"?xba \<noteq> {}" using P3 by blast
  have P12:"?sba \<in> X" using L P10 P4 P6 bsup_finite2 is_supE1 latt_iff  by (metis (mono_tags, lifting) A7 A8) 
  have P13:"?sxba \<in> X" using L P11 P5 P7 bsup_finite2 is_supE1 latt_iff   by (metis (no_types, lifting) A7 A8) 
  have P14:"(Sup R X {?sba, (Inf R X {b, x})}) \<in> X" using  P12 P9  L l_sup_closed using A6 A7 A8 by fastforce 
  have B0:"Inf R X {b, ?s} = ?sba"  using A0 A1 insert.hyps(4) insert.prems(1) by blast
  have B1:"Inf R X {b, (Sup R X {?s, x})} = Sup R X {(Inf R X {b, ?s}), (Inf R X {b, x})}"  by (meson A0 A5 A6 A7 A8 L P0 P1 P2 P3 bsup_finite2 distr_latticeD3 is_supE1 lattD42) 
  have B2:"... = Sup R X {(?sba), (Inf R X {b, x})}"  using B0 by fastforce
  have B3:"... = Sup R X {Inf R X {b, a}|a. a \<in> (insert x F)}" 
  proof-
    have B4:"?ba \<subseteq> ?xba" by blast
    have B5:"is_sup R X ?ba ?sba"  using A7 A8 L P10 P4 P6 bsup_finite2 lattD42 by blast 
    have B6:"is_sup R X {Inf R X {b, x},?sba} (Sup R X {(Inf R X {b, x}), (?sba)} )"  by (simp add: A8 L P12 P9 lattD32) 
    have B7:"is_sup R X {Inf R X {b, x},?sba} (Sup R X {(?sba), (Inf R X {b, x})})" by (metis B6 insert_commute) 
    have B8:"is_sup R X (insert (Inf R X {b, x}) ?ba) (Sup R X {(?sba), (Inf R X {b, x})})"     using A7 B5 B7 P4 sup_ubd by fastforce 
    have B9:"insert (Inf R X {b, x}) ?ba =  {Inf R X {b, a}|a. a \<in> (insert x F)}"  using B5 B7 sup_ubd by blast
    show "(Sup R X {(?sba), (Inf R X {b, x})}) =  Sup R X {Inf R X {b, a}|a. a \<in> (insert x F)}"   using A8 B8 B9 sup_equality by fastforce
  qed
  have B10:"Inf R X {b, (Sup R X {?s, x})} = Sup R X {Inf R X {b, a}|a. a \<in> (insert x F)}" using B0 B1 B3 by presburger
  have B11:"Inf R X {b, (Sup R X {?s, x})} = Inf R X {b, (Sup R X (insert x F))}"
  proof-
    have B12:"Sup R X {Sup R X F, x} = Sup R X (insert x F)"   by (simp add: A6 A7 A8 L P0 P1 P2 P3 fsup_insert insert_commute)
    show " Inf R X {b, Sup R X {Sup R X F, x}} = Inf R X {b, Sup R X (insert x F)}"  by (simp add: B12)
  qed
  have B13:"Inf R X {b, (Sup R X (insert x F))} =  Sup R X {Inf R X {b, a}|a. a \<in> (insert x F)}" using B10 B11 by presburger
  then show ?case
    by auto
qed


lemma distr_finite1:
  assumes A0:"b \<in> X" and
          A1: "\<And>a1 a2. \<lbrakk>a1 \<in> X; a2 \<in> X\<rbrakk> \<Longrightarrow> Sup R X {b, (Inf R X {a1, a2})} = Inf R X {Sup R X {b, a}|a. a \<in> {a1, a2}}" and 
          A2:"finite A" and
          A3:"A \<noteq> {}" and
          A4:"A \<subseteq> X" and
          A5:"distributive_lattice R X"  and 
          A6:"refl R X" and
          A7:"trans R X" and
          A8:"antisym R X" 
  shows "Sup R X {b, (Inf R X A)} = Inf R X {Sup R X {b, a}|a. a \<in> A}"
proof-
  let ?R="dual R"
  have B0:"distributive_lattice ?R X"    by (simp add: A5 A6 A7 A8 distributive_lattice_dualization)
  obtain B1:"refl ?R X" and B2:"trans ?R X" and B3:"antisym ?R X"  by (simp add: A6 A7 A8 refl_dualI)
  obtain B4: "\<And>a1 a2. \<lbrakk>a1 \<in> X; a2 \<in> X\<rbrakk> \<Longrightarrow> Inf ?R X {b, (Sup ?R X {a1, a2})} = Sup ?R X {Inf ?R X {b, a}|a. a \<in> {a1, a2}}"
  proof -
    assume a1: "(\<And>a1 a2. \<lbrakk>a1 \<in> X; a2 \<in> X\<rbrakk> \<Longrightarrow> Inf (dual R) X {b, Sup (dual R) X {a1, a2}} = Sup (dual R) X {Inf (dual R) X {b, a} |a. a \<in> {a1, a2}}) \<Longrightarrow> thesis"
    have "pord (dual R) X"
      by (metis (no_types) \<open>\<And>thesis::bool. (\<lbrakk>refl (dual (R::('a::type \<times> 'a::type) set)) (X::'a::type set); trans (dual R) X; antisym (dual R) X\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>)
    then show ?thesis
      using a1 A0 B0 distr_eq_tmp1 by fastforce
  qed  
  have B5:"Inf ?R X {b, (Sup ?R X A)} = Sup ?R X {Inf ?R X {b, a}|a. a \<in> A}"
  using B0 B1 B2 B3 B4 A0 A2 A3 A4 distr_finite2[of b X ?R A] by blast
  show "Sup R X {b, (Inf R X A)} = Inf R X {Sup R X {b, a}|a. a \<in> A}"
    by (smt (verit) B5 Collect_cong Sup_def converse_converse)
qed

 
lemma fin_distr2:"\<lbrakk>distributive_lattice R X; trans R X; antisym R X; refl R X; finite A;A \<noteq> {};A \<subseteq> X; b \<in> X\<rbrakk>\<Longrightarrow>Inf R X {b, (Sup R X  A)} = Sup R X {Inf R X {b, a}|a. a \<in> A}"
  using distr_finite2[of b X R A] distr_eq_tmp1  by fastforce
lemma fin_distr1:"\<lbrakk>distributive_lattice R X; trans R X; antisym R X; refl R X;finite A;A \<noteq> {};A \<subseteq> X; b \<in> X\<rbrakk>\<Longrightarrow>Sup R X { b, (Inf R X  A)} = Inf R X {Sup R X {b, a}|a. a \<in> A}" 
   using distr_finite1[of b X R A]  by (simp add: distr_eq_tmp3)

lemma finite_ind_in:
  "\<lbrakk>refl R X; antisym R X; trans R X; is_inf_semilattice R X; finite I; I \<noteq> {}; (\<forall>i. i \<in> I \<longrightarrow> f i \<in> X)\<rbrakk> \<Longrightarrow>is_inf R X (f`I) (Inf R X (f`I))"
  by (metis Sup_def antisym_on_converse bsup_finite2 finite_imageI image_is_empty image_subset_iff is_sup_semilattice_def trans_on_converse)

lemma finite_ind_fil:
  "\<lbrakk>refl R X; antisym R X; trans R X;is_inf_semilattice R X; finite I; I \<noteq> {}; is_greatest R X top; (\<forall>i. i \<in> I \<longrightarrow> is_filter R X  (f i))\<rbrakk> \<Longrightarrow> is_inf (pwr X) (filters_on R X) (f`I) (\<Inter>(f`I))"
  by (simp add: filters_inf_semilattice_inf filters_on_iff image_subsetI pow_neI)

lemma finite_ind_fil_lattice:
   "\<lbrakk>refl R X; antisym R X; trans R X;is_lattice R X; finite I; I \<noteq> {}; is_greatest R X top; (\<forall>i. i \<in> I \<longrightarrow> is_filter R X  (f i))\<rbrakk> \<Longrightarrow> is_inf (pwr X) (filters_on R X) (f`I) (\<Inter>(f`I))"
  by (simp add: finite_ind_fil lattD41)

lemma finite_ind_fil2:
  fixes f::"'b \<Rightarrow> 'a set" and x::"'b \<Rightarrow> 'a" and I::"'b set"
  assumes A0:"is_lattice R X" and
          A1: "is_greatest R X top" and 
          A2:"finite I" and
          A3:"I \<noteq> {}" and
          A4:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X  (f i))" and
          A5:"(\<And>i. i \<in> I \<Longrightarrow> (x i) \<in> (f i))" and
          A6:"is_sup R X (x` I) s" and 
          A7:"refl R X" and 
          A8:"antisym R X" and 
          A9:"trans R X"
  shows "s \<in> (\<Inter>(f` I))"
proof-
  have B0:"\<And>i. i \<in> I \<longrightarrow> s \<in> f i"
    proof
      fix i assume A10:"i \<in> I"
      have B1:"(x i) \<in> (f i)" by (simp add: A5 A10)
      have B2:"(x i) \<in> (x` I)"   by (simp add: A10) 
      have B5:"s \<in> X"    by (meson A6 is_supE1) 
      have B6:"(x i, s)\<in>R" by (meson A6 B2 is_supD1121)  
      show "s \<in> f i"     by (meson A10 A4 B1 B5 B6 filter_memI) 
  qed
  show "s \<in>  (\<Inter>(f` I))"   using B0 by blast
qed

lemma finite_ind_fil3:
  fixes f::"'b \<Rightarrow> 'a set"  and I::"'b set"
  assumes A0:"is_lattice R X" and
          A1:"is_greatest R X top" and 
          A2:"finite I" and 
          A3: "I \<noteq> {}" and
          A4:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X  (f i))" and
          A5: "s \<in> (\<Inter>(f` I))" and
          A6:"refl R X" and 
          A7:"antisym R X" and 
          A8:"trans R X"
  shows "\<exists>(x::'b \<Rightarrow> 'a). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> is_sup R X (x` I) s"
proof-
  define x where "x = (\<lambda>(i::'b). s)"
  have B0:"is_sup R X (x` I) s"
    apply(rule is_supI7)
    apply (metis A3 A4 A5 InterD equals0I filterD21 imageI)
    apply (simp add: ub_imageI x_def)
    apply (metis A4 A5 A6 INT_iff filterD21 reflD2 ub_imageI)
    using A3 ubE x_def by fastforce
  have B1:" (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))"  using A5 x_def by blast
  show ?thesis  using B0 B1 by auto
qed

lemma finite_ind_fil4:
  fixes f::"'b \<Rightarrow> 'a set" and x::"'b \<Rightarrow> 'a" and I::"'b set"
  assumes A0:"is_lattice R X" and 
          A1:"is_greatest R X top" and
          A2:"finite I" and 
          A3:"I \<noteq> {}" and
          A4:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X  (f i))" and
          A5:"(\<And>i. i \<in> I \<Longrightarrow> (x i) \<in> (f i))" and
          A6:"refl R X" and 
          A7:"antisym R X" and 
          A8:"trans R X"
  shows "Sup R X (x` I) \<in> \<Inter>(f`I)"
proof-
  let ?F="(x` I)" let ?s="Sup R X (x` I)"
  have B0:"finite ?F"
    by (simp add: A2)
  have B1:"?F \<subseteq> X"   by (meson A4 A5 filterD21 image_subsetI)
  have B2:"is_sup R X ?F ?s"   by (simp add: A0 A3 A7 A8 B0 B1 bsup_finite2 lattD42)
  then show ?thesis 
  using A0 A1 A2 A3 A4 A5 A6 A7 A8 finite_ind_fil2[of R X top I f x ?s] by blast
qed

lemma finite_ind_fil5:
  fixes f::"'b \<Rightarrow> 'a set"  and I::"'b set"
  assumes A0:"is_lattice R X" and 
          A1:"is_greatest R X top" and
          A2:"finite I"  and
          A3:"I \<noteq> {}" and 
          A4:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X  (f i))" and
          A5: "s \<in> (\<Inter>(f` I))" and
          A6:"refl R X" and 
          A7:"antisym R X" and 
          A8:"trans R X"
  shows "s \<in> {Sup R X (x` I)|x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))}"
  by (auto, metis A0 A1 A2 A3 A4 A5 A6 A7 A8 finite_ind_fil3 sup_equality)

lemma finite_ind_fil6:
  fixes f::"'b \<Rightarrow> 'a set" and x::"'b \<Rightarrow> 'a" and I::"'b set"
  assumes A0:"is_lattice R X" and 
          A1:"is_greatest R X top" and 
          A2:"finite I" and 
          A3:"I \<noteq> {}" and
          A4:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X  (f i))" and
          A5:"refl R X" and 
          A6:"antisym R X" and 
          A7:"trans R X"
  shows "\<Inter>(f`I) = {Sup R X (x` I)|x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))}"
  apply(auto)
  apply (smt (verit, best) A0 A1 A2 A3 A4 A5 A6 A7 INT_iff finite_ind_fil3 sup_equality)
  by (smt (verit) A0 A1 A2 A3 A4 A5 A6 A7 INT_E finite_ind_fil4)

lemma exp_lattice_filter_inf:
 fixes f::"'b \<Rightarrow> 'a set" and x::"'b \<Rightarrow> 'a" and I::"'b set"
  assumes A0:"is_lattice R X" and 
          A1:"is_greatest R X top" and 
          A2:"finite I" and
          A3: "I \<noteq> {}" and
          A4:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X  (f i))" and
          A5:"refl R X" and 
          A6:"antisym R X" and 
          A7:"trans R X"
  shows "Inf (pwr X) (filters_on R X) (f`I) = {Sup R X (x` I)|x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))}"
  using A0 A1 A2 A3 A4 A5 A6 A7 finite_ind_fil_lattice[of R X I top f] finite_ind_fil6[of R X top I f]
  by (metis (mono_tags, lifting) Sup_def antisym_on_converse filters_is_clr1 powrel6 sup_equality)
        

lemma filter_closure_of_filters4_ne:
  "\<lbrakk>refl R X; antisym R X; trans R X;is_inf_semilattice R X;A \<subseteq> filters_on R X; A \<noteq> {}; G \<in> ubd (pwr X) (filters_on R X) A\<rbrakk> \<Longrightarrow> (filter_closure R X (\<Union>A)) \<subseteq> G"
  by (metis PowI Pow_empty filterD1 filter_cl_least2a filter_pow_memD filters_is_clr1 filters_on_iff insertI1 is_supE3 powrel9 pwr_mem_iff subset_Pow_Union subset_singletonD ubdD2 ubd_iso2b)


lemma filter_closure_of_filters5_ne:
  "\<lbrakk>refl R X; antisym R X; trans R X;is_inf_semilattice R X;A \<subseteq> filters_on R X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_sup (pwr X) (filters_on R X) A  (filter_closure R X (\<Union>A))"
  by (smt (verit, del_insts) filter_closure_of_filters3_ne filter_closure_of_filters4_ne filters_is_clr1 in_mono is_supI5 powsimp1 pwr_memI ubd_sub)

lemma filter_closure_of_filters6_ne:
  "\<lbrakk>refl R X; antisym R X; trans R X;is_inf_semilattice R X;A \<subseteq> filters_on R X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Sup (pwr X) (filters_on R X) A= (filter_closure R X (\<Union>A))"
  by (simp add: filter_closure_of_filters5_ne filters_is_clr1 powrel6 sup_equality)

lemma filter_closure_of_filters7:
  "\<lbrakk>refl R X; antisym R X; trans R X;is_inf_semilattice R X;A \<subseteq> filters_on R X; is_greatest R X top\<rbrakk> \<Longrightarrow> Sup (pwr X) (filters_on R X) A = (filter_closure R X (\<Union>A))"
  by (simp add: filter_closure_of_filters5 filters_is_clr1 powrel6 sup_equality)


lemma filter_closure_of_filters8:
  "\<lbrakk>refl R X; antisym R X; trans R X;is_lattice R X;A \<subseteq> filters_on R X; is_greatest R X top\<rbrakk> \<Longrightarrow> Sup (pwr X) (filters_on R X) A = (filter_closure R X (\<Union>A))"
  by (simp add: filter_closure_of_filters7 latt_iff)

lemma filter_closure_of_filters8_ne:
  "\<lbrakk>refl R X; antisym R X; trans R X;is_lattice R X;A \<subseteq> filters_on R X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Sup (pwr X)(filters_on R X) A= (filter_closure R X (\<Union>A))"
  by (simp add: filter_closure_of_filters6_ne lattD41)

lemma filter_closure_of_filters9:
  "\<lbrakk>refl R X; antisym R X; trans R X;distributive_lattice R X;A \<subseteq> filters_on R X; is_greatest R X top\<rbrakk> \<Longrightarrow> Sup(pwr X) (filters_on R X) A = (filter_closure R X (\<Union>A))"
  by (simp add: distr_latticeD5 filter_closure_of_filters8)

lemma filter_closure_of_filters9_ne:
  "\<lbrakk>refl R X; antisym R X; trans R X;distributive_lattice R X;A \<subseteq> filters_on R X; A \<noteq> {}\<rbrakk> \<Longrightarrow> Sup (pwr X) (filters_on R X) A= (filter_closure R X (\<Union>A))"
  by (simp add: distr_latticeD5 filter_closure_of_filters8_ne)

lemma finite_ind_fil7:
  fixes f::"'b \<Rightarrow> 'a set" and I::"'b set"
  assumes A0:"is_lattice R X" and
          A1:"is_greatest R X top" and 
          A2:"I \<noteq> {}" and 
          A3:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X  (f i))" and
          A4:"refl R X" and 
          A5:"antisym R X" and 
          A6:"trans R X"
  shows "Sup (pwr X) (filters_on R X) (f`I) = {x \<in> X. \<exists>F \<in> Fpow_ne (\<Union>(f`I)). (Inf R X F, x)\<in>R}"
proof-
  let ?A="\<Union>(f`I)"
  have B0:"?A \<noteq> {}"    using A2 A3 filterD1 by fastforce
  have B1:"filter_closure R X (?A) = {x \<in> X. \<exists>F \<subseteq> ?A. finite F \<and> F \<noteq> {} \<and> (Inf R X F, x)\<in>R} " using B0 by(rule filter_closure_ne_simp)
  have B2:"... = {x \<in> X. \<exists>F \<in> Fpow_ne ?A.  (Inf R X F, x)\<in>R}"  using fpow_ne_iff2 using fpow_ne_iff2 by(fastforce)
  have B3:"filter_closure R X (?A) = {x \<in> X. \<exists>F \<in> Fpow_ne ?A.  (Inf R X F, x)\<in>R}" using B1 B2 by auto
  show ?thesis using filter_closure_of_filters8   by (metis (no_types, lifting) A0 A1 A3 A4 A5 A6 B3 filters_on_iff image_subset_iff)
qed
lemma inf_comp:
  "\<lbrakk>refl R X; antisym R X; trans R X;A1 \<subseteq>X; A2 \<subseteq> X;is_inf R X A1 i1; is_inf R X A2 i2; (\<And>a2. a2 \<in> A2 \<longrightarrow> (\<exists>a1 \<in> A1. (a1, a2)\<in>R)) \<rbrakk> \<Longrightarrow> (i1, i2)\<in>R"
  by (smt (z3) converse_iff greatestD2 is_supD1 is_supD32 subset_eq trans_onD ubdI ubd_mem_iff3)

lemma finite_ind_fil8:
  fixes f::"'b \<Rightarrow> 'a set" and x::"'b \<Rightarrow> 'a" and I::"'b set"
  assumes A0:"is_lattice R X" and
          A1:"is_greatest R X top" and
          A2:"finite I" and
          A3:"I \<noteq> {}" and
          A4:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X (f i))" and
          A5:"F \<in> Fpow_ne (\<Union>(f`I))" and
          A6:"(Inf R X F,y)\<in>R" and
          A7:"y \<in> X" and
          A8:"refl R X" and 
          A9:"antisym R X" and 
          A10:"trans R X"
  shows "\<exists>(x::'b \<Rightarrow> 'a). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> (Inf R X (x` I), y)\<in>R"

proof-
  define G where "G = {(i, z)|z i. z \<in> F \<and> (z \<in> f i)}"
  have B0:"\<And>i. i \<in> I \<longrightarrow>  G``{i} \<noteq> {}  \<longrightarrow> G``{i} \<subseteq> F"
  proof
    fix i assume A3:"i \<in> I"
    show "G``{i}  \<noteq> {} \<longrightarrow> G``{i} \<subseteq> F"
    proof
      assume A4:"G``{i} \<noteq> {}"    
      show "G``{i} \<subseteq> F"
      proof
        fix z assume A5:"z \<in> G``{i}"
        have B1:"(i, z) \<in> G"  using A5 by auto 
        show "z \<in> F" using B1 by(auto simp add:G_def)
      qed
    qed
  qed
  have P:"\<And>i z. i \<in> I \<longrightarrow> G``{i} \<noteq> {} \<longrightarrow> z \<in> G``{i} \<longrightarrow> z \<in> (f i)"
    proof
    fix i z assume A6:"i \<in> I"
    show "G``{i}  \<noteq> {} \<longrightarrow> z \<in> G``{i} \<longrightarrow> z \<in> (f i)"
    proof
      assume A7:"G``{i}  \<noteq> {}" show " z \<in> G``{i} \<longrightarrow> z \<in> (f i)"
      proof
       assume A8:"z \<in> G``{i}" 
       have P0:"(i, z) \<in> G" using A8 by auto
       show "z \<in> f i" using P0 by(auto simp add:G_def)
      qed
    qed
  qed
  define x where "x = (\<lambda>i. if G``{i} \<noteq> {} then Inf R X (G``{i}) else SOME z. z \<in> (f i))"
  have B2:"\<And>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)"
  proof
    fix i assume A6:"i \<in> I"
    show "x i \<in> f i"
    proof(cases " G``{i} \<noteq> {}")
      case True
      have B3:"x i =  Inf R X (G``{i})"  by (simp add: True x_def)
      have B4:"G``{i} \<subseteq> (f i)"   using A6 P by blast
      have B5:"finite (G``{i})"    by (meson A6 B0 True assms(6) fpow_neD4 infinite_super)
      have B6:" Inf R X (G``{i}) \<in> (f i)"  using A6 B4 B5 True assms(1) assms(5) filter_finf_closed3 lattD41
        using A10 A9 by blast
      then show ?thesis  by (simp add: B3)
    next
      case False
      then show ?thesis  by (metis A6 assms(5) ex_in_conv filterD1 someI2_ex x_def)
    qed
  qed
  have B7:"\<And>z. z \<in> F \<longrightarrow> (\<exists>w \<in> (x` I). (w, z)\<in>R)"
  proof
    fix z assume A7:"z \<in> F"
    obtain i where B8:"i \<in> I \<and> z \<in> (f i)"  by (metis A7 UN_E assms(6) fpow_neD1 in_mono)
    have B9:"G``{i} \<noteq> {}" using A7 B8 by(auto simp add:G_def)
    have B10:"x i =  Inf R X (G``{i})" by (simp add: B9 x_def)
    have B11:"z \<in> G``{i}" by (simp add: A7 B8 G_def)
    have B12:"finite (G``{i}) \<and> (G``{i}) \<subseteq> X"   by (meson B0 B8 B9 P assms(5) assms(6) filterD21 fpow_neD4 infinite_super subsetI)
    have B13:"(Inf R X (G``{i}), z)\<in>R" using B11 B12 assms(1)  by (metis A10 A8 A9 B9 Sup_def antisym_on_converse converseD is_supD1121 l_fininf sup_equality)
    show " (\<exists>w \<in> (x` I). (w, z)\<in>R)"
      by (metis B10 B13 B8 imageI)
  qed
  have B14:"finite (x` I) \<and> (x` I) \<subseteq> X"
    using B2 assms(3) assms(5) filterD21 by fastforce 
  have B15:"\<And>i. i \<in> I \<longrightarrow> (f i) \<subseteq> X"
    using A4 filterD2 by blast  
  have B16:"\<Union>(f`I) \<subseteq> X"   by (simp add: B15 UN_least)
  have B17:"finite F \<and> F \<subseteq> X" by (metis B16 assms(6) fpow_neD4 subset_trans)
  have B18:"(Inf R X (x` I), Inf R X F)\<in>R"
    apply(rule_tac ?X="X" and ?A1.0="x` I" and ?A2.0="F" in inf_comp)
    apply (simp add: A8)
    apply (simp add: A9)
    apply (simp add: A10)
    apply (simp add: B14)
    apply (simp add: B17)
    apply (metis A0 A10 A3 A8 A9 B14 antisym_on_converse image_is_empty is_sup_unique l_fininf the_equality)
    apply (metis A0 A10 A5 A9 B17 Sup_def antisym_on_converse bsup_finite2 fpow_ne_iff2 is_sup_semilattice_def latt_iff trans_on_converse)
    using B7 by blast
  have B19:"(Inf R X (x` I), y)\<in>R"
    by (smt (verit, ccfv_SIG) A0 A10 A3 A5 A6 A7 A8 A9 B14 B17 B18 antisym_on_converse fpow_ne_iff2 image_is_empty is_supE1 is_sup_unique l_fininf the_equality trans_onD)
  show ?thesis
    using B19 B2 by blast
qed


lemma finite_ind_fil9:
  fixes f::"'b \<Rightarrow> 'a set" and x::"'b \<Rightarrow> 'a" and I::"'b set"
  assumes A0:"is_lattice R X" and 
          A1:"is_greatest R X top" and 
          A2:"I \<noteq> {}" and
          A3:"finite I" and
          A4:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X  (f i))" and
          A5:"refl R X" and 
          A6:"antisym R X" and 
          A7:"trans R X"
  shows "Sup (pwr X) (filters_on R X) (f`I)  \<subseteq> {y \<in> X. \<exists>(x::'b \<Rightarrow> 'a). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> (Inf R X (x` I), y)\<in>R}" (is "?L \<subseteq> ?R")
proof
  fix z assume A8:"z \<in> ?L"
  obtain F where B0:"F \<in> Fpow_ne (\<Union>(f`I)) \<and> (Inf R X F, z)\<in>R" using A0 A1 A2 A8 finite_ind_fil7[of R X top I]  using A4 A5 A6 A7  by fastforce 
  have B1:"(f`I) \<noteq> {}" by (simp add: A2) 
  have B2:"z \<in> X" using A0 A1 B1
    by (meson A3 A4 A5 A6 A7 A8 filterD21 filters_on_iff filters_on_lattice_sup_semilattice3b finite_imageI image_subsetI) 
  have B3:"F \<in> Fpow_ne (\<Union>(f`I)) \<and> (Inf R X F, z)\<in>R  \<and> z \<in> X"   by (simp add: B0 B2)
  obtain x where B4:"(\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> (Inf R X (x` I), z)\<in>R" using A0 A1 A2 B0 B3 finite_ind_fil8[of R X top I f F z]
    using A3 A4 A5 A6 A7 by blast 
  show "z \<in> ?R" using B3 B4 by(auto)
qed

lemma finite_ind_fil10:
  fixes f::"'b \<Rightarrow> 'a set" and I::"'b set"
  assumes A0:"is_lattice R X"and 
          A1:"is_greatest R X top" and 
          A2:"I \<noteq> {}" and 
          A3:"finite I" and
          A4:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X  (f i))" and
          A5:"refl R X" and 
          A6:"antisym R X" and 
          A7:"trans R X"
  shows "{y \<in> X. \<exists>(x::'b \<Rightarrow> 'a). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> (Inf R X (x` I), y)\<in>R} \<subseteq> Sup(pwr X) (filters_on R X) (f`I) " (is "?L \<subseteq> ?R")
proof
  fix z assume A2:"z \<in> ?L"
  obtain x where B0:"(\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> (Inf R X (x` I) ,z)\<in>R" using A2 by auto
  have B1:"(x` I) \<in> Fpow_ne (\<Union>(f`I))"  by(auto simp add:Fpow_ne_def Fpow_def B0 assms)
  show "z \<in> ?R" using assms B0 B1 A2 finite_ind_fil7[of R X top I] by auto
qed
lemma finite_ind_fil11:
  fixes f::"'b \<Rightarrow> 'a set" and I::"'b set"
  assumes A0:"is_lattice R X"and 
          A1:"is_greatest R X top" and 
          A2:"I \<noteq> {}" and 
          A3:"finite I" and
          A4:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X  (f i))" and
          A5:"refl R X" and 
          A6:"antisym R X" and 
          A7:"trans R X"
    shows "Sup (pwr X) (filters_on R X) (f`I) = {y \<in> X. \<exists>(x::'b \<Rightarrow> 'a). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> (Inf R X (x` I), y)\<in>R}"
  apply(rule order.antisym) 
  using A0 A1 apply(rule finite_ind_fil9)
  apply (simp add: A2)
  apply (simp add: A3)
  apply (simp add: A4)
  apply (simp add: A5)
  apply (simp add: A6)
  apply (simp add: A7)
  apply (simp add: A3)
  using A0 A1 apply(rule finite_ind_fil10)
  apply (simp add: A2)
  apply (simp add: A3)
  apply (simp add: A4)
  apply (simp add: A5)
  apply (simp add: A6)
  by (simp add: A7)

lemma finite_ind_fil11b:
  fixes f::"'b \<Rightarrow> 'a set" and I::"'b set"
  assumes A0:"is_lattice R X" and
          A1:"is_greatest R X top" and 
          A2:"I \<noteq> {}" and
          A3:"finite I" and 
          A4:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X  (f i))" and
          A5:"y \<in> Sup (pwr  X)(filters_on R X) (f`I)"  and
          A6:"refl R X" and 
          A7:"antisym R X" and 
          A8:"trans R X"
  shows "\<exists>(x::'b \<Rightarrow> 'a). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> (Inf R X (x` I), y)\<in>R"
  using finite_ind_fil11[of R X top I f] assms by(auto)

lemma finite_ind_fil12:
  fixes f::"'b \<Rightarrow> 'a set" and x::"'b \<Rightarrow> 'a" and I::"'b set"
  assumes A0:"distributive_lattice R X" and 
          A1:"is_greatest R X top" and
          A2:"I \<noteq> {}" and 
          A3:"finite I" and 
          A4:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X  (f i))" and
          A5:"y \<in> X" and
          A6: "(\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))" and
          A7:"(Inf R X (x` I), y)\<in>R" and
          A8:"refl R X" and 
          A9:"antisym R X" and 
          A10:"trans R X"
  shows " \<exists>(x1::'b \<Rightarrow> 'a). (\<forall>i. i \<in> I \<longrightarrow> (x1 i) \<in> (f i)) \<and> Inf R X (x1` I) =y "
proof-
  define x1 where "x1 = (\<lambda>i. Sup R X {y, x i})"
  have B00:"finite (x` I)"   by (simp add: A3) 
  have B01:"x` I \<subseteq> X"  using A4 assms(7) filterD21 by fastforce 
  have B02:"x` I \<noteq> {}"  by (simp add: A2) 
  have B03:"finite (x1 ` I)"   by (simp add: A3) 
  have B04:"(x1 ` I) \<subseteq> X"
    by (metis A0 A5 A9 B01 distr_latticeD5 image_subset_iff lattD4 ssupD4 x1_def)  
  have B05:"(x1 ` I) \<noteq> {}"  using A2 by force
  have B06:"is_lattice R X"   by (simp add: A0 distr_latticeD5)
  have B07:"Inf R X (x` I) \<in> X"  by (metis A0 A10 A8 A9 B00 B01 B02 Sup_def antisym_on_converse distr_latticeD5 is_supE1 l_fininf sup_equality)
  have B0:"y = Sup R X {y, Inf R X (x` I)}"   by (metis A5 A7 A8 A9 B07 ge_sup2 reflD2)
  have B1:"... = Inf R X {Sup R X {y,a}|a.  a \<in> (x` I)}" using fin_distr1[of R X "x`I" "y"]   using A0 A10 A5 A8 A9 B00 B01 B02 by fastforce
  have B2:"... = Inf R X {Sup R X {y, x i}|i. i \<in> I}"  by (smt (verit, best) Collect_cong imageE image_eqI)
  have B3:"... = Inf R X {x1 i|i. i \<in> I}"  using x1_def by auto
  have B4:"... = Inf R X (x1 ` I)"  by (simp add: Setcompr_eq_image)
  have B5:"Inf R X (x1 ` I) = y"  using B0 B1 B2 B3 B4 by presburger
  have B6:"\<forall>i. i \<in> I \<longrightarrow> (x1 i) \<in> (f i)"   by (simp add: A10 A4 A5 A6 A8 A9 B06 filter_on_lattice_sup01 x1_def) 
  show ?thesis  using B5 B6 by blast
qed

lemma finite_ind_fil13:
  fixes f::"'b \<Rightarrow> 'a set" and I::"'b set"
  assumes A0:"distributive_lattice R X" and
          A1:"is_greatest R X top" and 
          A2:"I \<noteq> {}" and 
          A3:"finite I" and
          A4:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X (f i))" and
          A5:"refl R X" and 
          A6:"antisym R X" and 
          A7:"trans R X"
  shows "Sup (pwr X) (filters_on R X) (f`I) \<subseteq> {y \<in> X. \<exists>(x::'b \<Rightarrow> 'a). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf R X (x` I) = y}" (is "?L \<subseteq> ?R")
proof
  fix y assume A2:"y \<in> ?L"
  have B0:"is_lattice R X" by (simp add: A0 distr_latticeD5)
  have B1:"y \<in> X" by (smt (verit, best) A2 A4 A5 A6 A7 B0 assms(3) filterD21 filters_on_iff filters_on_lattice_csup2 image_is_empty image_subset_iff) 
  obtain x where B2:"(\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and>( Inf R X (x` I), y)\<in>R" using finite_ind_fil11b  by (metis A1 A2 A3 A4 A5 A6 A7 B0 assms(3))
  obtain x1 where B3:"(\<forall>i. i \<in> I \<longrightarrow> (x1 i) \<in> (f i)) \<and> Inf R X (x1` I) =y" using finite_ind_fil12[of R X top I f y x] A0 A1 A2  B1 B2    using A3 A4 A5 A6 A7 assms(3) by blast 
  show "y \<in> ?R"
    using B1 B3 by blast
qed


lemma finite_ind_fil14:
  fixes f::"'b \<Rightarrow> 'a set" and I::"'b set"
  assumes A0:"distributive_lattice R X" and
          A1:"is_greatest R X top" and
          A2:"I \<noteq> {}" and
          A3:"finite I" and
          A4:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X  (f i))" and  
          A5:"refl R X" and 
          A6:"antisym R X" and 
          A7:"trans R X"
  shows "{y \<in> X. \<exists>(x::'b \<Rightarrow> 'a). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf R X (x` I) = y} \<subseteq> Sup (pwr X) (filters_on R X) (f`I) " (is "?L \<subseteq> ?R")
proof
  fix y assume A2:"y \<in> ?L"
  have B0:"is_lattice R X" by (simp add: A0 distr_latticeD5)
  have B1:"y \<in> X"  using A2 by blast
  obtain x1 where B3:"(\<forall>i. i \<in> I \<longrightarrow> (x1 i) \<in> (f i)) \<and> Inf R X (x1` I) =y" using A2 by blast
  have B4:"(\<forall>i. i \<in> I \<longrightarrow> (x1 i) \<in> (f i)) \<and> (Inf R X (x1` I), y)\<in>R"  using A5 B1 B3 reflE1 by auto  
  have B5:"y \<in> {y \<in> X. \<exists>(x::'b \<Rightarrow> 'a). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> (Inf R X (x` I), y)\<in>R}"    using B1 B4 by blast 
  show "y \<in> ?R"  using finite_ind_fil10[of R X top I f]
    using A1 A3 A4 A5 A6 A7 B0 B5 assms(3) by blast 
qed

lemma finite_ind_fil15:
  fixes f::"'b \<Rightarrow> 'a set" and I::"'b set"
  assumes A0:"distributive_lattice R X" and
          A1:"is_greatest R X top" and
          A2:"I \<noteq> {}" and
          A3:"finite I" and
          A4:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X  (f i))" and  
          A5:"refl R X" and 
          A6:"antisym R X" and 
          A7:"trans R X" 
  shows "Sup (pwr X) (filters_on R X) (f`I) = {y \<in> X. \<exists>(x::'b \<Rightarrow> 'a). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf R X (x` I) = y}"
  using finite_ind_fil13[of R X top I f] finite_ind_fil14[of R X top I f]
  using A0 A1 A2 A3 A4 A5 A6 A7 by fastforce 


lemma maximalI2:
  "\<lbrakk>antisym R X; A \<subseteq> X;x \<in> A; \<not>(\<exists>a \<in> A. (x, a)\<in>R \<and> x \<noteq> a)\<rbrakk> \<Longrightarrow> is_maximal R A x"
  by (metis maximalI1)

lemma maximalI3:
  "\<lbrakk>antisym R X;A \<subseteq> X;is_greatest R A x\<rbrakk> \<Longrightarrow> is_maximal R A x"
  by (simp add: antisym_onD greatest_iff in_mono is_maximal_def)

lemma mredI1:
  "\<lbrakk>A \<in> Pow_ne X; x \<notin> A; is_inf R X A x\<rbrakk> \<Longrightarrow> meet_reducible R X x"
  using meet_reducible_def by fastforce 

lemma mredI2:
  "\<exists>A \<in> Pow_ne X. x \<notin> A \<and> is_inf R X A x \<Longrightarrow> meet_reducible R X x"
   by (simp add: meet_reducible_def)

lemma mredD1:
  "meet_reducible R X x \<Longrightarrow> (\<exists>A \<in> Pow_ne X. x \<notin> A \<and> is_inf R X A x)" 
   by (simp add: meet_reducible_def) 

lemma mredD2:
  "\<lbrakk>antisym R X; meet_reducible R X x\<rbrakk> \<Longrightarrow> \<not>(is_greatest R X x)"
proof-
  assume A0:"antisym R X" and A1:" meet_reducible R X x"
  obtain A where B0:"A \<in> Pow_ne X" and B1:"x \<notin> A" and B2:"is_inf R X A x"  by (meson A1 mredD1) 
  have B3:"A \<subseteq> X"  by (simp add: B0 pow_neD1)
  obtain a where B4:"a \<in> A"  using B0 pow_ne_bot by fastforce  
  have B3:"(x, a) \<in> R \<and> x \<noteq> a"
    using B1 B2 B4 is_supD1121 by fastforce  
  show "\<not>(is_greatest R X x)" 
  proof(rule ccontr)
   assume A1:"\<not>(\<not>(is_greatest R X x))" then obtain B30:"is_greatest R X x" by simp
  then have B31:"(a, x) \<in> R"
    by (meson B0 B4 greatestD12 in_mono pow_neD1 ubE)
  have B32:"a \<in> X"
    by (meson B0 B4 in_mono pow_neD1)
  have B33:"(x, a) \<in>R"
    by (simp add: B3)
  then have B34:"a = x"
    by (meson A0 B2 B31 B32 antisym_onD is_supE1)
  then show False
    using B3 by auto
  qed
qed


lemma mredD3:
  "\<lbrakk>m \<in> X; antisym R X; refl R X; trans R X; is_clattice R X;  \<not>(is_greatest R X m)\<rbrakk> \<Longrightarrow> {x \<in> X. (m, x)\<in>R \<and> m \<noteq> x} \<noteq> {}"
  by (smt (verit, del_insts) clatD21 empty_iff greatestD11 greatestD14 mem_Collect_eq subset_refl sup_max_eq2) 

lemma mredD4:
  assumes A0:"is_clattice R X" and A1:"m \<in> X" and A2:"\<not>(is_greatest R X m)" and A3:"\<not>((m, Inf R X {x \<in> X. (m, x)\<in>R \<and> m \<noteq> x}) \<in> R \<and> m \<noteq> Inf R X {x \<in> X. (m, x)\<in>R \<and> m \<noteq> x})" and
          A4:"antisym R X" and A5:"trans R X" and A6:"refl R X"
  shows "meet_reducible R X m"
proof-
  let ?A="{x \<in> X. (m, x)\<in>R \<and> m \<noteq> x}"
  obtain B0:"?A \<subseteq> X" and B1:"?A \<noteq> {}"by (metis (no_types, lifting) A0 A1 A2 A4 A5 A6 Collect_empty_eq mem_Collect_eq mredD3 subsetI) 
  have B2:"(m, Inf R X ?A)\<in>R"  by (metis (no_types, lifting) A0 A1 A4 A5 B0 B1 cinfD62 clatD2 converseI mem_Collect_eq ub_iff1)  
  have B3:"m = Inf R X ?A"    using A3 B2 by blast  
  have B4:"?A \<in> Pow_ne X"  using B1 pow_ne_iff2 by blast
  have B5:"m \<notin> ?A"  by simp
  have B6:"is_inf R X ?A m"   by (metis (no_types, lifting) A0 A4 A5 B0 B1 B3 cinfD4 clatD2) 
  show "meet_reducible R X m"  using B4 B6 mredI1 by fastforce 
qed

lemma filter_compl1:
  "\<lbrakk>antisym R X; trans R X; refl R X; is_lattice R X; is_pfilter R X F\<rbrakk> \<Longrightarrow> (X -  F) \<noteq> {}"
  using is_pfilterD3 is_pfilter_def by fastforce

lemma filter_compl2: 
  "\<lbrakk>antisym R X; trans R X; refl R X;is_lattice R X; is_pfilter R X F\<rbrakk> \<Longrightarrow> (X - F \<noteq> X)"
  by (metis Diff_disjoint inf.idem inf.orderE is_pfilterD3 pfilter_on_lattice_inf4b)
lemma pfilter_compl3: 
  "\<lbrakk>antisym R X; trans R X; refl R X;is_lattice R X; is_pfilter R X F; x \<in> (X-F); y \<in> X; (y, x)\<in>R\<rbrakk> \<Longrightarrow>y \<in> (X-F)"
  by (metis Diff_iff filter_memI is_pfilter_def)

lemma pfilter_compl4:
   "\<lbrakk>antisym R X; trans R X; refl R X;is_lattice R X; is_pfilter R X F\<rbrakk> \<Longrightarrow> is_ord_cl X (X-F) (dual R)"
  by (simp add: filterD4 is_ord_cl_comp1 is_pfilter_def)

lemma prime_filter_compl5:
   "\<lbrakk>antisym R X; trans R X; refl R X; is_lattice R X; is_pfilter R X F; sup_prime R X F; x \<in> (X-F); y \<in> (X-F)\<rbrakk> \<Longrightarrow> Sup R X {x, y} \<in> (X-F)"
   by (metis Diff_iff  l_sup_closed primefilterD1)
lemma prime_filter_compl6:
   "\<lbrakk>antisym R X; trans R X; refl R X;is_lattice R X; is_pfilter R X F; sup_prime R X F\<rbrakk> \<Longrightarrow> is_dir (X-F) R"
  by (meson Diff_subset is_dirI4 lattD42 prime_filter_compl5)


lemma prime_filter_compl7: 
  "\<lbrakk>antisym R X; trans R X; refl R X;is_lattice R X; is_pfilter R X F; sup_prime R X F; x \<in> X; y \<in> X; Inf R X {x, y} \<in> (X-F)\<rbrakk> \<Longrightarrow> (x \<in> (X-F)) \<or> (y \<in> (X-F))"  
  by (metis Diff_iff filter_finf_closed1 is_pfilterD1 lattD41) 

lemma prime_filter_compl8: 
  "\<lbrakk>antisym R X; trans R X; refl R X;is_lattice R X; is_pfilter R X F;  sup_prime R X F\<rbrakk> \<Longrightarrow> is_ideal R X (X-F)" 
   by (meson Diff_subset is_filter_def filter_compl1 idealI1 is_ord_cl_comp1 is_pfilterD1 prime_filter_compl6)

lemma prime_filter_compl9:"\<lbrakk>antisym R X; trans R X; refl R X;is_lattice R X; is_pfilter R X F;  sup_prime R X F\<rbrakk> \<Longrightarrow> inf_prime R X (X-F)" 
  by (meson inf_primeI1 prime_filter_compl7)

lemma prime_filter_on_lattice:
  assumes A0:"is_lattice R X" and 
          A1:"antisym R X" and
          A2:"trans R X" and 
          A3:"refl R X" and
          A4:"is_pfilter R X F" and 
          A5:"sup_prime R X F" and
          A6:"a \<in> filters_on R X" and
          A7:"b \<in> filters_on R X" and
          A8:"F=Inf (pwr X) (filters_on R X) {a, b}"
  shows "F = a \<or> F =b"
proof-
  have B0:"F=a \<inter> b"  by (metis A0 A1 A2 A3 A6 A7 A8 Sup_def antisym_on_converse filters_is_clr1 filters_lattice_inf powrel6 sup_equality) 
  have B1:"a \<subseteq> F \<or> b \<subseteq> F" using B0 A0 A1 A2 A3 A4 B0 A5 A6 A7 sup_prime_pfilterD4[of R X F a b] filters_on_iff by auto
  have B2:"\<not>(a \<subseteq> F) \<longrightarrow> b = F" using B0 B1 by blast
  show ?thesis
    using B0 B2 by blast
qed

lemma compact_dense:
  assumes A0:"is_clattice R X" and 
          A1:"compactly_generated R X" and
          A2:"x \<in> X" and 
          A3:"antisym R X" and
          A4:"trans R X" and
          A5:"refl R X"
  shows "x = Sup R X {k \<in> compact_elements R X. (k, x)\<in>R}"
proof-
  let ?K=" compact_elements R X"
  let ?Kd="{k \<in> ?K. (k, x)\<in>R}"
  obtain Kx where A6:"Kx \<in> Pow ?K" and A7:"is_sup R X Kx x" by (meson A1 A2 compactly_generatedD1)
  have B0:"?K \<subseteq> X"   by (simp add: compact_elements_sub)
  have B1:"?Kd \<subseteq> X" using B0 by blast
  have B2:"Kx \<subseteq> ?Kd" using A6 A7 is_supD1121 by fastforce
  have B3:"(Sup R X ?Kd, Sup R X Kx)\<in>R"   by (metis (no_types, lifting) A0 A2 A3 A7 A4 B1 clatD21 is_supE4 mem_Collect_eq sup_equality ubdI ubd_mem_iff) 
  have B4:" Sup R X Kx = x"   by (simp add: A3 A7 sup_equality) 
  have B6:"(x, Sup R X ?Kd)\<in>R"   using A0 A3 A4 B1 B2 B4 sup_iso1 by blast 
  show ?thesis using B3 B4 B6 by (metis (no_types, lifting) A0 A2 A3 A4 B1 B2 antisym_onD bot.extremum_uniqueI clatD31)
qed

lemma compactly_generated_meets:
  assumes A0:"is_clattice R X" and 
          A1:"compactly_generated R X" and
          A2:"x \<in> X" and
          A3:"y \<in> X" and 
          A4:"\<not>((y, x)\<in>R)" and
          A5:"antisym R X" and
          A6:"trans R X" and
          A7:"refl R X"
  shows "\<exists>k \<in> compact_elements R X. (k, y)\<in>R \<and> \<not>((k,x)\<in>R)"
  by (meson A1 A2 A3 A4 PowD compactly_generatedD1 is_supD1121 is_supE4 subset_iff ub_def)

lemma meet_reduction1:
  assumes A0:"is_clattice R X" and
          A1:"antisym R X" and
          A2:"trans R X" and
          A3:"refl R X" and
          A4:"m \<in> X" and
          A5:"meet_reducible R X m"
  shows " m \<in> lbd R X {x \<in> X. (m, x)\<in>R \<and> m \<noteq> x}"
   using A4 ubd_mem_iff2 by fastforce 


lemma meet_reduction2:
  assumes A0:"is_clattice R X" and
          A1:"antisym R X" and
          A2:"trans R X" and
          A3:"refl R X" and
          A4:"m \<in> X" and
          A5:"meet_reducible R X m"
  shows " m = Inf R X {x \<in> X. (m, x)\<in>R \<and> m \<noteq> x}"
proof-
  let ?A="{x \<in> X. (m, x)\<in>R \<and> m \<noteq> x}"
  obtain A where B0:"A \<in> Pow_ne X" and B1:"m \<notin> A" and  B2:"is_inf R X A m"
    by (metis A5 meet_reducible_def) 
  obtain B3:"\<And>x. x \<in> A \<Longrightarrow> (m, x)\<in>R \<and> m \<noteq> x"
  proof
    fix x assume A6:"x \<in> A"  show "(m, x)\<in>R \<and> m \<noteq> x"  using A6 B1 B2 is_supD1121 by fastforce
  qed
  obtain B2:"A \<subseteq> ?A"  using B0 \<open>\<And>thesis::bool. ((\<And>x::'a::type. x \<in> (A::'a::type set) \<Longrightarrow> (m::'a::type, x) \<in> (R::('a::type \<times> 'a::type) set) \<and> m \<noteq> x) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> pow_neD1 by auto 
  have B3:"?A \<subseteq> X"  by simp
  have B4:"?A \<noteq> {}"   by (metis B0 B2 bot.extremum_uniqueI pow_ne_iff2) 
  have B5:"(m, Inf R X ?A)\<in>R"   by (metis (no_types, lifting) A0 A1 A2 A4 B3 B4 cinfD62 clatD2 converseI mem_Collect_eq ubI)
  have B6:"(Inf R X ?A,Inf R X A)\<in>R"   by (simp add: A0 A1 A2 B2 inf_anti1) 
  have B7:"(Inf R X ?A, m)\<in>R"
    by (smt (verit) A0 A1 A2 Sup_def \<open>\<And>thesis::bool. (\<And>A::'a::type set. \<lbrakk>A \<in> Pow_ne (X::'a::type set); (m::'a::type) \<notin> A; is_inf (R::('a::type \<times> 'a::type) set) X A m\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> antisym_on_converse converse_iff inf_anti1 is_supD1121 mem_Collect_eq pow_neD1 subset_iff sup_equality)
  show "m=Inf R X ?A"
    by (metis (no_types, lifting) A0 A1 A2 A4 B3 B4 B5 B7 antisym_onD clatD32)
qed

lemma meet_reduction3:
  assumes A0:"is_clattice R X" and
          A1:"antisym R X" and
          A2:"trans R X" and
          A3:"refl R X" and
          A4:"m \<in> X" and
          A5:"meet_reducible R X m"
  shows "is_inf R X {x \<in> X. (m, x)\<in>R \<and> m \<noteq> x} m"
proof-
  let ?A="{x \<in> X. (m, x)\<in>R \<and> m \<noteq> x}"
  obtain A where B0:"A \<in> Pow_ne X" and B1:"m \<notin> A" and  B2:"is_inf R X A m"
    by (metis A5 meet_reducible_def) 
  obtain B3:"\<And>x. x \<in> A \<Longrightarrow> (m, x)\<in>R \<and> m \<noteq> x"
  proof
    fix x assume A6:"x \<in> A"  show "(m, x)\<in>R \<and> m \<noteq> x"  using A6 B1 B2 is_supD1121 by fastforce
  qed
  obtain B2:"A \<subseteq> ?A"  using B0 \<open>\<And>thesis::bool. ((\<And>x::'a::type. x \<in> (A::'a::type set) \<Longrightarrow> (m::'a::type, x) \<in> (R::('a::type \<times> 'a::type) set) \<and> m \<noteq> x) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> pow_neD1 by auto 
  have B3:"?A \<subseteq> X"  by simp
  have B4:"?A \<noteq> {}"   by (metis B0 B2 bot.extremum_uniqueI pow_ne_iff2) 
  have B5:"(m, Inf R X ?A)\<in>R"   by (metis (no_types, lifting) A0 A1 A2 A4 B3 B4 cinfD62 clatD2 converseI mem_Collect_eq ubI)
  have B6:"(Inf R X ?A,Inf R X A)\<in>R"   by (simp add: A0 A1 A2 B2 inf_anti1) 
  have B7:"(Inf R X ?A, m)\<in>R"
    by (smt (verit) A0 A1 A2 Sup_def \<open>\<And>thesis::bool. (\<And>A::'a::type set. \<lbrakk>A \<in> Pow_ne (X::'a::type set); (m::'a::type) \<notin> A; is_inf (R::('a::type \<times> 'a::type) set) X A m\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> antisym_on_converse converse_iff inf_anti1 is_supD1121 mem_Collect_eq pow_neD1 subset_iff sup_equality)
  show "is_inf R X {x \<in> X. (m, x)\<in>R \<and> m \<noteq> x} m"
    by (metis (no_types, lifting) A0 A1 A2 A4 B3 B4 B5 B7 antisym_onD cinfD4 clatD2 clatD32)
qed


lemma mirred_temp1:
  assumes A0:"is_clattice R X" and 
          A1:"compactly_generated R X" and 
          A2:"a \<in> X" and
          A3:"b \<in> X" and 
          A4:"\<not>((b,a)\<in>R)" and
          A5:"is_compact R X k" and
          A6:"(k,b)\<in>R" and
          A8:"\<not>((k,a)\<in>R)" and 
          A9:"D \<subseteq>  {q \<in> X. (a,q)\<in>R \<and> \<not> ((k, q)\<in>R)}" and
          A10:"is_dir D R" and
          A11:"D \<noteq> {}"  and         
          A12:"antisym R X" and
          A13:"trans R X" and
          A14:"refl R X" 
  shows "Sup R X D \<in> {q \<in> X. (a,q)\<in>R \<and> \<not> ((k,q)\<in>R)}"
proof-
  let ?Q="{q \<in> X. (a,q)\<in>R \<and> \<not> ((k,q)\<in>R)}"
  have B0:"?Q \<subseteq> X" by simp
  obtain j where B1:"is_sup R X D j" by (meson A0 A12 A13 A9 B0 clatD21 dual_order.trans)
  have B2:"j \<in> X" using B1 is_supE1 by fastforce 
  have B3:"\<forall>d. d \<in> D \<longrightarrow> (a,d)\<in>R"   using A9 by blast
  have B4:"a \<in> lbd R X D"  by (simp add: A2 B3 ubdI)
  have B5:"(a, j)\<in>R"  by (smt (verit, ccfv_threshold) A11 A13 A2 A9 B1 B2 is_supE2 mem_Collect_eq ne_subset_ne subset_iff trans_on_def ub_def)
  have B6:"\<not> ((k,j)\<in>R)"
  proof(rule ccontr)
    assume P0:"\<not>(\<not> ((k,j)\<in>R))" obtain P1:"(k,j)\<in>R"  using P0 by auto
    have B7:"(k,Sup R X D)\<in>R"   using B1 P1 sup_equality A12 by fastforce
    have B8:"D \<in> Pow_ne X" by (meson A11 A9 B0 pow_neI subset_trans)
    have B9:"is_sup_semilattice R X"    by (simp add: A0 clatD1 csup_fsup)
    obtain d where B10:"d \<in> D \<and> (k,d)\<in>R" using ccompact0   using A10 A5 B7 B8 B9    by (metis A12 A13 A14)
    show False   using A9 B10 by blast
  qed
  have B11:"j \<in> ?Q"   by (simp add: B2 B5 B6)
  show "Sup R X D \<in> ?Q"using B1 B11 sup_equality using A12 by fastforce
qed

lemma mirred_temp2b:
  assumes A0:"is_clattice R X" and 
          A1:"compactly_generated R X" and
          A2:"a \<in> X" and
          A3:"b \<in> X" and 
          A4:"\<not>((b,a)\<in>R)" and 
          A5:"is_compact R X k" and
          A6:"(k,b)\<in>R" and
          A7:"\<not>((k,a)\<in>R)" and
          A8:"antisym R X" and
          A9:"trans R X" and
          A10:"refl R X" 
  shows "\<exists>m \<in> {q \<in> X. (a,q)\<in>R \<and> \<not> ((k,q)\<in>R)}. \<forall>q \<in> {q \<in> X. (a,q)\<in>R \<and> \<not> ((k,q)\<in>R)}.  (m,q)\<in>R \<longrightarrow> q = m"
proof(rule predicate_Zorn)
  show "partial_order_on {q \<in> X.(a,q)\<in>R \<and> \<not> ((k,q)\<in>R)} (relation_of (\<lambda>x y. (x, y) \<in> R) {q \<in> X. (a,q)\<in>R \<and> \<not> ((k,q)\<in>R)})"
    by (smt (verit, best) A10 A8 A9 antisym_onD mem_Collect_eq partial_order_on_relation_ofI reflD2 trans_onD)
  show "\<And>C. C \<in> Chains (relation_of ((\<lambda>x y. (x, y) \<in> R))  {q \<in> X. (a,q)\<in>R \<and> \<not> ((k,q)\<in>R)}) \<Longrightarrow> \<exists>u\<in>{q \<in> X. (a,q)\<in>R \<and> \<not> ((k,q)\<in>R)}. \<forall>q\<in>C. (q, u)\<in>R"
proof-
    let ?Q="{q \<in> X. (a,q)\<in>R \<and> \<not> ((k,q)\<in>R)}"
    fix C assume A8:"C \<in> Chains (relation_of (\<lambda>x y. (x, y) \<in> R) ?Q)"
    have B0:"C \<subseteq> X"   using A8 Chains_relation_of by blast
    have B1:"\<forall>c. c \<in> C \<longrightarrow> (a, c)\<in>R"   using A8 Chains_relation_of by force
    have B2:"\<forall>c. c \<in> C \<longrightarrow> \<not> (k, c)\<in>R"   using A8 Chains_relation_of by blast
    show "\<exists>u\<in> ?Q. \<forall>q\<in>C. (q, u)\<in>R"
      proof(cases "C = {}")
        case True
        then show ?thesis  using A2 A7   using A10 reflE1 by force
      next
        case False
        have B3:"C \<noteq> {}"   by (simp add: False)
        have B4:"\<And>x y. x \<in> C \<and> y \<in> C \<longrightarrow> (\<exists>z \<in> C. (x,z)\<in>R \<and> (y, z)\<in>R)"
        proof
          fix x y assume A10:"x \<in> C \<and>  y \<in> C"
          have B1:"(x, y) \<in> relation_of ((\<lambda>x y. (x, y) \<in> R)) ?Q \<or> (y, x) \<in> relation_of ((\<lambda>x y. (x, y) \<in> R)) ?Q" using Chains_def[of " relation_of ((\<lambda>x y. (x, y) \<in> R)) ?Q"] A8 A10 by auto
          have B2:"(x, y)\<in>R \<or> (y, x)\<in>R" using B1  relation_of_def[of "((\<lambda>x y. (x, y) \<in> R))" "?Q"] by blast
          show "(\<exists>z \<in> C. (x,z)\<in>R \<and> (y, z)\<in>R)"  using A10 B2    by (meson B0 assms(11) reflE1 subset_iff) 
        qed
        have B5:"is_dir C R" by (simp add: B4 is_dirI1)
        have B6:"C \<subseteq> ?Q"    using A8 Chains_relation_of by blast
        have B7:"Sup R X C \<in> ?Q" using A0 A1 A2 A3 A4 A5 A6 A7 B3 B5 B6  mirred_temp1[of R X a b k C]     using A10 A9 assms(9) by fastforce 
        have B8:"\<forall>c  \<in> C. (c, Sup R X C)\<in>R"
          by (meson A0 A9 B0 False assms(9) clatD41 is_supD1121)  
        then show ?thesis    using B7 by blast 
    qed
  qed
qed

lemma mirred_temp2c:
  assumes A0:"is_clattice R X" and
          A1:"compactly_generated R X" and
          A2:"a \<in> X" and
          A3:"b \<in> X" and 
          A4:"\<not>((b,a)\<in>R)" and
          A5:"is_compact R X k" and
          A6:"(k,b)\<in>R" and
          A7:"\<not>((k,a)\<in>R)" and
          A8:"m \<in> {q \<in> X. (a,q)\<in>R \<and> \<not> ((k,q)\<in>R)} \<and> ( \<forall>q \<in> {q \<in> X. (a,q)\<in>R \<and> \<not> ((k,q)\<in>R)}.  (m,q)\<in>R \<longrightarrow> q = m)" and
          A9:"antisym R X" and
          A10:"trans R X" and
          A11:"refl R X" 
  shows "\<not>(meet_reducible R X m)"
proof(rule ccontr)
  let ?Q="{q \<in> X. (a,q)\<in>R \<and> \<not> ((k,q)\<in>R)}"
  assume P:"\<not>\<not>(meet_reducible R X m)"
  obtain P1:"meet_reducible R X m"  using P by auto
  have B0:"\<And>x. x \<in> X \<and> (m, x)\<in>R \<and> (m \<noteq> x) \<longrightarrow> (k,x)\<in>R"
  proof
    fix x assume A9: "x \<in> X \<and> (m, x)\<in>R \<and> (m \<noteq> x)"
    have B01:"x \<notin> ?Q" using A8 A9 nless_le by blast 
    have B02:"(a, x) \<in> R"  using A8 A9  by (metis (mono_tags, lifting) A10 A2 mem_Collect_eq trans_onD) 
    show "(k,x)\<in>R" using A9 B01 B02 by blast
  qed
  have B1:"m=Inf R X {x \<in> X. (m,x)\<in>R \<and> (m \<noteq> x)}"  using A0 A8 P meet_reduction2  A10 A11 A9 by fastforce 
  have B2:"k \<in> lbd R X {x \<in> X.(m,x)\<in>R \<and> (m \<noteq> x)}"   by (metis (mono_tags, lifting) A5 B0 compactD2 converseI mem_Collect_eq ubdI) 
  obtain B20:"m \<in> X"   using A8 by blast 
  obtain B21:"is_inf R X  {x \<in> X. (m,x)\<in>R \<and> (m \<noteq> x)} m"  by (simp add: A0 A10 A11 A9 B20 P1 meet_reduction3)
  have B3:"(k, m)\<in>R"  using B2 B21 is_supE3 by fastforce 
  show False  using A8 B3 by blast
qed

lemma mirred_temp2d:
  assumes A0:"is_clattice R X" and 
          A1:"compactly_generated R X" and
          A2:"a \<in> X" and
          A3:"b \<in> X" and 
          A4:"\<not>((b,a)\<in>R)"and
          A5:"antisym R X" and
          A6:"trans R X" and
          A7:"refl R X" 
  obtains m where "m \<in> X" "meet_irr R X m" "(a, m)\<in>R" "\<not> ((b, m)\<in>R)"
proof-
  obtain k where B0:"k \<in> compact_elements R X" and  B1:"(k, b)\<in>R" and B2: "\<not> ((k,a)\<in>R)"  using A0 A1 A2 A3 A4 compactly_generated_meets by (metis A5 A6 A7)
  have B0b:"is_compact R X k" using B0 compact_elements_mem_iff1   by fastforce
  obtain m where B3:"m \<in> {q \<in> X. (a,q)\<in>R \<and> \<not> ((k,q)\<in>R)} \<and> (\<forall>q \<in> {q \<in> X. (a,q)\<in>R \<and> \<not> ((k,q)\<in>R)}.  (m,q)\<in>R \<longrightarrow> q = m)" using A0 A1 A2 A3 A4 B0b B1 B2 mirred_temp2b[of R X a b k]  A5 A6 A7 by blast
  have B4:"\<not>(meet_reducible R X m)" using mirred_temp2c[of R X a b  k m] A0 A1 A2 A3 A4 B0b B1 B2 B3 A5 A6 A7 by blast
  show ?thesis  using B1 B3 B4   by (metis (mono_tags, lifting) A3 A6 B0b compactD2 mem_Collect_eq that trans_onD) 
qed

lemma mirred_temp3:
  assumes A0:"is_clattice R X" and
          A1:"compactly_generated R X" and 
          A2:"a \<in> X" and
          A3:"antisym R X" and
          A4:"trans R X" and
          A5:"refl R X" 
  shows "a = Inf R X {m \<in> X. meet_irr R X m \<and> (a, m)\<in>R}"
proof-
  let ?M="{m \<in> X. meet_irr R X m \<and> (a, m)\<in>R}" 
  obtain top where top:"is_greatest R X top" using A0 clatD1 csupD3 by blast
  obtain B0:"?M \<subseteq> X" and B1:"top \<in> ?M" and B2:"?M \<noteq> {}" by (metis (no_types, lifting) A2 A3 empty_iff greatestD11 greatestD14 mem_Collect_eq mredD2 subsetI top) 
  obtain b where idef:"is_inf R X ?M b"  using A0 B0 clatD22  A3 A4 by blast 
  have B4:"(a, b)\<in>R"  using A2 idef is_supE4 ub_def   by (metis (no_types, lifting) converseD converseI mem_Collect_eq) 
  have B5: "\<not>((a,b)\<in>R \<and> a \<noteq> b)"
  proof(rule ccontr)
    assume B5dneg:"\<not> \<not> ((a,b)\<in>R \<and> a \<noteq> b)" obtain B5neg:"(a,b)\<in>R \<and> a \<noteq> b"  using B5dneg by auto
    obtain m where B50:"m \<in> X" and B51:"meet_irr R X m" and  B52:"(a, m)\<in>R" and B53:"\<not> ((b, m)\<in>R)"   by (meson A0 A1 A2 A3 A4 A5 B5neg antisym_onD idef is_supE1 mirred_temp2d) 
    have B54:"m \<in> ?M"   by (simp add: B50 B51 B52)
    have B55:"(b, m)\<in>R"   using B54 idef is_supD1121 by fastforce 
    show False
      using B53 B55 by auto
  qed
  have "a = b"  using B4 B5 nless_le by blast
  show ?thesis  using A3 B4 B5 idef inf_equality by fastforce
qed

lemma lattice_equality_sup:
  assumes A0:"is_lattice R X" and A1:" antisym R X"  and A2:"trans R X" and A3:"refl R X" and A4:"F \<subseteq>X" and A5:"finite F" and A6:"F \<noteq> {}" and A7:"Sup R X F = s"
  shows "is_sup R X F s"
  using A0 A1 A2 A4 A5 A6 A7 bsup_finite2 lattD4 by blast

lemma lattice_equality_inf:
  assumes A0:"is_lattice R X" and A1:" antisym R X"  and A2:"trans R X" and A3:"refl R X" and A4:"F \<subseteq>X" and A5:"finite F" and A6:"F \<noteq> {}" and A7:"Inf R X F = i"
  shows "is_inf R X F i"
  by (metis A0 A1 A2 A3 A4 A5 A6 A7 inf_equality l_fininf)

lemma meet_irr_imp_fmeet_irr:
  "\<lbrakk>m \<in> X; is_lattice R X; antisym R X; trans R X; refl R X; meet_irr R X m\<rbrakk> \<Longrightarrow> fin_inf_irr R X m"
proof-
  assume A0:"m \<in> X" and A1:"is_lattice R X" and A2:"antisym R X" and A3:"trans R X" and A4:"refl R X" and A5:"meet_irr R X m"
  have B0:"\<And>a b. a \<in> X \<and> b \<in> X \<and>  m = Inf R X {a, b} \<longrightarrow> m = a \<or> m = b"
  proof
    fix a b assume A6:" a \<in> X \<and> b \<in> X \<and>  m = Inf R X {a, b} "
    have B1:" {a, b} \<in> Pow_ne X"   by (simp add: A6 pow_ne_iff2)
    have B10:"{a, b} \<subseteq> X"  using B1 pow_neD1 by blast
    have B11:"finite {a, b}" by simp
    have B12:"{a,b} \<noteq> {}" by auto
    have B2:"is_inf R X {a, b} m" using lattice_equality_inf[of R X "{a,b}" m]   by (simp add: A1 A2 A3 A4 A6)
    have B3:"m \<in> {a, b}"    by (metis A5 B1 B2 mredI1) 
    show "m = a \<or> m = b"  using B3 by fastforce
  qed
  show "fin_inf_irr R X m"
    by (meson B0 fin_inf_irrI1)
qed

lemma pfilters_metofprimes:
  assumes A0:"distributive_lattice R X" and 
          A1:"is_greatest R X top" and
          A2:"F \<in> pfilters_on R X" and
          A3:"antisym R X" and
          A4:"trans R X" and
          A5:"refl R X" 
  obtains M where "\<forall>Fm. Fm \<in> M \<longrightarrow> Fm \<in> filters_on R X \<and> meet_irr (pwr X) (filters_on R X) Fm " and "F = Inf (pwr X) (filters_on R X) M"
proof-
  let ?FX="(filters_on R X)" let ?RX="pwr X"
  have B0:"compactly_generated ?RX ?FX"  using A0 A1 A3 A4 A5  distr_latticeD5 filters_on_lattice_compactgen lattD1 by metis
  have B1:"is_clattice ?RX ?FX"  using A0 A1 A3 A4 A5  distr_latticeD5 lattice_filters_complete by metis
  have B2:"F \<in> ?FX" by (simp add: A2 filters_on_iff pfilters_memD1)
  have B3:"F = Inf ?RX ?FX {Fm \<in> ?FX. meet_irr ?RX ?FX Fm \<and> (F, Fm)\<in>?RX}" using mirred_temp3[of ?RX ?FX F] B0 B1 B2  by (meson filters_is_clr1 powrel3 powrel6 powrel7 refl_def refl_onD subset_iff)
  have B4:"\<forall>Fm.  Fm \<in> {Fm \<in> ?FX. meet_irr ?RX ?FX Fm \<and> (F,Fm)\<in>?RX} \<longrightarrow> Fm \<in> ?FX \<and> meet_irr ?RX ?FX Fm "  by fastforce
  then show ?thesis  using B3 that by blast
qed

lemma sup_prime_pfilterI3:
  assumes A0:"distributive_lattice R X" and 
          A1:"antisym R X" and 
          A2:"trans R X" and 
          A3:"refl R X" and
          A4:"fin_inf_irr (pwr X) (filters_on R X) F" and 
          A5:"is_pfilter R X F"
  shows "sup_prime R X F"
proof-
  let ?R="pwr X" let ?X="filters_on R X" 
  obtain C1:"antisym ?R ?X" and C2:"refl ?R ?X" and C3:"trans ?R ?X"  by (meson filters_is_clr1 powrel6 powrel7 powsimp1 pwr_mem_iff reflI1 subset_refl)
  obtain C4:"F \<in> ?X"  by (simp add: A5 filters_on_iff is_pfilterD1)
  obtain C5:"distributive_lattice ?R ?X"    by (simp add: A0 A1 A2 A3 lattice_filters_distr)
  have B0:"elem_inf_prime ?R ?X F" using elem_inf_primeI3[of ?R ?X F] C1 C2 C3 C4 C5 A4 by blast
  have B1:"(\<And>F1 F2. \<lbrakk>F1 \<in> ?X; F2 \<in> ?X; (Inf ?R ?X {F1, F2}, F)\<in>(pwr X)\<rbrakk> \<Longrightarrow> (F1, F)\<in>?R \<or> (F2, F)\<in>?R)" by (meson B0 elem_inf_primeD1)
  have B2:"(\<And>F1 F2. \<lbrakk>is_filter R X  F1; is_filter R X  F2; F1 \<inter> F2 \<subseteq> F\<rbrakk> \<Longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F)"   by (metis A0 A1 A2 A3 A5 B1 distr_latticeD5 filters_lattice_inf_op filters_on_iff is_pfilterD3 powrel8 pwr_memI) 
  show ?thesis by (simp add: A0 A1 A2 A3 A5 B2 distr_latticeD5 sup_prime_pfilterI2) 
qed

lemma prime_filter_irr3_converse:
  "\<lbrakk>distributive_lattice R X; antisym R X; trans R X; refl R X; fin_inf_irr (pwr X) (filters_on R X) F; is_pfilter R X F\<rbrakk> \<Longrightarrow> sup_prime R X F"  by (simp add: is_pfilterI1 sup_prime_pfilterI3)


lemma pfilters_metofprimes2:
  assumes A0:"distributive_lattice R X" and
          A1:"is_greatest R X top" and
          A2:"F \<in> pfilters_on R X" and
          A3:"antisym R X" and 
          A4:"trans R X" and 
          A5:"refl R X"
  obtains M where "\<forall>Fm. Fm \<in> M \<longrightarrow> Fm \<in> filters_on R X \<and> sup_prime R X Fm " and "F = Inf (pwr X) (filters_on R X) M"
proof-
  let ?FX="(filters_on R X)" let ?RX="pwr X"
  have B0:"compactly_generated ?RX ?FX"   using A0 A1 A3 A4 A5 distr_latticeD5 filters_on_lattice_compactgen lattD1 by metis
  obtain C1:"antisym ?RX ?FX" and C2:"refl ?RX ?FX" and C3:"trans ?RX ?FX"  by (meson filters_is_clr1 powrel6 powrel7 powsimp1 pwr_mem_iff reflI1 subset_refl)
  obtain C4:"distributive_lattice ?RX ?FX"  by (simp add: A0 A3 A4 A5 lattice_filters_distr)
  have B1:"is_clattice ?RX ?FX"  using A0 A1 A3 A4 A5 distr_latticeD5 lattice_filters_complete by metis
  have B2:"F \<in> ?FX" by (simp add: A2 filters_on_iff pfilters_memD1)
  have B3:"F = Inf ?RX ?FX {Fm \<in> ?FX. meet_irr ?RX ?FX Fm \<and> (F, Fm)\<in>?RX}" using mirred_temp3[of ?RX ?FX F] B0 B1 B2  by (meson filters_is_clr1 powrel3 powrel6 powrel7 refl_def refl_onD subset_iff)
  have B4:"\<And>Fm.  Fm \<in> {Fm \<in> ?FX. meet_irr ?RX ?FX Fm \<and> (F, Fm)\<in>?RX} \<Longrightarrow> Fm \<in> ?FX \<and> sup_prime R X Fm " 
  proof-
    fix Fm assume A6:"Fm \<in> {Fm \<in> ?FX. meet_irr ?RX ?FX Fm \<and>(F, Fm)\<in>?RX}" 
    have B40:"Fm \<in> ?FX \<and> meet_irr ?RX ?FX Fm"  using A6 by blast
    have B41:"fin_inf_irr ?RX ?FX Fm" using A0 B40 distr_lattice_filters meet_irr_imp_fmeet_irr[of Fm ?FX ?RX] A4 A5 C1 C2 C3 A3 by blast
    have B43:"is_greatest ?RX ?FX X"  
    proof-
      have B430:"X \<in> ?FX"    by (metis A0 distr_latticeD5 filters_is_clr1b lattD41)
      have B431:"X \<in> ubd ?RX ?FX ?FX"   by (meson B430 C2 pwr_mem_iff reflD2 ubdI)
      show ?thesis   by (simp add: B431 is_greatest_def)
    qed
    have B44:"sup_prime R X Fm"
    proof(cases "is_pfilter R X Fm")
      case True then show ?thesis using A0 B40 B41 filters_on_iff prime_filter_irr3_converse sup_prime_def A3 A4 A5 by blast
    next
      case False obtain B45:"Fm = X"  using B40 False filters_on_iff    using is_pfilter_def by blast 
      then show ?thesis using sup_primeI1   by metis
    qed
    show "Fm \<in> ?FX \<and> sup_prime R X Fm"  by (simp add: B40 B44)
  qed
  then show ?thesis  using B3 that by blast
qed


section FilterOfSets

lemma setfilters0:
  "is_filter (pwr X) (Pow X) EF \<Longrightarrow> F \<in> EF \<Longrightarrow> F \<subseteq> X"
  using filterD2 by blast

lemma setfilters1:
  assumes A0:"is_filter (pwr X) (Pow X) EF" and A1:"F1 \<in> EF" and A2:"F2 \<in> EF"
  shows "F1 \<inter> F2 \<in> EF"
proof-
  have B0:"is_inf (pwr X) (Pow X) {F1, F2} (F1 \<inter> F2)" by (meson A0 A1 A2 PowI binf_powrrel setfilters0)
  then show "(F1 \<inter> F2) \<in> EF"   by (meson A0 A1 A2 filter_finf_closed)
qed
       

lemma setfilters2:
  assumes A0:"is_filter (pwr X) (Pow X) EF" and A1:"A \<in> EF" and A2:"B \<in> Pow X" and A3:"A \<subseteq> B"
  shows "B \<in> EF"
  by (meson A0 A1 A2 A3 PowD filter_memI pwr_mem_iff)

lemma setfilters3:
  "is_pfilter (pwr X) (Pow X) EF \<longleftrightarrow> (is_filter (pwr X) (Pow X) EF) \<and> (EF \<noteq> (Pow X))"
  using is_pfilter_def by blast


lemma pfilter_sets:
  assumes A0:"F \<subseteq> Pow X" and 
          A1:"F \<noteq> {}" and
          A2:"F \<noteq> Pow X" and
          A3:"(\<And>A B. \<lbrakk>A \<in> F; B \<in> F\<rbrakk> \<Longrightarrow> A \<inter> B \<in> F)" and
          A4:"(\<And>A B. \<lbrakk>A \<in> F; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> B \<in> F)" 
  shows "is_pfilter (pwr X) (Pow X) F "
  apply(rule is_pfilterI1)
  apply(rule filterI1, simp add:A1, simp add:A0)
  proof-
  show "is_dir F (dual (pwr X))"
    apply(rule is_dirI1)
    proof-
        fix A B assume "A \<in> F" "B \<in> F"
        then obtain "A \<inter> B \<in> F \<and> A \<inter> B \<subseteq> A \<and>  A \<inter> B \<subseteq> B" using A3[of A B] by simp
        then show "\<exists>c\<in>F.  (A, c) \<in> dual (pwr X) \<and> (B, c) \<in> dual (pwr X)"
          by (meson A0 \<open>(A::'a::type set) \<in> (F::'a::type set set)\<close> \<open>(B::'a::type set) \<in> (F::'a::type set set)\<close> converse_iff powsimp1 pwr_mem_iff)
    qed
  show "is_ord_cl (Pow X) F (pwr X)"   using A4 is_ord_clI1 by (metis powrel8) 
  show "Pow X \<noteq> F"   using A2 by auto
qed

lemma sets_pfilter:
  assumes "is_pfilter (pwr X) (Pow X) F"
  shows A1:"F \<noteq> {}" and
        A2:"F \<noteq> Pow X" and
        A3:"(\<And>A B. \<lbrakk>A \<in> F; B \<in> F\<rbrakk> \<Longrightarrow> A \<inter> B \<in> F)" and
        A4:"(\<And>A B. \<lbrakk>A \<in> F; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> B \<in> F)"
  using assms filterD1 is_pfilterD1 apply auto[1]
  using assms is_pfilter_def apply blast 
  proof-
    show "\<And>(A::'a set) B::'a set. A \<in> F \<Longrightarrow> B \<in> F \<Longrightarrow> A \<inter> B \<in> F"
  proof-
      have B0: "is_dir F (dual (pwr X))"  using assms filterD3 is_pfilter_def by blast
      fix A B assume "A \<in> F" "B \<in> F"
      then have B1:"\<exists>c\<in>F.  (A, c) \<in> dual (pwr X) \<and> (B, c) \<in> dual (pwr X)"  using B0 is_dirE1[of F "pwr X" A B]  by (meson is_dirE1)
      then obtain C where "C \<in> F" "C \<subseteq> A" "C \<subseteq> B"   by (metis converse.simps pwr_memD) 
      then have B2:"C \<in> F \<and> C \<subseteq> A \<inter> B" by blast
      also have B3:"A \<inter> B \<in> Pow X"
        by (meson Pow_iff \<open>(A::'a::type set) \<in> (F::'a::type set set)\<close> assms in_mono inf.coboundedI1 is_pfilterD3)
      then show "A \<inter> B \<in> F"
        using \<open>(A::'a::type set) \<in> (F::'a::type set set)\<close> \<open>(B::'a::type set) \<in> (F::'a::type set set)\<close> assms is_pfilterD1 setfilters1 by blast  
    qed
    show "\<And>(A::'a set) B::'a set. A \<in> F \<Longrightarrow> B \<in> Pow X \<Longrightarrow> A \<subseteq> B \<Longrightarrow> B \<in> F"
      using assms  is_pfilterD1  by (metis setfilters2) 
  show "F \<noteq> Pow X"  using assms is_pfilter_def by blast
qed
 
lemma pfilter_sets_comp:
  assumes A0:"is_pfilter (pwr X) (Pow X) F" and A1:"(X-A) \<in> F"
  shows "A \<notin> F"
proof(rule ccontr)
  assume "\<not>(A \<notin> F)"
  then have  "A \<in> F" by simp
  then have "(X-A) \<inter> A \<in> F"  using A0 A3 is_pfilterI1 local.A1 by blast
  then have "{} \<in> F"  by (simp add: Int_commute)
  then have "F=Pow X"
    by (meson A0 empty_subsetI filterD2 is_pfilterD1 setfilters2 subset_antisym subset_iff)
  then show False using A0   by (simp add: is_pfilter_def)
qed
    
lemma pfilters_sets_comp2:
   "is_pfilter (pwr X) (Pow X) F \<Longrightarrow> A \<in> F \<Longrightarrow> (X-A) \<notin> F"
  using pfilter_sets_comp by blast

lemma pfilters_sets_comp3:
   "\<lbrakk>is_pfilter (pwr X) (Pow X) F; A \<subseteq> X; \<exists>U \<in> F. U \<inter> (X-A) = {}\<rbrakk> \<Longrightarrow> A \<in> F"
  by (metis Diff_Diff_Int Diff_mono Diff_triv PowI inf.absorb_iff2 order.order_iff_strict setfilters0 setfilters2 setfilters3)


lemma principal_filter_sets:
  "x \<in> X \<Longrightarrow> is_filter (pwr X) (Pow X) (lorc (pwr X) (Pow X) {x})"
  by (meson Pow_iff empty_subsetI insert_subsetI lorc_filter powrel1 powrel2 pwr_memI reflI1 subset_refl)

lemma principal_pfilter_sets:
  "x \<in> X \<Longrightarrow> is_pfilter (pwr X) (Pow X) (lorc (pwr X) (Pow X) {x})"
  by (metis Pow_bottom empty_not_insert empty_subsetI equalityI is_pfilterI1 lorcD12 principal_filter_sets pwr_mem_iff)


lemma pmb_filters2:
  assumes A0:"is_pfilter (pwr X) (Pow X) F" and
          A1:"\<And>x. x \<in> (Pow X) \<Longrightarrow> (x \<in> F \<or> (X-x) \<in> F) \<and> \<not>(x \<in> F \<and> (X-x) \<in> F)"
  shows "is_maximal (pwr (Pow X)) (pfilters_on (pwr X) (Pow X)) F"
proof-
  let ?X="Pow X" let ?R="(pwr X)"
  have B0:"F \<in> pfilters_on ?R ?X"  using A0 is_pfilter_def  by (simp add: pfilters_memI)
  have B1:"\<And>G. \<lbrakk>G \<in> filters_on ?R ?X;  F \<subset> G \<rbrakk> \<Longrightarrow> G = ?X"
  proof-
    fix G assume A2:"G \<in> filters_on ?R ?X" and A3:"F \<subset> G"
    obtain z where B10: "z \<in> G - F"  using A3 by auto
    have B11:"z \<notin> F" using B10 by blast 
    have B12:"X-z \<in> F"  by (meson A1 A2 B10 Diff_iff filterD21 filters_on_iff)
    have B13:"X-z \<in> G \<and> z \<in> G"  using A3 B10 B12 by blast
    have B14:"is_filter ?R ?X G"   using A2 filters_on_iff by auto
    show "G=?X"  using B13 B14    using is_pfilterI1 pfilters_sets_comp2 by blast 
  qed
  have B2:"\<And>G. \<lbrakk>G \<in> pfilters_on ?R ?X;  F \<subseteq> G \<rbrakk> \<Longrightarrow> G = F" using B1   by (metis filters_on_iff is_pfilter_def pfilters_memD0 psubsetI)
  show ?thesis  by (metis B0 B2 maximal_pfiltersI1)
qed

lemma finer_proper_filter:
  assumes A0:"is_pfilter (pwr X) (Pow X) F" and A1:"A \<in> Pow X" and A2:"\<forall>B \<in> F. B \<inter> A \<noteq> {}"
  defines "H \<equiv> {E \<in> Pow X. \<exists>B \<in> F. A \<inter> B \<subseteq> E}" 
  shows "is_pfilter (pwr X) (Pow X) H" and "F \<subseteq> H"
proof-
  let ?X="Pow X" let ?R="(pwr X)"
  show "is_pfilter ?R ?X H"
  proof(rule is_pfilterI1)
    show "is_filter ?R ?X H"
    apply(rule filterI1)
      using A0 H_def filterD1 is_pfilterD1 local.A1 apply fastforce
      using H_def  apply blast
      proof(rule is_dirI1)
        show "\<And>(a::'a set) b::'a set. a \<in> H \<Longrightarrow> b \<in> H \<Longrightarrow> \<exists>c::'a set\<in>H. (a, c) \<in> dual (pwr X) \<and> (b, c) \<in> dual (pwr X)"
        proof-
          fix a b assume A3:"a \<in> H" and A4:"b \<in> H"
          obtain aB bB where B0:"aB \<in> F" and B1:"bB \<in> F" and B2:"A \<inter> aB \<subseteq> a" and B3:"A \<inter> bB \<subseteq> b"  using H_def local.A3 local.A4 by auto
          obtain B4:"aB \<inter> bB \<in> F"  using A0 B0 B1 A3 by (simp add: Posets19.A3) 
          obtain B5:"A \<inter> aB \<inter> bB \<in> H"    using B2 B4 H_def local.A3 by blast
          also have B6:"A \<inter> aB \<inter> bB \<subseteq> a \<and> A \<inter> aB \<inter> bB \<subseteq> b"    using B2 B3 by blast
          then show " \<exists>c::'a set\<in>H. (a, c) \<in> dual (pwr X) \<and> (b, c) \<in> dual (pwr X)"   using calculation
            by (metis (no_types, lifting) H_def PowD converse_iff local.A3 local.A4 mem_Collect_eq pwr_memI)
        qed
        show "is_ord_cl (Pow X) H (pwr X)"
        apply(rule is_ord_clI1) using H_def inf.absorb_iff2 powrel8 by fastforce 
      qed
  show "Pow X \<noteq> H"
    proof-
      have B7:"{} \<notin> H"   by (simp add: H_def Int_commute local.A2)
      then show ?thesis by blast
     qed
  qed
  show "F \<subseteq> H"
  proof
    fix f assume A4:"f \<in> F"
    have B8:"X \<in> F"
      by (meson A0 Pow_top is_pfilterD1 is_pfilterD3 local.A4 powsimp1 setfilters2) 
    also have B9:"X \<inter> f \<subseteq> f" by simp
    then show "f \<in> H"  using A0 H_def is_pfilterD3 local.A4 by force
  qed
qed

lemma principal_ufilter_sets:
  "x \<in> X \<Longrightarrow> is_maximal (pwr (Pow X)) (pfilters_on (pwr X) (Pow X)) (lorc (pwr X) (Pow X) {x})"
  apply(rule pmb_filters2)
  apply (simp add: principal_pfilter_sets)
  by (simp add: lorc_mem_iff1 pwr_mem_iff)

unused_thms

end
