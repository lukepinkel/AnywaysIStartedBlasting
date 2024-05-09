theory PosetsRel3
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

definition Pow_ne::"'a set \<Rightarrow> 'a set set" where 
  "Pow_ne X = Pow X - {{}}"

definition Fpow_ne::"'a set \<Rightarrow> 'a set set" where 
  "Fpow_ne X = Fpow X - {{}}"

lemma Pow_ne_iff[iff]:
  "A \<in> Pow_ne X \<longleftrightarrow> (A \<subseteq> X) \<and> (A \<noteq> {})"
  by (simp add:Pow_ne_def)

lemma Fpow_ne_iff[iff]:
  "A \<in> Fpow_ne X \<longleftrightarrow>  A \<subseteq> X \<and> finite A \<and> A \<noteq> {}"
  by(simp add: Fpow_ne_def Fpow_def) 

lemma leq_iff_leq_eq:
  "\<lbrakk>a \<in> X; b \<in> X; antisym_on X R; (a, a) \<in> R; (b, b) \<in> R\<rbrakk> \<Longrightarrow> (\<forall>x \<in> X. (x, a) \<in> R \<longleftrightarrow> (x, b)\<in>R) \<Longrightarrow> a =b" 
  by (simp add: antisym_onD)

lemma geq_iff_geq_eq:
  "\<lbrakk>a \<in> X; b \<in> X; antisym_on X R;(a, a) \<in> R; (b, b) \<in> R\<rbrakk> \<Longrightarrow> (\<forall>x \<in> X. (a, x) \<in> R \<longleftrightarrow> (b, x) \<in> R) \<Longrightarrow> a =b" 
  by (simp add: antisym_onD)


section Definitions
subsection Bounds

definition ubd::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where  
  "ubd R X A \<equiv> {b \<in> X.  (\<forall>a. a \<in> A \<longrightarrow> (a, b) \<in> R)}"

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

abbreviation semitop where
  "semitop R X top \<equiv> is_inf_semilattice R X \<and> is_greatest R X top"

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

definition filters_on::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "filters_on R X \<equiv> {F. is_filter R X F}"

definition pfilters_on::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "pfilters_on R X \<equiv> {F. is_pfilter R X F}"

definition filter_closure::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where 
  "filter_closure R X A \<equiv> {x \<in> X. \<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and> (Inf R X F,  x) \<in> R}"

definition binary_filter_sup::"'a rel \<Rightarrow> 'a set \<Rightarrow>'a set\<Rightarrow> 'a set \<Rightarrow> 'a set" where 
  "binary_filter_sup R X A B = {x \<in> X. \<exists>a \<in> A. \<exists>b \<in> B. (Inf R X {a, b}, x) \<in> R}"

definition lcro::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a set" where 
  "lcro R X a \<equiv> {y \<in> X. (a, y) \<in> R} "

abbreviation lorc where 
  "lorc R X a \<equiv> lcro (converse R) X a"

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


definition mesh::"'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" (infixl "(#)" 70)
   where "A # B \<equiv> (\<forall>a. \<forall>b. a \<in> A \<longrightarrow> b \<in> B \<longrightarrow> a \<inter> b \<noteq> {})"

definition grill::"'a set set \<Rightarrow> 'a set set \<Rightarrow> 'a set set" 
  where "grill PX A \<equiv> {E \<in> PX. {E}#A}"

definition pwr  where
    "pwr X \<equiv> {(A, B). A \<subseteq> X \<and> B \<subseteq> X \<and> A \<subseteq> B}"


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

lemma refl_empty1:
  "refl {} {}"
  by (simp add: refl_def)

lemma refl_empty2:
  "refl R {}"
  by (simp add: refl_def)

lemma refl_singleton:
  "refl  {(x,x)} {x}"
  by (simp add: refl_def)

lemma refl_in:
  "(\<And>i. i \<in> I \<Longrightarrow> refl (R i) (X i)) \<Longrightarrow> refl (\<Inter>(R`I)) (\<Inter>(X`I))"
  by (simp add: refl_def)

lemma refl_un:
  "(\<And>i. i \<in> I \<Longrightarrow> refl (R i) (X i)) \<Longrightarrow> refl (\<Union>(R`I)) (\<Union>(X`I))"
  by(rule reflI1, auto dest: reflD2)


lemma pwr_memI:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> X; A \<subseteq> B\<rbrakk> \<Longrightarrow> (A,B)\<in>pwr X"
  by (simp add:pwr_def)

lemma pwr_memD:
  "(A,B)\<in>pwr X \<Longrightarrow> A \<subseteq> X \<and> B \<subseteq> X \<and> A \<subseteq> B"
  by (simp add:pwr_def)

lemma ubdI1:
  "\<lbrakk>b \<in> X; (\<And>a. a \<in> A \<Longrightarrow>(a, b) \<in> R)\<rbrakk>\<Longrightarrow>b \<in> ubd R X A"
  by (simp add:ubd_def)

lemma ubd_space:
  "ubd R X A \<subseteq> X"
  by (simp add:ubd_def)

lemma ubdD1:
  "b \<in> ubd R X A \<Longrightarrow> b \<in> X"
  by (simp add:ubd_def)

lemma ubdD2:
  "\<lbrakk>b \<in> ubd R X A; a \<in> A\<rbrakk> \<Longrightarrow> (a,b)\<in>R \<and> b \<in> X "
  by (simp add:ubd_def)

lemma ubd_empty:
  "ubd R X {} = X"
  unfolding ubd_def by simp

lemma ubd_snd_anti:
  "\<lbrakk>A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> ubd R X B \<subseteq> ubd R X A"
  unfolding ubd_def by auto

lemma ubd_fst_iso:
  "\<lbrakk>Y \<subseteq> X\<rbrakk> \<Longrightarrow> ubd R Y A \<subseteq> ubd R X A"
  unfolding ubd_def by auto

lemma ubd_snd_anti1:
  assumes ab:"(A,B)\<in>pwr X" and bx:"(B,X)\<in>pwr X"
  shows "(ubd R X B, ubd R X A)\<in>pwr X"
proof-
  obtain "A \<subseteq> B" and "B \<subseteq> X"
    using ab pwr_memD by blast
  then obtain "ubd R X B \<subseteq> ubd R X A"
    by (simp add: ubd_snd_anti)
  then show "(ubd R X B, ubd R X A)\<in>pwr X"
    by (simp add: pwr_memI ubd_space)
qed

lemma ubd_fst_iso1:
  assumes yx:"(Y,X)\<in>pwr X" 
  shows " (ubd R Y A,ubd R X A)\<in>pwr X"
proof-
  obtain sub:"Y \<subseteq> X"
    using pwr_memD yx by blast 
  then obtain "ubd R Y A \<subseteq> ubd R X A" and "ubd R X A \<subseteq> X"
    by (simp add: ubd_fst_iso ubd_space)
  also obtain "ubd R Y A \<subseteq> X"
    unfolding ubd_def using sub by blast
  then show "(ubd R Y A, ubd R X A)\<in>pwr X"
    by (simp add: calculation(1) calculation(2) pwr_memI)
qed

lemma ubd_singleton:
  "ubd R X {x} = {b \<in> X. (x, b) \<in> R}"
  by (simp add: ubd_def)

lemma ubd_singleton_mem:
  "b \<in> ubd R X {x} \<longleftrightarrow> b \<in> X \<and> (x, b) \<in> R"
  by (simp add: ubd_def)

lemma ubd_iso3:
  assumes A0:"x1 \<in>X" and A1:"x2 \<in> X" and A2:"(x1,x2)\<in>R" and A3:"trans R X" and A4:"C \<subseteq> X"
  shows "ubd R C {x2} \<subseteq> ubd R C {x1}"
proof
  fix b assume A5:"b \<in> ubd R C {x2}" 
  obtain B0:"(x2,b)\<in>R" and B1:"b \<in> X" and B2:"b \<in> C"
    using A4 A5 ubd_singleton_mem by fastforce
  then obtain B3:"(x1,b)\<in>R" 
    using A0 A1 A2 A3 trans_onD[of X R x1 x2 b] by blast
  then show "b \<in> ubd R C {x1}"
    by (simp add: B2 ubd_singleton_mem)  
qed
  

lemma is_greatestI1:
  "m \<in> ubd R A A \<Longrightarrow> is_greatest R A m"
  by (simp add:is_greatest_def)

lemma is_greatestI2:
  "\<lbrakk>m \<in> A; A \<subseteq> X; m \<in> ubd R X A\<rbrakk> \<Longrightarrow> is_greatest R A m"
  unfolding is_greatest_def ubd_def by blast

lemma is_greatestI3:
  "\<lbrakk>m \<in> A; (\<And>a. a \<in> A \<Longrightarrow> (a,m)\<in>R)\<rbrakk> \<Longrightarrow> is_greatest R A m"
  by (simp add: is_greatestI1 ubdI1)

lemma is_greatestD1:
  "is_greatest R A m \<Longrightarrow> m \<in> A"
  by (simp add: is_greatest_def ubd_def)

lemma is_greatestD2:
  "is_greatest R A m \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (a,m)\<in>R)"
  by (simp add: is_greatest_def ubd_def)

lemma is_greatestD3:
  "is_greatest R A m \<Longrightarrow> m \<in> ubd R A A"
  by (simp add:is_greatest_def)

lemma is_greatestD4:
  "\<lbrakk>is_greatest R A m; a \<in> A\<rbrakk>\<Longrightarrow>(a,m)\<in>R"
  by (simp add: is_greatestD2)

lemma greatestD5:
  "is_greatest R A m \<Longrightarrow> (\<forall>a. a \<in> A \<longrightarrow> (a,m)\<in>R) \<and> m\<in>A"
  by (simp add: is_greatest_def ubd_def)

lemma greatest_unique:
  "\<lbrakk>antisym_on A R; is_greatest R A m1; is_greatest R A m2\<rbrakk> \<Longrightarrow> m1 =m2"
  by (simp add: antisym_onD greatestD5)

lemma greatest_equalityI1:
  "\<lbrakk>antisym_on A R; (\<And>a. a \<in> A \<Longrightarrow> (a, m)\<in>R); m \<in> A\<rbrakk> \<Longrightarrow> Greatest R A = m"
  by (simp add: Greatest_def is_greatestI3 greatest_unique the_equality) 

lemma is_greatest_iso2:
  "A \<subseteq> B \<Longrightarrow> is_greatest R A ma \<Longrightarrow> is_greatest R B mb \<Longrightarrow> (ma, mb)\<in>R"
  by (simp add: greatestD5 in_mono)

lemma is_supI1:
  "is_least R (ubd R X A) m \<Longrightarrow> is_sup R X A m"
  by (simp add: is_sup_def)

lemma is_supI2:
  "\<lbrakk>A \<subseteq>X; m \<in> X;(\<And>a. a\<in>A\<Longrightarrow>(a,m)\<in>R);(\<And>b. b\<in>ubd R X A\<Longrightarrow>(m,b)\<in>R)\<rbrakk>\<Longrightarrow> is_least R (ubd R X A) m"
  by (simp add: is_greatestI3 ubdI1)

lemma is_supI3:
  "\<lbrakk>x\<in>X; (\<And>a. a\<in>A \<Longrightarrow> (a,x)\<in>R); (\<And>b. b\<in>X\<Longrightarrow>(\<And>a. a\<in>A \<Longrightarrow>(a,b)\<in>R)\<Longrightarrow> (x,b)\<in>R)\<rbrakk> \<Longrightarrow> is_sup R X A x"
  unfolding is_sup_def is_greatest_def ubd_def by blast

lemma is_supD1:
  "is_sup R X A x \<Longrightarrow> (x \<in> X) \<and> (\<forall>a. a \<in> A \<longrightarrow> (a,x)\<in>R) \<and> (\<forall>b. b \<in> X \<longrightarrow> (\<forall>a. a \<in> A \<longrightarrow> (a,b)\<in>R) \<longrightarrow> (x,b)\<in>R)"
  unfolding is_sup_def is_greatest_def ubd_def by blast

lemma is_supD2:
  "\<lbrakk>is_sup R X A x; y \<in> ubd R X A\<rbrakk> \<Longrightarrow> (x, y)\<in>R "
  unfolding is_sup_def is_greatest_def ubd_def by blast

lemma is_supD3:
  "\<lbrakk>is_sup R X A x; a \<in> A \<rbrakk> \<Longrightarrow> (a, x) \<in> R"
  by (simp add: is_supD1)

lemma is_supD4:
  "is_sup R X A s \<Longrightarrow> s \<in> X"
  by (simp add: is_supD1)

lemma is_sup_unique:
  "\<lbrakk>antisym_on X R; is_sup R X A m1;  is_sup R X A m2\<rbrakk> \<Longrightarrow> m1 = m2"
  by (simp add: antisym_onD is_supD1)

lemma is_sup_iso1:
  "A \<subseteq> B \<Longrightarrow> is_sup R X A ma \<Longrightarrow> is_sup R X B mb \<Longrightarrow> (ma, mb)\<in>R "
  by (simp add: is_supD1 subset_iff)

lemma is_sup_iso2:
  "A \<subseteq> Y \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> is_sup R Y A my \<Longrightarrow> is_sup R X A mx \<Longrightarrow> (mx, my) \<in> R"
  by (simp add: is_supD1 subsetD)

lemma sup_maxI1:
  "is_sup R X A x \<Longrightarrow> x \<in> A \<Longrightarrow> (is_greatest R A x)"
  by (simp add: is_greatestI3 is_supD1)

lemma sup_maxE1:
  "(is_greatest R A x) \<Longrightarrow> x \<in> X \<Longrightarrow> is_sup R X A x"
  by (simp add: greatestD5 is_supI3)

lemma sup_in_subset:
  "A \<subseteq> B \<Longrightarrow>  B \<subseteq> X \<Longrightarrow> is_sup R X A s \<Longrightarrow> s \<in> B \<Longrightarrow> is_sup R B A s"
  unfolding is_sup_def is_greatest_def ubd_def by blast

lemma sup_empty:
  "is_sup R X {} i \<longleftrightarrow> (is_least R X i)"
  by (simp add: is_sup_def ubd_empty)

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

lemma sup_singleton:
  assumes A0:"antisym R X" and A1:"refl R X" and A2:"x \<in> X"
  shows sup_singleton1:"is_sup R X {x} x" and
        sup_singleton2:"Sup R X {x} = x" 
proof-
  show "is_sup R X {x} x"
    using A1 A2 is_supI3 reflD2 by fastforce 
  then show "Sup R X {x} = x" 
     by (simp add: A0 sup_equality) 
qed      

lemma sup_exI1:
  "\<lbrakk>(\<And>R X A s. is_sup R X A s \<Longrightarrow> P s); antisym R X; is_sup R X A s\<rbrakk> \<Longrightarrow> P (Sup R X A)"
  by (simp add: sup_equality)

lemma sup_exI2:
  "\<lbrakk>antisym_on X R; A \<subseteq> X; (\<exists>s. is_sup R X A s); (\<And>R X A s. is_sup R X A s \<Longrightarrow> P s)\<rbrakk> \<Longrightarrow> P (Sup R X A)"
proof-
assume ant:"antisym R X" and "A \<subseteq> X" and "\<exists>s. is_sup R X A s" and res:"(\<And>R X A s. is_sup R X A s \<Longrightarrow> P s)" 
  then obtain m where iss:"is_sup R X A m" 
    by blast
  then have "P m"
    by (simp add: res)
  then show "P (Sup R X A)"
     using ant iss sup_equality by fastforce
qed



lemma sup_families1:
  assumes A0:"I \<noteq> {}" and A1:"\<forall>i. i \<in> I \<longrightarrow> is_sup R X (A i) (s i)" and A2:"trans R X" and A3:"\<forall>i. i \<in> I \<longrightarrow> A i \<subseteq> X"
  shows "is_sup R X (\<Union>(A`I)) t \<longleftrightarrow> is_sup R X (s`I) t"
proof(rule Upper_eq_sup_eq)
  show "ubd R X (\<Union> (A ` I)) = ubd R X (s ` I)" (is "?L = ?R")
  proof
    show "?L \<subseteq> ?R"
    proof
      fix u assume L:"u \<in> ?L"  
      show "u \<in> ?R" 
      proof(rule ubdI1)
        show "\<And>si. si \<in> s ` I \<Longrightarrow> (si, u) \<in> R"
        proof-
          fix si assume s0:"si \<in> (s ` I)"
          then obtain i where s1:"i \<in> I"  and s2:"si = s i" 
             by blast
          then obtain s3:"is_sup R X (A i) (s i)" 
            using A1 by blast
          have s4:"A i \<subseteq> \<Union> (A ` I)"  
            using s1 by blast
          then show "(si, u)\<in>R"  
            using L s2 s3 ubd_snd_anti[of "A i" "\<Union>(A`I)" X R]
            by (simp add: A3 UN_least in_mono is_supD2) 
        qed
        show "u \<in> X" 
          using L ubdD1[of u R X " \<Union> (A ` I)"] by blast
      qed
    qed
    next show "?R \<subseteq> ?L"
    proof
      fix u assume R:"u \<in> ?R" 
      show "u \<in> ?L" 
      proof(rule ubdI1) 
        show "\<And>x. x \<in> \<Union> (A ` I)  \<Longrightarrow> (x, u) \<in> R"
        proof-
          fix x assume x0:"x \<in> \<Union> (A ` I)"
          then obtain i where x1:"i \<in> I" and x2:"x \<in> A i" 
            by blast
          then obtain x3:"(x, s i)\<in> R" 
            using A1 is_supD3[of R X "A i" "s i" x] by blast
          obtain x4:"(s i, u)\<in>R" 
            using R x1 ubdD1 ubdD2 x1 by fastforce
          obtain x5:"x \<in> X" 
            using A3 x1 x2 by blast
          obtain x6:"s i \<in> X" 
            using A1 is_supD1[of R X "A i" "s i"] x1 by blast
          obtain x7:"u \<in> X" 
            using R ubdD1[of u R X "s ` I"] by blast
          then show "(x, u) \<in> R" 
            using A2 x3 x4 x5 x6 trans_onD[of X R x "s i" u]  by blast 
        qed
        show "u \<in> X" 
          using R ubdD1[of u R X "s ` I"] by blast
      qed
    qed
  qed
qed   

lemma sup_families:
  assumes tran:"trans R X" and anti:"antisym R X" and sub:"(\<And>Ai. Ai \<in> A \<Longrightarrow> Ai \<subseteq> X)" and
          nemp:"A \<noteq> {}" and sups:"(\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_sup R X Ai si)"
  shows "(is_sup R X ((\<lambda>Ai. Sup R X Ai)`A) s) \<longleftrightarrow> (is_sup R X (\<Union>A) s)" 
proof(rule Upper_eq_sup_eq)
  show "ubd R X (Sup R X ` A) = ubd R X (\<Union> A)" (is "?L = ?R")
  proof
    show "?L \<subseteq> ?R"
    proof
      fix u assume L0:"u \<in> ?L"  
      show "u \<in> ?R" 
      proof(rule ubdI1)
        show u0:"u \<in> X"
          using L0 ubdD1[of u R X "(\<lambda>Ai. Sup R X Ai)`A"] by blast
        show "\<And>a. a \<in> \<Union> A \<Longrightarrow> (a, u) \<in> R"
        proof-
          fix a assume a0:"a \<in> \<Union>A"
          then obtain Ai where a1:"Ai \<in> A" and a2:"a \<in> Ai"  
            by blast  
          then obtain sup_ex:"\<exists>si. is_sup R X Ai si" and aisub:"Ai \<subseteq> X"
            by (simp add: sups sub)
          then obtain si where sup_wit:"is_sup R X Ai si"
            by force 
          then obtain "si \<in> X"
            by (simp add: is_supD4)
          then obtain a3:"Sup R X Ai \<in> X"
            using anti sup_equality sup_wit by fastforce
          obtain a4:"a \<in> X" and a5:"u \<in> X"
            using a2 aisub u0 by blast 
          then obtain "(a, si)\<in>R"
            using a2 is_supD3[of R X Ai si a] sup_wit by blast
          then obtain a6:"(a, Sup R X Ai)\<in>R"
            using anti sup_equality sup_wit by force 
          also obtain a7:"(Sup R X Ai, u)\<in>R"
            using L0 a1 ubdD2 by fastforce
          then show a8:"(a,u)\<in>R" 
            using a3 a4 u0 calculation tran trans_onD[of X R a "Sup R X Ai" u]  by blast 
        qed
      qed
   qed
  next
   show "?R \<subseteq> ?L"
   proof
      fix u assume R0:"u \<in> ?R"
      show "u \<in> ?L"
      proof(rule ubdI1)
        show u0:"u \<in> X" 
          using R0 ubdD1[of u R X] by blast
        show "\<And>a. a \<in> Sup R X ` A \<Longrightarrow> (a, u) \<in> R"
        proof-
          fix a assume a0:"a \<in> Sup R X ` A"
          then obtain Ai where a1:"Ai \<in> A" and a2:"a = Sup R X Ai" 
            by blast
          then obtain a3:"is_sup R X Ai a"
            using anti sup_equality sups by fastforce 
          obtain a4:"Ai \<subseteq>  (\<Union> A)" 
            by (simp add: Sup_upper a1)
          then show "(a,u)\<in>R"
            using R0 a3 is_supD1 u0 ubdD2 by fastforce
        qed
      qed
    qed
  qed
qed
         
lemma sup_insert:
  assumes A0:"s1 \<in> X" and A1:"is_sup R X F s1" and A2:"s2 \<in> X" and A3:"is_sup R X {s1, x} s2" and
          A4:"trans R X" and A5:"antisym_on X R" and A6:"(insert x F) \<subseteq> X"
  shows "is_sup R X (insert x F) s2"
proof(rule is_supI1)
  show B0:"s2 \<in> X" by (simp add: A2)
  show B1:"\<And>a. a \<in> insert x F \<Longrightarrow> (a, s2) \<in> R"
  proof-
    fix a assume B10:"a \<in> insert x F"
    show "(a, s2)\<in>R"
    proof(cases "a \<in> F")
      case True then show ?thesis by (meson A0 A1 A3 A4 A6 B0 in_mono insertCI is_supD3 trans_onD)
    next
      case False then obtain "a=x"  using B10 by blast 
      then show ?thesis using A3 is_supD3 by fastforce
    qed
  qed
  show B2:" \<And>b. b \<in> X \<Longrightarrow> (\<And>a. a \<in> insert x F \<Longrightarrow> (a, b) \<in> R) \<Longrightarrow> (s2, b) \<in> R"
  proof-
    fix b assume B20:"b \<in> X" and B21:"(\<And>a. a \<in> insert x F \<Longrightarrow> (a, b) \<in> R)"
    then obtain B22:"(\<And>a. a \<in> {s1, x} \<Longrightarrow> (a, b)\<in>R)"  using A1 is_supD1 by force
    then show "(s2, b) \<in> R"  by (meson A3 B20 is_supD1)
  qed
qed

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
  case (singleton x) then show ?case using A0 by force
next
  case (insert x F)
  obtain s1 where B0:"s1 \<in> X" and B1:"is_sup R X F s1"
    using insert.hyps(4) insert.prems by blast
  obtain s2 where B2:"s2 \<in> X" and B3:"is_sup R X {s1, x} s2"
    by (meson A0 B0 insert.prems insert_subset)
  have B3:"is_sup R X (insert x F) s2"  by (meson A4 A5 B0 B1 B2 B3 insert.prems sup_insert)
  then show ?case using B2 by blast
qed


lemma inf_finite:
  assumes A0:"\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> \<exists>b \<in> X. is_inf R  X {a1, a2} b" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X" and
          A4:"trans R X" and
          A5:"antisym_on X R"
  shows "\<exists>b \<in> X. is_inf R X A b"
  by (simp add: A0 A1 A2 A3 A4 A5 sup_finite)

lemma bsup_finite:
  assumes A0: "\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> is_sup R X {a1, a2} (Sup R X {a1, a2})" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X" and 
          A4:"trans R X" and
          A5:"antisym_on X R"
  shows "is_sup R X A (Sup R X A)"
proof-
  have "\<exists>b. is_sup R X A b"  by (metis A0 A1 A2 A3 A4 A5 is_supD1 sup_finite)
  then show ?thesis using A3 A5 sup_equality2 by blast
qed

lemma binf_finite:
  assumes A0: "\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> is_inf R X {a1, a2} (Inf R X {a1, a2})" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X" and 
          A4:"trans R X" and
          A5:"antisym_on X R"
  shows "is_inf R X A (Inf R X A)"
  by (metis A0 A1 A2 A3 A4 A5 Sup_def antisym_on_converse bsup_finite trans_on_converse)


lemma assoc_sup:
  assumes por:"pord R X" and ax:"a \<in> X" and bx:"b \<in> X" and cx:"c \<in> X" and dx:"d \<in> X" and
          sab:"is_sup R X {a, b} s" and  tcd:"is_sup R X {c, d} t"
  shows assoc_sup1:"\<And>x. x \<in> ubd R X {s, t} \<Longrightarrow>  x \<in> ubd R X {a, b, c, d}" and
        assoc_sup2:"\<And>x. x \<in> ubd R X {a, b, c, d} \<Longrightarrow> x \<in> ubd R X {s, t}" and
        assoc_sup3:"ubd R X {s, t} =  ubd R X {a, b, c, d}" and
        assoc_sup4:"\<And>r. is_sup R X {a, b, c, d} r \<Longrightarrow> is_sup R X  {s, t} r" and
        assoc_sup5:"\<And>r. is_sup R X  {s, t} r \<Longrightarrow>  is_sup R X {a, b, c, d} r"
proof-
  show P0:"\<And>x. x \<in> ubd R X {s, t} \<Longrightarrow>  x \<in> ubd R X {a, b, c, d}" 
  proof-
    fix x assume xst:"x \<in> ubd R X {s,t}" then obtain xx:"x \<in> X" and sx:"s \<in> X" and tx:"t \<in> X"
      by (meson is_supD1 sab tcd ubdD1)
    then obtain asr:"(a,s)\<in>R" and bsr:"(b,s)\<in>R" and ctr:"(c,t)\<in>R" and dtr:"(d,t)\<in>R"
      by (meson insertCI is_supD1 sab tcd)
    then obtain axr:"(a,x)\<in>R" and bxr:"(b,x)\<in>R" and cxr:"(c,x)\<in>R" and dxr:"(d,x)\<in>R"
      by (meson ax bx cx dx insertCI por sx trans_onD tx ubdD1 xst)
    then show "x \<in> ubd R X {a, b, c, d}" unfolding ubd_def using xx by(auto)
  qed
  show P1:"\<And>x. x \<in> ubd R X {a, b, c, d} \<Longrightarrow> x \<in> ubd R X {s, t}"
  proof-
    fix x assume xabcd:"x \<in> ubd R X {a,b,c,d}" then obtain xx:"x \<in> X" and sx:"s \<in> X" and tx:"t \<in> X"
      by (meson is_supD1 sab tcd ubdD1)
    then obtain asr:"(a,s)\<in>R" and bsr:"(b,s)\<in>R" and ctr:"(c,t)\<in>R" and dtr:"(d,t)\<in>R"
      by (meson insertCI is_supD1 sab tcd)
    then obtain axr:"(a,x)\<in>R" and bxr:"(b,x)\<in>R" and cxr:"(c,x)\<in>R" and dxr:"(d,x)\<in>R"
      by (meson insertCI ubdD1 xabcd)
    then show "x \<in> ubd R X {s,t}" unfolding ubd_def
      using is_supD1 sab tcd xx by fastforce
  qed
  show P2:"ubd R X {s, t} =  ubd R X {a, b, c, d}" 
    using P0 P1 by blast 
  show P3:"\<And>r. is_sup R X {a, b, c, d} r \<Longrightarrow> is_sup R X  {s, t} r" 
  proof-
    fix r assume rabcd:"is_sup R X {a,b,c,d} r"  
    then show "is_sup R X  {s, t} r"
      using P2 Upper_eq_sup_eq2 by fastforce
  qed
  show P4:"\<And>r. is_sup R X  {s, t} r \<Longrightarrow> is_sup R X {a, b, c, d} r" 
  proof-
    fix r assume rabcd:"is_sup R X {s,t} r"  
    then show "is_sup R X  {a,b,c,d} r"
      using P2 Upper_eq_sup_eq2 by fastforce
  qed
qed

lemma assoc_inf:
  assumes por:"pord R X" and ax:"a \<in> X" and bx:"b \<in> X" and cx:"c \<in> X" and dx:"d \<in> X" and
          sab:"is_inf R X {a, b} s" and  tcd:"is_inf R X {c, d} t"
  shows assoc_inf1:"\<And>x. x \<in> lbd R X {s, t} \<Longrightarrow>  x \<in> lbd R X {a, b, c, d}" and
        assoc_inf2:"\<And>x. x \<in> lbd R X {a, b, c, d} \<Longrightarrow> x \<in> lbd R X {s, t}" and
        assoc_inf3:"lbd R X {s, t} =  lbd R X {a, b, c, d}" and
        assoc_inf4:"\<And>r. is_inf R X {a, b, c, d} r \<Longrightarrow> is_inf R X  {s, t} r" and
        assoc_inf5:"\<And>r. is_inf R X  {s, t} r \<Longrightarrow>  is_inf R X {a, b, c, d} r"
proof-
 have rpor:"pord (dual R) X"
  by (simp add: por refl_dualI)
 show P0:"\<And>x. x \<in> lbd R X {s, t} \<Longrightarrow>  x \<in> lbd R X {a, b, c, d}"
  by (meson assoc_sup1 ax bx cx dx rpor sab tcd)
 show P1:"\<And>x. x \<in> lbd R X {a, b, c, d} \<Longrightarrow> x \<in> lbd R X {s, t}"
  using assoc_sup2 ax bx cx dx rpor sab tcd by metis  
 show P2:"lbd R X {s, t} =  lbd R X {a, b, c, d}" 
  using assoc_sup3 ax bx cx dx rpor sab tcd by metis  
 show P3:"\<And>r. is_inf R X {a, b, c, d} r \<Longrightarrow> is_inf R X  {s, t} r"
   using assoc_sup4 ax bx cx dx rpor sab tcd by metis  
 show P4:"\<And>r. is_inf R X  {s, t} r \<Longrightarrow>  is_inf R X {a, b, c, d} r"
  using assoc_sup5 ax bx cx dx rpor sab tcd by metis  
qed



subsection Duality

lemma sup_imp_inf_ub:
  "is_sup R X A s \<Longrightarrow>  is_inf R X (ubd R X A) s"
  unfolding is_sup_def is_greatest_def ubd_def by blast
  
lemma sup_if_inf_ub:
  "A \<subseteq> X \<Longrightarrow> is_inf R X (ubd R  X A) s \<Longrightarrow>  is_sup R X A s"
  by (simp add: in_mono is_greatest_def is_sup_def ubd_def)
  
lemma inf_imp_sup_lb:
  "is_inf R X A s \<Longrightarrow>  is_sup R X (lbd R X A) s"
  using sup_imp_inf_ub by fastforce
  
lemma inf_if_sup_lb:
  "A \<subseteq> X \<Longrightarrow> is_sup R X (lbd R X A) s \<Longrightarrow>  is_inf R X A s"
  by (simp add: sup_if_inf_ub)


end