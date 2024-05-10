theory PosetsRel3
  imports Main
begin

hide_const top bot
hide_const(open) List.list.Nil
no_notation List.list.Nil ("[]")  
no_notation Cons (infixr "#" 65) 
hide_type list
hide_const rev Sup Inf trans refl Greatest
declare [[show_consts, show_results]]


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

definition Sup::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a" 
  where  "Sup R X A \<equiv> (THE m. is_sup R X A m)"

abbreviation Inf::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where  
  "Inf R X A \<equiv> Sup (converse R) X A"

subsection Lattices
definition is_sup_semilattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_sup_semilattice R X \<equiv> (X \<noteq> {}) \<and> (\<forall>a b. a \<in> X \<and> b \<in> X \<longrightarrow> (\<exists>x. is_sup R X {a, b} x))"

definition is_fsup_closed::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_fsup_closed R X A \<equiv> (\<forall>a1 a2. a1 \<in> A \<and>  a2 \<in> A \<longrightarrow> Sup R X {a1, a2} \<in> A)"

abbreviation is_inf_semilattice::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_inf_semilattice R X \<equiv> is_sup_semilattice (converse R) X"

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

definition Pow_ne::"'a set \<Rightarrow> 'a set set" where 
  "Pow_ne X = Pow X - {{}}"

definition Fpow_ne::"'a set \<Rightarrow> 'a set set" where 
  "Fpow_ne X = Fpow X - {{}}"

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
  "ord R X \<equiv> antisym R X \<and> trans R X"

definition refl::"'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "refl R X \<equiv> (\<forall>x. x \<in> X \<longrightarrow> (x, x) \<in> R)"

abbreviation preord where
  "preord R X \<equiv> trans R X \<and> refl R X"

abbreviation pord where
  "pord R X \<equiv> trans R X \<and> antisym R X \<and> refl R X"

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

  
definition ClN::"('a \<times> 'a set) set \<Rightarrow> 'a set \<Rightarrow> ('a set \<times> 'a) set" where
  "ClN N X \<equiv> {(B, x). B \<in> Pow X \<and> x \<in> X \<and> {B}#( N``{x})}"

definition NCl:: "('a set \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a set) set" where 
  "NCl Cl X \<equiv> {(x, A). A \<in> Pow X \<and> x \<in> X \<and> {A}#(converse Cl)``{x}}"

definition NAdh::"('a set set \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a set) set" where
  "NAdh Adh X \<equiv> {(x, A). A \<in> Pow X \<and> x \<in> X \<and> (\<forall>\<E> \<in> pfilters_on (pwr X) (Pow X). (\<E>, x) \<in> Adh \<longrightarrow> {A}#\<E>)}"

definition AdhN::"('a \<times> 'a set) set \<Rightarrow> 'a set \<Rightarrow> ('a set set \<times> 'a) set" where
  "AdhN N X \<equiv> {(\<E>, x). \<E> \<in> pfilters_on (pwr X) (Pow X) \<and> x \<in> X \<and> (\<forall>A. A \<in>  Pow X \<and> (x, A) \<in> N \<longrightarrow> {A}#\<E>)}"

definition AdhCl::"('a set \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> ('a set set \<times> 'a) set" where
  "AdhCl Cl X \<equiv> {(\<F>, x). \<F> \<in>  pfilters_on (pwr X) (Pow X) \<and> x \<in> X \<and> (\<forall>A. A \<in>  Pow X \<and> A \<in> \<F> \<longrightarrow> (A, x) \<in> Cl)}"

definition ClAdh::"('a set set \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow>('a set \<times> 'a) set " where
  "ClAdh Adh X \<equiv> {(A, x). A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F> \<in> pfilters_on (pwr X) (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> Adh)}"

definition NLim::"('a set set \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a set) set" where
  "NLim Lim X \<equiv> {(x, A). A \<in> Pow X \<and> x \<in> X \<and> (\<forall>\<E>. \<E> \<in> pfilters_on (pwr X) (Pow X) \<and> (\<E>, x) \<in> Lim \<longrightarrow>A \<in> \<E>)}"

definition LimN::"('a \<times> 'a set) set \<Rightarrow> 'a set \<Rightarrow> ('a set set \<times> 'a) set" where
  "LimN N X \<equiv> {(\<E>, x). \<E> \<in> pfilters_on (pwr X) (Pow X) \<and> x \<in> X \<and> (\<forall>A \<in>  Pow X. (x, A) \<in> N \<longrightarrow> A \<in> \<E>)}"

definition LimCl::"('a set \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> ('a set set \<times> 'a) set" where
  "LimCl Cl X \<equiv> {(\<F>, x). \<F> \<in>  pfilters_on (pwr X) (Pow X) \<and> x \<in> X \<and> (\<forall>A. A \<in>  Pow X \<and> {A}#\<F> \<longrightarrow> (A, x) \<in> Cl)}"

definition ClLim::"('a set set \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow>('a set \<times> 'a) set " where
  "ClLim Lim X \<equiv> {(A, x). A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F> \<in> pfilters_on (pwr X) (Pow X). {A} # \<F> \<and> (\<F>, x) \<in> Lim)}"

definition AdhLim::"('a set set \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow>('a set set \<times> 'a) set" where
  "AdhLim Lim X \<equiv> {(\<F>, x). \<F> \<in> (pfilters_on (pwr X) (Pow X))\<and>  x \<in> X \<and> (\<exists>\<G> \<in> pfilters_on (pwr X) (Pow X). \<G> # \<F> \<and> (\<G>, x) \<in> Lim)}"

definition LimAdh::"('a set set \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow>('a set set \<times> 'a) set" where
  "LimAdh Adh X \<equiv> {(\<F>, x). \<F> \<in> (pfilters_on (pwr X) (Pow X))\<and>  x \<in> X \<and> (\<forall>\<G>. \<G> \<in> pfilters_on (pwr X) (Pow X) \<and> \<G> # \<F>  \<longrightarrow> (\<G>, x) \<in> Adh)}"

section Powerset
lemma Pow_ne_iff:
  "A \<in> Pow_ne X \<longleftrightarrow> (A \<subseteq> X) \<and> (A \<noteq> {})"
  by (simp add:Pow_ne_def)

lemma Fpow_ne_iff:
  "A \<in> Fpow_ne X \<longleftrightarrow>  A \<subseteq> X \<and> finite A \<and> A \<noteq> {}"
  by(simp add: Fpow_ne_def Fpow_def) 

lemma Pow_neI1:
  "\<lbrakk>A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> A \<in> Pow_ne X"
  by (simp add:Pow_ne_def)

lemma Pow_neI2:
  "\<lbrakk>A \<in> Pow X; A \<noteq> {}\<rbrakk> \<Longrightarrow> A \<in> Pow_ne X"
  by (simp add:Pow_ne_def)

lemma Pow_neD:
  "A \<in> Pow_ne X \<Longrightarrow> A \<subseteq>X \<and> A \<in> Pow X \<and> A \<noteq> {}"
  by (simp add:Pow_ne_def)

lemma Fpow_neI1:
  "\<lbrakk>A \<subseteq> X; A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow> A \<in> Fpow_ne X"
  unfolding Fpow_ne_def Fpow_def by auto

lemma Fpow_neI2:
  "\<lbrakk>A \<in> Pow X; A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow> A \<in> Fpow_ne X"
  unfolding Fpow_ne_def Fpow_def by auto

lemma Fpow_neD:
  "A \<in> Fpow_ne X \<Longrightarrow> finite A \<and> A \<subseteq>X \<and> A \<in> Pow X \<and> A \<noteq> {}"
  unfolding Fpow_ne_def Fpow_def by auto

section Reflexivity

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

section SubsetRelation

lemma pwr_memI:
  "\<lbrakk>A \<subseteq> X; B \<subseteq> X; A \<subseteq> B\<rbrakk> \<Longrightarrow> (A,B)\<in>pwr X"
  by (simp add:pwr_def)

lemma pwr_memD:
  "(A,B)\<in>pwr X \<Longrightarrow> A \<subseteq> X \<and> B \<subseteq> X \<and> A \<subseteq> B"
  by (simp add:pwr_def)

lemma pwr_antisym:
  "antisym (pwr X) (Pow X)"  
  by(auto simp add:antisym_on_def pwr_def)

lemma pwr_trans:
  "trans (pwr X) (Pow X)"
  by(auto simp add:trans_on_def pwr_def)

lemma pwr_refl:
  "refl (pwr X) (Pow X)"
  by(auto simp add:refl_def pwr_def)

lemma pwr_ar_inf:
  "A \<subseteq> Pow X \<Longrightarrow> is_inf (pwr X) (Pow X) A (X \<inter>(\<Inter>A))" 
  unfolding is_sup_def is_greatest_def ubd_def pwr_def converse_def by(auto)

lemma pwr_ne_inf:
  "A \<subseteq> Pow X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> is_inf (pwr X) (Pow X) A (\<Inter>A)" 
  unfolding is_sup_def is_greatest_def ubd_def pwr_def converse_def by blast

lemma pwr_ar_sup:
  "A \<subseteq> Pow X \<Longrightarrow> is_sup (pwr X) (Pow X) A (\<Union>A)" 
  unfolding is_sup_def is_greatest_def ubd_def pwr_def by auto

lemma pwr_antisym_sub:
  "C \<subseteq> Pow X \<Longrightarrow> antisym (pwr X) C"
  using pwr_antisym[of X] antisym_on_subset[of "Pow X" "pwr X" C] by auto

lemma pwr_trans_sub:
  "C \<subseteq> Pow X \<Longrightarrow> trans (pwr X) C" 
  using pwr_trans[of X] trans_on_subset[of "Pow X" "pwr X" C] by auto

lemma pwr_refl_sub:
  "C \<subseteq> Pow X \<Longrightarrow> refl(pwr X) C"  
  using pwr_refl[of X] refl_subset by blast

section Bounds

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

section Greatest

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
  "is_greatest R A m \<Longrightarrow> (\<forall>a. a \<in> A \<longrightarrow> (a,m)\<in>R) \<and> (m \<in> A)"
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

lemma greatest_unique:
  "\<lbrakk>antisym R A; is_greatest R A m1; is_greatest R A m2\<rbrakk> \<Longrightarrow> m1 =m2"
  by (simp add: antisym_onD is_greatestD1)

lemma greatest_equalityI1:
  "\<lbrakk>antisym R A; (\<And>a. a \<in> A \<Longrightarrow> (a, m)\<in>R); m \<in> A\<rbrakk> \<Longrightarrow> Greatest R A = m"
  by (simp add: Greatest_def is_greatestI3 greatest_unique the_equality) 

lemma greatest_equalityI2:
  "\<lbrakk>antisym R A; is_greatest R A m\<rbrakk> \<Longrightarrow> Greatest R A = m"
  by (simp add:Greatest_def greatest_unique the_equality)

lemma greatest_unique_witness:
  "\<lbrakk>antisym R A; is_greatest R A m\<rbrakk> \<Longrightarrow> \<exists>!x. is_greatest R A x"
  using greatest_unique by fastforce

lemma greatest_unique_ex:
  "\<lbrakk>antisym R A; \<exists>m. is_greatest R A m\<rbrakk> \<Longrightarrow> \<exists>!x. is_greatest R A x"
  using greatest_unique by fastforce

lemma greatestI:
  assumes max:"is_greatest R A m" and 
          ant:"antisym R A" and
          prp:"\<And>x. is_greatest R A x \<Longrightarrow> Q x"
  shows "Q (Greatest R A)"
proof-
  obtain P1:"\<And>x. is_greatest R A x \<Longrightarrow> x = m"
    using ant greatest_unique max by fastforce 
  show "Q (Greatest R A)"
  proof(unfold Greatest_def)
    show "Q (THE m. is_greatest R A m)"
      using max P1 prp theI2[of "\<lambda>x. is_greatest R A x" m Q] by blast
  qed
qed

lemma ex_greatestI:
  assumes exm:"\<exists>m. is_greatest R A m" and 
          ant:"antisym R A" and
          prp:"\<And>x. is_greatest R A x \<Longrightarrow> Q x"
   shows "Q (Greatest R A)"
proof-
  obtain m where max:"is_greatest R A m"
    using exm by auto 
  then show ?thesis 
    using ant prp greatestI[of R A m] by auto
qed

lemma ex_max:
  assumes ant:"antisym R A" and ex:"\<exists>m. is_greatest R A m" 
  shows ex_max0:"\<And>a. a \<in> A \<Longrightarrow> (a,Greatest R A)\<in>R" and
        ex_max1:"Greatest R A \<in> A" and
        ex_max2:"Greatest R A \<in> ubd R A A" and
        ex_max3:"\<And>X. A \<subseteq> X \<Longrightarrow> Greatest R A \<in> ubd R X A"
proof-
  show P0:"\<And>a. a \<in> A \<Longrightarrow> (a,Greatest R A)\<in>R" 
    using ant ex is_greatestD1[of R A] greatest_equalityI2[of A R] by fastforce  
  show P1:"Greatest R A \<in> A"
    using ant ex is_greatestD1[of R A] greatest_equalityI2[of A R] by fastforce  
  show P2:"Greatest R A \<in> ubd R A A" 
    using ant ex is_greatest_def[of R A] greatest_equalityI2[of A R] by blast
  show P3:"\<And>X. A \<subseteq> X \<Longrightarrow> Greatest R A \<in> ubd R X A"
    using P2 ubd_fst_iso by fastforce
qed

lemma is_greatest_iso2:
  "A \<subseteq> B \<Longrightarrow> is_greatest R A ma \<Longrightarrow> is_greatest R B mb \<Longrightarrow> (ma, mb)\<in>R"
  by (simp add: is_greatestD1 in_mono)

section Sup
subsection Intro
lemma is_supI1:
  "is_least R (ubd R X A) m \<Longrightarrow> is_sup R X A m"
  by (simp add: is_sup_def)

lemma is_supI2:
  "\<lbrakk>A \<subseteq>X; m \<in> X;(\<And>a. a\<in>A\<Longrightarrow>(a,m)\<in>R);(\<And>b. b\<in>ubd R X A\<Longrightarrow>(m,b)\<in>R)\<rbrakk>\<Longrightarrow> is_least R (ubd R X A) m"
  by (simp add: is_greatestI3 ubdI1)

lemma is_supI3:
  "\<lbrakk>x\<in>X; (\<And>a. a\<in>A \<Longrightarrow> (a,x)\<in>R); (\<And>b. b\<in>X\<Longrightarrow>(\<And>a. a\<in>A \<Longrightarrow>(a,b)\<in>R)\<Longrightarrow> (x,b)\<in>R)\<rbrakk> \<Longrightarrow> is_sup R X A x"
  unfolding is_sup_def is_greatest_def ubd_def by blast

lemma Upper_eq_sup_eq:
  "ubd R  X A = ubd R  X B \<Longrightarrow> (is_sup R X A s \<longleftrightarrow> is_sup R X B s)"
  by (simp add: is_sup_def)

lemma Upper_eq_sup_eq2:
  "\<lbrakk>is_sup R X A s1;  ubd R X A=ubd R X B\<rbrakk> \<Longrightarrow> is_sup R X B s1"
  by (simp add: is_sup_def)

subsection Destruction

lemma is_supD1:
  "is_sup R X A x \<Longrightarrow> (x \<in> X) \<and> (\<forall>a. a \<in> A \<longrightarrow> (a,x)\<in>R) \<and> (\<forall>b. b \<in> X \<longrightarrow> (\<forall>a. a \<in> A \<longrightarrow> (a,b)\<in>R) \<longrightarrow> (x,b)\<in>R)"
  unfolding is_sup_def is_greatest_def ubd_def by blast

lemma is_infD1:
  "is_inf R X A x \<Longrightarrow> (x \<in> X) \<and> (\<forall>a. a \<in> A \<longrightarrow> (x,a)\<in>R) \<and> (\<forall>b. b \<in> X \<longrightarrow> (\<forall>a. a \<in> A \<longrightarrow> (b,a)\<in>R) \<longrightarrow> (b,x)\<in>R)"
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

lemma is_supD5:
  "\<lbrakk>is_sup R X A x; b\<in>X; (\<And>a. a \<in> A \<Longrightarrow> (a,b)\<in>R)\<rbrakk> \<Longrightarrow> (x,b)\<in>R"
  by (simp add: is_supD1)

lemma is_supD6:
  "is_sup R X A s \<Longrightarrow> s \<in> ubd R X A"
  by (simp add: is_greatestD1 is_sup_def)

subsection Uniqueness

lemma is_sup_unique:
  "\<lbrakk>antisym R X; is_sup R X A m1;  is_sup R X A m2\<rbrakk> \<Longrightarrow> m1 = m2"
  by (simp add: antisym_onD is_supD1)

lemma is_inf_unique:
  "\<lbrakk>antisym R X; is_inf R X A m1;  is_inf R X A m2\<rbrakk> \<Longrightarrow> m1 = m2"
  by (simp add: antisym_onD is_infD1)

lemma is_sup_unique_witness:
  "\<lbrakk>antisym R X; is_sup R X A s\<rbrakk> \<Longrightarrow> \<exists>!x. is_sup R X A x"
  using is_sup_unique by fastforce

lemma is_inf_unique_witness:
  "\<lbrakk>antisym R X; is_inf R X A s\<rbrakk> \<Longrightarrow> \<exists>!x. is_inf R X A x"
  using is_inf_unique by fastforce

lemma is_sup_unique_ex:
  "\<lbrakk>antisym R X; \<exists>s. is_sup R X A s\<rbrakk> \<Longrightarrow> \<exists>!x. is_sup R X A x"
  using is_sup_unique_witness by fastforce

lemma is_inf_unique_ex:
  "\<lbrakk>antisym R X; \<exists>s. is_inf R X A s\<rbrakk> \<Longrightarrow> \<exists>!x. is_inf R X A x"
  using is_inf_unique_witness by fastforce

lemma Upper_eq_sup_eq3:
  "\<lbrakk>is_sup R X A s1;  is_sup R X B s2;ubd R X A=ubd R X B; antisym R X\<rbrakk> \<Longrightarrow> s1=s2"
  by(drule_tac ?R="R" and ?X="X" and ?A="A" and ?s1.0="s1" and ?B="B" in Upper_eq_sup_eq2,simp,simp add: is_sup_unique)

lemma sup_equality:
  "\<lbrakk>is_sup R X A m; antisym R X\<rbrakk> \<Longrightarrow> Sup R X A = m"
  by (simp add: Sup_def is_sup_unique the_equality) 

subsection IsotonicityAndMaximums

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
  by (simp add: is_greatestD1 is_supI3)

lemma sup_in_subset:
  "A \<subseteq> B \<Longrightarrow>  B \<subseteq> X \<Longrightarrow> is_sup R X A s \<Longrightarrow> s \<in> B \<Longrightarrow> is_sup R B A s"
  unfolding is_sup_def is_greatest_def ubd_def by blast

lemma sup_empty:
  "is_sup R X {} i \<longleftrightarrow> (is_least R X i)"
  by (simp add: is_sup_def ubd_empty)

subsection PropIntros


lemma supI:
  assumes lub:"is_sup R X A s" and 
          ant:"antisym R X" and
          prp:"\<And>x. is_sup R X A x \<Longrightarrow> Q x"
  shows "Q (Sup R X A)"
proof-
  obtain P1:"\<And>x. is_sup R X A x \<Longrightarrow> x = s"
    using ant is_sup_unique lub by fastforce 
  show "Q (Sup R X A)"
  proof(unfold Sup_def)
    show "Q (THE s. is_sup R X A s)"
      using lub P1 prp theI2[of "\<lambda>x. is_sup R X A x" s Q] by blast
  qed
qed

lemma ex_supI:
  assumes exs:"\<exists>s. is_sup R X A s" and 
          ant:"antisym R X" and
          prp:"\<And>x. is_sup R X A x \<Longrightarrow> Q x"
  shows "Q (Sup R X A)"
proof-
  obtain s where lub:"is_sup R X A s"
    using exs by auto 
  then show ?thesis 
    using ant prp supI[of R X A s] by blast
qed
  
lemma ex_sup:
  assumes ant:"antisym R X" and ex:"\<exists>s. is_sup R X A s"
  shows ex_sup0:"\<And>a. a \<in> A \<Longrightarrow> (a,Sup R X A)\<in>R" and
        ex_sup1:"Sup R X A \<in> ubd R X A" and
        ex_sup2:"(\<And>b. b \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (a,b)\<in>R) \<Longrightarrow> (Sup R X A, b)\<in>R)" and
        ex_sup3:"\<And>b. b \<in> ubd R X A \<Longrightarrow> (Sup R X A,b)\<in>R" and
        ex_sup4:"is_least R (ubd R X A) (Sup R X A)" and
        ex_sup5:"Sup R X A \<in> X"
proof-
  show P0:"\<And>a. a \<in> A \<Longrightarrow> (a,Sup R X A)\<in>R"
    using ant ex is_supD1[of R X A] sup_equality[of R X A] by blast
  show P1:"Sup R X A \<in> ubd R X A" 
    using ant ex is_supD6[of R X A] ex_supI[of R X A "\<lambda>x. x \<in> ubd R X A"]  by blast 
  show P2:"(\<And>b. b \<in> X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (a,b)\<in>R) \<Longrightarrow> (Sup R X A, b)\<in>R)" 
    using ant ex is_supD5[of R X A] ex_supI[of R X A] by blast
  show P3:"\<And>b. b \<in> ubd R X A \<Longrightarrow> (Sup R X A,b)\<in>R" 
    using P2 ubdD1[of _ R X A] ubdD2[of _ R X A] by blast
  show P4:"is_least R (ubd R X A) (Sup R X A)"
    using ant ex is_sup_def sup_equality by fastforce
  show P5:"Sup R X A \<in> X"
    using P1 ubdD1[of _ R X A] by blast
qed


lemma Upper_eq_sup_eq4:
  assumes ant:"antisym R X" and ex1:"\<exists>s1. is_sup R X A1 s1" and ubd_eq:"ubd R X A1 = ubd R X A2"
  shows "Sup R X A1 = Sup R X A2"
  using ant ex1 sup_equality[of R X] ubd_eq Upper_eq_sup_eq2[of R X A1 _ A2] by blast

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

lemma sup_families1:
  assumes A0:"I \<noteq> {}" and 
          A1:"\<forall>i. i \<in> I \<longrightarrow> is_sup R X (A i) (s i)" and 
          A2:"trans R X" and 
          A3:"\<forall>i. i \<in> I \<longrightarrow> A i \<subseteq> X"
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
  assumes tran:"trans R X" and 
          anti:"antisym R X" and
          sub:"(\<And>Ai. Ai \<in> A \<Longrightarrow> Ai \<subseteq> X)" and
          nemp:"A \<noteq> {}" and 
          sups:"(\<And>Ai. Ai \<in> A \<Longrightarrow> \<exists>si. is_sup R X Ai si)"
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
(*
  (1). \strikethrough{the family results seem like they should naturally lend to the associativity result below but
  somehow we need to obtain some arbitrary unique indices to associate to {a,b} and {c,d} or else
  we need to handle the duplicate cases separately (whence we can let the sets be their own indices)
  but that seems a bit gross}
  (2). using the non indexed version that uses the Sup operator turned out to work lmfao 
*)
lemma assoc_sup:
  assumes por:"pord R X" and ax:"a \<in> X" and bx:"b \<in> X" and cx:"c \<in> X" and dx:"d \<in> X" and
          sab:"is_sup R X {a, b} s" and tcd:"is_sup R X {c, d} t"
  shows "is_sup R X {a, b, c, d} r \<longleftrightarrow> is_sup R X  {s, t} r"
proof-
  have B0:"{s,t}=(Sup R X)`{{a,b}, {c,d}}"
    using por sab sup_equality tcd by force
  have B1:"\<Union>{{a,b}, {c,d}} = {a,b,c,d}"
    by auto
  have B2:"is_sup R X ((Sup R X)`{{a,b}, {c,d}}) r \<longleftrightarrow> (is_sup R X (\<Union>{{a,b}, {c,d}}) r)"
  proof(rule sup_families)
    show "trans R X"
      by (simp add: por)
    show "antisym R X"
      by (simp add: por)
    show "\<And>Ai. Ai \<in> {{a, b}, {c, d}} \<Longrightarrow> Ai \<subseteq> X"
      using ax bx cx dx by blast
    show "{{a, b}, {c, d}} \<noteq> {}"
      by simp
    show "\<And>Ai. Ai \<in> {{a, b}, {c, d}} \<Longrightarrow> \<exists>si. is_sup R X Ai si"
      using sab tcd by auto
  qed
  then show ?thesis
    using B0 B1 by force
qed


         
lemma sup_insert:
  assumes A0:"s1 \<in> X" and A1:"is_sup R X F s1" and A2:"s2 \<in> X" and A3:"is_sup R X {s1, x} s2" and
          A4:"trans R X" and A6:"(insert x F) \<subseteq> X"
  shows "is_sup R X (insert x F) s2"
proof-
  obtain B0:"x \<in> X" and B1:"F \<subseteq> X"
    using A6 by auto
  obtain B2:"(s1,s2)\<in>R" and B3:"(x,s2)\<in>R"
    using A3 is_supD3[of R X "{s1,x}" s2] by blast
  have B4:"\<And>a. a \<in> (insert x F) \<Longrightarrow> (a,s2)\<in>R"
  proof-
    fix a assume A7:"a \<in> (insert x F)"
    show "(a,s2)\<in>R"
    proof(cases "a\<in>F")
      case True       
       then obtain "(a,s1)\<in>R" and "a \<in>X"
         using A1 B1 is_supD3 by fastforce
       then show ?thesis 
         using A4 A0 A2 B2 trans_onD[of X R a s1 s2]  by blast
    next
      case False 
      then obtain "a=x"
        using A7 by blast 
      then obtain "(a,s2)\<in>R"
        by (simp add: B3)
      then show ?thesis
        by simp
    qed
  qed
  show ?thesis
  proof(rule is_supI3)
    show B5:"s2 \<in> X" 
      by (simp add: A2)
    show B6:"\<And>a. a \<in> insert x F \<Longrightarrow> (a, s2) \<in> R"
      by (simp add: B4)
    show B7:" \<And>b. b \<in> X \<Longrightarrow> (\<And>a. a \<in> insert x F \<Longrightarrow> (a, b) \<in> R) \<Longrightarrow> (s2, b) \<in> R"
    proof-
      fix b assume B20:"b \<in> X" and B21:"(\<And>a. a \<in> insert x F \<Longrightarrow> (a, b) \<in> R)"
      then obtain B22:"(\<And>a. a \<in> {s1, x} \<Longrightarrow> (a, b)\<in>R)"
        using A1 is_supD1 by force 
      then show "(s2, b) \<in> R" 
        using is_supD5[of R X "{s1,x}" s2 b] A3 B20 by fastforce
    qed
  qed
qed

lemma sup_finite:
  assumes A0:"\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> \<exists>b. is_sup R  X {a1, a2} b" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X" and
          A4:"trans R X"
  shows "\<exists>b. is_sup R X A b"
  using A1 A2 A3 
proof (induct A rule: finite_ne_induct)
  case (singleton x) 
  then show ?case using A0 by force
next
  case (insert x F)
  obtain s1 where B1:"is_sup R X F s1" and B2:"x \<in> X" and B3:"F \<subseteq> X"
    using insert.hyps(4) insert.prems by blast
  obtain B0:"s1 \<in> X" 
    using B1 is_supD4[of R X F s1] by blast
  obtain s2 where B5:"is_sup R X {s1, x} s2"
    using A0 B0 B2 by blast
  obtain B4:"s2 \<in> X"
    using B5 is_supD4[of R X " {s1, x}" s2] by blast
  then have B6:"is_sup R X (insert x F) s2" 
    using sup_insert[of s1 X R F s2 x] A4 B0 B1 B5 insert.prems by simp
  then show ?case
    using B4 by auto
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


lemma inf_equality:
  "\<lbrakk>is_inf R X A m; antisym R X\<rbrakk> \<Longrightarrow> Inf R X A = m"
  by (simp add: Sup_def is_inf_unique the_equality) 

section MinimaMaxima

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

section SupSemilattices

lemma sup_semilattice_dual:
  "is_sup_semilattice R X \<longleftrightarrow> is_inf_semilattice (dual R ) X"
  by (simp add: is_sup_semilattice_def)

lemma sup_semilattice_ex1:
  assumes ssl:"is_sup_semilattice R X" 
  shows "\<And>x1 x2. \<lbrakk>x1 \<in> X; x2 \<in> X\<rbrakk> \<Longrightarrow> \<exists>s. is_sup R X {x1,x2} s"
  using ssl unfolding is_sup_semilattice_def by simp

lemma sup_semilattice_ex2:
  assumes ssl:"is_sup_semilattice R X" and ant:"antisym R X"
  shows "\<And>x1 x2. \<lbrakk>x1 \<in> X; x2 \<in> X\<rbrakk> \<Longrightarrow> \<exists>!s. is_sup R X {x1,x2} s"
  using ant ssl sup_semilattice_ex1[of R X ] is_sup_unique_ex[of X R] by auto 

lemma sup_semilattice_supI:
  assumes A0:"antisym R X" and 
          A1:"is_sup_semilattice R X" and 
          A2:"\<And>s. is_sup R X {a,b} s \<Longrightarrow> Q s" and
          A3:"a\<in>X" and 
          A4:"b\<in>X" 
        shows "Q (Sup R X {a,b})"
proof-
  obtain s where P0:"is_sup R X {a,b} s" 
    using A1 A3 A4 sup_semilattice_ex1[of R X a b] by auto
  obtain P1:"\<And>x. is_sup R X {a,b} x \<Longrightarrow> x = s"
    using A0 P0 is_sup_unique[of X R] by simp
  show "Q (Sup R X {a,b})"
  proof(unfold Sup_def)
    show "Q (THE m. is_sup R X {a, b} m)"
      using P0  P1  A2 theI2[of "\<lambda>x. is_sup R X {a,b} x" s Q] by blast
  qed
qed


lemma inf_semilattice_infI:
  assumes A0:"antisym R X" and 
          A1:"is_inf_semilattice R X" and 
          A2:"\<And>s. is_inf R X {a,b} s \<Longrightarrow> Q s" and
          A3:"a\<in>X" and 
          A4:"b\<in>X" 
        shows "Q (Inf R X {a,b})"
  by (simp add: A0 A1 A2 A3 A4 sup_semilattice_supI)

(*
  there is probably a way to automate this - or at least clean it up maybe with composition
  of lemmas
*)

lemma sup_semilattice_ex_sup:
  assumes ant:"antisym R X" and 
          ssl:"is_sup_semilattice R X" and 
          aix:"a\<in>X" and 
          bix:"b\<in>X" 
  shows ssl_ex_sup0:"\<And>x. x \<in>{a,b} \<Longrightarrow> (x,Sup R X {a,b})\<in>R" and
        ssl_ex_sup0a:"(a,Sup R X {a,b})\<in>R" and
        ssl_ex_sup0b:"(b,Sup R X {a,b})\<in>R" and
        ssl_ex_sup1:"Sup R X {a,b} \<in> ubd R X {a,b}" and
        ssl_ex_sup2:"\<And>z. z \<in> X \<Longrightarrow> (\<And>x. x \<in> {a,b} \<Longrightarrow> (x,z)\<in>R) \<Longrightarrow> (Sup R X {a,b}, z)\<in>R" and
        ssl_ex_sup3:"\<And>z. z \<in> ubd R X {a,b} \<Longrightarrow> (Sup R X {a,b},z)\<in>R" and
        ssl_ex_sup4:"is_least R (ubd R X {a,b}) (Sup R X {a,b})" and
        ssl_ex_sup5:"Sup R X {a,b} \<in> X" and
        ssl_ex_sup6:"Sup R X {a,b} = Sup R X {b,a}"
proof-
  obtain ex:"\<exists>s. is_sup R X {a,b} s"
    by (simp add: aix bix ssl sup_semilattice_ex1)
  let ?A="{a,b}"
  show P0:"\<And>x. x \<in> {a,b} \<Longrightarrow> (x,Sup R X {a,b})\<in>R"
    using ant ex is_supD1[of R X ?A] sup_equality[of R X ?A] by blast
  show P0a:"(a,Sup R X ?A)\<in>R"
    by (simp add: P0)
  show P0b:"(b,Sup R X ?A)\<in>R"
    by (simp add: P0)
  show P1:"Sup R X ?A \<in> ubd R X ?A" 
    using ant ex is_supD6[of R X ?A] ex_supI[of R X ?A "\<lambda>x. x \<in> ubd R X ?A"]  by blast 
  show P2:"(\<And>z. z \<in> X \<Longrightarrow> (\<And>x. x \<in> ?A \<Longrightarrow> (x,z)\<in>R) \<Longrightarrow> (Sup R X ?A, z)\<in>R)" 
    using ant ex is_supD5[of R X ?A] ex_supI[of R X ?A] by blast
  show P3:"\<And>z. z \<in> ubd R X ?A \<Longrightarrow> (Sup R X ?A,z)\<in>R" 
    using P2 ubdD1[of _ R X ?A] ubdD2[of _ R X ?A] by blast
  show P4:"is_least R (ubd R X ?A) (Sup R X ?A)"
    using ant ex is_sup_def sup_equality by fastforce
  show P5:"Sup R X ?A \<in> X"
    using P1 ubdD1[of _ R X ?A] by blast
  show P6:"Sup R X {a,b}=Sup R X {b,a}"
    by (simp add: insert_commute)
qed

lemma bsup_eqs:
  assumes ord:"ord R X" and
          ssl:"is_sup_semilattice R X"
shows bsup_ge1:"\<And>a b c. \<lbrakk>a \<in>X; b \<in> X; c \<in> X; (a,c)\<in>R;(b,c)\<in>R\<rbrakk>\<Longrightarrow>(Sup R X {a,b},c)\<in>R" and
      bsup_le1:"\<And>a b c. \<lbrakk>a \<in>X; b \<in> X; c \<in> X;(c,a)\<in>R\<rbrakk>\<Longrightarrow>(c,Sup R X{a,b})\<in>R" and
      bsup_le2:"\<And>a b c. \<lbrakk>a \<in>X; b \<in> X; c \<in> X;(c,b)\<in>R\<rbrakk>\<Longrightarrow>(c,Sup R X{a,b})\<in>R" and 
      bsup_as1:"\<And>a b c. \<lbrakk>a \<in>X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Sup R X {a,b}, c} = Sup R X {a,b,c}" and
      bsup_as2:"\<And>a b c. \<lbrakk>a \<in>X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Sup R X {a,c}, b} = Sup R X {a,b,c}" and
      bsup_as3:"\<And>a b c. \<lbrakk>a \<in>X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Sup R X {b,c}, a} = Sup R X {a,b,c}" 
proof-   
  show P0:"\<And>a b c. \<lbrakk>a \<in>X; b \<in> X; c \<in> X; (a,c)\<in>R;(b,c)\<in>R\<rbrakk>\<Longrightarrow>(Sup R X {a,b},c)\<in>R"
  proof-
    fix a b c assume aix:"a\<in>X" and  bix:"b\<in>X" and cix:"c\<in>X" and ac:"(a,c)\<in>R" and bc:"(b,c)\<in>R"
    then show "(Sup R X {a,b},c)\<in>R" using assms ssl_ex_sup2[of X R a b c] by blast
  qed
  show P1:"\<And>a b c. \<lbrakk>a \<in>X; b \<in> X; c \<in> X;(c,a)\<in>R\<rbrakk>\<Longrightarrow>(c,Sup R X{a,b})\<in>R"
  proof-
    fix a b c assume aix:"a\<in>X" and  bix:"b\<in>X" and  cix:"c\<in>X"  and cra:"(c,a)\<in>R"
    obtain "Sup R X {a,b}\<in>X" and "(a,Sup R X {a,b})\<in>R"
      by (simp add: aix bix ord ssl ssl_ex_sup0a ssl_ex_sup5)
    then show "(c,Sup R X {a,b})\<in>R" 
      using ord aix cix cra trans_onD[of X R c a "Sup R X {a,b}"] by blast
  qed
  show P2:"\<And>a b c. \<lbrakk>a \<in>X; b \<in> X; c \<in> X;(c,b)\<in>R\<rbrakk>\<Longrightarrow>(c,Sup R X{a,b})\<in>R"
  proof-
    fix a b c assume aix:"a\<in>X" and  bix:"b\<in>X" and  cix:"c\<in>X"  and cra:"(c,b)\<in>R"
    then show "(c,Sup R X{a,b})\<in>R" 
      using P1[of b a c] ssl_ex_sup6 ord ssl by fastforce
  qed
  show P3:"\<And>a b c. \<lbrakk>a \<in>X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Sup R X {a,b}, c} = Sup R X {a,b,c}"
  proof-
    fix a b c assume aix:"a\<in>X" and  bix:"b\<in>X" and  cix:"c\<in>X" 
    obtain sx:"Sup R X {a,b}\<in> X"
      by (simp add: aix bix ord ssl ssl_ex_sup5)
    show "Sup R X {Sup R X {a,b}, c} = Sup R X {a,b,c}"
    proof(rule Upper_eq_sup_eq4)
      show "antisym R X"
        by (simp add: ord)
      show "\<exists>s1. is_sup R X {Sup R X {a, b}, c} s1"
        by (simp add: cix ssl sup_semilattice_ex1 sx)
      show "ubd R X {Sup R X {a, b}, c} = ubd R X {a, b, c}" (is "?lhs = ?rhs")
      proof
        show "?lhs \<subseteq> ?rhs"
        proof
          fix x assume L0:"x \<in> ?lhs"
          then obtain xix:"x \<in> X" and "(Sup R X {a,b},x)\<in>R" and "(c,x)\<in>R"
            using ubdD2[of _ R X "{Sup R X {a,b},c}"] insertCI by blast
          also obtain "(a,Sup R X{a,b})\<in>R" and "(b,Sup R X{a,b})\<in>R"
            by (simp add: ord aix bix ssl ssl_ex_sup0a ssl_ex_sup0b)
          then obtain "(a,x)\<in>R" and "(b,x)\<in>R" and "(c,x)\<in>R" and "x \<in> X"
            using aix bix sx ord calculation trans_onD[of X R] by blast
          then show "x \<in> ?rhs" 
            unfolding ubd_def by auto
        qed
      next
        show "?rhs \<subseteq> ?lhs"
        proof
          fix x assume R0:"x \<in> ?rhs"
          then obtain lta:"(a,x)\<in>R" and ltb:"(b,x)\<in>R" and ltc:"(c,x)\<in>R" and xix:"x \<in> X"
            unfolding ubd_def by blast
          also obtain "(a,Sup R X{a,b})\<in>R" and "(b,Sup R X{a,b})\<in>R"
            by (simp add: ord aix bix ssl ssl_ex_sup0a ssl_ex_sup0b)
          then obtain "(Sup R X {a,b},x)\<in>R" and "(c,x)\<in>R" and "x \<in> X"
            by (simp add: P0 aix bix lta ltb ltc xix)
          then show "x \<in> ?lhs" 
            unfolding ubd_def by auto
        qed
      qed
    qed
  qed
  show P4:"\<And>a b c. \<lbrakk>a \<in>X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Sup R X {a,c}, b} = Sup R X {a,b,c}"
  proof-
    fix a b c assume aix:"a\<in>X" and  bix:"b\<in>X" and  cix:"c\<in>X" 
    then show "Sup R X {Sup R X {a,c}, b} = Sup R X {a,b,c}"
      using P3[of a c b] by(auto simp add:insert_commute)
  qed
  show P5:"\<And>a b c. \<lbrakk>a \<in>X; b \<in> X; c \<in> X\<rbrakk> \<Longrightarrow> Sup R X {Sup R X {b,c}, a} = Sup R X {a,b,c}"
  proof-
    fix a b c assume aix:"a\<in>X" and  bix:"b\<in>X" and  cix:"c\<in>X" 
    then show "Sup R X {Sup R X {b,c}, a} = Sup R X {a,b,c}"
      using P4[of b a c] by(auto simp add:insert_commute)
  qed
qed

lemma bsup_or:
  assumes por:"pord R X" and
          ssl:"is_sup_semilattice R X"
  shows bsup_or1:"\<And>a b. \<lbrakk>a\<in>X;b\<in>X; (a,b)\<in>R\<rbrakk>\<Longrightarrow> Sup R X {a,b} = b" and
        bsup_or2:"\<And>a b. \<lbrakk>a\<in>X;b\<in>X; (b,a)\<in>R\<rbrakk>\<Longrightarrow> Sup R X {a,b} = a" 
proof-
  show P0:"\<And>a b. \<lbrakk>a\<in>X;b\<in>X; (a,b)\<in>R\<rbrakk>\<Longrightarrow> Sup R X {a,b} = b"
  proof-
    fix a b  assume aix:"a\<in>X" and  bix:"b\<in>X" and alt:"(a,b)\<in>R"
    obtain blt:"(b,b)\<in>R" 
      using bix por reflD2[of R X b] by blast
    show "Sup R X {a,b} = b"
    proof(rule sup_equality)
      show "is_sup R X {a, b} b"
      proof(rule is_supI3)
        show "b \<in> X"
          by (simp add: bix)          
        show "\<And>x. x \<in> {a, b} \<Longrightarrow> (x, b) \<in> R"
          using alt blt by auto
        show "\<And>z. z \<in> X \<Longrightarrow> (\<And>x. x \<in> {a, b} \<Longrightarrow> (x, z) \<in> R) \<Longrightarrow> (b, z) \<in> R"
          by simp
      qed
      show "antisym R X"
        by (simp add: por)
    qed
  qed
  show P1:"\<And>a b. \<lbrakk>a\<in>X;b\<in>X; (b,a)\<in>R\<rbrakk>\<Longrightarrow> Sup R X {a,b} = a" 
  proof-
    fix a b  assume aix:"a\<in>X" and  bix:"b\<in>X" and blt:"(b,a)\<in>R" 
    then show "Sup R X {a,b} = a"
      using P0[of b a] por ssl ssl_ex_sup6[of X R ] by simp
  qed
qed

lemma sup_iso:
  assumes ord:"ord R X" and
          ssl:"is_sup_semilattice R X" and
          a1x:"a1 \<in> X" and b1x:"b1 \<in> X" and 
          a2x:"a2\<in>X" and b2x:"b2\<in>X" and 
          lt1:"(a1,b1)\<in>R" and lt2:"(a2,b2)\<in>R"
  shows "(Sup R X {a1,a2}, Sup R X {b1,b2})\<in>R"
  using assms by (simp add:  bsup_ge1 bsup_le1 bsup_le2 ssl_ex_sup5)


lemma bsup_assoc2:
  assumes A0:"ord R X" and A1:"is_sup_semilattice R X" and A2:"x \<in> X" and A3:"y \<in> X" and A4:"z \<in> X"
  shows "Sup R X {Sup R X {x, y}, z} =Sup R X {x, Sup R X {y, z}}"
proof-
  have B0:"Sup R X {Sup R X {x, y}, z} = Sup R X {x,y,z}"
    by (simp add: A0 A1 A2 A3 A4 bsup_as1) 
  also have B1:"... = Sup R X {Sup R X {y,z}, x}"
    by (simp add: A0 A1 A2 A3 A4 bsup_as3)
  also have B2:"...  = Sup R X {x, Sup R X {y,z}}"
    by (simp add: insert_commute)
  finally show ?thesis
    by simp 
qed

lemma sup_semilattice_fin_sup:
  assumes ord:"ord R X" and 
          ssl:"is_sup_semilattice R X" and
          fne:"A \<in> Fpow_ne X"
  shows ssl_fin_sup0:"\<exists>s. is_sup R X A s" and
        ssl_fin_sup1:"\<And>x. x \<in>A \<Longrightarrow> (x,Sup R X A)\<in>R" and
        ssl_fin_sup2:"Sup R X A \<in> ubd R X A" and
        ssl_fin_sup3:"\<And>z. z \<in> X \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> (x,z)\<in>R) \<Longrightarrow> (Sup R X A, z)\<in>R" and
        ssl_fin_sup4:"\<And>z. z \<in> ubd R X A \<Longrightarrow> (Sup R X A,z)\<in>R" and
        ssl_fin_sup5:"is_least R (ubd R X A) (Sup R X A)" and
        ssl_fin_sup6:"Sup R X A \<in> X" and
        ssl_fin_sup7:"is_sup R X A (Sup R X A)"
proof-
  obtain apow:"A \<subseteq> X" and afin:"finite A" and ane:"A \<noteq> {}"
    using fne unfolding Fpow_ne_def Fpow_def by auto
  then show P0:"\<exists>s. is_sup R X A s"
    using ord ssl sup_finite[of X R A] by (simp add: is_sup_semilattice_def)
  show P1:"\<And>x. x \<in>A \<Longrightarrow> (x,Sup R X A)\<in>R"
    by (simp add: P0 ex_sup0 ord)
  show P2:"Sup R X A \<in> ubd R X A"
    by (simp add: P0 ex_sup1 ord)
  show P3:"\<And>z. z \<in> X \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> (x,z)\<in>R) \<Longrightarrow> (Sup R X A, z)\<in>R"
    by (simp add: P0 ex_sup2 ord) 
  show P4:"\<And>z. z \<in> ubd R X A \<Longrightarrow> (Sup R X A,z)\<in>R"
    by (simp add: P0 ex_sup3 ord) 
  show P5:"is_least R (ubd R X A) (Sup R X A)"
    by (simp add: P0 ex_sup4 ord) 
  show P6:"Sup R X A \<in> X"
    by (simp add: P0 ex_sup5 ord)
  show P7:"is_sup R X A (Sup R X A)"
    by (simp add: P5 is_supI1)
qed


lemma finite_sup_closed2:
  assumes A0: "\<And>a1 a2. a1 \<in> A \<Longrightarrow> a2 \<in> A \<Longrightarrow>  Sup R X {a1, a2} \<in> A" and 
          A1:"finite E" and
          A2:"E \<noteq> {}" and
          A3:"E \<subseteq> A" and
          A4:"A \<subseteq> X" and
          A5:"is_sup_semilattice R X" and 
          A6:"antisym R X" and 
          A7:"trans R X"
  shows "Sup R X E \<in> A"
  using A1 A2 A3 A4 A5
proof (induct E rule: finite_ne_induct)
  case (singleton x) 
  then show ?case    
    using A0 by fastforce
next
  case (insert x F)
  obtain B0:"\<And>a1 a2. a1 \<in> X \<Longrightarrow> a2 \<in> X \<Longrightarrow> \<exists>b. is_sup R  X {a1, a2} b"
    by (simp add: A5 sup_semilattice_ex1)
  obtain B1:"F \<subseteq> X" and B2:"finite F" and B3:"F \<noteq> {}"
    using A4 insert.hyps(1) insert.hyps(2) insert.prems(1) by blast
  obtain B4:"F \<in> Fpow_ne X"
    by (simp add: B1 B2 B3 Fpow_ne_iff)
  obtain B5:"(insert x F) \<subseteq> X"
    using A4 insert.prems(1) by blast
  obtain s where B6:"is_sup R X F s"
    using A5 A6 A7 B4 ssl_fin_sup0 by blast  
  obtain B7:"s \<in> A" and B8:"x \<in> A" and B9:"s \<in> X"
    using B6 A4 A5 A6 insert.hyps(4) insert.prems(1) sup_equality by fastforce 
  obtain t where B10:"is_sup R X {s, x} t" 
    using B7 B8 A4 A5 in_mono sup_semilattice_ex1[of R X s x] by auto
  obtain B11:"t \<in> X"
    using B10 is_supD4[of R X "{s,x}" t] by blast
  obtain B12:"is_sup R X (insert x F) t"
    using B9 B6 B11 B10 A7 B5 sup_insert[of s X R F t x] by blast
  obtain B13:"t \<in> A"
    using A0 A6 B7 B8 B10 sup_equality by fastforce
  then show ?case
    using A6 B12 sup_equality by force
qed



lemma semilattice_assoc_sup:
  assumes por:"pord R X" and sem:"is_sup_semilattice R X" and
          ax:"a \<in> X" and bx:"b \<in> X" and cx:"c \<in> X" and dx:"d \<in> X"
  shows "Sup R X {Sup R X {a,b}, Sup R X {c,d}} = Sup R X {a,b,c,d}"
proof(rule sup_equality)
  obtain B0:"{a,b}\<in>Fpow_ne X" and B1:"{c,d}\<in>Fpow_ne X" and B2:"{a,b,c,d}\<in>Fpow_ne X"
    using Fpow_ne_iff ax bx cx dx by auto
  obtain B3:"is_sup R X {a, b} (Sup R X {a,b})" and B4:"is_sup R X {c,d}(Sup R X {c,d})" and
         B5:"is_sup R X {a,b,c,d} (Sup R X {a,b,c,d})"
    using B0 B1 B2 por sem ssl_fin_sup7[of X R] by blast
  show "is_sup R X {Sup R X {a, b}, Sup R X {c, d}} (Sup R X {a, b, c, d})"
    using assoc_sup[of X R a b c d] using por ax bx cx dx B3 B4 B5 by blast
  show "antisym R X" 
    by (simp add:por)
qed

section Lattices

lemma lattI1:
  "\<lbrakk>X \<noteq> {}; (\<And>a b. \<lbrakk>a\<in>X;b\<in>X\<rbrakk>\<Longrightarrow>(\<exists>x. is_inf R X {a,b} x) \<and>  (\<exists>x. is_sup R X {a,b} x))\<rbrakk> \<Longrightarrow> is_lattice R X"
  by (simp add: is_lattice_def)

lemma lattI2:
  "\<lbrakk>is_inf_semilattice R X; is_sup_semilattice R X\<rbrakk> \<Longrightarrow> is_lattice R X"
  by (simp add: is_sup_semilattice_def lattI1)

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
  "\<lbrakk>antisym R X;is_lattice R X;  a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  is_sup R X {a, b} (Sup R X {a, b}) "
  by (metis lattD22 sup_equality)

lemma lattD31:
  "\<lbrakk>antisym R X; is_lattice R X;  a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow>  is_inf R X {a, b} (Inf R X {a, b})"
  by (metis antisym_on_converse lattD21 sup_equality)

lemma lattD4:
  "is_lattice R X \<Longrightarrow> is_sup_semilattice R X \<and> is_inf_semilattice R X"
  by (simp add: is_sup_semilattice_def is_lattice_def)

lemma lattD5:
  "\<lbrakk>antisym R X; is_lattice R X; x \<in> X; y \<in> X; Sup R X {x, y} = y\<rbrakk> \<Longrightarrow> (x, y)\<in>R"
  by (metis insertCI is_supD1 lattD32)

lemma lattD6:
  "\<lbrakk>antisym R X; is_lattice R X; x \<in> X; y \<in> X; Inf R X {x, y} = x\<rbrakk> \<Longrightarrow> (x, y)\<in>R"
  by (metis insertCI is_infD1 lattD31)

lemma latt_iff:
  "is_lattice R X \<longleftrightarrow> (is_inf_semilattice R X) \<and> (is_sup_semilattice R X)"
  by(rule iffI,simp add:lattD4,simp add:lattI2)

lemma dual_lattice:
  "is_lattice R X \<longleftrightarrow> is_lattice (dual R) X"
  by (metis converse_converse is_lattice_def)

lemma latt_eqs1:
  assumes por:"pord R X" and 
          lat:"is_lattice R X" 
  shows lat_ge_iff1:"\<And>x y. \<lbrakk>x\<in>X;y\<in>X\<rbrakk> \<Longrightarrow> (x,y)\<in>R \<longleftrightarrow> Sup R X {x,y} =y" and
        lat_ge_iff2:"\<And>x y. \<lbrakk>x\<in>X;y\<in>X\<rbrakk> \<Longrightarrow> (y,x)\<in>R \<longleftrightarrow> Sup R X {x,y} =x" and
        lat_ge_iff3:"\<And>x y. \<lbrakk>x\<in>X;y\<in>X\<rbrakk> \<Longrightarrow> (x,y)\<in>R \<longleftrightarrow> Inf R X {x,y} =x" and
        lat_ge_iff4:"\<And>x y. \<lbrakk>x\<in>X;y\<in>X\<rbrakk> \<Longrightarrow> (y,x)\<in>R \<longleftrightarrow> Inf R X {x,y} =y" and
        lat_absorb1:"\<And>x y. \<lbrakk>x\<in>X;y\<in>X\<rbrakk> \<Longrightarrow> Sup R X {x, Inf R X {x, y}} = x" and
        lat_absorb2:"\<And>x y. \<lbrakk>x\<in>X;y\<in>X\<rbrakk> \<Longrightarrow> Inf R X {x, Sup R X {x, y}} = x"
proof-
  obtain ssl:"is_sup_semilattice R X" and isl:"is_inf_semilattice R X" 
    using lat latt_iff by fastforce
  obtain dor:"pord (dual R) X"
    by (simp add: por refl_iff) 
  obtain dsl:"is_sup_semilattice (dual R) X"
    using dual_lattice lat latt_iff by auto
  show P0:"\<And>x y. \<lbrakk>x\<in>X;y\<in>X\<rbrakk> \<Longrightarrow> (x,y)\<in>R \<longleftrightarrow> Sup R X {x,y} =y"
  proof-
    fix x y assume "x \<in> X" and "y \<in> X"
    then show "(x,y)\<in>R \<longleftrightarrow> Sup R X {x,y} =y"
      using lat lattD5[of X R x y] bsup_or[of X R x y] por latt_iff by blast
  qed
  show P1:"\<And>x y. \<lbrakk>x\<in>X;y\<in>X\<rbrakk> \<Longrightarrow> (y,x)\<in>R \<longleftrightarrow> Sup R X {x,y} =x"
    by (simp add: P0 insert_commute)
  show P2:"\<And>x y. \<lbrakk>x\<in>X;y\<in>X\<rbrakk> \<Longrightarrow> Sup R X {x, Inf R X {x, y}} =x" 
  proof-
    fix x y assume x1:"x \<in> X" and y1:"y \<in> X"
    obtain ixy:"(Inf R X {x,y},x)\<in>R"  and "Inf R X {x,y}\<in>X"
      by (meson converseD insertCI is_supD1 lat lattD31 por x1 y1)
    then show "Sup R X {x, Inf R X {x, y}} =x"
      by (simp add: P1 x1)
  qed
  show P3:"\<And>x y. \<lbrakk>x\<in>X;y\<in>X\<rbrakk> \<Longrightarrow> (x,y)\<in>R \<longleftrightarrow> Inf R X {x,y} =x" 
    using bsup_or2[of X "dual R"] converseI[of _ _ R] dor isl lat lattD6[of X R] por by blast
  show P4:"\<And>x y. \<lbrakk>x\<in>X;y\<in>X\<rbrakk> \<Longrightarrow> (y,x)\<in>R \<longleftrightarrow> Inf R X {x,y} =y" 
    by (simp add: P3 insert_commute)
  show P5:"\<And>x y. \<lbrakk>x\<in>X;y\<in>X\<rbrakk> \<Longrightarrow> Inf R X {x,Sup R X {x, y}} = x"
    using P3 por ssl ssl_ex_sup0a[of X R] ssl_ex_sup5[of X R] by simp
qed

lemma distrib_sup_le: 
  assumes A0:"ord R X" and A1:"is_lattice R X" and A2:"x \<in> X" and A3:"y \<in> X" and A4:"z \<in> X"
  shows "(Sup R X {x, Inf R X {y, z}}, Inf R X {Sup R X {x, y}, Sup R X {x, z}})\<in>R"
proof-
  obtain isl:"is_sup_semilattice R X" and ssl:"is_inf_semilattice R X" and dor:"ord (dual R) X"
    using A0 A1 antisym_on_converse lattD4 trans_on_converse by blast
  obtain sxy1:"Sup R X {x, y} \<in> X" and sxz1:"Sup R X {x, z} \<in> X"
    by (simp add: A0 A2 A3 A4 isl ssl_ex_sup5)
  obtain iyz1:"Inf R X {y, z} \<in> X"
    using A3 A4 dor ssl ssl_ex_sup5[of X "dual R" y z] by blast
  obtain xs1:"(x, Sup R X {x, y})\<in>R" and xs2:"(x, Sup R X {x, z})\<in>R"
    by (simp add: A0 A2 A3 A4 isl ssl_ex_sup0a)
  obtain ys1:"(y, Sup R X {x, y})\<in>R" and zs1:"(z, Sup R X {x, z})\<in>R"
    by (simp add: A0 A2 A3 A4 isl ssl_ex_sup0b)
  obtain xi1:"(x, Inf R X {Sup R X {x, y}, Sup R X {x, z}})\<in>R"
    using A2 sxy1 sxz1 xs1 xs2 ssl bsup_ge1[of X "dual R" "Sup R X {x,y}" "Sup R X {x,z}" x] 
          converseD converseI dor by blast
  obtain B0:" Inf R X {Sup R X {x, y}, Sup R X {x, z}} \<in>X"
    using dor sxy1 sxz1 ssl ssl_ex_sup5[of X "dual R" "Sup R X {x,y}" "Sup R X {x,z}"] by blast
  then obtain B1:"(Inf R X {y, z}, Inf R X {Sup R X {x, y}, Sup R X {x, z}})\<in>R"
    using A3 A4 sxz1 sxy1  ys1 zs1 dor ssl sup_iso[of X "dual R"] by auto 
  then show "(Sup R X {x, Inf R X {y, z}}, Inf R X {Sup R X {x, y}, Sup R X {x, z}})\<in>R"
    by (simp add: A0 A2 B0 bsup_ge1 isl iyz1 xi1) 
qed

lemma distrib_inf_le: 
  "\<lbrakk>ord R X;is_lattice R X; x \<in>X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> (Sup R X {Inf R X {x, y}, Inf R X {x, z}}, Inf R X {x, Sup R X {y, z}}) \<in> R"
  using distrib_sup_le[of X "dual R" x y z] dual_lattice[of R X]  by (simp add: Sup_def)

section DistributiveLattices

lemma distribD1:
  assumes A0:"is_lattice R X" and
          A1:"ord R X" and 
          A2:"refl R X" and
          A3:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}" and
          A4:" x \<in> X \<and> y \<in> X \<and> z \<in> X"
  shows "Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
proof-
  obtain A5:"is_sup_semilattice R X" and A6:"is_inf_semilattice R X" 
    using A0 lattD4 by blast
  obtain A7:"Inf R X {y, z} \<in> X" and A8:"Inf R X {x, z} \<in> X" and A9:"Sup R X {x, y} \<in> X"
    by (simp add: A1 A4 A5 A6 ssl_ex_sup5)  
  have B0:"Sup R X {x, Inf R X {y, z}} = Sup R X {Sup R X {x, Inf R X {x, z}}, Inf R X {y, z}}"
    by (simp add: A0 A1 A2 A4 lat_absorb1)  (*x \<or> (x \<and> z) = ((x \<or> (x \<and> z) \<or> (z \<and> y)))*)
  have B1:"... = Sup R X {x, Sup R X {Inf R X {z, x}, Inf R X {z, y}}}"
    by (metis A1 A4 A5 A7 A8 bsup_assoc2 doubleton_eq_iff)  (* x \<or> ((z \<and> x) \<or> (z \<and> y)) *) (*also fixme*)
  have B2:"... = Sup R X {x, Inf R X {z, Sup R X {x, y}}}" (*x \<or> (z \<and> (x \<or> y))*)
    by (simp add: A3 A4) 
  have B3:"... = Sup R X {Inf R X {Sup R X {x, y}, x}, Inf R X {Sup R X {x, y}, z}}"  by (metis A0 A1 A2 A4 doubleton_eq_iff lattice_absorb2 reflD2)
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
  using distribD1[of "dual R" X x y z]
  by (metis A0 A1 A2 A3 A4 dual_lattice Sup_def antisym_on_converse converse_converse refl_iff trans_on_converse)


lemma distribD3:
  assumes A0:"is_lattice R X" and
          A1:"ord R X" and 
          A2:"refl R X" and
          A3:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> (Inf R X {Sup R X {x, y}, Sup R X {x, z}}, Sup R X {x, Inf R X {y, z}})\<in>R"
  shows      "\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
proof-
  fix x y z assume A4:"x\<in>X" and A5:"y\<in>X" and A6:"z\<in>X"
  let ?a="Sup R X {x, Inf R X {y, z}}" let ?b="Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
  obtain A7:"?a\<in>X" and A8:"?b\<in>X"  by (meson A0 A1 A4 A5 A6 is_supD1 lattD31 lattD42 ssupD4) 
  have B0:"(?a, ?b)\<in>R" by (simp add: A0 A1 A4 A5 A6 distrib_sup_le) 
  also have B1:"(?b, ?a)\<in>R" by (simp add: A3 A4 A5 A6)
  then show "?a=?b"  by (meson A1 A7 A8 antisym_onD calculation) 
qed

lemma distribD4:
  assumes A0:"is_lattice R X" and
          A1:"ord R X" and 
          A2:"refl R X" and
          A3:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> (Inf R X {x, Sup R X {y, z}}, Sup R X {Inf R X {x, y}, Inf R X {x, z}})\<in>R"
  shows      "\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}"
  using distribD3[of "dual R" X]  by (meson A0 A1 A3 distrib_inf_le antisym_onD is_supD1 lattD31 lattD42 ssupD4)



lemma distI3:
  assumes A0:"is_lattice R X" and
          A1:"ord R X" and 
          A2:"refl R X" and
          A3:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> (Inf R X {x, Sup R X {y, z}}, Sup R X {Inf R X {x, y}, Inf R X {x, z}})\<in>R" 
  shows      "\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow>  Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
proof-
  have B0:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk> \<Longrightarrow> Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}"
    by (meson A0 A1 A3 distrib_inf_le antisym_on_def is_supD1 lattD31 lattD42 ssupD4)
  then show B1:"\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}" 
  proof-
     fix x y z assume A4:"x \<in> X" "y \<in> X" "z \<in> X"
     then show "Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}}"
      by(simp add: A0 A1 A2 A3 A4 B0 distribD1[of R X x y z])
  qed
qed




lemma distr_latticeI1:
  "\<lbrakk>pord R X; is_lattice R X; (\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> (Inf R X {Sup R X {x, y}, Sup R X {x, z}}, Sup R X {x, Inf R X {y, z}})\<in>R)\<rbrakk> \<Longrightarrow> distributive_lattice R X"
  by(simp add:distributive_lattice_def distribD3)

lemma distr_latticeI2:
  "\<lbrakk>pord R X; is_lattice R X; (\<And>x y z. \<lbrakk>x \<in> X; y \<in> X; z \<in> X\<rbrakk>\<Longrightarrow> (Inf R X {x, Sup R X {y, z}}, Sup R X {Inf R X {x, y}, Inf R X {x, z}})\<in>R)\<rbrakk> \<Longrightarrow> distributive_lattice R X"
  by(simp add:distributive_lattice_def distI3)


lemma distr_latticeD1:
  "\<lbrakk>distributive_lattice R X; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow>  Sup R X {x, Inf R X {y, z}} = Inf R X {Sup R X {x, y}, Sup R X {x, z}} "
  by (simp add: distributive_lattice_def insert_commute)

lemma distr_latticeD2:
  "\<lbrakk>distributive_lattice R X; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow>  Sup R X {Inf R X {y, z}, x} = Inf R X {Sup R X {y, x}, Sup R X {z, x}}"
  by (simp add: distributive_lattice_def insert_commute)
 
lemma distr_latticeD3:
  "\<lbrakk>pord R X; distributive_lattice R X; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow>  Inf R X {x, Sup R X {y, z}} = Sup R X {Inf R X {x, y}, Inf R X {x, z}}"
  using distribD2 distributive_lattice_def by fastforce
 
lemma distr_latticeD4:
  "\<lbrakk>pord R X; distributive_lattice R X; x \<in> X; y \<in> X; z \<in> X \<rbrakk> \<Longrightarrow>  Inf R X {Sup R X {y, z}, x} = Sup R X {Inf R X {y, x}, Inf R X {z, x}}"
  by (simp add: distr_latticeD3 insert_commute)

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

subsection LatticeDuals

lemma distributive_lattice_dual:
  assumes por:"pord R X"
  shows "distributive_lattice R X  \<Longrightarrow> distributive_lattice (dual R) X"
proof-
  assume lhs:"distributive_lattice R X" 
  show "distributive_lattice (dual R) X"
  proof(rule distr_latticeI1)
    show "pord (dual R) X"
      by (simp add: por refl_iff)
    show "is_lattice (dual R) X"
      using dual_lattice distr_latticeD5 lhs by blast
    show " \<And>x y z. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> z \<in> X \<Longrightarrow> (Inf (dual R) X {Sup (dual R) X {x, y}, Sup (dual R) X {x, z}}, Sup (dual R) X {x, Inf (dual R) X {y, z}}) \<in> dual R"
    proof-
      fix x y z assume x0:"x \<in> X" and y0:"y \<in> X" and z0:"z \<in> X"
      have B0:"Inf (dual R) X {Sup (dual R) X {x, y}, Sup (dual R) X {x, z}} = Sup R X {Inf R X {x,y}, Inf R X {x,z}}"
        by (simp add: Sup_def)
      have B1:"Sup (dual R) X {x, Inf (dual R) X {y, z}} = Inf R X {x, Sup R X {y,z}}"
        by (simp add: Sup_def)
      have B2:"(Inf R X {x, Sup R X {y, z}}, Sup R X {Inf R X {x, y}, Inf R X {x, z}})\<in>R"
        using por x0 y0 z0 distrib_inf_le[of X R x y z] distr_latticeD3[of X R x y z] lhs distr_latticeD5[of R X] by fastforce 
      then show "(Inf (dual R) X {Sup (dual R) X {x, y}, Sup (dual R) X {x, z}}, Sup (dual R) X {x, Inf (dual R) X {y, z}}) \<in> dual R"
        using B0 B1 by force
    qed
  qed
qed

lemma dist_lattice_dual:
  assumes por:"pord R X"
  shows "distributive_lattice R X  \<longleftrightarrow> distributive_lattice (dual R) X" (is "?lhs \<longleftrightarrow>?rhs")
proof
  assume lhs:?lhs 
  show ?rhs
  using distributive_lattice_dual lhs por by blast
next
  assume rhs:?rhs then obtain "pord (dual R) X"
    by (simp add: por refl_iff)
  then show ?lhs using distributive_lattice_dual[of X "dual R"]   by (simp add: rhs)
qed

lemma lattice_dualization:
  assumes lat:"is_lattice R X" and por:"pord R X" and
          lem:"(\<And>R X. \<lbrakk>is_lattice R X; pord R X\<rbrakk> \<Longrightarrow> P R X)"
  shows "P (converse R) X"
  using dual_lattice lat lem por refl_dualI by fastforce

lemma distributive_lattice_dualization:
  assumes lat:"distributive_lattice R X" and por:"pord R X" and
          lem:"(\<And>R X. \<lbrakk>distributive_lattice R X; pord R X\<rbrakk> \<Longrightarrow> P R X)"
  shows "P (converse R) X"
  by (simp add: distributive_lattice_dual lat lem por refl_dualI)



subsection IndexedExtrema


lemma sinfD4:
  "\<lbrakk>refl R X; antisym R X; trans R X; is_inf_semilattice R X; a \<in> X;  b \<in> X\<rbrakk> \<Longrightarrow> (Inf R X {a, b}) \<in> X"
  by (metis inf_equality is_supD1)

lemma distr_eq:
  assumes por:"pord R X" and lat:"is_lattice R X"
  shows distr_eq1:"\<And>a1 b. \<lbrakk>a1 \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> Inf R X {b, (Sup R X {a1})} = Sup R X {Inf R X {b, a}|a. a \<in> {a1}}" and
        distr_eq2:"\<And>a1 b. \<lbrakk>a1 \<in> X;b \<in> X\<rbrakk> \<Longrightarrow> Sup R X{b, (Inf R X {a1})} = Inf R X {Sup R X {b, a}|a. a \<in> {a1}}" 
proof-
  show P0:"\<And>a1 b. \<lbrakk>a1 \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> Inf R X {b, (Sup R X {a1})} = Sup R X {Inf R X {b, a}|a. a \<in> {a1}}"
  proof-
    fix a1 b assume A0:"a1 \<in> X" and A1:"b \<in> X" 
    have B0:"Sup R X {a1} = a1" using  por lat A0 A1 sup_singleton2 by metis 
    also have B1:"{Inf R X {b, a}|a. a \<in> {a1}} = {Inf R X {b, a1}}"   by auto
    then show "Inf R X {b, (Sup R X {a1})} = Sup R X {Inf R X {b, a}|a. a \<in> {a1}}"
    by (metis (no_types, lifting) por lat A0 A1 is_supD1 lattD31 sup_singleton2) 
  qed
  show P1:"\<And>a1 b. \<lbrakk>a1 \<in> X;b \<in> X\<rbrakk> \<Longrightarrow> Sup R X{b, (Inf R X {a1})} = Inf R X {Sup R X {b, a}|a. a \<in> {a1}}" 
  proof-
    fix a1 b assume A0:"a1 \<in> X" and A1:"b \<in> X" 
    have B0:"Inf R X {a1} = a1"
      by (simp add: A0 inf_singleton2 por)  
    also have B1:"{Sup R X {b, a}|a. a \<in> {a1}} = {Sup R X {b, a1}}"  by auto
    then show "Sup R X {b, (Inf R X {a1})} = Inf R X {Sup R X {b, a}|a. a \<in> {a1}}"
      by (simp add: A0 A1 inf_singleton2 lat lattD42 por ssupD4) 
  qed
qed

lemma distr_eq_dist:
  assumes por:"pord R X" and lat:"distributive_lattice R X"
  shows distr_eq_dist1:"\<And>a1 a2 b. \<lbrakk>a1 \<in> X; a2 \<in>X; b \<in> X\<rbrakk> \<Longrightarrow> Inf R X {b, Sup R X {a1, a2}} = Sup R X {Inf R X {b, a}|a. a \<in> {a1, a2}}" and
        distr_eq_dist2:"\<And>a1 a2 b. \<lbrakk>a1 \<in> X; a2 \<in>X; b \<in> X\<rbrakk> \<Longrightarrow> Sup R X {b, (Inf R X {a1, a2})} = Inf R X {Sup R X {b, a}|a. a \<in> {a1, a2}}" 
proof-
   show P0:"\<And>a1 a2 b. \<lbrakk>a1 \<in> X; a2 \<in>X; b \<in> X\<rbrakk> \<Longrightarrow> Inf R X {b, Sup R X {a1, a2}} = Sup R X {Inf R X {b, a}|a. a \<in> {a1, a2}}"
   proof-
     fix a1 a2 b assume A0:"a1 \<in> X" and A1:"a2 \<in> X" and A2:"b \<in> X"
     obtain B0:"is_lattice R X" and B1:"Sup R X {a1, a2} \<in> X" and B2:"Inf R X {b, a1} \<in> X" and B3:"Inf R X {b, a2}\<in>X"
        by (meson A0 A1 A2 distributive_lattice_def is_supD1 lat lattD31 lattD42 por ssupD4)
    obtain B4:"{Inf R X {b, a}|a. a \<in> {a1, a2}} = {Inf R X {b, a1}, Inf R X {b, a2}}" by blast
    then show "Inf R X {b, Sup R X {a1, a2}} = Sup R X {Inf R X {b, a}|a. a \<in> {a1, a2}}"
      by (simp add: A0 A1 A2 distr_latticeD3 lat por)
   qed
   show P1:"\<And>a1 a2 b. \<lbrakk>a1 \<in> X; a2 \<in>X; b \<in> X\<rbrakk> \<Longrightarrow> Sup R X {b, (Inf R X {a1, a2})} = Inf R X {Sup R X {b, a}|a. a \<in> {a1, a2}}" 
   proof-
     fix a1 a2 b assume A0:"a1 \<in> X" and A1:"a2 \<in> X" and A2:"b \<in> X"
     obtain B0:"is_lattice R X" and B1:"Inf R X {a1, a2} \<in> X" and B2:"Sup R X {b, a1} \<in> X" and B3:"Sup R X {b, a2}\<in>X"
        by (meson A0 A1 A2 distributive_lattice_def is_supD1 lat lattD31 lattD42 por ssupD4)
    obtain B4:"{Sup R X {b, a}|a. a \<in> {a1, a2}} = {Sup R X {b, a1}, Sup R X {b, a2}}" by blast
    then show "Sup R X {b, Inf R X {a1, a2}} = Inf R X {Sup R X {b, a}|a. a \<in> {a1, a2}}"
      by (simp add: A0 A1 A2 distr_latticeD1 lat)
   qed
qed



lemma l_sup_closed:
  "\<lbrakk>refl R X; antisym R X; trans R X;is_lattice R X;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Sup R X {x, y} \<in> X" 
  by (simp add: lattD42 ssupD4) 

lemma l_inf_closed:
  "\<lbrakk>refl R X; antisym R X; trans R X;is_lattice R X;x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> Inf R X {x, y} \<in> X" by (simp add: lattD41 sinfD4)

lemma l_finsup:
  "\<lbrakk>refl R X; antisym R X; trans R X;is_lattice R X; A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>s. is_sup R X A s"
  by (meson Fpow_ne_iff lattD42 sup_semilattice_fsup) 

lemma l_fininf:
  "\<lbrakk>refl R X; antisym R X; trans R X;is_lattice R X; A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>s. is_inf R X A s" 
   by (simp add: l_finsup  lattice_dualization) 

lemma s_finsup:
  "\<lbrakk>refl R X; antisym R X; trans R X;is_sup_semilattice R X; A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>s. is_sup R X A s"
  by (meson Fpow_ne_iff sup_semilattice_fsup)
 
lemma s_fininf:"\<lbrakk>refl R X; antisym R X; trans R X;is_inf_semilattice R X; A \<subseteq> X; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>s. is_inf R X A s"
  by (metis inf_finite is_supD1) 

lemma sup_insertE1:
  "\<And>a. is_sup R X A m \<Longrightarrow> (x, m) \<in> R \<Longrightarrow> a \<in> insert x A \<Longrightarrow> (a, m) \<in> R"
  using is_supD1 by fastforce

lemma sup_insert2:
  "\<lbrakk>is_sup R X A m; (x, m)\<in>R\<rbrakk> \<Longrightarrow> is_sup R X (insert x A) m"
  by(rule is_supI1, simp add: is_supD1,auto elim: sup_insertE1, simp add:is_supD1)

lemma sup_insert62:
  assumes A0:"is_sup R X A s1" and A1:"is_sup R X {s1,x} s2" and A2:"trans R X" and A3:"A \<subseteq> X"
  shows "s2 \<in> ubd R X A"
proof(rule ubdI)
  show "s2 \<in> X"
    using A1 is_supD1 by fastforce
  show "\<And>a. a \<in> A \<Longrightarrow> (a, s2) \<in> R"
    by (meson A0 A1 A2 A3 insertCI is_supD1 subsetD trans_onD)
qed


lemma sup_insert9:
  assumes A0:"is_sup R X A s1" and A1:"is_sup R X {s1,x} s2" and A2:"trans R X" and A3:"A \<subseteq> X"
  shows "s2 \<in> (ubd R X (insert x A))"
proof(rule ubdI)
  show "s2 \<in> X"
    using A1 is_supD1 by fastforce
  show "\<And>a. a \<in> (insert x A) \<Longrightarrow> (a, s2) \<in> R"
  proof-
    fix a assume A4:"a \<in> (insert x A)"
    show "(a,s2)\<in>R"
    proof(cases "a=x")
    case True then show ?thesis
      using A1 is_supD1 by fastforce
    next
    case False then obtain A5:"a \<in> A" using A4 by blast then show ?thesis
      by (meson A0 A1 A2 A3 sup_insert62 ubdD1) 
  qed
  qed
qed


lemma inf_insert9:
   "\<lbrakk>trans R Y;A \<subseteq> Y;is_inf R Y A s1; is_inf R Y {s1, x} s2\<rbrakk> \<Longrightarrow>  s2 \<in> (lbd R Y (insert x A))" 
   by (simp add: sup_insert9) 


lemma sup_ubd:
  assumes A0:"is_sup R X A s1" and A1:"is_sup R X {s1,x} s2" and A2:"trans R X" and A3:"A \<subseteq> X"
  shows "is_sup R X (insert x A) s2"
proof(rule is_supI1)
  show P0:"s2 \<in> X"
    using A1 is_supD1 by fastforce
  show Pq:"\<And>a. a \<in> insert x A \<Longrightarrow> (a, s2) \<in> R"
    by (meson A0 A1 A2 A3 sup_insert9 ubdD2)
  show "\<And>b. b \<in> X \<Longrightarrow> (\<And>a. a \<in> insert x A \<Longrightarrow> (a, b) \<in> R) \<Longrightarrow> (s2, b) \<in> R"
  proof-
    fix b assume A4:"b \<in> X" and A5:"(\<And>a. a \<in> insert x A \<Longrightarrow> (a, b) \<in> R)"
    then obtain "\<And>a. a \<in> {s1,x} \<Longrightarrow> (a,b)\<in>R" using A0 is_supD1 by force
    then show "(s2,b)\<in>R"
    by (meson A1 A4 is_supD1)
  qed
qed

lemma inf_lbd: 
  "\<lbrakk>trans R Y; F \<subseteq> Y;is_inf R Y F s; is_inf R Y {x, s} t\<rbrakk> \<Longrightarrow> is_inf R Y (insert x F) t"
  by (simp add: insert_commute sup_ubd) 

lemma fsup_insert:
  assumes por:"pord R X"  and lat:"is_lattice R X" and fne:"F \<in> Fpow_ne X" and xmem:"x \<in> X"
  shows "Sup R X {x, (Sup R X F)} = Sup R X (insert x F)"
proof-
  let ?Fx="insert x F"
  obtain fin1:"finite F" and fsub1:"F \<subseteq> X" and fne1:"F \<noteq> {}" using fne unfolding Fpow_ne_def Fpow_def by fastforce
  obtain fin2:"finite (?Fx)" and fsub2:"?Fx \<subseteq> X" and fne2:"?Fx \<noteq> {}" using fne xmem by force
  obtain fne3:"?Fx \<in> Fpow_ne X" using fin2 fsub2 by blast
  obtain B0:"is_sup R X F (Sup R X F)" and B1:" is_sup R X ?Fx (Sup R X ?Fx)"
    by (meson fne fne3 lat lattD42 por sup_semilattice_fsup)
  then obtain B2:"is_sup R X ?Fx (Sup R X {x,Sup R X F})"
    by (simp add: fsub1 insert_commute is_supD1 lat lattD32 por sup_ubd xmem)
  then show ?thesis
    by (simp add: por sup_equality)
qed

lemma finf_insert:
  "\<lbrakk>pord R X; is_lattice R X; F \<in> Fpow_ne X; x \<in> X\<rbrakk> \<Longrightarrow> Inf R X {x, (Inf R X F)} = Inf R X (insert x F)"
  by (metis Sup_def antisym_on_converse fsup_insert lattice_dualization trans_on_converse) 

lemma distr_finite2:
  assumes A0:"b \<in> X" and
          A1: "\<And>a1 a2. \<lbrakk>a1 \<in> X; a2 \<in> X\<rbrakk> \<Longrightarrow> Inf R X {b, (Sup R X {a1, a2})} = Sup R X {Inf R X {b, a}|a. a \<in> {a1, a2}}" and 
          A2:"finite A" and
          A3:"A \<noteq> {}" and
          A4:"A \<subseteq> X" and
          A5:"distributive_lattice R X" and 
          A6:"pord R X"         
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
  have P4:"?ba \<subseteq> X" 
  proof
    fix z assume "z \<in> ?ba" then obtain a where "a \<in> F" and "z=Inf R X {b,a}" by blast
    then show "z \<in> X" by (meson A0 A6 L P1 l_inf_closed subset_eq)
  qed
  have P5:"?xba \<subseteq> X" 
  proof
    fix z assume "z \<in> ?xba" then obtain a where "a \<in> (insert x F)" and "z=Inf R X {b,a}" by blast
    then show "z \<in> X" by (meson A0 A6 L in_mono insert.prems(1) l_inf_closed)
  qed
  have P6:"finite ?ba" using P2 by force
  have P7:"finite ?xba"  by (simp add: insert.hyps(1))
  have P8:"?xba = {Inf R X {b, x}} \<union> ?ba" by (auto)
  have P9:"Inf R X {b, x} \<in> X"
    using P5 by blast
  have P10:"?ba \<noteq> {}"  
     using P3 by blast
  have P11:"?xba \<noteq> {}" 
     using P3 by blast
  have P12:"?sba \<in> X"
    by (metis (no_types, lifting) A6 Fpow_ne_iff L P10 P4 P6 is_supD1 lattD42 sup_semilattice_fsup) 
  have P13:"?sxba \<in> X"
    by (metis (no_types, lifting) A6 Fpow_ne_iff L P11 P5 P7 is_supD1 lattD42 sup_semilattice_fsup) 
  have P14:"(Sup R X {?sba, (Inf R X {b, x})}) \<in> X"
    by (simp add: A6 L P12 P9 l_sup_closed) 
  have B0:"Inf R X {b, ?s} = ?sba"  
    using A0 A1 insert.hyps(4) insert.prems(1) by blast
  have B1:"Inf R X {b, (Sup R X {?s, x})} = Sup R X {(Inf R X {b, ?s}), (Inf R X {b, x})}"
    by (meson A0 A5 A6 Fpow_ne_iff L P0 P1 P2 P3 distr_latticeD3 is_supD1 lattD42 sup_semilattice_fsup)
  have B2:"... = Sup R X {(?sba), (Inf R X {b, x})}"  
    using B0 by fastforce
  have B3:"... = Sup R X {Inf R X {b, a}|a. a \<in> (insert x F)}" 
  proof-
    have B4:"?ba \<subseteq> ?xba" 
      by blast
    have B5:"is_sup R X ?ba ?sba"
      by (metis (mono_tags, lifting) A6 Fpow_ne_iff L P10 P4 P6 lattD42 sup_semilattice_fsup) 
    have B6:"is_sup R X {Inf R X {b, x},?sba} (Sup R X {(Inf R X {b, x}), (?sba)} )"
      by (simp add: A6 L P12 P9 lattD32)  
    have B7:"is_sup R X {Inf R X {b, x},?sba} (Sup R X {(?sba), (Inf R X {b, x})})" 
      by (metis B6 insert_commute) 
    have B8:"is_sup R X (insert (Inf R X {b, x}) ?ba) (Sup R X {(?sba), (Inf R X {b, x})})"
      by (smt (verit, best) A6 B5 B7 P4 insert_commute sup_ubd)  
    have B9:"insert (Inf R X {b, x}) ?ba =  {Inf R X {b, a}|a. a \<in> (insert x F)}"  
      using B5 B7 sup_ubd by blast
    show "(Sup R X {(?sba), (Inf R X {b, x})}) =  Sup R X {Inf R X {b, a}|a. a \<in> (insert x F)}"
      using A6 B8 B9 sup_equality by fastforce 
  qed
  have B10:"Inf R X {b, (Sup R X {?s, x})} = Sup R X {Inf R X {b, a}|a. a \<in> (insert x F)}" 
    using B0 B1 B3 by presburger
  have B11:"Inf R X {b, (Sup R X {?s, x})} = Inf R X {b, (Sup R X (insert x F))}"
  proof-
    have B12:"Sup R X {Sup R X F, x} = Sup R X (insert x F)"
      by (simp add: A6 L P0 P1 P2 P3 fsup_insert insert_commute) 
    show " Inf R X {b, Sup R X {Sup R X F, x}} = Inf R X {b, Sup R X (insert x F)}" 
       by (simp add: B12)
  qed
  have B13:"Inf R X {b, (Sup R X (insert x F))} =  Sup R X {Inf R X {b, a}|a. a \<in> (insert x F)}" 
    using B10 B11 by presburger
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
          A6:"pord R X"
  shows "Sup R X {b, (Inf R X A)} = Inf R X {Sup R X {b, a}|a. a \<in> A}"
proof-
  let ?R="dual R"
  have B0:"pord ?R X"
    by (simp add: A6 refl_dualI)
  have B1:"distributive_lattice ?R X"
    by (simp add: A5 A6 distributive_lattice_dualization)
  have B2:"\<And>a1 a2. \<lbrakk>a1 \<in> X; a2 \<in> X\<rbrakk> \<Longrightarrow> Inf ?R X {b, (Sup ?R  X {a1, a2})} = Sup ?R X {Inf ?R X {b, a}|a. a \<in> {a1, a2}}"
  proof-
    fix a1 a2 assume A7:"a1 \<in> X" and A8:"a2 \<in> X"
    then obtain B20:"Inf R X {a1, a2}=Sup ?R X {a1,a2}" and B21:"Sup R X {b, a1}=Inf ?R X {b,a1}" and  
                B22:"Sup R X {b, a2}=Inf ?R X {b,a2}"
                  by (simp add: Sup_def) 
    then obtain B23:" Sup R X {b, (Inf R X {a1, a2})}=Inf ?R X {b, (Sup ?R  X {a1, a2})}"
      using Sup_def by auto
    have B24:"{Inf ?R X {b, a}|a. a \<in> {a1, a2}}={Sup R X {b, a}|a. a \<in> {a1, a2}}" (is "?lhs=?rhs")
    proof
      show "?lhs \<subseteq> ?rhs"
      proof
        fix i assume "i \<in>?lhs" then obtain a where a1a2:"a \<in> {a1,a2}" and "i=(Inf ?R X {b,a})" by blast
        then have "i=Sup R X {b,a}"
          by (simp add: Sup_def)
        then show "i \<in> ?rhs" using a1a2 by blast
      qed
    next
      show "?rhs \<subseteq> ?lhs"
      proof
        fix i assume "i \<in> ?rhs" then obtain a where a1a2:"a \<in> {a1,a2}" and "i=Sup R X {b,a}" by blast
        then have "i=Inf ?R X {b ,a}"
          by(simp add:Sup_def)
        then show "i \<in> ?lhs" using a1a2 by blast
      qed
    qed
    obtain B24:"Sup ?R X {Inf ?R X {b, a}|a. a \<in> {a1, a2}}=Inf R X {Sup R X {b, a}|a. a \<in> {a1, a2}}"
      by (simp add: Sup_def)
    obtain B25:"Sup R X {b, (Inf R X {a1, a2})} = Inf R X {Sup R X {b, a}|a. a \<in> {a1, a2}}"
      using A1 A7 A8 by blast
    then show "Inf ?R X {b, (Sup ?R  X {a1, a2})} = Sup ?R X {Inf ?R X {b, a}|a. a \<in> {a1, a2}}"
      using B23 B24 by presburger
  qed
  then have "Inf ?R X {b, (Sup ?R X A)} = Sup ?R X {Inf ?R X {b, a}|a. a \<in> A}" 
    using distr_finite2[of b X ?R]  A0 A2 A3 A4 B0 B1 by blast
  then show ?thesis
    by (simp add: Sup_def)
qed
  
lemma fin_distr2:"\<lbrakk>distributive_lattice R X; trans R X; antisym R X; refl R X; finite A;A \<noteq> {};A \<subseteq> X; b \<in> X\<rbrakk>\<Longrightarrow>Inf R X {b, (Sup R X  A)} = Sup R X {Inf R X {b, a}|a. a \<in> A}"
  using distr_finite2[of b X R A] by (simp add: distr_eq_dist1)

lemma fin_distr1:"\<lbrakk>distributive_lattice R X; trans R X; antisym R X; refl R X;finite A;A \<noteq> {};A \<subseteq> X; b \<in> X\<rbrakk>\<Longrightarrow>Sup R X { b, (Inf R X  A)} = Inf R X {Sup R X {b, a}|a. a \<in> A}" 
   using distr_finite1[of b X R A]  by (simp add: distr_eq_dist2)

lemma finite_ind_in:
  "\<lbrakk>refl R X; antisym R X; trans R X; is_inf_semilattice R X; finite I; I \<noteq> {}; (\<forall>i. i \<in> I \<longrightarrow> f i \<in> X)\<rbrakk> \<Longrightarrow>is_inf R X (f`I) (Inf R X (f`I))"
  by (simp add: image_subsetI inf_semilattice_finf)

subsection CompleteLattices

lemma csupD2:
  "\<lbrakk>ord R X; is_csup_semilattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup R X A x)"
  by (simp add: is_csup_semilattice_def)
lemma csupD4:
  "\<lbrakk>ord R X; is_csup_semilattice R X;  A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_sup R X A (Sup R X A)"
  by (metis csupD2 sup_equality)
lemma csupD50:
  "\<lbrakk>ord R X; is_csup_semilattice R X;  A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (Sup R X A) \<in> X"
  by (meson csupD4 is_supD1)


lemma csupD61:
  "\<lbrakk>ord R X; is_csup_semilattice R X;  A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> b \<in> ubd R X A \<Longrightarrow> (Sup R X A, b) \<in> R "
  by (meson csupD4 is_supD2)


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
  by (metis dual_order.refl is_csup_semilattice_def is_supD1 sup_maxI1)

lemma cinfD4:
  "\<lbrakk>ord R X; is_cinf_semilattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_inf R X A (Inf R X A)"
  by (metis antisym_on_converse cinfD2 is_sup_unique the1I2)

lemma clatD41:
  "\<lbrakk>ord R X; is_clattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_sup R X A (Sup R X A)"
  by (simp add: clatD21 sup_exI)

lemma cinfD50:
  "\<lbrakk>ord R X; is_cinf_semilattice R X; A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (Inf R X A) \<in> X"
  by (meson cinfD4 is_supD1)


lemma cinfD61:
  "\<lbrakk>ord R X; is_cinf_semilattice R X;  A \<subseteq> X; A \<noteq> {}\<rbrakk> \<Longrightarrow> b \<in> lbd R X A \<Longrightarrow> (b, Inf R X A) \<in> R "
  by (meson cinfD4 converseD is_supD2)

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
  by (metis bot.extremum_uniqueI csupD4 dual_order.trans is_sup_iso1)

lemma sup_iso1:
  "\<lbrakk>ord R X;is_clattice R X; A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> (Sup R X A, Sup R X B)\<in>R"
  by (metis clatD21 dual_order.trans is_sup_iso1 sup_equality)

lemma sup_iso2:
  "\<lbrakk>ord R X;is_clattice R X; is_clattice R Y;A \<subseteq> Y; Y \<subseteq> X; Y \<noteq> {}\<rbrakk> \<Longrightarrow> (Sup R X A, Sup R Y A)\<in>R"
  by (meson antisym_on_subset clatD21 is_sup_iso2 order_trans sup_equality2 trans_on_subset)

lemma inf_anti1:
  "\<lbrakk>ord R X; is_clattice R X; A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> (Inf R X B, Inf R X A)\<in>R"
  by (meson clatD22 converseD dual_order.trans inf_equality2 is_sup_iso1)

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

lemma dual_isotone:
  "isotone Rx X Ry f \<longleftrightarrow> isotone (dual Rx) X (dual Ry) f"
  unfolding isotone_def converse_def by blast

lemma isotone_emp:
  "isotone Rx {} Ry f"
   by(blast intro:isotoneI1)

lemma isotoneD41: 
   "\<lbrakk>isotone R X Ry f; b \<in>ubd R X A; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f b) \<in> ubd Ry (f`X) (f`A)"
proof(rule ubdI)
  show "isotone R X Ry f \<Longrightarrow> b \<in> ubd R X A \<Longrightarrow> A \<subseteq> X \<Longrightarrow> f b \<in> f ` X" using ubdD1 by fastforce
  show " \<And>y. isotone R X Ry f \<Longrightarrow> b \<in> ubd R X A \<Longrightarrow> A \<subseteq> X \<Longrightarrow> y \<in> f ` A \<Longrightarrow> (y, f b) \<in> Ry"
  proof-
    fix y assume A0:" isotone R X Ry f " and A1:"b \<in> ubd R X A" and A2:"A \<subseteq> X" and A3:"y \<in> f`A"
    then obtain a where B0:"a \<in> A" and B1:"f a = y"  by blast
    then obtain B2:"(a, b)\<in>R"   by (meson A1 ubdD2)
    then obtain B3:"(f a, f b)\<in>Ry"  by (meson A0 A1 A2 B0 isotoneD1 subsetD ubdD1)
    then show "(y, f b)\<in>Ry"   by (simp add: B1)
  qed
qed

lemma isotoneD42: 
  "\<lbrakk>isotone R X Ry f; b \<in>lbd R X A; A \<subseteq> X\<rbrakk> \<Longrightarrow> (f b) \<in> lbd Ry (f`X) (f`A)"
  using isotoneD41[of "dual R" X "dual Ry" f b] dual_isotone by blast

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

lemma extensiveD3:
  "\<lbrakk>trans R X;(f`X) \<subseteq> X;extensive R X f; x \<in> X; y \<in> X; (x, y)\<in>R\<rbrakk> \<Longrightarrow> (x,f y)\<in>R"
  using extensiveD1[of R X f y] trans_onD[of X R x y "f y"] by blast

lemma extensiveD4:
  "\<lbrakk>trans R X; extensive R X f; (f`X) \<subseteq> X; x1 \<in> X;x2 \<in> X; (f x2) \<in> X;  (f x1, f x2)\<in>R\<rbrakk> \<Longrightarrow> (x1, (f x2))\<in>R"
  using extensiveD1[of R X f x1] trans_onD[of X R x1 "f x1" "f x2"] by blast

lemma extensive_ub:
  "trans R X \<Longrightarrow> extensive R X f \<Longrightarrow> f ` X \<subseteq> X \<Longrightarrow> A \<subseteq> X \<Longrightarrow> b \<in> ubd R X (f ` A) \<Longrightarrow> a \<in> A \<Longrightarrow> (a, b) \<in> R"
proof-
  fix a assume A0:"trans R X" and A1:"extensive R X f" and A2:"f`X \<subseteq> X" and A3:"A \<subseteq> X" and A4:" b \<in> ubd R X (f ` A)" and A5:"a \<in> A"
    then have "(a, f a)\<in>R" by (metis extensiveD1 in_mono)  
    also have "(f a, b)\<in>R" using A4 A5 ubdD2 by fastforce 
    then show "(a,b)\<in>R" using A0 trans_onD[of X R a "f a" b]  by (metis A2 A3 A4 A5 calculation image_subset_iff subsetD ubdD1)
qed
  


lemma extensive_ub_imp:
  "\<lbrakk>trans R X; extensive R X f ; (f`X \<subseteq> X); A \<subseteq> X ; b \<in> ubd R (f`X) (f`A) \<rbrakk> \<Longrightarrow> b \<in> ubd R X A"
  by (metis extensive_ub subset_eq ubdI ubd_iso2 ubd_sub)


lemma extensive_ub_imp2:
  "\<lbrakk>trans R X;extensive R X f; (f`X \<subseteq> X); A \<subseteq> X; b \<in> ubd R X (f`A)\<rbrakk> \<Longrightarrow> b \<in> ubd R X A"
  by (meson extensive_ub ubdD1 ubdI)

lemma is_iso_extD1:
  "\<lbrakk>isotone R X R f;  extensive R X f;  (f`X \<subseteq> X);  x \<in> X\<rbrakk> \<Longrightarrow> (f x, f (f x))\<in>R"
  by (simp add: extensive_def image_subset_iff)

lemma is_iso_sup:
  "isotone R X R f \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_sup R X A x \<Longrightarrow> is_sup R (f`X) (f`A) y  \<Longrightarrow> (y, f x)\<in>R"
  by (simp add: greatestD is_supD2 is_sup_def isotoneD41)

lemma is_iso_inf:
  "isotone R X R f \<Longrightarrow> A \<subseteq> X \<Longrightarrow> is_inf R A X x \<Longrightarrow> is_inf R (f`X) (f`A) y  \<Longrightarrow> (f x, y)\<in>R"
  using is_iso_sup[of "dual R" X f A x y] dual_isotone[of R X R f] by (metis converseD greatestI2 is_supD1 subsetD sup_maxE1)

subsection Idempotency

lemma idempotentI1:
  "(\<And>x. x \<in> X \<Longrightarrow> (f (f x) = f x)) \<Longrightarrow> idempotent X f"
  by (simp add: idempotent_def)

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

lemma closureI1:
  "\<lbrakk>extensive R X f; idempotent X f; isotone R X R f; (f`X \<subseteq> X)\<rbrakk> \<Longrightarrow> closure R X f"
  by (simp add: closure_def)

lemma closureI3:
  "\<lbrakk>trans R X; refl R X; antisym R X;extensive R X f; f`X \<subseteq> X;  closure_cond R X f\<rbrakk> \<Longrightarrow> closure R X f"
  by (simp add: closure_def idempotentI3 isotoneI2)

lemma closureD:
  "closure R X f \<Longrightarrow> extensive R X f \<and> idempotent X f \<and> isotone R X R f \<and> (f`X \<subseteq> X)"
  by (simp add: closure_def)


subsection ClosureRanges
lemma clrI1:
  "\<lbrakk>C \<noteq> {}; C \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> (\<exists>c. is_least R (ubd R C {x}) c)) \<rbrakk> \<Longrightarrow> clr R X C"
  by (simp add:closure_range_def)

lemma clrD1:
  "clr R X C \<Longrightarrow> (C \<noteq> {}) \<and> (C \<subseteq> X) \<and> (\<forall>x. x \<in> X \<longrightarrow> (\<exists>c. is_least R (ubd R C {x}) c)) "
  by (simp add:closure_range_def)

lemma clrD2:
  "clr R X C \<Longrightarrow> (\<forall>x. x \<in> X \<longrightarrow> (\<exists>c. is_sup R C {x} c)) "
  by (simp add: closure_range_def is_sup_def)


definition cl_from_clr::"'a rel \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "cl_from_clr R C \<equiv> (\<lambda>x. Least R  (ubd R  C {x}))"

lemma clr_equality:
  assumes A0:"antisym R X" and A1:"clr R X C" and A2:"is_least R (ubd R  C {x}) c"
  shows " cl_from_clr R C x = c"
proof-
  obtain B0:"(ubd R  C {x}) \<subseteq> X" and B1:"c \<in> X" 
   by (meson A1 A2 clrD1 greatestD subsetD subset_trans ubd_sub)
  then show "cl_from_clr R C x = c" 
    unfolding cl_from_clr_def Least_def using A0 A1 A2 greatest_equality3
    by (metis Greatest_def antisym_on_converse antisym_on_subset)
qed


lemma clr_induced_closure_id:
  assumes A0:"refl R C" and A1:"antisym R X" and A2:"clr R X C"
  shows "(cl_from_clr R C)`X = C"
proof
  show B0:"(cl_from_clr R C)`X  \<subseteq> C"
  proof
    fix y assume L:"y \<in> (cl_from_clr R C)`X"
    then obtain x where "x \<in> X" and "is_least R (ubd R C {x}) y"  
      using A1 A2 clrD1 clr_equality by fastforce
    then show "y \<in> C" 
      by (meson greatestD ubdD1)
  qed
  next
  show B1:"C \<subseteq> (cl_from_clr R C)`X"
  proof
    fix y assume B10:"y \<in> C"
    then obtain "is_least R (ubd R C {y}) y"  
      by (metis A0 greatestI2 is_sup_def reflE1 singletonD singletonI sup_maxE1)
    also obtain "y \<in> X"  
      using A2 B10 clrD1 by blast
    then show "y \<in> (cl_from_clr R C)`X"
      by (metis A1 A2 calculation clr_equality rev_image_eqI)
  qed
qed
  
lemma cl_is_closure:
   assumes A0:"refl R C" and A1:"antisym R X" and A2:"trans R X" and A3:"clr R X C"
  shows "closure R X (cl_from_clr R C)"
proof(rule closureI1)
  obtain B0:"C \<subseteq> X" and B1:"refl R C"  and B2:"trans R C" by (meson A0 A2 A3 clrD1 trans_on_subset) 
  then show B3:"cl_from_clr R C ` X \<subseteq> X" by (simp add: A1 A3 clr_induced_closure_id)
  show B4:"isotone R X R (cl_from_clr R C)"
  proof(rule isotoneI1)
    fix x1 x2 assume A4:"x1 \<in> X" and A5:"x2 \<in> X" and A6:"(x1,x2)\<in>R"
    then obtain B30:"ubd R C {x2} \<subseteq> ubd R C {x1}" using ubd_iso3[of x1 X x2 R C] A2 B0 by fastforce
    obtain c1 c2 where B31:"is_least R (ubd R C {x1}) c1" and B32:"is_least R (ubd R C {x2}) c2"  by (meson A3 A4 A5 clrD1)
    obtain B33:"(c1,c2)\<in>R"  by (meson B30 B31 B32 converseD is_greatest_iso2)
    then show "(cl_from_clr R C x1, cl_from_clr R C x2) \<in> R" using A1 A3 B31 B32 clr_equality by fastforce
  qed
  show B5:"extensive R X (cl_from_clr R C)"
  proof(rule extensiveI1)
    fix x assume A7:"x \<in> X"
    show "(x, cl_from_clr R C x)\<in>R" by (metis A1 A3 A7 clrD1 clr_equality greatestD singletonI ubdD1)
  qed
  show "idempotent X (cl_from_clr R C)"
  proof(rule idempotentI1)
    fix x assume A8:"x \<in> X"
    then obtain xc where B0:"xc \<in> X" and B1:"is_least R (ubd R C {x}) xc" by (meson A3 clrD1 greatestD subsetD ubd_sub)
    then obtain B2:"is_least R (ubd R C {xc}) xc"  by (metis converse_iff greatestD greatestI2 ubd_singleton_mem)
    then show "cl_from_clr R C (cl_from_clr R C x) = cl_from_clr R C x" using A1 A3 B1 clr_equality by fastforce
  qed
qed

lemma closure_is_clr:
  assumes A0:"antisym R X" and A1:"closure R X f" and A2:"X \<noteq> {}"
  shows closure_is_clr1:"f ` X \<noteq> {}"  and 
        closure_is_clr2:"f ` X \<subseteq> X" and
        closure_is_clr3:"\<And>x. x \<in> X \<Longrightarrow>is_least R (ubd R (f`X) {x}) (f x)" and
        closure_is_clr4:"\<And>x. x \<in> X \<Longrightarrow> \<exists>c. is_least R (ubd R (f ` X) {x}) c" and
        closure_is_clr5:"clr R X (f`X)"
proof-
  show B0:"f ` X \<noteq> {}" by (simp add: A2)
  show B1:"f ` X \<subseteq> X" using A1 closureD by blast
  show B2:"\<And>x. x \<in> X \<Longrightarrow> is_least R (ubd R (f`X) {x}) (f x)"
  proof-
    fix x assume A3:"x \<in> X"
    obtain B20:"extensive R X f" and B21:"isotone R X R f" and B22:"idempotent X f" using A1 closureD by blast 
    show B23:"is_least R (ubd R (f`X) {x}) (f x)"
    proof(rule greatestI2)
      show "f x \<in> ubd R (f ` X) {x}" by (meson A3 B20 extensiveD1 image_eqI ubd_singleton_mem)
      show "\<And>a. a \<in> ubd R (f ` X) {x} \<Longrightarrow> (a, f x) \<in> dual R"   by (metis A3 B1 B21 B22 converseI idempotent_isotoneD1 ubd_singleton_mem)
    qed
  qed
  then show B3:"\<And>x. x \<in> X \<Longrightarrow> \<exists>c. is_least R (ubd R (f ` X) {x}) c" by blast
  show "clr R X (f`X)"  using B0 B1 B3 closure_range_def by blast
qed


lemma closure_induced_clr_id:
  "\<lbrakk>antisym R X; closure R X f; X \<noteq> {};x\<in>X\<rbrakk>  \<Longrightarrow> (cl_from_clr R (f`X)) x = f x"
  by (simp add: closure_is_clr3 closure_is_clr5 clr_equality)

lemma closure_induced_clr_dual:
  "\<lbrakk>antisym R X; closure R X f1; closure R X f2; (\<And>x. x \<in> X \<Longrightarrow> (f1 x,f2 x)\<in>R)\<rbrakk> \<Longrightarrow> (f2`X) \<subseteq> (f1`X)"
  by (smt (verit, ccfv_SIG) antisym_on_def closureD extensive_def idempotentD3 in_mono rev_image_eqI subsetI)

                    
lemma clr_induced_closure_dual:
  "\<lbrakk>refl R C; antisym R X;clr R X C1; clr R X C2; C2 \<subseteq> C1; x \<in> X\<rbrakk> \<Longrightarrow> (((cl_from_clr R C1) x),((cl_from_clr R C2) x))\<in>R"
  by (metis clrD1 clr_equality converseD is_greatest_iso2 ubd_iso2)

lemma extensiveI4:
  "refl R X \<Longrightarrow> (\<And>A s. A \<subseteq> X \<Longrightarrow> is_sup R X A s \<Longrightarrow> (s,f s)\<in>R) \<Longrightarrow>  f`X \<subseteq> X \<Longrightarrow> extensive R X f"
proof(rule extensiveI1)
  fix x assume A0:"refl R X" and A1:"(\<And>A s. A \<subseteq> X \<Longrightarrow> is_sup R X A s \<Longrightarrow> (s,f s)\<in>R) " and A2:" f`X \<subseteq> X" and A3:"x \<in> X"
  then obtain B0:"is_sup R X {x} x" and B1:"{x} \<subseteq> X"  using A0 A3 is_supI1 reflD2 by fastforce 
  then show "(x, f x) \<in> R"  using A1 by presburger  
qed

lemma idempotentI4:
  assumes A0:"refl R X" and
          A1:"antisym R X" and 
          A2:"(\<And>A s1 s2. A \<subseteq> X \<Longrightarrow> is_sup R X A s1 \<Longrightarrow> is_sup R X (f`A) s2 \<Longrightarrow> f s1 = f s2)" and
          A3:"f`X \<subseteq> X" 
  shows "idempotent X f"
proof(rule idempotentI1)
  fix x assume A5:"x \<in> X"
  obtain B0:"is_sup R X {x} x" and B1:"{x} \<subseteq> X" and B2:"f x \<in> X"  using A0 A3 A5 is_supI1 reflD2 by fastforce 
  then obtain B3:"is_sup R X ({f x}) (f x)" by (metis A0 is_supI1 refl_def singletonD singletonI)
  then obtain B4:"is_sup R X (f`{x}) (f x)"  by force
  then show "f (f x) = f x"  by (metis A2 B0 B1)
qed


lemma isotoneI4:
  assumes A0:"(\<And>A s. \<lbrakk>A \<subseteq> X; is_sup R X A s\<rbrakk> \<Longrightarrow> is_sup R (f`X) (f`A) (f s))" and A1:"f`X \<subseteq>X " and A2:"refl R X"
  shows "isotone R X R f"
proof(rule isotoneI1)
  show "\<And>x1 x2. \<lbrakk>x1 \<in> X;x2 \<in> X; (x1, x2)\<in>R\<rbrakk> \<Longrightarrow> (f x1,f x2)\<in>R"
  proof-
    fix x1 x2 assume A3:"x1 \<in> X" and A4:"x2 \<in> X" and A5:"(x1,x2)\<in>R"
    have B01:"is_sup R X {x1, x2} x2"  using A2 A4 A5 is_supI1 reflD2 by fastforce
    have B02:"is_sup R (f`X) (f`{x1, x2}) (f x2)"  by (meson A0 A3 A4 B01 empty_subsetI insert_subset)
    then show "(f x1, f x2)\<in>R"     by (simp add: is_supD3) 
  qed
qed

lemma induced_clr_props:
  assumes A0:"refl R X" and A1:"antisym R X" and A2:"clr R X C" and A3:"A \<subseteq> C" and A4:"is_inf R X A i"
  shows clrD8:"(cl_from_clr R C) i \<in> lbd R X A" and
        clrD9:"((cl_from_clr R C) i,i)\<in>R" and
        clrD10:"(cl_from_clr R C) i = i" and
        clrD11:"i \<in> C"
proof-
  obtain c where B0:"is_least R (ubd R C {i}) c" by (meson A2 A4 clrD1 is_supD1)
  then obtain B1:"c \<in> X" and B2:"cl_from_clr R C i \<in> X" by (metis A1 A2 clrD1 clr_equality greatestD subsetD ubdD1)
  show B3:"(cl_from_clr R C) i \<in> lbd R X A"
  proof(rule ubdI)
    show B30:"cl_from_clr R C i \<in> X" by (simp add:B2)
    show B31:"\<And>a. a \<in> A \<Longrightarrow> (a, cl_from_clr R C i) \<in> dual R"  by (metis A1 A2 A3 A4 B0 clr_equality converseD greatestD is_supD3 subsetD ubd_singleton_mem)
  qed
  show B4:"((cl_from_clr R C) i,i)\<in>R" using A4 B3 is_supD2 by fastforce 
  show B5:"(cl_from_clr R C) i = i"  by (metis A1 A2 A4 B0 B2 B4 antisym_onD clr_equality greatestD is_supD1 ubd_singleton_mem) 
  show B6:"i \<in> C" by (metis A1 A2 B0 B5 clr_equality is_supD1 sup_empty ubdD1)
qed

lemma moore_clI1:
  assumes A0:"C \<subseteq> Pow X" and inf_closed:"(\<And>E. E \<subseteq> C\<Longrightarrow> (X \<inter> (\<Inter>E)) \<in> C)" 
  shows "clr (pwr X) (Pow X) C"
proof(rule clrI1)
  show B0:"C \<noteq> {}"  using inf_closed by blast
  show B1:"C \<subseteq> Pow X" by(simp add:A0)
  show B2:"\<And>x. x \<in> Pow X \<Longrightarrow> \<exists>c. is_least (pwr X) (ubd (pwr X) C {x}) c"
  proof-
    fix x assume A1:"x \<in> Pow X"
    let ?c="(X \<inter> (\<Inter>(ubd (pwr X) C {x})))"
    obtain B20:"?c \<in> C"  by (simp add: inf_closed ubd_sub)
    have B21:"is_least (pwr X) (ubd (pwr X) C {x})  ?c"
    proof(rule greatestI2)
      show B22:"?c \<in> ubd (pwr X) C {x}" 
      proof(rule ubdI)
        show "?c \<in> C" by (simp add:B20)
        obtain "x \<subseteq> ?c" by (meson A1 Int_subset_iff PowD le_Inf_iff pwr_mem_iff ubd_singleton_mem)
        then show "\<And>a. a \<in> {x} \<Longrightarrow> (a, ?c) \<in> pwr X"   by (simp add: pwr_memI)
      qed
      show B23:"\<And>a. a \<in> ubd (pwr X) C {x} \<Longrightarrow> (a,?c) \<in> dual (pwr X)"  by (meson B1 is_supD1 powrel4 subset_trans ubd_sub)
    qed
    then show "\<exists>c. is_least (pwr X) (ubd (pwr X) C {x}) c" by blast
  qed
qed
  

lemma moore_clI3:
  "C \<subseteq> Pow X \<Longrightarrow> X \<in> C \<Longrightarrow> (\<And>E. E \<subseteq> C \<Longrightarrow> E \<noteq> {} \<Longrightarrow> (\<Inter>E) \<in> C) \<Longrightarrow> clr (pwr X ) (Pow X) C"
  by (metis Inf_insert empty_not_insert insert_subsetI moore_clI1)

lemma clr_cinf_semilattice1:
  assumes A0:"clr R X C" and
          A1:"is_cinf_semilattice R X" and 
          A2:"antisym R X" and 
          A3:"refl R X" and
          A4:"trans R X" and 
          A5:"A \<subseteq> C" and
          A6:"A \<noteq> {}"
  shows "(\<exists>x. is_inf R C A x \<and> is_inf R X A x)"
proof-
  obtain B0:"C \<subseteq> X" and B1:"A \<subseteq> X" using A0 A5 clrD1 by blast
  then obtain i where B2:"is_inf R X A i" using A1 A2 A4 A6 cinfD2 by blast
  then obtain B3:"i \<in> C"  by (meson A0 A2 A3 A5 clrD11)
  have B4:"is_inf R C A i"
  proof(rule is_supI1)
    show "i \<in> C" by (simp add:B3)
    show "\<And>a. a \<in> A \<Longrightarrow> (a, i) \<in> dual R"  by (meson B2 is_supD3)
    show "\<And>b. b \<in> C \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (a, b) \<in> dual R) \<Longrightarrow> (i, b) \<in> dual R" by (meson B0 B2 is_supD1 subsetD)
  qed
  from B2 B4 show ?thesis by blast
qed
   


lemma clr_clattice:
  assumes A0:"clr R X C" and A1:"is_clattice R X" and A2:"antisym R X" and A3:"refl R X" and A4:"trans R X"
  shows clr_clattice1:"\<And>A. A \<subseteq> C \<Longrightarrow> (\<exists>x. is_sup R C A x \<and> is_inf R X (ubd R C A) x)" and
        clr_clattice2:"is_clattice R C"
proof-
  show "\<And>A. A \<subseteq> C \<Longrightarrow> (\<exists>x. is_sup R C A x \<and> is_inf R X (ubd R C A) x)"
  proof-
    fix A assume A2:"A \<subseteq> C" then have B0:"A \<subseteq> X"   using A0 clrD1 by blast
    also have B1:"ubd R C A \<subseteq> X" by (meson A0 clrD1 dual_order.trans ubd_sub)
    then obtain x where B2:"is_inf R X (ubd R C A) x"  using A1 A4 assms(3) clatD22 by blast
    then have B1:"is_sup R C A x"   by (metis A0 A2 A3 assms(3) clrD11 clrD1 converse_converse inf_if_sup_lb sup_in_subset ubd_sub)
    then show "(\<exists>x. is_sup R C A x \<and> is_inf R X (ubd R C A) x)"  using B2 by auto
  qed
  then show "is_clattice R C" by (metis A0 closure_range_def is_clattice_def)
qed


section Subsets
subsection Directedness

lemma is_dirI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X\<rbrakk> \<Longrightarrow> (\<exists>c \<in> X.  (a, c) \<in> R \<and>  (b, c) \<in> R)) \<Longrightarrow> is_dir X R"
  by (simp add: is_dir_def)

lemma is_dirE1:
  "is_dir X R \<Longrightarrow> a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> (\<exists>c \<in> X. (a, c)\<in>R \<and> (b, c)\<in>R)"
  by (simp add: is_dir_def)

lemma is_dirD1:
  "is_dir X R \<Longrightarrow> (\<And>a b. \<lbrakk>a\<in>X;b\<in>X\<rbrakk>\<Longrightarrow>(\<exists>c\<in>X.(a,c)\<in>R\<and>(b,c)\<in>R))"
  by (simp add: is_dir_def)

lemma dir_finite1:
  assumes A0: "\<And>a1 a2. a1\<in>X \<Longrightarrow>a2\<in>X\<Longrightarrow>(\<exists>c \<in> X. (a1,c)\<in>R \<and> (a2,c)\<in>R)" and 
          A1:"finite A" and
          A2:"A \<noteq> {}" and
          A3:"A \<subseteq> X" and 
          A4:"trans R X" 
  shows "(\<exists>c \<in> X. \<forall>a. a \<in> A \<longrightarrow> (a, c)\<in>R)"
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


lemma inf_dwdir:
  "is_sup_semilattice R X \<Longrightarrow> is_dir X R" and
  "is_inf_semilattice R X \<Longrightarrow> is_dir X (converse R)" 
proof-
  show "is_sup_semilattice R X \<Longrightarrow> is_dir X R"
  proof(rule is_dirI1)
    fix a b assume A0:"is_sup_semilattice R X" and A1:"a\<in>X" and A2:"b\<in>X"
    then obtain c where "is_sup R X {a,b} c" by (meson ssupD2)  
    then show "\<exists>c\<in>X. (a, c) \<in>  R \<and> (b, c) \<in> R" by (meson insertCI is_supD1)
  qed
  show "is_inf_semilattice R X \<Longrightarrow> is_dir X (converse R)"
  proof(rule is_dirI1)
    fix a b assume A0:"is_inf_semilattice R X" and A1:"a\<in>X" and A2:"b\<in>X"
    then obtain c where "is_inf R X {a,b} c"  by blast
    then show "\<exists>c\<in>X. (a, c) \<in> dual R \<and> (b, c) \<in> dual R"
    by (meson insertCI is_supD1)
  qed
qed
  
subsection OrderClosure
lemma is_ord_clI1:
  "(\<And>a b. \<lbrakk>a \<in> A; b \<in> X; (a,b)\<in>R\<rbrakk> \<Longrightarrow> b \<in> A ) \<Longrightarrow> is_ord_cl X A R"
  by (auto simp add:is_ord_cl_def)

lemma is_ord_clE1:
  "is_ord_cl X A R  \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> X \<Longrightarrow> (a, b)\<in>R \<Longrightarrow> b \<in> A "
   by (simp add:is_ord_cl_def)

lemma is_ord_clD1:
  "is_ord_cl X A R \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> A; b \<in> X; (a,b)\<in>R\<rbrakk> \<Longrightarrow> b \<in> A )"
   by (simp add:is_ord_cl_def)

lemma is_ord_cl_unin:
  assumes A0:"(\<And>E. E \<in>\<E> \<Longrightarrow> is_ord_cl X E R)" 
  shows is_ord_cl_un:"is_ord_cl X (\<Union>\<E>) R" and
        is_ord_cl_in:"\<E> \<noteq> {} \<Longrightarrow> is_ord_cl X (\<Inter>\<E>) R"
proof-
  show "is_ord_cl X (\<Union>\<E>) R"  using A0 unfolding is_ord_cl_def by blast
  show "\<E> \<noteq> {} \<Longrightarrow> is_ord_cl X (\<Inter>\<E>) R"
  proof-
    assume A1:"\<E> \<noteq> {}"
    then show "is_ord_cl X (\<Inter>\<E>) R" using A0 unfolding is_ord_cl_def by blast
  qed
qed

subsection Filters
subsubsection DefinitionAndBasicProps

lemma is_filterI1:
  "\<lbrakk>F \<noteq> {}; F \<subseteq> X; is_dir F (dual R); is_ord_cl X F R\<rbrakk> \<Longrightarrow> is_filter R X F"
  by (simp add: is_filter_def)

lemma is_filterD1:
  "is_filter R X F \<Longrightarrow> (F \<noteq> {}) \<and> (F \<subseteq> X) \<and> is_dir F (dual R) \<and> (is_ord_cl X F R)"
  by (simp add: is_filter_def)

lemma top_filters1:
  assumes A0:"is_filter R X F" and A1:"is_greatest R X top"
  shows "top \<in> F"
proof-
  obtain f where B0:"f \<in> F" by (metis A0 ex_in_conv is_filterD1)
  then obtain B1:"f \<in> X" and B2:"(f,top)\<in>R"  by (meson A1 assms greatestD in_mono is_filterD1)
  then show "top \<in> F"  by (meson A1 B0 assms greatestD is_filterD1 is_ord_clE1)
qed


lemma top_filters2:
 "\<lbrakk>refl R X; antisym R X; is_greatest R X top\<rbrakk> \<Longrightarrow> is_filter R X {top}"
proof-
  assume A1:"refl R X" and A2:"antisym R X" and A3:"is_greatest R X top"
  then obtain B0:"{top} \<noteq>{}" and B1:"{top} \<subseteq> X" and B2:"is_dir {top} (dual R)" and B3:"is_ord_cl X {top} R"
    by (simp add: antisym_on_def greatestD is_dir_def is_ord_cl_def)
  then show "is_filter R X {top}"  by (simp add: is_filter_def)
qed

lemma bot_filters1:
  "is_inf_semilattice R X \<Longrightarrow> is_filter R X X"
  by (simp add: is_filter_def inf_dwdir is_ord_cl_def is_sup_semilattice_def)

lemma filter_inf_closed1:
  assumes A0:"is_filter R X F" and A1:"a \<in> F" and A2:"b \<in> F" and A3:"is_inf R X {a,b} i"
  shows "i \<in>F"
proof-
  obtain c where c0:"c \<in> F" and c1:"(c,a)\<in>R" and c2:"(c,b)\<in>R" 
    using A0 is_filterD1[of R X F] A1 A2 is_dirE1[of F "dual R" a b] by blast
  obtain "a \<in> X" and "b \<in> X" and "c \<in> X" using A0 A1 A2 c0 is_filterD1[of R X F] by blast
  then obtain "(c,i)\<in>R" and "i\<in>X" using A3 c1 c2 is_supD1 by fastforce
  then show "i \<in> F" using A0 c0 is_filterD1[of R X F] is_ord_clE1[of X F R c i] by blast
qed

lemma filter_inf_closed2:
  "\<lbrakk>antisym R X; is_inf_semilattice R X; is_filter R X F; a \<in> F; b \<in> F\<rbrakk> \<Longrightarrow> Inf R X {a, b} \<in> F"
  by (metis filter_inf_closed1 inf_equality is_filterD1 subset_eq)

lemma filter_inf_closed3:
  "\<lbrakk>antisym R X; trans R X; is_inf_semilattice R X; is_filter R X F; A \<subseteq> F; A \<noteq> {}; finite A\<rbrakk> \<Longrightarrow> Inf R X A \<in> F"
  by (simp add: filter_inf_closed2 finite_inf_closed2 is_filterD1)

subsection SetOfFilters

lemma filters_on_iff:
  "F \<in> filters_on R X \<longleftrightarrow> is_filter R X F"
  by (simp add: filters_on_def)

lemma pfilters_on_iff:
  "F \<in> pfilters_on R X \<longleftrightarrow> is_pfilter R X F"
  by (simp add: pfilters_on_def)

lemma is_pfilterD1: 
  "is_pfilter R X A \<Longrightarrow> is_filter R X A" 
  by(simp add:is_pfilter_def)

lemma is_pfilterD2:
  "is_pfilter R X A \<Longrightarrow>  X \<noteq> A"
  by(simp add:is_pfilter_def)

lemma is_pfilterI1:
  "\<lbrakk>is_filter R X A; X \<noteq> A\<rbrakk> \<Longrightarrow> is_pfilter R X A"
  by(simp add:is_pfilter_def)

lemma is_pfilterI2:
  "\<lbrakk>is_least R X bot; bot \<notin> A; is_filter R X A\<rbrakk> \<Longrightarrow> is_pfilter R X A"
  by (metis greatestD is_pfilterI1)

subsubsection FiltersClosureRange

lemma filter_inter:
  assumes A0:"is_inf_semilattice R X" and 
          A1:"is_greatest R X top" and 
          A2:"antisym R X" and 
          A3:"EF \<in> Pow (filters_on R X)" and
          A4:"EF \<noteq> {}"
  shows filter_inter1:"is_filter R X (\<Inter>EF)" and
        filter_inter2:"\<Inter>EF \<in> (filters_on R X)"
proof-
  let ?F="\<Inter>EF"
  obtain B0:"\<And>F. F \<in> EF \<Longrightarrow> is_filter R X F" using A3 filters_on_iff by fastforce
  obtain B1:"\<And>F. F \<in> EF \<Longrightarrow> top \<in> F" using A1 B0 top_filters1[of R X _ top] by blast
  obtain B2:"\<And>F. F \<in> EF \<Longrightarrow> F \<subseteq> X \<and> is_dir F (dual R) \<and> is_ord_cl X F R"  using B0 is_filterD1 by blast 
  show "is_filter R X (\<Inter>EF)"
  proof(rule is_filterI1)
    show F0:"?F \<noteq> {}" using B1 by auto
    show F1:"?F \<subseteq> X" using A4 B2 by auto
    show F2:"is_dir ?F (dual R)"
    proof(rule is_dirI1)
      fix a b assume A5:"a \<in> ?F" and A6:"b \<in> ?F"
      then obtain F23:"\<And>F. F \<in> EF \<Longrightarrow> Inf R X {a,b}\<in>F" 
        by (simp add: A0 A2 B0 filter_inf_closed2)
      also obtain F20:"a \<in> X" and F21:"b \<in> X" and F22:"Inf R X {a,b}\<in>X"  
        by (metis A0 A2 A5 A6 F1 inf_equality is_supD1 subset_iff)
      then obtain "Inf R X {a,b} \<in> ?F" and "(Inf R X {a,b},a)\<in>R" and "(Inf R X {a,b},b)\<in>R"  
        by (metis A0 A2 InterI calculation converseD inf_equality insertCI is_supD3)
      then show "\<exists>c \<in> ?F. (a,c)\<in>(dual R)\<and>(b,c)\<in>(dual R)" by blast
    qed
    show F3:"is_ord_cl X ?F R"  by (simp add: A4 B2 is_ord_cl_in)
  qed
  then show "?F \<in> filters_on R X" unfolding filters_on_def  by blast
qed


lemma filters_clr:
  assumes A0:"is_inf_semilattice R X" and 
          A1:"is_greatest R X top" and 
          A2:"antisym R X" 
  shows "clr (pwr X) (Pow X) (filters_on R X)"
proof(rule moore_clI3)
  show "filters_on R X \<subseteq> Pow X" unfolding filters_on_def using is_filterD1 by blast
  show "X \<in> filters_on R X" using bot_filters1[of X R] A0 filters_on_iff[of X R X] by blast
  show "\<And>E. E \<subseteq> filters_on R X \<Longrightarrow> E \<noteq> {} \<Longrightarrow> \<Inter> E \<in> filters_on R X" 
    using A0 A1 A2 filter_inter2[of X R top] by blast
qed

subsubsection FilterClosure

lemma filter_closure_memI1:
  "\<lbrakk>x \<in> X;  (\<exists>F. F \<subseteq> A \<and> finite F \<and> F \<noteq> {} \<and> (Inf R X F, x)\<in>R)\<rbrakk> \<Longrightarrow> x \<in> filter_closure R X A"
  unfolding filter_closure_def by auto

lemma filter_closure_memI2:
  "\<lbrakk>x \<in> X; F \<subseteq> A; finite F; F \<noteq> {}; (Inf R X F, x)\<in>R\<rbrakk> \<Longrightarrow> x \<in> filter_closure R X A"
  unfolding filter_closure_def by auto

lemma filter_closure_memD1:
  "\<lbrakk>A \<noteq> {}; x \<in> filter_closure R X A\<rbrakk> \<Longrightarrow> (\<exists>F. F \<subseteq> A \<and> finite F \<and> F \<noteq> {} \<and> (Inf R X F, x)\<in>R)"
  by (simp add: filter_closure_def)

lemma filter_closure_singleton:
  assumes ref:"refl R X" and ant:"antisym R X" and asub:"A \<subseteq> X" and amem:"a \<in> A"
  shows "a \<in> filter_closure R X A"
proof-
  obtain B0:"a \<in> X" and B1:"{a}\<subseteq>A" and B2:"finite {a}" and B3:"{a}\<noteq>{}" using amem asub by blast 
  also obtain "Inf R X {a} = a" and "(a,a)\<in>R" 
      using B0 ant ref inf_singleton2[of X R a] reflD2[of R X a] by blast
  then show ?thesis using filter_closure_memI2[of a X "{a}" A R] B0 B1 B2 B3 by auto
qed

lemma filter_cl0:
  "\<lbrakk>refl R X;antisym R X;A \<subseteq> X\<rbrakk> \<Longrightarrow> A \<subseteq> filter_closure R X A"
  by (simp add: filter_closure_singleton subsetI)

lemma filter_closure:
  assumes por:"pord R X"
  shows filter_closure1_ne:"is_inf_semilattice R X \<Longrightarrow> (\<And>A. A \<in> Pow_ne X \<Longrightarrow> is_ord_cl X (filter_closure R X A) R)" and
        filter_closure1_em:"is_greatest R X m \<Longrightarrow> is_ord_cl X (filter_closure R X {}) R" and
        filter_closure2_ne:"is_inf_semilattice R X \<Longrightarrow> (\<And>A. A \<in> Pow_ne X \<Longrightarrow> is_dir (filter_closure R X A) (converse R))" and
        filter_closure2_em:"is_greatest R X m \<Longrightarrow> is_dir (filter_closure R X {}) (converse R)"
proof-
  show P0:"is_inf_semilattice R X \<Longrightarrow> (\<And>A. A \<in> Pow_ne X \<Longrightarrow> is_ord_cl X (filter_closure R X A) R)"
  proof-
    assume isl:"is_inf_semilattice R X" 
    show "\<And>A. A \<in> Pow_ne X \<Longrightarrow> is_ord_cl X (filter_closure R X A) R"
    proof-
      fix A assume amem:"A \<in> Pow_ne X" then obtain asub:"A \<subseteq> X" and ane:"A \<noteq> {}" using Pow_ne_def by blast
      then obtain frm:"filter_closure R X A= {x \<in> X. \<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and> (Inf R X F,  x) \<in> R}"
        by (simp add: filter_closure_def)
      have "\<And>a b. \<lbrakk>a \<in> filter_closure R X A; b \<in> X;(a, b) \<in> R\<rbrakk> \<Longrightarrow> b \<in> filter_closure R X A"
      proof-
        fix a b assume A0:"a \<in> filter_closure R X A" and A1:"b\<in>X" and A2:"(a,b)\<in>R"
        then obtain F where B0:"F \<subseteq> A" and B1:"finite F" and B2:"F \<noteq> {}" and B3:"(Inf R X F,a)\<in>R"
          using filter_closure_memD1[of A a R X] ane by auto
        obtain B4:"a \<in> X" and B5:"F \<subseteq> X" 
          using A0 B0 asub frm by auto
        obtain B6:"Inf R X F \<in> X"
          by (simp add: B1 B2 B5 bot_filters1 filter_inf_closed2 finite_inf_closed2 por isl)
        then obtain B7:"(Inf R X F,b)\<in>R" 
          using A1 A2 B3 B4 B6 por trans_onD[of X R "Inf R X F" a b] by auto
        then show "b \<in> filter_closure R X A" 
          using B0 B1 B2 B7 by (simp add: A1 filter_closure_memI2)
      qed
      then show "is_ord_cl X (filter_closure R X A) R" using is_ord_clI1 by blast
    qed
  qed
  show P1:"is_greatest R X m \<Longrightarrow> is_ord_cl X (filter_closure R X {}) R"
  proof-
    assume top:"is_greatest R X m" 
    then obtain "(filter_closure R X {}) = {m}"
      by (simp add: filter_closure_def greatest_equality3 por)
    then show ?thesis
      by (simp add: is_filterD1 por top top_filters2) 
  qed
  show P2:"is_inf_semilattice R X \<Longrightarrow> (\<And>A. A \<in> Pow_ne X \<Longrightarrow> is_dir (filter_closure R X A) (converse R))"
  proof-
     assume isl:"is_inf_semilattice R X" 
     show "\<And>A. A \<in> Pow_ne X \<Longrightarrow> is_dir (filter_closure R X A) (converse R)"
     proof-
      fix A assume amem:"A \<in> Pow_ne X" then obtain asub:"A \<subseteq> X" and ane:"A \<noteq> {}" using Pow_ne_def by blast
	    obtain frm:"filter_closure R X A= {x \<in> X. \<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and> (Inf R X F,  x) \<in> R}"
	  	    by (simp add: filter_closure_def ane)
	    let ?FC="filter_closure R X A"
      show "is_dir (filter_closure R X A) (converse R)"
      proof(rule is_dirI1)
		    fix a b assume A6:"a \<in> ?FC"  and A7:"b \<in> ?FC" 
		    obtain Fa where B01:"Fa \<subseteq> A" and B02:"finite Fa" and B03:"Fa \<noteq> {}" and B04:"(Inf R X Fa, a)\<in>R"
			    by (meson A6 filter_closure_memD1 ane) 
		    obtain Fb where B05:"Fb \<subseteq> A" and B06:"finite Fb" and B07:"Fb \<noteq> {}" and B08:"(Inf R X Fb, b)\<in>R"
			    by (meson A7 filter_closure_memD1 ane)
		    obtain B10:"Fb \<subseteq> X" and B11:"Fa \<subseteq> X" and B12:"a \<in> X" and B13:"b \<in> X"
			    using A6 A7 B01 B05 asub frm by force 
		    let ?Fab="Fa \<union> Fb"
		    obtain B14:"?Fab \<subseteq> A" and B15:"?Fab \<subseteq> X" and B16:"Fa \<subseteq> ?Fab" and B17:"Fb \<subseteq> ?Fab"	
			    by (simp add: B01 B05 B10 B11)
		    obtain B18:"finite ?Fab" and B19:"?Fab \<noteq> {}"
			    using B02 B03 B06 by blast
		    obtain B20:"Inf R X ?Fab \<in> X"
			    by (metis B15 B18 B19 bot_filters1 filter_inf_closed3 por isl) 
		    obtain B21:"Inf R X ?Fab \<in> ?FC"
			    by (meson B14 B18 B19 B20 filter_closure_memI2 por reflD2)
		    obtain B22:"is_inf R X ?Fab (Inf R X ?Fab)"
			    by (metis B15 B18 B19 Fpow_ne_iff antisym_on_converse inf_equality2 is_sup_semilattice_def por isl sup_semilattice_fsup trans_on_converse) 
		    obtain B23:"is_inf R X Fa (Inf R X Fa)" and B24:"is_inf R X Fb (Inf R X Fb)"
			    by (metis B02 B03 B06 B07 B10 B11 Fpow_ne_iff antisym_on_converse inf_equality2 is_sup_semilattice_def por isl sup_semilattice_fsup trans_on_converse)
		    obtain B25:"(Inf R X ?Fab, Inf R X Fa)\<in>R" and B26:"(Inf R X ?Fab, Inf R X Fb)\<in>R"
			    by (meson B16 B17 B22 B23 B24 converse_iff is_sup_iso1)
		    then obtain B27:"(Inf R X ?Fab, a) \<in> R" and B28:"(Inf R X ?Fab, b)\<in>R"
			    by (meson B04 B08 B12 B13 B20 B23 B24 is_supD1 por trans_onD)
		    then show "\<exists>c\<in>filter_closure R X A. (a, c) \<in> dual R \<and> (b, c) \<in> dual R"
			    using B21 by blast
        qed
      qed
    qed
  show P3:"is_greatest R X m \<Longrightarrow> is_dir (filter_closure R X {}) (converse R)"
  proof-
    assume top:"is_greatest R X m" 
    then obtain "(filter_closure R X {}) = {m}"
      by (simp add: filter_closure_def greatest_equality3 por)
    then show "is_dir (filter_closure R X {}) (converse R)"
      using is_filterD1 por top top_filters2 by fastforce
  qed
qed


lemma filters_on_inf_semilattice1:
  assumes por:"pord R X" and lat:"is_inf_semilattice R X"
  shows semilat_filters_isl0:"\<And>A. A \<in> Pow_ne (filters_on R X) \<Longrightarrow> is_sup (pwr X) (filters_on R X) A (filter_closure R X (\<Union>A))" and
        semilat_filters_isl1:"\<And>A. A \<in> Pow_ne (filters_on R X) \<Longrightarrow> (\<exists>F. is_sup (pwr X) (filters_on R X) A F)" and
        semilat_filters_isl2:"\<And>A. A \<in> Pow_ne (filters_on R X) \<Longrightarrow> Sup (pwr X) (filters_on R X) A= (filter_closure R X (\<Union>A))"  
proof-
  show P0:"\<And>A. A \<in> Pow_ne (filters_on R X) \<Longrightarrow> is_sup (pwr X) (filters_on R X) A (filter_closure R X (\<Union>A))"
  proof-
    fix EF assume A0:"EF \<in> Pow_ne (filters_on R X)" 
    then obtain A1:"EF \<subseteq> filters_on R X" and A2:"EF \<noteq> {}"
       by auto
    then obtain A3:"\<And>F. F \<in> EF \<Longrightarrow> is_filter R X F"
      using filters_on_iff by auto
    then obtain A4:"EF \<subseteq> Pow X" and A5:"{} \<notin> EF"
      by (meson PowI is_filterD1 subsetI)
    let ?A="\<Union>EF"
    have B0:"?A \<in> Pow_ne X"
      using A2 A4 A5 by fastforce
    let ?S="filter_closure R X ?A"
    have B1:"is_filter R X ?S"
    proof(rule is_filterI1)
      show  P0:"?S \<noteq> {}"
        by (metis B0 Pow_ne_iff empty_subsetI filter_cl0 por subset_antisym)
      show P1:"?S \<subseteq> X"
      proof-
        obtain "?A \<noteq> {}" 
          using B0 by blast 
        then obtain "?S= {x \<in> X. \<exists>F \<subseteq> ?A. finite F \<and> F \<noteq> {} \<and> (Inf R X F,  x) \<in> R}"
          unfolding filter_closure_def  by presburger 
        then show ?thesis 
          by blast
      qed
      show "is_dir ?S (dual R)"
        by (meson B0 filter_closure2_ne lat por)
      show "is_ord_cl X ?S R"
        by (meson B0 filter_closure1_ne lat por)
    qed
    show B2:"is_sup (pwr X) (filters_on R X) EF ?S"
    proof(rule is_supI1)
      show "?S \<in> filters_on R X"
        by (simp add: B1 filters_on_iff)
      show "\<And>a . a \<in> EF \<Longrightarrow> (a, ?S) \<in> pwr X"
        by (meson B0 B1 Pow_ne_iff Sup_le_iff filter_cl0 is_filterD1 por pwr_memI)
      show "\<And>b. b \<in> filters_on R X \<Longrightarrow> (\<And>a. a \<in> EF \<Longrightarrow> (a, b) \<in> pwr X) \<Longrightarrow> (?S, b) \<in> pwr X"
      proof-
        fix b assume A6:"b \<in> filters_on R X" and A7:"\<And>a. a \<in> EF \<Longrightarrow> (a, b) \<in> pwr X"
        have C0:"?S \<subseteq> b"
        proof
          fix x assume fcmen:"x \<in> ?S" 
          then obtain Fx where C1:"Fx \<subseteq>  (\<Union>EF)" and C2:"finite Fx" and C3:"Fx \<noteq> {}" and  C4:"(Inf R X Fx,x)\<in>R"
            by (metis B0 Pow_ne_iff filter_closure_memD1)
          then obtain C5:"Fx \<subseteq> b" and B6:"Fx \<subseteq> X"
            by (metis A7 Sup_le_iff dual_order.trans pwr_memD)
          obtain C6:"Inf R X Fx \<in> b"
            using A6 C2 C3 C5 filter_inf_closed3 filters_on_iff lat por by blast
          then show "x \<in> b"
            by (meson A6 B1 C4 fcmen filters_on_iff is_filterD1 is_ord_clE1 subsetD)
        qed
        then show " (?S, b) \<in> pwr X"
          by (meson A6 filters_on_iff is_filterD1 pwr_memI)
      qed
    qed
  qed
  show P1:"\<And>EF. EF \<in> Pow_ne (filters_on R X) \<Longrightarrow> (\<exists>S. is_sup (pwr X) (filters_on R X) EF S)"
    using P0 by auto
  show P2:"\<And>A. A \<in> Pow_ne (filters_on R X) \<Longrightarrow> Sup (pwr X) (filters_on R X) A= (filter_closure R X (\<Union>A))"
    by (simp add: P0 antisym_on_def powrel8 subset_antisym sup_equality)  
qed

  
lemma filter_cl1:
  assumes por:"pord R X" and sem:"semitop R X top" and asub:"A \<subseteq> X"
  shows "is_ord_cl X (filter_closure R X A) R"
  using asub por sem filter_closure1_ne[of X R A] filter_closure1_em[of X R top] by fastforce

lemma filter_cl2:
  assumes por:"pord R X" and sem:"semitop R X top" and asub:"A \<subseteq> X"
  shows  "is_dir (filter_closure R X A) (converse R)"
  using asub por sem filter_closure2_ne[of X R A] filter_closure2_em[of X R top] by fastforce

lemma filter_cl_range:
	assumes ant:"antisym R X" and ref:"refl R X" and top:"is_greatest R X top" and sub:"A \<subseteq> X"
	shows filter_cl_sp:"(filter_closure R X A) \<subseteq> X" and
				filter_cl_ne:"(filter_closure R X A) \<noteq> {}"
proof-
	show "(filter_closure R X A) \<subseteq> X" 
	proof(cases "A={}")
		case True then show ?thesis 	
			by (metis ant filter_closure_def greatest_equality3 is_filterD1 ref top top_filters2) 
	next
		case False then obtain ne:"A \<noteq> {}" 
			by simp 
		obtain frm:"filter_closure R X A= {x \<in> X. \<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and> (Inf R X F,  x) \<in> R}"
			by (simp add: filter_closure_def ne)
		then show ?thesis
			by blast
	qed
	show "(filter_closure R X A) \<noteq> {}"
		by (metis ant empty_not_insert filter_cl0 filter_closure_def ref sub subset_empty)
qed

lemma filter_cl3:
  "\<lbrakk>pord R X; semitop R X top; A \<subseteq> X\<rbrakk> \<Longrightarrow> is_filter R X (filter_closure R X A)"
	using is_filterI1[of "filter_closure R X A" X R] filter_cl1[of X R top A] filter_cl2[of X R top A]
	filter_cl_range[of X R top A] by fastforce

lemma filter_cl_ubd:
  assumes por:"pord R X" and 
				 sem:"semitop R X top" and 
				 sub:"A \<subseteq> X"
	shows "(filter_closure R X A) \<in>  (ubd (pwr X) (filters_on R X) {A})"
	unfolding ubd_def filters_on_def pwr_def  using filter_cl3[of X R top A]
	by (simp add: filter_cl0 is_filterD1 por sem sub)

lemma filter_cl_least:
  assumes por:"pord R X" and 
				sem:"semitop R X top" and 
				fil:"is_filter R X F" and 
				asb:"A \<subseteq> F"
	shows filter_cl_least1:"(filter_closure R X A) \<subseteq> F" and
			  filter_cl_least2:"(filter_closure R X A,F)\<in>pwr X"
proof-
	show "(filter_closure R X A) \<subseteq> F"
	proof(cases "A={}")
		case True
		then show ?thesis
			by (metis Int_insert_right_if1 asb fil filter_closure_def greatest_equality3 inf.absorb_iff2 por sem top_filters1) 
		next
		case False then obtain ne:"A \<noteq> {}" 
			by simp 
		obtain frm:"filter_closure R X A= {x \<in> X. \<exists>F \<subseteq> A. finite F \<and> F \<noteq> {} \<and> (Inf R X F,  x) \<in> R}"
				by (simp add: filter_closure_def ne)
		show ?thesis
		proof
			fix a assume amem:"a \<in>filter_closure R X A"
			then obtain Fa where B01:"Fa \<subseteq> A" and B02:"finite Fa" and B03:"Fa \<noteq> {}" and B04:"(Inf R X Fa, a)\<in>R"
				by (meson filter_closure_memD1 ne)
			then obtain B05:"Fa \<subseteq> F" 	and B06:"a \<in> X" 
				using amem asb frm by blast 
			then obtain B07:"Inf R X Fa \<in> F"
				by (simp add: B02 B03 fil filter_inf_closed3 por sem)
			then show "a \<in> F" 
				by (meson B04 B06 fil is_filterD1 is_ord_clE1)
		qed
	qed
	then show "(filter_closure R X A,F)\<in>pwr X"
		by (meson fil is_filterD1 pwr_memI)
qed

lemma filter_cl_lub:
  assumes por:"pord R X" and 
				sem:"semitop R X top" and 
				fil:"is_filter R X F" and 
				asb:"A \<subseteq> X"
	shows "is_least (pwr X) (ubd (pwr X) (filters_on R X) {A}) (filter_closure R X A)"
proof(rule greatestI2)
	show "filter_closure R X A \<in> ubd (pwr X) (filters_on R X) {A}"
		by (meson asb filter_cl_ubd por sem)
	show "\<And>a. a \<in> ubd (pwr X) (filters_on R X) {A} \<Longrightarrow> (a, filter_closure R X A) \<in> dual (pwr X)"
		by (metis converseI filter_cl_least2 filters_on_iff por pwr_mem_iff sem ubd_singleton_mem)
qed


lemma filter_closure_of_empty:
	assumes ref:"refl R X" and ant:"antisym R X" and sem:"semitop R X top"
	shows filter_closure_of_empty1:"is_least (pwr X) (ubd  (pwr X) (filters_on R X) {{}}) {top}" and
			filter_closure_of_empty2:"(cl_from_clr (pwr X) (filters_on R X)) {} = {top}"
proof-
	show "is_least (pwr X) (ubd  (pwr X) (filters_on R X) {{}}) {top}"
  proof(rule greatestI2)
		show "{top} \<in> ubd (pwr X) (filters_on R X) {{}}"
			by (meson ant empty_subsetI filters_on_iff is_filterD1 pwr_memI ref sem top_filters2 ubd_singleton_mem)
		show "\<And>a. a \<in> ubd (pwr X) (filters_on R X) {{}} \<Longrightarrow> (a, {top}) \<in> dual (pwr X)"
		by (metis converseI filters_on_iff insert_subsetI pwr_mem_iff sem top_filters1 ubd_singleton_mem)
	qed
	then show "(cl_from_clr (pwr X) (filters_on R X)) {} = {top}"
	by (meson ant clr_equality filters_clr powrel1 sem)
qed



lemma filter_cl_eq_cl:
  assumes por:"pord R X" and 
				sem:"semitop R X top" and 
				asb:"A \<subseteq> X"
	shows "filter_closure R X A = (cl_from_clr (pwr X) (filters_on R X)) A"
	by (metis asb clr_equality filter_cl_lub filters_clr por powrel1 sem top_filters2)

lemma filters_on_lattice_inf_semilattice1:
  assumes por:"pord R X" and lat:"is_lattice R X"
  shows lattice_filters_isl0:"\<And>F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk>\<Longrightarrow> is_filter R X (F1 \<inter> F2)" and
        lattice_filters_isl1:"\<And>F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk>\<Longrightarrow> is_inf (pwr X) (filters_on R X) {F1, F2} (F1 \<inter> F2)" and
        lattice_filters_isl2:"is_inf_semilattice (pwr X) (filters_on R X)" and
        lattice_filters_isl3:"\<And>A. \<lbrakk>A \<subseteq> filters_on R X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_filter R X (filter_closure R X (\<Union> A))" and
        lattice_filters_isl4:"\<And>A. \<lbrakk>A \<subseteq> filters_on R X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup (pwr X) (filters_on R X) A x)" and
        lattice_filters_isl5:"is_csup_semilattice (pwr X) (filters_on R X)" and
        lattice_filters_isl6:"is_sup_semilattice (pwr X) (filters_on R X)" and
        lattice_filters_isl7:"\<And>F1 F2. \<lbrakk>F1 \<in> filters_on R X; F2 \<in> filters_on R X\<rbrakk> \<Longrightarrow>Inf (pwr X) (filters_on R X) {F1, F2} =  (F1 \<inter> F2)"  and
        lattice_filters_isl8:"\<And>EF. EF \<in> Fpow_ne (filters_on R X) \<Longrightarrow> (Sup (pwr X) (filters_on R X) EF) \<in> filters_on R X" and
        lattice_filters_isl9:"\<And>EF. EF \<in> Pow_ne (filters_on R X) \<Longrightarrow> filter_closure R X (\<Union> EF) \<in> filters_on R X" and
        lattice_filters_isl10:"\<And>EF. EF \<in> Pow_ne (filters_on R X) \<Longrightarrow> (\<And>a. a \<in> EF \<Longrightarrow> (a, filter_closure R X (\<Union> EF)) \<in> pwr X)" and
        lattice_filters_isl11:"\<And>EF. EF \<in> Pow_ne (filters_on R X) \<Longrightarrow> (\<And>b. b \<in> filters_on R X \<Longrightarrow> (\<And>a. a \<in> EF \<Longrightarrow> (a, b) \<in> pwr X) \<Longrightarrow> (filter_closure R X (\<Union> EF), b) \<in> pwr X)" and
        lattice_filters_isl12:"\<And>EF. EF \<in> Pow_ne (filters_on R X) \<Longrightarrow> is_sup (pwr X) (filters_on R X) EF (filter_closure R X (\<Union>EF))"
proof-
 have pwr0:"pord (pwr X) (Pow X)"
    by (simp add: powrel1 powrel2 pwr_mem_iff refl_def)
 have fil0:"pord (pwr X) (filters_on R X)"
   by (meson PowI filters_on_iff is_filterD1 powrel6 powrel7 pwr_memI refl_def subsetI)
 show P0:"\<And>F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk>\<Longrightarrow>is_filter R X (F1 \<inter> F2)"
  proof-
    fix F1 F2 assume fil1:"is_filter R X F1" and  fil2:"is_filter R X F2"
    obtain B0:"F1 \<subseteq> X" and B1:"F2 \<subseteq> X"
      using fil1 fil2 is_filterD1 by blast 
    obtain f1 f2 where B2:"f1 \<in> F1" and B3:"f2 \<in> F2" and B4:"f1 \<in> X" and B5:"f2 \<in> X"
      by (metis is_filter_def fil1 fil2 subsetD subset_empty subset_emptyI)
    obtain B6:"Sup R X {f1,f2} \<in> F1" and  B7:"Sup R X {f1,f2} \<in> F2"
      by (meson B2 B3 B4 B5 bsup_ge1 bsup_ge2 fil1 fil2 is_filterD1 is_ord_clE1 lat lattD42 por ssupD4)
    show "is_filter R X (F1 \<inter> F2)"
    proof(rule is_filterI1)
      show "F1 \<inter> F2 \<noteq> {}"
        using B6 B7 by blast
      show "F1 \<inter> F2 \<subseteq> X"
        using B0 by auto
      show "is_dir (F1 \<inter> F2) (dual R)"
      proof(rule is_dirI1)
        fix a b assume A0:"a \<in> F1 \<inter> F2" and A1:"b \<in> F1 \<inter> F2"
        then obtain B8:"a \<in> F1" and B9:"a \<in> F2" and B10:"b \<in> F1" and B11:"b \<in> F2" and B12:"a \<in> X"  and B13:"b \<in> X" 
           using B1 by blast
        then obtain B14:"Inf R X {a,b}\<in>F1" and B15:"Inf R X{a,b}\<in>F2"
          by (meson fil1 fil2 filter_inf_closed1 lat lattD31 por)    
        then show "\<exists>c\<in> F1 \<inter> F2.  (a, c) \<in> dual R \<and> (b, c) \<in> dual R"
          by (metis B12 B13 Int_iff binf_le1 binf_le2 converse_iff lat latt_iff por)
      qed
      show "is_ord_cl X (F1 \<inter> F2) R"
      proof(rule is_ord_clI1)
        fix a b assume "a \<in> F1 \<inter> F2" and "b \<in> X" and "(a,b)\<in>R"
        then show "b \<in> F1 \<inter> F2"  by (metis Int_iff fil1 fil2 is_filterD1 is_ord_clE1)
      qed
    qed
  qed
  show P1:"\<And>F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk>\<Longrightarrow> is_inf (pwr X) (filters_on R X) {F1, F2} (F1 \<inter> F2)"
  proof-
    fix F1 F2 assume fil1:"is_filter R X F1" and  fil2:"is_filter R X F2"
    show "is_inf (pwr X) (filters_on R X) {F1, F2} (F1 \<inter> F2)"
    proof(rule is_supI1)
      show "F1 \<inter> F2 \<in> filters_on R X"
        by (simp add: P0 fil1 fil2 filters_on_iff)
      show "\<And>a. a \<in> {F1, F2} \<Longrightarrow> (a, F1 \<inter> F2) \<in> dual (pwr X)"
        by (metis Int_lower2 converse_iff empty_iff fil1 fil2 inf_le1 insert_iff is_filterD1 pwr_memI)
      show "\<And>b. b \<in> filters_on R X \<Longrightarrow> (\<And>a. a \<in> {F1, F2} \<Longrightarrow> (a, b) \<in> dual (pwr X)) \<Longrightarrow> (F1 \<inter> F2, b) \<in> dual (pwr X)"
        by (simp add: inf.coboundedI2 pwr_mem_iff)
    qed
   qed
   show P2:"is_inf_semilattice (pwr X) (filters_on R X)"
    by (metis P1 bot_filters1 empty_iff filters_on_iff lat lattD41)
  show P3:"\<And>A. \<lbrakk>A \<subseteq> filters_on R X; A \<noteq> {}\<rbrakk> \<Longrightarrow> is_filter R X (filter_closure R X (\<Union> A))" 
  proof-
    fix A assume A0:"A \<subseteq> filters_on R X" and A1:"A \<noteq> {}"
    then obtain B0:"A \<subseteq> Pow X"
      by (metis Int_Collect PowI filters_on_def inf.orderE is_filterD1 subsetI)
    then obtain B1:"\<Union>A \<noteq> {}" and B2:"\<Union>A \<subseteq> X"
      by (metis A0 A1 Pow_empty Pow_top Sup_subset_mono Union_Pow_eq filters_on_iff is_filterD1 subsetD subset_Pow_Union subset_singletonD)
    let ?FC="filter_closure R X (\<Union> A)"
    show "is_filter R X ?FC"
    proof(rule is_filterI1)
      show fcne:"?FC \<noteq> {}"
        by (metis A0 A1 Sup_le_iff bot.extremum_uniqueI filter_cl0 filters_on_iff is_filterD1 por subset_eq)
      show fcsub:"?FC \<subseteq> X"
        by (metis (no_types, lifting) B1 CollectD filter_closure_def subsetI)
      show "is_dir ?FC (dual R)"
      proof(rule is_dirI1)
        fix a b assume A2:"a \<in> ?FC" and A3:"b \<in> ?FC" 
        obtain Fa where B01:"Fa \<subseteq> (\<Union>A)" and B02:"finite Fa" and B03:"Fa \<noteq> {}" and B04:"(Inf R X Fa, a)\<in>R"
          by (meson A2 B1 filter_closure_memD1)
        obtain Fb where B05:"Fb \<subseteq>  (\<Union>A)" and B06:"finite Fb" and B07:"Fb \<noteq> {}" and B08:"(Inf R X Fb, b)\<in>R"
          by (meson A3 B1 filter_closure_memD1)
        obtain B10:"Fb \<subseteq> X" and B11:"Fa \<subseteq> X" and B12:"a \<in> X" and B13:"b \<in> X"
          using A2 A3 B01 B05 B2 fcsub by blast
        let ?Fab="Fa \<union> Fb"
        obtain B14:"?Fab \<subseteq> (\<Union>A)" and B15:"?Fab \<subseteq> X" and B16:"Fa \<subseteq> ?Fab" and B17:"Fb \<subseteq> ?Fab"	
          by (simp add: B01 B05 B10 B11)
        obtain B18:"finite ?Fab" and B19:"?Fab \<noteq> {}"
          using B02 B03 B06 by blast
        obtain B20:"Inf R X ?Fab \<in> X"
          by (metis B15 B18 B19 bot_filters1 filter_inf_closed3 lat latt_iff por)
        obtain B21:"Inf R X ?Fab \<in> ?FC"
          by (meson B14 B18 B19 B20 filter_closure_memI2 por reflD2)
        obtain B22:"is_inf R X ?Fab (Inf R X ?Fab)"
          by (metis B15 B18 B19 Fpow_ne_iff antisym_on_converse inf_equality2 is_sup_semilattice_def lat latt_iff por sup_semilattice_fsup trans_on_converse)
        obtain B23:"is_inf R X Fa (Inf R X Fa)" and B24:"is_inf R X Fb (Inf R X Fb)"
        by (metis B02 B03 B06 B07 B10 B11 Fpow_ne_iff Sup_def antisym_on_converse is_sup_semilattice_def lat latt_iff por sup_semilattice_fsup trans_on_converse)
        obtain B25:"(Inf R X ?Fab, Inf R X Fa)\<in>R" and B26:"(Inf R X ?Fab, Inf R X Fb)\<in>R"
          by (meson B16 B17 B22 B23 B24 converse_iff is_sup_iso1)
        then obtain B27:"(Inf R X ?Fab, a) \<in> R" and B28:"(Inf R X ?Fab, b)\<in>R"
          by (meson B04 B08 B12 B13 B20 B23 B24 is_supD1 por trans_onD)
        then show "\<exists>c\<in>?FC. (a,c)\<in>(dual R)\<and>(b,c)\<in>(dual R)"
          using B21 by blast
      qed
      show "is_ord_cl X ?FC R"
      proof(rule is_ord_clI1)
          fix a b assume afc1:"a \<in> ?FC" and bx0:"b\<in>X" and altb:"(a,b)\<in>R"
          then obtain F where B4:"F \<subseteq> (\<Union>A)" and B5:"finite F" and B6:"F \<noteq> {}" and 73:"(Inf R X F,a)\<in>R"
            by (meson B1 filter_closure_memD1)
          obtain B8:"a \<in> X"
            using afc1 fcsub by auto 
          obtain  B10:"F \<subseteq> X"
            using B2 B4 by blast
          obtain B11:"Inf R X F \<in> X"
            by (metis B10 B5 B6 bot_filters1 filter_inf_closed3 lat latt_iff por)
          then obtain B12:"(Inf R X F,b)\<in>R"
            by (meson "73" B8 altb bx0 por trans_onD) 
          then show "b \<in> ?FC"
            by (meson B4 B5 B6 bx0 filter_closure_memI1)
        qed
      qed
  qed
  show P4:"\<And>A. \<lbrakk>A \<subseteq> filters_on R X; A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists>x. is_sup (pwr X) (filters_on R X) A x)"
  proof-
    fix A assume A0:"A \<subseteq> filters_on R X" and A1:"A \<noteq> {}"
    have "is_sup (pwr X) (filters_on R X) A (filter_closure R X (\<Union>A))"
    proof(rule is_supI1)
      show " filter_closure R X (\<Union> A) \<in> filters_on R X"
        by (simp add: A0 A1 P3 filters_on_iff)
      show "\<And>a.  a \<in> A \<Longrightarrow> (a, filter_closure R X (\<Union> A)) \<in> pwr X"
        by (metis A0 A1 Int_Collect P3 Sup_le_iff filter_cl0 filters_on_def inf.orderE is_filterD1 por pwr_memI)
      show "\<And>b. b \<in> filters_on R X \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> (a, b) \<in> pwr X) \<Longrightarrow> (filter_closure R X (\<Union> A), b) \<in> pwr X"
      proof-
        fix b assume bfil1:"b \<in> filters_on R X" and bubd1:"(\<And>a. a \<in> A \<Longrightarrow> (a,b)\<in>(pwr X))"
        then obtain bsup1:"\<And>a. a \<in> A \<Longrightarrow> a \<subseteq> b \<and> b \<subseteq> X \<and> a \<subseteq> X" and bfil2:"is_filter R X b"
          using filters_on_iff pwr_memD by blast
        have asub:"A \<subseteq> Pow X"
          by (simp add: bsup1 subsetI)
        then obtain B1:"\<Union>A \<noteq> {}" and B2:"\<Union>A \<subseteq> X"
          by (metis A0 A1 Int_Collect Pow_empty Pow_top Sup_subset_mono Union_Pow_eq filters_on_def inf.orderE is_filterD1 subset_Pow_Union subset_singletonD)
        let ?FC="filter_closure R X (\<Union> A)"
        have fcltb:"?FC \<subseteq> b"
        proof
          fix x assume xmem0:"x \<in>?FC"
          then obtain Fx where fx0:"Fx \<subseteq>(\<Union>A)" and fx1:"finite Fx" and fx2:"Fx \<noteq> {}" and fx3:"(Inf R X Fx, x)\<in>R"
            by (meson B1 filter_closure_memD1)
			    then obtain fx4:"Fx \<subseteq> X" 	and xmem1:"x \<in> X" and fx5:"Fx \<subseteq> b"
			      by (meson A0 A1 P3 Sup_le_iff bsup1 dual_order.trans is_filterD1 subsetD xmem0)
			    then obtain B07:"Inf R X Fx \<in> b"
			      by (metis bfil2 filter_inf_closed3 fx1 fx2 lat latt_iff por)
			    then show "x \<in> b"
			      by (meson bfil2 fx3 is_filterD1 is_ord_clE1 xmem1) 
          qed
        then show "(?FC, b) \<in> pwr X"
          using B1 bsup1 pwr_memI by fastforce
		  qed
    qed
    then show "\<exists>x. is_sup (pwr X) (filters_on R X) A x" by blast
  qed
  show P5:"is_csup_semilattice (pwr X) (filters_on R X)"
    by (simp add: P2 P4 is_csup_semilattice_def)
  show P6:"is_sup_semilattice (pwr X) (filters_on R X)"
    by (simp add: P5 csup_fsup)
  show P7:"\<And>F1 F2. \<lbrakk>F1 \<in> filters_on R X; F2 \<in> filters_on R X\<rbrakk> \<Longrightarrow>Inf (pwr X) (filters_on R X) {F1, F2} =  (F1 \<inter> F2)" 
  proof-
    fix F1 F2 assume f10:"F1 \<in> filters_on R X" and f20:"F2 \<in> filters_on R X"
    then obtain "is_inf (pwr X) (filters_on R X) {F1, F2} (F1 \<inter> F2)" using P1 by (simp add: filters_on_iff)
    then show "Inf (pwr X) (filters_on R X) {F1, F2} =  (F1 \<inter> F2)"
      by (simp add: fil0 inf_equality)
  qed
  show P8:"\<And>EF. EF \<in> Fpow_ne (filters_on R X) \<Longrightarrow> (Sup (pwr X) (filters_on R X) EF) \<in> filters_on R X"
  proof-
    fix EF assume ef0:"EF \<in> Fpow_ne (filters_on R X)" 
    then obtain ef1:"EF \<subseteq> filters_on R X" and ef2:"finite EF" and ef3:"EF \<noteq> {}" and ef4:"EF \<subseteq> Pow X"
      by (metis Fpow_ne_iff PowI filters_on_iff is_filterD1 subset_iff)
    then show "(Sup (pwr X) (filters_on R X) EF) \<in> filters_on R X"
      by (simp add: P5 csupD50 fil0)
  qed
  show P9:"\<And>EF. EF \<in> Pow_ne (filters_on R X) \<Longrightarrow> filter_closure R X (\<Union> EF) \<in> filters_on R X"
  proof-
    fix EF assume ef0:"EF \<in> Pow_ne (filters_on R X)"
    show "filter_closure R X (\<Union> EF) \<in> filters_on R X"
      using P3 ef0 filters_on_iff by auto
  qed
  show P10:"\<And>EF. EF \<in> Pow_ne (filters_on R X) \<Longrightarrow> (\<And>a. a \<in> EF \<Longrightarrow> (a, filter_closure R X (\<Union> EF)) \<in> pwr X)"
    by (metis Int_Collect P3 Pow_ne_iff Sup_le_iff filter_cl0 filters_on_def inf.orderE is_filterD1 por pwr_memI)
  show P11:"\<And>EF. EF \<in> Pow_ne (filters_on R X) \<Longrightarrow> (\<And>b. b \<in> filters_on R X \<Longrightarrow> (\<And>a. a \<in> EF \<Longrightarrow> (a, b) \<in> pwr X) \<Longrightarrow> (filter_closure R X (\<Union> EF), b) \<in> pwr X)"
  proof-
    fix EF assume ef0:"EF \<in> Pow_ne (filters_on R X)"
    show "\<And>b. b \<in> filters_on R X \<Longrightarrow> (\<And>a. a \<in> EF \<Longrightarrow> (a, b) \<in> pwr X) \<Longrightarrow> (filter_closure R X (\<Union> EF), b) \<in> pwr X"
    proof-
      fix b assume bfil:"b \<in> filters_on R X" and bub:"(\<And>a. a \<in> EF \<Longrightarrow> (a, b) \<in> pwr X)"
      have fcsub:"filter_closure R X (\<Union> EF) \<subseteq> b"
      proof
        fix x assume fcmen:"x \<in> filter_closure R X (\<Union> EF)" 
        then obtain Fx where B1:"Fx \<subseteq>  (\<Union>EF)" and B2:"finite Fx" and B3:"Fx \<noteq> {}" and  B4:"(Inf R X Fx,x)\<in>R"
          by (metis is_filter_def Pow_empty Pow_ne_iff ef0 filter_closure_memD1 filters_on_def insert_subset mem_Collect_eq subset_Pow_Union subset_singletonD)
        then obtain B5:"Fx \<subseteq> b" and B6:"Fx \<subseteq> X"
          by (meson Union_least bub dual_order.trans pwr_memD)
        obtain B7:"\<And>F. F \<in> EF \<Longrightarrow> is_filter R X F" and B8:"EF \<noteq> {}"
          using ef0 filters_on_iff by fastforce
        obtain B9:"Inf R X Fx \<in> b"
          by (metis B2 B3 B5 bfil filter_inf_closed3 filters_on_iff lat latt_iff por)
        then show "x \<in> b"
          by (meson B4 P9 bfil ef0 fcmen filters_on_iff is_filterD1 is_ord_clE1 subsetD)
      qed
      show "(filter_closure R X (\<Union> EF), b) \<in> pwr X"
        by (meson bfil fcsub filters_on_iff is_filterD1 pwr_memI) 
    qed
  qed
  show P12:"\<And>EF. EF \<in> Pow_ne (filters_on R X) \<Longrightarrow> is_sup (pwr X) (filters_on R X) EF (filter_closure R X (\<Union>EF))"
  proof-
    fix EF assume ef0:"EF \<in> Pow_ne (filters_on R X)"
    show " is_sup (pwr X) (filters_on R X) EF (filter_closure R X (\<Union>EF))"
    proof(rule is_supI1) 
      show "filter_closure R X (\<Union> EF) \<in> filters_on R X"
        using P9 ef0 by auto
      show "\<And>a. a \<in> EF \<Longrightarrow> (a, filter_closure R X (\<Union> EF)) \<in> pwr X"
        using P10 ef0 by presburger
      show "\<And>b. b \<in> filters_on R X \<Longrightarrow> (\<And>a. a \<in> EF \<Longrightarrow> (a, b) \<in> pwr X) \<Longrightarrow> (filter_closure R X (\<Union> EF), b) \<in> pwr X"
        using P11 ef0 by blast
   qed
  qed
qed

lemma distr_lattice_filters:
  "\<lbrakk>pord R X ;distributive_lattice R X\<rbrakk> \<Longrightarrow> is_lattice (pwr X) (filters_on R X)"
  by (simp add: distributive_lattice_def latt_iff lattice_filters_isl2 lattice_filters_isl6)




subsubsection FiltersAndDirectedUnions

lemma lattice_filter_dunion1:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; D \<noteq> {}; D \<subseteq> filters_on R X; is_dir D (pwr X)\<rbrakk> \<Longrightarrow> \<Union>D \<noteq> {} "
  by (simp add: is_filter_def filters_on_iff subset_iff)

lemma lattice_filter_dunion2:
  "\<lbrakk>antisym R X;trans R X; refl R X;is_lattice R X; D \<noteq> {}; D \<subseteq> filters_on R X; is_dir D (pwr X)\<rbrakk> \<Longrightarrow> is_ord_cl X (\<Union>D) (R)"
  by (simp add: filters_on_iff is_filterD1 is_ord_cl_un subset_iff)

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
    have B4:"Inf R X {x, y} \<in> Dxy"
    using A0 A3 B1 B2 B3 filter_inf_closed2 latt_iff by fastforce  
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
  assumes por:"pord R X" and 
          lat:"is_lattice R X" and 
          nem:"D \<noteq> {}"  and
          fil:"D \<subseteq> filters_on R X" and
          dir:" is_dir D (pwr X)"
 shows "is_dir (\<Union>D) (converse R)"
proof(rule is_dirI1)
  let ?U="(\<Union>D)"
  fix a b assume A0:"a \<in>?U" and A1:"b \<in> ?U"
  then obtain Fa Fb where B0:"Fa \<in> D" and B1:"a \<in> Fa" and B2:"Fb \<in> D" and B3:"b \<in> Fb" by blast
  then obtain Fab where B4:"Fab \<in> D" and B5:"(Fa,Fab)\<in>(pwr X)" and B6:"(Fb,Fab)\<in>(pwr X)" by (meson dir is_dirE1)
  then obtain B7:"Fa \<subseteq> Fab" and B8:"Fb \<subseteq> Fab"  by (simp add: pwr_mem_iff)
  then obtain B9:"a \<in> Fab" and B10:"b \<in> Fab" and B11:"is_filter R X Fab" using B1 B3 B4 fil filters_on_iff by blast
  then obtain B12:"a \<in> X" and B13:"b \<in> X"  using is_filterD1 by blast
  then obtain B14:"Inf R X {a,b}\<in>Fab"  by (metis B9 B10 B11 filter_inf_closed2 lat latt_iff por)
  then obtain B15:"(Inf R X {a,b},a)\<in>R" and B16:"(Inf R X {a,b},b)\<in>R" by (metis B12 B13 binf_le1 binf_le2 lat latt_iff por)
  then show "\<exists>c\<in>?U. (a,c)\<in>(dual R)\<and>(b,c)\<in>(dual R)"  using B14 B4 by blast
qed

lemma lattice_filter_dunion9:
  "\<lbrakk>pord R X;is_lattice R X; D \<noteq> {}; D \<subseteq> filters_on R X; is_dir D (pwr X)\<rbrakk> \<Longrightarrow> is_filter R X (\<Union>D)"
  by (metis is_filter_def lattice_filter_dunion1 lattice_filter_dunion2 lattice_filter_dunion7 lattice_filter_dunion8) 

lemma lattice_filters_complete:
  "\<lbrakk>pord R X;is_lattice R X;  is_greatest R X top\<rbrakk> \<Longrightarrow> is_clattice (pwr X) (filters_on R X)"
  by (metis Sup_le_iff Union_Pow_eq clr_clattice2 filters_clr latt_iff pow_is_clattice powrel1 powrel2 pwr_memI refl_def subsetI)

lemma filters_inf_semilattice_inf:
  assumes por:"pord R X" and sem:"semitop R X top" and 
          mem:" EF \<in> Pow_ne (filters_on R X)"
  shows "is_inf (pwr X) (filters_on R X) EF (\<Inter>EF)"
proof(rule is_supI1)
  let ?I="\<Inter>EF"
  obtain mem1:"EF \<noteq> {}" and mem2:"EF \<in> Pow(filters_on R X)"  using mem by blast
  then show P0:"?I \<in> filters_on R X"  
    by (metis filter_inter2 por sem)
  then show P1:"\<And>a. a \<in> EF \<Longrightarrow> (a,?I)\<in>(dual (pwr X))" 
    by (meson Inter_lower PowD Sup_le_iff converseI lattice_filter_dunion7 mem1 mem2 pwr_memI)
  then show P2:"\<And>b. b \<in> filters_on R X \<Longrightarrow> (\<And>a. a \<in> EF \<Longrightarrow> (a, b) \<in> dual (pwr X)) \<Longrightarrow> (?I, b) \<in> dual (pwr X)"
    by (metis Inf_greatest Inter_subset converse.cases converseI mem1 pwr_memD pwr_memI)
qed

subsection PrincipalFilters

lemma lcroI1:
  "y \<in> X \<Longrightarrow> (a, y)\<in>R \<Longrightarrow> y \<in> lcro R X a" 
  by (simp add:lcro_def)

lemma lcroD1:
  "y \<in> lcro R X a \<Longrightarrow> y \<in> X \<and> (a, y)\<in>R"
   by (simp add:lcro_def)

lemma lcroD2:"\<lbrakk>trans R X; a \<in> X;x \<in> X; y \<in> lcro R X a; (y, x)\<in>R\<rbrakk> \<Longrightarrow> x \<in> lcro R X a"
  by (meson lcroD1 lcroI1 trans_onD)

lemma lcro_eq_upbd:
  "(lcro R X a) = (ubd R  X {a})"
  by (simp add: lcro_def ubd_singleton)

lemma lcro_memI1:
  "refl R X \<Longrightarrow> a \<in> X \<Longrightarrow> a \<in> lcro R X a "
  by (simp add: lcroI1 reflD1)

lemma lcro_subset1:
  "(lorc R X a) \<subseteq> X"
  by (simp add: ubd_sub lcro_eq_upbd)

lemma lcro_top:
  "\<lbrakk>is_greatest R X m; a \<in> X\<rbrakk> \<Longrightarrow> m \<in> lcro R X a"
  by (simp add: greatestD lcroI1)

lemma lcro_sup_latticeD1:
  "\<lbrakk>pord R X;is_sup_semilattice R X; x \<in> X; y \<in> X\<rbrakk>\<Longrightarrow> Sup R X {x, y} \<in> (lcro R X x)"
  by (simp add: bsup_ge1 lcroI1 ssupD4)

lemma lcro_inf_latticeD1:
  "\<lbrakk>pord R X; is_least R X bot\<rbrakk> \<Longrightarrow> lcro R X bot = X"
  unfolding lcro_def is_greatest_def ubd_def by auto
  
lemma lcro_dual_iso1:
  "\<lbrakk>pord R X; a \<in> X; b \<in> X;(b,a)\<notin>R\<rbrakk> \<Longrightarrow>\<not> ((lcro R X a) \<subseteq> (lcro R X b))"
  by (metis lcroD1 lcro_memI1 subsetD)

lemma lcro_dual_iso2:
  "\<lbrakk>pord R X; a \<in> X; b \<in> X;(b,a)\<in>R\<rbrakk> \<Longrightarrow> ((lcro R X a) \<subseteq> (lcro R X b))"
  by (simp add: lcro_eq_upbd ubd_iso3)


lemma lcro_upclI:
  "\<lbrakk>pord R X; a \<in> X\<rbrakk> \<Longrightarrow> is_ord_cl X (lcro R X a) R"
  by (meson is_ord_clI1 lcroD2)

lemma lcro_filter:
  assumes por:"pord R X" and x0:"x \<in> X"
  shows "is_filter R X (lcro R X x)"
proof(rule is_filterI1)
  show  "lcro R X x \<noteq> {}"
    using lcro_memI1 por x0 by force
  show  "lcro R X x \<subseteq> X"
    by (simp add: lcro_def)
  show  "is_dir (lcro R X x) (dual R)"
    by (meson converseI is_dirI1 lcroD1 lcro_memI1 por x0)
  show  "is_ord_cl X (lcro R X x) R"
    by (simp add: lcro_upclI por x0)
qed


lemma lcro_inter2:
  assumes A0:"is_lattice R X" and A1:"F\<in> Fpow_ne X" and por:"pord R X"
  shows "Sup (pwr X )(filters_on R X) {lcro R X f|f. f \<in> F} =lcro R X (Inf R X F)"
proof-
  let ?A="{lcro R X f|f. f \<in> F}"
  from A1 obtain A1a:"F \<subseteq> X" and A1b:"finite F" and A1c:"F \<noteq> {}"
    by fastforce 
  then obtain B0a:"?A \<subseteq> (filters_on R X)"
    using filters_on_iff lcro_filter por by fastforce 
  obtain B0b:"finite ?A" and B0c:"?A \<noteq> {}"
    using A1b A1c by force
  obtain B0d:"Inf R X F \<in> X"
    by (metis A0 A1a A1b A1c bot_filters1 filter_inf_closed3 latt_iff por) 
  have B0:"\<And>f. f \<in> F \<Longrightarrow> (lcro R X f) \<subseteq> (lcro R X (Inf R X F))"
    by (smt (verit) A0 A1a A1b A1c B0d binf_finite converseD is_supD3 lattD31 lcro_dual_iso2 por subsetD) 
  then have B1:" (lcro R X (Inf R X F)) \<in> ubd (pwr X) (filters_on R X) ?A"
    by (smt (verit) B0d filters_on_iff is_filterD1 lcro_filter mem_Collect_eq por pwr_memI ubdI)
  then have B2:"(Sup (pwr X) (filters_on R X) ?A, lcro R X (Inf R X F))\<in>pwr X"
    by (metis (no_types, lifting) A0 B0a B0c antisym_on_def is_supD2 lattice_filters_isl4 order_antisym_conv por powrel8 sup_equality)
  have B3:"\<And>G. G \<in> ubd (pwr X) (filters_on R X) ?A \<Longrightarrow>  lcro R X (Inf R X F) \<subseteq> G"
  proof-
    fix G assume B30:"G \<in> ubd (pwr X) (filters_on R X) ?A" 
    then obtain B31:"\<And>f. f \<in> F \<Longrightarrow> f \<in> G"
      by (smt (verit) A1a lcro_memI1 mem_Collect_eq por pwr_mem_iff subsetD ubdD1)  
    then obtain B32:"F \<subseteq> G" and B33:"finite F" and B34:"F \<noteq> {}" using A1b A1c by blast
    then obtain B34:"Inf R X F \<in> G"
      by (smt (verit) A0 B30 filter_inf_closed3 filters_on_iff latt_iff por subsetD ubd_sub)  
    from B30 have B35:"is_filter R X G" unfolding ubd_def filters_on_def by auto
    then obtain B36:"is_ord_cl X G R" using is_filterD1 by auto
    then show "lcro R X (Inf R X F) \<subseteq> G"
      by (meson B34 is_ord_clE1 lcroD1 subsetI)
  qed
  then have "(lcro R X (Inf R X F), Sup (pwr X) (filters_on R X) ?A)\<in>pwr X"
    by (smt (verit, best) A0 B0a B0c antisym_on_def dual_order.eq_iff is_supD1 lattice_filters_isl4 por pwr_memD pwr_memI sup_equality ubdI)
  then show ?thesis
    using B2 powrel8 by blast
qed
    
subsection Compactness
subsubsection BasicLemmas

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

lemma join_denseD2:
  assumes ant:"antisym R X" and jnd:"join_dense R X D" and sub:"D \<subseteq> X"
  shows "\<And>x. x \<in> X \<Longrightarrow> x = Sup R X (lorc R D x)"
proof-
  fix x assume xmem:"x \<in> X" 
  obtain Dx where dmem:"Dx \<in> Pow D" and xsup:"is_sup R X Dx x"
    by (meson jnd join_denseD1 xmem) 
  then obtain B0:"\<And>d. d \<in> Dx \<Longrightarrow>(d, x) \<in> R" and B1:"Dx \<subseteq> X"
    by (metis PowD dual_order.trans is_supD1 sub)
  then obtain B2:"Dx \<subseteq> (lorc R D x)"
    by (meson PowD converse_iff dmem in_mono lcroI1 subsetI) 
  have B3:"is_sup R X (lorc R D x) x" 
  proof(rule is_supI1)
      show "x \<in> X" by (simp add: xmem)
      show "\<And>a. a \<in> lorc R D x \<Longrightarrow> (a, x) \<in> R" using lcroD1 by force
      show "\<And>b. b \<in> X \<Longrightarrow> (\<And>a. a \<in> lorc R D x \<Longrightarrow> (a, b) \<in> R) \<Longrightarrow> (x, b) \<in> R"  by (meson B2 is_supD1 subset_iff xsup)
  qed
  then show "x= Sup R X (lorc R D x)"  by (simp add: ant sup_equality) 
qed


lemma join_denseI2:
  "\<lbrakk>D \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> is_sup R X (lorc R D x) x) \<rbrakk> \<Longrightarrow> join_dense R X D"
  by (meson PowI join_dense_def lcro_subset1)  

lemma meet_denseD2:
  "\<lbrakk>antisym R X; meet_dense R X D; D \<subseteq> X\<rbrakk> \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x = Inf R X (lcro R D x))"
  by (metis Sup_def antisym_on_converse converse_converse join_denseD2) 

lemma meet_denseI2:
  "\<lbrakk>D \<subseteq> X; (\<And>x. x \<in> X \<Longrightarrow> is_inf R X (lcro R D x) x) \<rbrakk> \<Longrightarrow> meet_dense R X D"
  by (simp add: join_denseI2) 

lemma compactly_generated_iff:
  "compactly_generated R X \<longleftrightarrow> join_dense R X (compact_elements R X)" 
  by(auto simp add:compactly_generated_def join_dense_def)

lemma compactD1:
  assumes por:"pord R X" and cmp:"is_compact R X c" and
          amem:"A \<in> Pow_ne X" and agt:"(c, Sup R X A) \<in> R" and dir:"is_dir A R"
  shows "(\<exists>F\<in>Fpow_ne A. \<exists>a \<in> A. (\<forall>x. x \<in> F \<longrightarrow> (x,a)\<in>R)  \<and> (c, Sup R X F) \<in> R)"
proof-
  obtain F where B0:"F \<in> Fpow_ne A" and B1:"(c, Sup R X F) \<in> R" and B2:"A \<subseteq> X"
    by (meson Pow_ne_iff agt amem cmp compactD)
  then obtain B3:"F \<subseteq> A" and B4:"F \<subseteq> X" and B5:"finite F" and B6:"F \<noteq> {}" by blast
  have B7:"pord R A" by (meson B2 antisym_on_subset por refl_subset trans_on_subset)
  then obtain a where B8:"a \<in> A" and B9:"(\<forall>x. x \<in> F \<longrightarrow> (x,a)\<in>R)"
    by (metis B3 B5 B6 dir dir_finite1 is_dir_def)
  then show ?thesis using B0 B1 by blast
qed

lemma compactD3:
  assumes por:"pord R X" and cmp:"is_compact R X c" and
          amem:"A \<in> Pow_ne X" and agt:"(c, Sup R X A) \<in> R" and
           dir:"is_dir A R" and sem:"is_sup_semilattice R X"
  shows "\<exists>a \<in> A. (c, a) \<in> R"
proof-
  obtain F a where B0:"F \<in> Fpow_ne A" and B1:"a \<in> A" and B2:"(\<forall>x. x \<in> F\<longrightarrow>(x,a)\<in>R)" and B3:"(c, Sup R X F)\<in>R"
    by (meson agt amem cmp compactD1 dir por)
  then obtain B4:"A \<subseteq> X" and B5:"A \<noteq> {}" and B6:"a \<in> X" and B7:"pord R A"
    by (metis Pow_ne_iff amem antisym_on_subset por refl_subset subsetD trans_on_subset)
  then obtain B8:"F \<subseteq> A" and B9:"finite F" and B10:"F \<noteq> {}" and B11:"F \<subseteq> X"
    using B0 by blast
  then obtain B12:"a \<in> ubd R X F"
    by (simp add: B2 B6 ubdI)
  then obtain B13:"(Sup R X F,a)\<in>R"
    by (meson B10 B11 B9 Fpow_ne_iff is_supD2 por sem sup_semilattice_fsup)
  then obtain B14:"(c,a)\<in>R"
    by (meson B10 B11 B3 B6 B9 Fpow_ne_iff cmp compactD2 is_supD1 por sem sup_semilattice_fsup trans_onD)
  then show ?thesis using B1 by blast
qed

subsubsection FiniteSupClosure

definition fne_sup_cl::"'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow>  'a set" where
  "fne_sup_cl R X A\<equiv> {x \<in> X. \<exists>F \<in> Fpow A. F \<noteq> {} \<and> is_sup R X F x}"


lemma fne_sup_cl_imp1:
   "x \<in> fne_sup_cl R X A \<Longrightarrow> (\<exists>F \<in> Fpow A. F \<noteq> {} \<and> is_sup R X F x)" 
  by (simp add: fne_sup_cl_def)

lemma fne_sup_cl_obtains:  
  assumes "x \<in> fne_sup_cl R X A"  
  obtains F where "F \<in> Fpow A \<and> F \<noteq> {} \<and> is_sup R X F x"  
  by (meson assms fne_sup_cl_imp1)

lemma fne_sup_cl_memI:
  "x \<in> X \<Longrightarrow> F \<in> Fpow A \<Longrightarrow> F \<noteq> {} \<Longrightarrow> is_sup R X F x \<Longrightarrow> x \<in> fne_sup_cl R X A"
  unfolding fne_sup_cl_def  by blast 

lemma fne_sup_cl_memI2:
  "F \<in> Fpow A \<Longrightarrow> F \<noteq> {} \<Longrightarrow> is_sup R X F x \<Longrightarrow> x \<in> fne_sup_cl R X A"
  unfolding fne_sup_cl_def by(auto simp add:is_supD1)

lemma fne_sup_cl_props:
  assumes por:"pord R X"
  shows fne_sup_cl_rng1:"\<And>A. fne_sup_cl R X A \<subseteq> X" and
        fne_sup_cl_ext1:"\<And>A. A \<subseteq> X \<Longrightarrow> A \<subseteq> fne_sup_cl R X A" and
        fne_sup_cl_ext2:"extensive (pwr X) (Pow X) (\<lambda>A. fne_sup_cl R X A)" and
        fne_sup_cl_iso1:"\<And>A B. \<lbrakk>A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> fne_sup_cl R X A \<subseteq> fne_sup_cl R X B" and
        fne_sup_cl_iso2:"isotone (pwr X) (Pow X) (pwr X) (\<lambda>A. fne_sup_cl R X A)" and
        fne_sup_cl_ide1:"\<And>A. A \<subseteq> X \<Longrightarrow> fne_sup_cl R X (fne_sup_cl R X A) = fne_sup_cl R X A" and
        fne_sup_cl_ide2:"idempotent (Pow X) (\<lambda>A. fne_sup_cl R X A)" and
        fne_sup_cl_rng2:"(\<lambda>A. fne_sup_cl R X A)`(Pow X) \<subseteq> Pow X" and
        fne_sup_cl_iscl:"closure (pwr X) (Pow X) (\<lambda>A. fne_sup_cl R X A)" and
        fne_sup_cl_dir1:"is_sup_semilattice R X \<Longrightarrow> (\<And>A. A \<subseteq>X \<Longrightarrow>is_dir (fne_sup_cl R X A) R)"
proof-
  show P0:"\<And>A. fne_sup_cl R X A \<subseteq> X" 
    unfolding fne_sup_cl_def by auto
  show P1:"\<And>A. A \<subseteq> X \<Longrightarrow> A \<subseteq> fne_sup_cl R X A"
  proof-
    fix A assume sub:"A \<subseteq> X"
    show "A \<subseteq> fne_sup_cl R X A" 
    proof
      fix a assume a0:"a \<in> A" 
      obtain a1:"a \<in> X" and a2:"{a}\<in>Fpow A"
        using CollectI Fpow_Pow_finite PowI a0 sub by auto
      obtain a3:"is_sup R X {a} a"
        by (simp add: a1 por sup_singleton1)
      show "a \<in> fne_sup_cl R X A" using fne_sup_cl_memI2 a2 a3 by fastforce
    qed
  qed
  show P2:"extensive (pwr X) (Pow X) (\<lambda>A. fne_sup_cl R X A)"
    by (simp add: P0 P1 extensive_def pwr_mem_iff) 
  show P3:"\<And>A B. \<lbrakk>A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> fne_sup_cl R X A \<subseteq> fne_sup_cl R X B" 
  proof-
    fix A B assume A0:"A \<subseteq> B" and A1:"B \<subseteq> X" 
    then obtain B0:"A \<subseteq> X" by simp
    then show "fne_sup_cl R X A \<subseteq> fne_sup_cl R X B"
      unfolding fne_sup_cl_def  using A0 Fpow_mono by force
  qed
  show P4:"isotone (pwr X) (Pow X) (pwr X) (\<lambda>A. fne_sup_cl R X A)"
    by (simp add: P0 P3 isotone_def pwr_mem_iff)
  show P5:"\<And>A. A \<subseteq> X \<Longrightarrow> fne_sup_cl R X (fne_sup_cl R X A) = fne_sup_cl R X A"
  proof-
    fix A assume sub:"A \<subseteq> X" let ?L1="fne_sup_cl R X A" let ?L2="fne_sup_cl R X ?L1"
    show "?L2 = ?L1"
    proof
      show "?L1 \<subseteq>?L2"  by (simp add: P0 P1) 
    next
      show "?L2 \<subseteq> ?L1"
      proof
        fix s assume A0:"s \<in>?L2"
        obtain E where B0:"E \<in> Fpow ?L1" and B1:"E \<noteq> {}" and B2:"is_sup R X E s"  by (meson A0 fne_sup_cl_imp1) 
        define F where "F \<equiv> (\<lambda>x. SOME Fx. Fx \<in> Fpow A \<and> Fx \<noteq> {} \<and> is_sup R X Fx x)"
        have B3:"\<And>x. x \<in> E \<Longrightarrow> (F x) \<in> Fpow A \<and> (F x) \<noteq> {} \<and> is_sup R X (F x) x"
        proof-
          fix x assume B30:"x \<in> E"
          let ?P="\<lambda>Fx. Fx \<in> Fpow A \<and> Fx \<noteq> {} \<and> is_sup R X Fx x"
          obtain Fx where "Fx \<in> Fpow A" and "Fx \<noteq> {}" and "is_sup R X Fx x"
            by (meson B30  B0 Fpow_subset_Pow PowD fne_sup_cl_imp1 in_mono)
          then show "(F x) \<in> Fpow A \<and> (F x) \<noteq> {} \<and> is_sup R X (F x) x"
            unfolding F_def using someI[of "?P" "Fx"]  by blast
        qed
        obtain sfA0:"E \<noteq> {}" and sfA1:"\<And>x. x \<in> E \<Longrightarrow> is_sup R X (F x) (id x)"
          by (simp add: B1 B3) 
        have sfA3:"\<And>x. x \<in> E \<Longrightarrow> (F x) \<subseteq> X"
        proof-
          fix x assume sfA30:"x \<in> E"
          then obtain "(F x) \<in> Fpow A"
            by (simp add: B3)
          then obtain "(F x) \<subseteq> A"
            by (simp add: Fpow_Pow_finite)
          then show "(F x) \<subseteq> X"  using sub by auto
        qed
        obtain B4:"is_sup R X (id`E) s"  by (simp add: B2)
        then obtain B5:"is_sup R X (\<Union>(F`E)) s" 
          using sup_families1[of E R X F id] sfA0 sfA1 sfA3 por  by blast
        obtain B7:"finite (\<Union>(F`E))" by (metis B0 B3 Fpow_Pow_finite Int_Collect finite_UN)
        obtain B8:"(\<Union>(F`E)) \<noteq> {}"  by (simp add: B3 sfA0) 
        obtain B9:"(\<Union>(F`E)) \<subseteq> A"  using B3 Fpow_subset_Pow by blast
        then obtain "(\<Union>(F`E)) \<in> Fpow A" by (simp add: B7 Fpow_Pow_finite)  
        then show "s \<in> ?L1"
          by (meson B5 B8 fne_sup_cl_memI2)
      qed
    qed
  qed
  show P6:"idempotent (Pow X) (\<lambda>A. fne_sup_cl R X A)"
    by (simp add: P5 idempotent_def)
  show P7:"(\<lambda>A. fne_sup_cl R X A)`(Pow X) \<subseteq> Pow X"
    by (simp add: P0 image_subsetI)
  show P8:"closure (pwr X) (Pow X) (\<lambda>A. fne_sup_cl R X A)"
    by (simp add: P2 P4 P6 P7 closureI1)
  show P9:"is_sup_semilattice R X \<Longrightarrow> (\<And>A. A \<subseteq>X \<Longrightarrow>is_dir (fne_sup_cl R X A) R)"
  proof-
    assume sem:"is_sup_semilattice R X"
    show "\<And>A. A \<subseteq> X \<Longrightarrow> is_dir (fne_sup_cl R X A) R"
    proof-
      fix A assume sub:"A \<subseteq> X"
      show "is_dir (fne_sup_cl R X A) R"
      proof(rule is_dirI1)
       fix a b assume a0:"a \<in> fne_sup_cl R X A" and b0:"b \<in> fne_sup_cl R X A" 
       then obtain Ea Eb where B0:"Ea \<in> Fpow A" and B1:"Ea \<noteq> {}"  and B2:"is_sup R X Ea a" and
                               B3:"Eb \<in> Fpow A" and B4:"Eb \<noteq> {}" and B5:"is_sup R X Eb b"
                               by (meson fne_sup_cl_imp1)
        then obtain B6:"Ea \<union> Eb \<in> Fpow A" and B7:"Ea \<union> Eb \<noteq> {}"
          by (simp add: Fpow_def) 
        then obtain B8:"Ea \<union> Eb \<subseteq> X" and B9:"finite (Ea \<union> Eb)"
          by (metis Fpow_Pow_finite Int_Collect PowD dual_order.trans sub)
        then obtain c where B10:"is_sup R X (Ea \<union> Eb) c"
          by (meson B7 Fpow_ne_iff por sem sup_semilattice_fsup)
        then obtain B11:"c \<in>  fne_sup_cl R X A"
          by (meson B6 B7 fne_sup_cl_memI2)
        obtain B12:"(a,c)\<in>R" and B13:"(b,c)\<in>R"
          by (meson B10 B2 B5 inf_sup_ord(4) is_sup_iso1 sup.cobounded1)
        then show "(\<exists>c\<in>fne_sup_cl R X A. (a, c) \<in> R \<and> (b, c) \<in> R)"
          using B11 by blast
      qed
    qed
  qed
qed



lemma ccompact1:
  assumes por:"pord R X" and sem:"is_csup_semilattice R X" and cmem:"c \<in> X" 
          and dir:"(\<And>A. \<lbrakk>A \<in> Pow_ne X; (c, Sup R X A) \<in> R; is_dir A R\<rbrakk> \<Longrightarrow> (\<exists>a \<in> A. (c, a) \<in> R))"
  shows "is_compact R X c"
proof(rule compactI)
  show "c \<in> X" by(simp add:cmem)
  show "\<And>A. A \<in> Pow_ne X \<Longrightarrow> (c,Sup R X A) \<in> R \<Longrightarrow> \<exists>A0. A0 \<in> Fpow_ne A \<and> (c, Sup R X A0) \<in> R"
  proof-
    fix A assume A0:"A \<in> Pow_ne X" and A1:"(c,Sup R X A)\<in>R"
    let ?C="fne_sup_cl R X A"
    obtain B0:"is_dir ?C R" and B1:"A \<subseteq> ?C" and B2:"A \<subseteq> X" and B3:"?C \<subseteq> X"
      by (meson A0 Pow_ne_iff csup_fsup fne_sup_cl_dir1 fne_sup_cl_ext1 fne_sup_cl_rng1 por sem)
    obtain B4:"(Sup R X A, Sup R X ?C) \<in> R"
      by (metis A0 B1 B3 Pow_ne_iff por sem sup_iso1b) 
    obtain B5:"(c, Sup R X ?C) \<in> R"
      by (metis A0 A1 B1 B3 B4 Pow_ne_iff cmem csupD50 por sem subset_empty trans_onD)
    obtain d where B6:"d \<in> ?C" and B7:"(c, d) \<in> R"
      by (metis A0 B0 B1 B3 B5 Pow_ne_iff bot.extremum_uniqueI dir) 
    obtain Fd where B8:"Fd \<in> Fpow_ne A" and B9:"is_sup R X Fd d"
      by (metis B6 Diff_iff Fpow_ne_def fne_sup_cl_imp1 singletonD)
    obtain B10:"(c, Sup R X Fd) \<in> R"
      using B7 B9 por sup_equality by force
    then show "\<exists>A0. A0 \<in> Fpow_ne A \<and> (c, Sup R X A0) \<in> R"
      using B8 by blast
  qed
qed
  

lemma bot_compact:
  assumes por:"pord R X" and bot:"is_least R X m"
  shows "is_compact R X m"
proof(rule compactI)
  show "m \<in> X"  using bot greatestD by fastforce 
  show "\<And>A. A \<in> Pow_ne X \<Longrightarrow> (m, Sup R X A) \<in> R \<Longrightarrow> \<exists>F. F \<in> Fpow_ne A \<and> (m, Sup R X F) \<in> R"
  proof-
    fix A assume A0:"A \<in> Pow_ne X" and A1:"(m, Sup R X A)\<in>R"
    obtain a where B0:"a \<in> A"  using A0 by blast
    obtain B1:"{a} \<in> Fpow_ne A" and B2:"a \<in> X" using A0 B0 by blast
    then obtain B3:"(m,Sup R X{a})\<in>R"
      using bot greatestD por sup_singleton2 by fastforce
    then show "\<exists>F. F \<in> Fpow_ne A \<and> (m, Sup R X F) \<in> R" using B1 by blast
  qed
qed

subsubsection CompactnessAndClosureRanges

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
  obtain xmem:"{x}\<in>?P" by (simp add: A3)
  obtain B0:"antisym ?R ?P" and B1:"refl ?R ?P" and B2:"trans ?R ?P"   by (meson powrel1 powrel2 powrel3 reflI1 refl_onD)
  let ?f="cl_from_clr ?R C"
  obtain B3:"C \<subseteq> Pow X" and B4:"A \<subseteq> C" and B5:"\<Union>A \<in> C"
    by (metis A0 A2 A4 A6 Pow_ne_iff closure_range_def)
  then obtain B6:"is_sup ?R C A (\<Union>A)" and B7:"Sup ?R C A = \<Union>A"
    by (simp add: powrel6 powrel9 sup_equality sup_in_subset) 
  from A0 A3 B0 B1 B3 obtain B8:"?f {x} \<in> C" and fxmem:"?f {x} \<in> ?P"
    by (metis Int_iff clr_induced_closure_id image_eqI inf.orderE refl_subset xmem)
  from A0 A3 B3 obtain B9:"({x}, ?f {x})\<in>?R"
    by (metis B0 clrD1 clr_equality greatestD singletonI ubdD1 xmem)
  then have B10:"{x} \<subseteq> ?f {x}"  using B9 powrel8 by blast 
  also have B11:"... \<subseteq> \<Union>A"   using A5 B7 by auto 
  then have B12:"{x} \<subseteq> \<Union>A" using calculation by blast 
  then obtain a where B13:"a \<in> A" and B14:"x \<in> a" by auto 
  then obtain amem:"a \<in> ?P" and amem2:"a \<in> C" and B15:"({x},a)\<in>?R"
    by (meson B3 B4 Pow_iff empty_subsetI insert_subsetI pwr_memI subsetD)
  then obtain B16:"a \<in> ubd ?R C {{x}}"
    by (meson B13 B4 subsetD ubd_singleton_mem)
  then obtain fa1:"?f a \<in> C" and fa2:"?f a \<in> ?P"
    by (metis A0 B0 B1 B3 IntE amem clr_induced_closure_id image_eqI inf.orderE refl_subset)
  then obtain  B17:"?f a = a"
    by (meson A0 B0 B1 B3 amem2 clr_equality is_sup_def powrel6 refl_subset sup_singleton1)
  then obtain B18:"(?f {x},?f a)\<in>?R"
    by (metis A0 B0 B16 closure_range_def clr_equality converseD greatestD xmem)
  then obtain B19:"(?f {x}, a)\<in>?R" and B20:"?f {x} \<subseteq> a"
    by (simp add: B17 powrel8) 
  then show "(\<exists>a\<in>A. ?f {x} \<subseteq> a)" using B13 by blast  
qed

      
lemma dir_set_closure_subset2:
  assumes A0:"clr (pwr X) (Pow X) C" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (pwr X)  \<Longrightarrow> \<Union>D \<in> C)" and
          A3:"x \<in> X" and 
          A4:"A \<in> Pow_ne C" and
          A5:"((cl_from_clr  (pwr X) C) {x}, Sup  (pwr X) C A) \<in> pwr X" and 
          A6:"is_dir A (pwr X)"
  shows "\<exists>a \<in> A. ((cl_from_clr (pwr X) C) {x}, a) \<in> pwr X"
  using dir_set_closure_subset[of X C x A]
  by (metis A0 A2 A3 A4 A5 A6 Int_iff Pow_iff Pow_ne_iff closure_range_def inf.orderE pwr_mem_iff)

lemma singleton_closure_compact:
  assumes A0:"clr (pwr X) (Pow X) C" and 
          A1:"(\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C)" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk>\<Longrightarrow> is_dir D (pwr X)  \<Longrightarrow> \<Union>D \<in> C)" and
          A3:"x \<in> X"
  shows "is_compact (pwr X) C (cl_from_clr (pwr X) C {x})"
proof(rule ccompact1)
  show P0:"pord (pwr X) C"
    by (meson A0 Pow_iff Pow_top clrD1 powrel6 powrel7 pwr_memI refl_def subsetD)
  show P1:"is_csup_semilattice (pwr X) C"
    by (meson A0 PowD clatD1 clr_clattice2 pow_is_clattice powrel1 powrel2 pwr_memI reflI1 subset_iff)
  show P2:"cl_from_clr (pwr X) C {x} \<in> C"
     by (metis A0 A3 P0 PowD PowI Pow_bottom clr_induced_closure_id insert_subsetI powrel1 rev_image_eqI)
  show "\<And>A. A \<in> Pow_ne C \<Longrightarrow> (cl_from_clr (pwr X) C {x}, Sup (pwr X) C A) \<in> pwr X \<Longrightarrow> is_dir A (pwr X) \<Longrightarrow> \<exists>a\<in>A. (cl_from_clr (pwr X) C {x}, a) \<in> pwr X"
    by (simp add: A0 A2 A3 dir_set_closure_subset2)
qed




lemma closed_compgen:
  assumes A0:"clr (pwr X) (Pow X) C" and 
          A1:"(\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C)" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (pwr X) \<Longrightarrow> \<Union>D \<in> C)" and
          A3:"E \<in> C"
  shows "(\<exists>A \<in> Pow (compact_elements (pwr X) C). is_sup (pwr X) C A E)"
proof-
   let ?R="pwr X"  let ?f="cl_from_clr ?R C" let ?A="{y. (\<exists>x \<in> E. y= ?f {x})}"
  obtain por:"pord (pwr X) (Pow X)" and clat:"is_clattice (pwr X) (Pow X)"
    by (simp add: pow_is_clattice powrel1 powrel2 pwr_memI refl_def)
  then obtain B0:"is_clattice (pwr X) C"  using A0 clr_clattice2 by blast
  have B1:"\<And>x. x \<in> X \<Longrightarrow> is_compact (pwr X) C (?f {x})" 
    by (metis A0 A1 A2 singleton_closure_compact)
  obtain B2:"E \<in> Pow X" 
    using A0 A3 clrD1 by blast 
  obtain B3:"\<And>x. x \<in> E \<Longrightarrow> {x} \<in> Pow X"  
    using B2 by blast 
  have B4:"?A \<subseteq> C"
  proof 
    fix y assume A9:"y \<in> ?A" then obtain x where B40:"x \<in> E" and B41:"y = ?f {x}" by blast
    then show "y \<in> C"  using B1 B2 compactD2 by fastforce 
  qed
  have B5:"\<And>x. x \<in> E \<Longrightarrow> {x} \<subseteq> ?f {x}"
  proof-
    fix x assume "x \<in> E" then obtain "{x}\<in>Pow X" using B3 by force
    then show "{x} \<subseteq> ?f {x}"
      by (metis A0 clrD1 clr_equality greatestD powrel1 powrel8 ubd_singleton_mem)
  qed
  have B6:"?f E = E" by (metis A0 A3 cl_is_closure closure_def clrD1 clr_induced_closure_id idempotentD3 por refl_subset)
  have B7:"\<And>x. x \<in> E \<Longrightarrow> ?f {x} \<subseteq> ?f E"
  proof-
    fix x assume B70:"x \<in> E" then obtain B71:"{x}\<in>Pow X" using B3 by force
    have B72:"({x}, E)\<in> pwr X"
      by (meson B2 B70 Pow_iff empty_subsetI insert_subsetI pwr_memI)
    then obtain B73:"(?f {x}, ?f E)\<in>pwr X"
      by (metis A0 A3 B6 B71 clrD1 clr_equality converse_iff greatestD por ubd_singleton_mem)
    then show "?f {x} \<subseteq> ?f E"
      using powrel8 by blast
  qed
  have B8:"E \<in> ubd ?R C ?A" 
  proof(rule ubdI)
    show B80:"E \<in> C" by (simp add: A3)
    show B81:"\<And>a. a \<in> ?A\<Longrightarrow> (a, E) \<in> pwr X" using B2 B6 B7 pwr_mem_iff by fastforce
  qed
  have B9:"E = (\<Union>x \<in> E. {x})"  by simp
  have B10:"... \<subseteq> (\<Union>x \<in> E. ?f {x})" using B5 by blast
  have B11:"... = (\<Union>?A)"  by blast
  have B12:"... = Sup ?R (Pow X) ?A" by (metis (no_types, lifting) A0 B4 clrD1 por powrel9 sup_equality) 
  have B13:"... \<subseteq> Sup ?R C ?A" using sup_iso2[of "Pow X" ?R C]
    by (metis (no_types, lifting) A0 B0 B4 clat clrD1 por pwr_mem_iff)
  have B14:"... \<subseteq> E"
    by (smt (verit, ccfv_SIG) A0 B10 B11 B2 B4 B8 B9 clrD1 is_supD1 powrel6 powrel8 powrel9 set_eq_subset sup_equality sup_in_subset ubdD1)
  have B15:"\<And>x. x \<in> ?A \<Longrightarrow> x \<in> compact_elements ?R C"
    using B1 B2 compact_elements_mem_iff1 by fastforce 
  have B16:"?A \<in> Pow (compact_elements ?R C)"
    using B15 by blast 
  have B17:"E = Sup ?R C ?A"
    using B10 B12 B13 B14 by auto 
  then obtain B18:"is_sup ?R C ?A E"
    by (metis (no_types, lifting) A0 B0 B4 clrD1 is_clattice_def powrel6 sup_equality)
  then show "\<exists>A \<in> Pow (compact_elements ?R C). is_sup ?R C A E"
    using B16 by blast  
qed


lemma clr_compgen:
  assumes A0:"clr (pwr X) (Pow X) C" and 
          A1:"(\<And>A. \<lbrakk>A \<subseteq> C; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in> C)" and
          A2:"(\<And>D. \<lbrakk>D \<subseteq> C; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (pwr X) \<Longrightarrow> \<Union>D \<in> C)"
  shows clr_compgen1:"compactly_generated (pwr X) C" and
        clr_compgen2:"\<And>x. x \<in> X \<Longrightarrow> is_compact (pwr X) C ((cl_from_clr (pwr X) C) {x})"
proof-
  show "compactly_generated (pwr X) C"
    by (simp add: A0 A1 A2 closed_compgen compactly_generatedI1) 
  show "\<And>x. x \<in> X \<Longrightarrow> is_compact (pwr X) C ((cl_from_clr (pwr X) C) {x})"
    by (simp add: A0 A1 A2 singleton_closure_compact)
qed


lemma filters_on_lattice_compactgen:
  assumes por:"pord R X" and lat:"is_lattice R X" and top:"is_greatest R X top"
  shows  "compactly_generated (pwr X) (filters_on R X)"
proof(rule clr_compgen1)
  show "clr (pwr X) (Pow X) (filters_on R X)"
    by (metis filters_clr lat latt_iff por top)
  show "\<And>A.  A \<subseteq> filters_on R X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<Inter> A \<in> filters_on R X"
    by (metis PowI filter_inter2 lat latt_iff por top)
  show "\<And>D. D \<subseteq> filters_on R X \<Longrightarrow> D \<noteq> {} \<Longrightarrow> is_dir D (pwr X) \<Longrightarrow> \<Union> D \<in> filters_on R X"
    by (simp add: filters_on_iff lat lattice_filter_dunion9 por)
qed


lemma filters_on_lattice_compactgen0:
  assumes lat:"is_lattice R X" and top:"is_greatest R X top" and nem:"X \<noteq> {}" and por:"pord R X"
  shows filters_on_lattice_compactgen01:"clr (pwr X) (Pow X) (filters_on R X)" and 
        filters_on_lattice_compactgen02:"(\<And>A. \<lbrakk>A \<subseteq>  (filters_on R X) ; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>A \<in>  (filters_on R X))" and
        filters_on_lattice_compactgen03:"(\<And>D. \<lbrakk>D \<subseteq>  (filters_on R X) ; D \<noteq> {}\<rbrakk> \<Longrightarrow> is_dir D (pwr X) \<Longrightarrow> \<Union>D \<in>  (filters_on R X) )"
proof-
  show "clr (pwr X) (Pow X) (filters_on R X)"
    by (metis filters_clr lat latt_iff por top) 
  show "\<And>A. A \<subseteq> filters_on R X \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<Inter> A \<in> filters_on R X"
    by (metis PowI filter_inter2 lat latt_iff por top) 
  show "\<And>D. D \<subseteq> filters_on R X \<Longrightarrow> D \<noteq> {} \<Longrightarrow> is_dir D (pwr X) \<Longrightarrow> \<Union> D \<in> filters_on R X"
  proof-
    fix D assume A0:"D \<subseteq> filters_on R X" and A1:"D \<noteq> {}" and A2:"is_dir D (pwr X)"
    have A3:"is_filter R X (\<Union> D)"
    proof(rule is_filterI1)
      show "\<Union> D \<noteq> {}"
        using A0 A1 A2 lat lattice_filter_dunion1 por by blast
      show "\<Union> D \<subseteq> X"
        by (meson A0 A1 lattice_filter_dunion7) 
      show "is_dir (\<Union> D) (dual R)"
      proof(rule is_dirI1)
        fix a b assume A4:"a \<in> \<Union> D " and A5:"b \<in> \<Union> D"
        then obtain Fa Fb where fa1:"Fa \<in> D" and fb1:"Fb \<in>D" and fa2:"a \<in> Fa" and fb2:"b\<in> Fb" by blast
        then obtain Fab where fab1:"Fab \<in> D" and  fab2:"Fa \<subseteq>  Fab" and fab3: "Fb \<subseteq> Fab"
          by (meson A2 is_dirE1 pwr_memD)
        then obtain fab4:"a \<in> Fab" and fab5:"b \<in> Fab" and fab6:"is_filter R X Fab"
          using A0 fa2 fb2 filters_on_iff by blast 
        then obtain fab7:"Inf R X {a, b} \<in> Fab"
          by (metis filter_inf_closed2 lat latt_iff por) 
        obtain fab8:"Inf R X {a,b}\<in> X" and fab9:"a \<in> X" and fab10:"b \<in> X"
          using fab4 fab5 fab6 fab7 is_filterD1 by blast
        obtain "(Inf R X {a, b}, a)\<in>R" and "(Inf R X {a, b},b)\<in>R"
          by (metis binf_le1 binf_le2 fab10 fab9 lat latt_iff por) 
        then show "\<exists>c\<in>\<Union> D. (a, c) \<in> dual R \<and> (b, c) \<in> dual R"
          using fab1 fab7 by blast 
       qed
      show "is_ord_cl X (\<Union> D) R"
        by (simp add: A0 A1 A2 lat lattice_filter_dunion2 por)
    qed
    then show "\<Union> D \<in> filters_on R X" 
      by (simp add: filters_on_iff)
  qed
qed




subsection UpDwClosure
subsubsection UpClosure


lemma up_cl_memD1:
  "x \<in> up_cl R X A \<Longrightarrow> x \<in> X \<and> (\<exists>a \<in> A. (a, x) \<in> R)"
  by (simp add: up_cl_def)

lemma up_cl_memI1:
  "\<lbrakk>x \<in> X;a \<in> A; (a, x) \<in> R\<rbrakk> \<Longrightarrow> x \<in> up_cl R X A"
  unfolding up_cl_def by auto

lemma up_cl_memI2:
  "x \<in> X \<Longrightarrow> (\<exists>a \<in> A. (a, x) \<in> R) \<Longrightarrow> x \<in> up_cl R X A"
  unfolding up_cl_def by auto


lemma up_cl_props:
  assumes por:"pord R X"
  shows up_cl_rng1:"\<And>A. up_cl R X A \<subseteq> X" and
        up_cl_ext1:"\<And>A. A \<subseteq> X \<Longrightarrow> A \<subseteq> up_cl R X A" and
        up_cl_ext2:"extensive (pwr X) (Pow X) (\<lambda>A. up_cl R X A)" and
        up_cl_iso1:"(\<And>A B. \<lbrakk>A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> up_cl R X A \<subseteq> up_cl R X B)" and
        up_cl_iso2:"isotone (pwr X) (Pow X) (pwr X) (\<lambda>A. up_cl R X A)" and
        up_cl_ide1:"\<And>A. A \<subseteq> X \<Longrightarrow> up_cl R X (up_cl R X A) = up_cl R X A" and
        up_cl_ide2:"idempotent (Pow X) (\<lambda>A. up_cl R X A)" and
        up_cl_rng2:"(\<lambda>A. up_cl R X A)`(Pow X) \<subseteq> Pow X" and
        up_cl_iscl:"closure (pwr X) (Pow X) (\<lambda>A. up_cl R X A)" and
        up_cl_orcl:"\<And>A. A \<subseteq> X \<Longrightarrow> is_ord_cl X (up_cl R X A) R"
proof-
  show P0:"\<And>A. up_cl R X A \<subseteq> X"
    by (simp add: up_cl_def)
  show P1:"\<And>A. A \<subseteq> X \<Longrightarrow> A \<subseteq> up_cl R X A"
    by (meson por reflD2 subsetD subsetI up_cl_memI1) 
  show P2:"extensive (pwr X) (Pow X) (\<lambda>A. up_cl R X A)"
    by (simp add: P0 P1 extensive_def pwr_mem_iff) 
  show P3:"(\<And>A B. \<lbrakk>A \<subseteq> B; B \<subseteq> X\<rbrakk> \<Longrightarrow> up_cl R X A \<subseteq> up_cl R X B)"
    using up_cl_def up_cl_memD1 by fastforce 
  show P4:"isotone (pwr X) (Pow X) (pwr X) (\<lambda>A. up_cl R X A)"
    by (simp add: P0 P3 isotone_def pwr_mem_iff) 
  show P5:"\<And>A. A \<subseteq> X \<Longrightarrow> up_cl R X (up_cl R X A) = up_cl R X A" 
  proof-
    fix A assume sub:"A \<subseteq> X" 
    show "up_cl R X (up_cl R X A) = up_cl R X A" (is "?L = ?R")
    proof-
      have "\<And>x. x \<in> ?L \<longleftrightarrow> x \<in> ?R"
      proof-
        fix x
        have "x \<in> ?L \<longleftrightarrow> x \<in> X \<and> (\<exists>a \<in> (up_cl R X A). (a, x) \<in> R)"
          unfolding up_cl_def by blast
        also have "... \<longleftrightarrow> x \<in> X \<and>(\<exists>a. a \<in> X \<and> (\<exists>b \<in> A. (b ,a)\<in>R) \<and> (a,x)\<in>R)"
           unfolding up_cl_def  by blast
        also have "... \<longleftrightarrow> x \<in> X \<and> (\<exists>a \<in> A. (a,x)\<in>R)"
           by (meson sub por reflD2 subsetD trans_onD)
        also have "... \<longleftrightarrow> x \<in> ?R"
          unfolding up_cl_def by blast
        finally show "x \<in> ?L \<longleftrightarrow> x \<in> ?R" by blast
      qed
     then show ?thesis by blast
    qed
  qed
  show P6:"idempotent (Pow X) (\<lambda>A. up_cl R X A)"
    by (simp add: P5 idempotent_def) 
  show P7:"(\<lambda>A. up_cl R X A)`(Pow X) \<subseteq> Pow X"
    by (simp add: P0 image_subsetI)
  show P8:"closure (pwr X) (Pow X) (\<lambda>A. up_cl R X A)"
    by (simp add: P2 P4 P6 P7 closureI1)
  show P9:"\<And>A. A \<subseteq> X \<Longrightarrow> is_ord_cl X (up_cl R X A) R"
  proof-
    fix A assume sub:"A \<subseteq> X"
    show "is_ord_cl X (up_cl R X A) R" 
    proof(rule is_ord_clI1)
      fix a b assume a0:"a \<in> up_cl R X A" and b0:"b \<in> X" and ab:"(a,b)\<in>R"
      then show "b \<in> up_cl R X A" using P5 sub up_cl_memI1[of b X a "up_cl R X A" R]  by blast
    qed
  qed
qed

lemma dwdir_upcl_is_dwdir:
  assumes A0:"is_dir A (converse R)" and A1:"A \<subseteq> X" and A2:"trans R X" and A3:"refl R X"
  shows "is_dir (up_cl R X A) (converse R)"
proof(rule is_dirI1)
  fix a b assume A4:"a \<in> up_cl R X A" and A5:"b \<in> up_cl R X A" 
  then obtain a1 b1 where B1:"a1 \<in> A" and B2:"b1 \<in> A" and B3:"(a1,a)\<in>R" and B4:"(b1,b)\<in>R"
    by (meson up_cl_memD1)
  then obtain c where B5: "c \<in> A" and B6:"(c,a1)\<in>R" and B7:"(c,b1)\<in>R"
    by (meson A0 converseD is_dirE1)
  then obtain "c \<in> up_cl R X A" and "(c,a)\<in>R" and "(c,b)\<in>R"
    by (meson A1 A2 A3 A4 A5 B1 B2 B3 B4 refl_def subsetD trans_onD up_cl_memD1 up_cl_memI1)
  then show "\<exists>c\<in>up_cl R X A. (a, c) \<in> dual R \<and> (b, c) \<in> dual R"
    by blast
qed

lemma leq_sup:
  "\<lbrakk>pord R X; is_lattice R X; x \<in> X; y \<in>X; z \<in> X;(x, z)\<in>R; (y,z)\<in>R\<rbrakk> \<Longrightarrow> (Sup R X {x, y}, z) \<in>R"
  by (simp add: bsup_ge3 lattD42)

subsection BinaryFilterSup

lemma filter_bsup_memD1:
  "x \<in> binary_filter_sup R X A B \<Longrightarrow>  (x \<in> X \<and> (\<exists>a \<in> A. \<exists>b \<in> B. (Inf R X {a, b}, x)\<in>R))"
   by (simp add:binary_filter_sup_def)

lemma filter_bsup_memI1:
  "(x \<in> X \<and> (\<exists>a \<in> A. \<exists>b \<in> B. (Inf R X {a, b}, x)\<in>R)) \<Longrightarrow> x \<in> binary_filter_sup R X A B "
  by (simp add:binary_filter_sup_def)

lemma filter_bsup_comm:
  "binary_filter_sup R X A B = binary_filter_sup R X B A"
  unfolding binary_filter_sup_def  by (metis (no_types, lifting) doubleton_eq_iff)

lemma filter_on_lattice_bsup:
  assumes por:"pord R X" and lat:"is_lattice R X" 
  shows filter_on_lattice_bsup1a:"\<And>a F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2; a \<in> F1\<rbrakk> \<Longrightarrow> a \<in> binary_filter_sup R X F1 F2" and
        filter_on_lattice_bsup1b:"\<And>a F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2; a \<in> F2\<rbrakk> \<Longrightarrow> a \<in> binary_filter_sup R X F1 F2" and
        filter_on_lattice_bsup2a:"\<And>F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow>  F1 \<subseteq> (binary_filter_sup R X F1 F2)" and
        filter_on_lattice_bsup2b:"\<And>F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow>  F2 \<subseteq> (binary_filter_sup R X F1 F2)" and
        filter_on_lattice_bsup3:"\<And>F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow>  is_ord_cl X (binary_filter_sup R X F1 F2) R" and
        filter_on_lattice_bsup4:"\<And>F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow>  is_dir (binary_filter_sup R X F1 F2) (dual R)" and
        filter_on_lattice_bsup5:"\<And>F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow>  binary_filter_sup R X F1 F2 \<noteq> {}" and
        filter_on_lattice_bsup6:"\<And>F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow>  binary_filter_sup R X F1 F2 \<subseteq> X" and
        filter_on_lattice_bsup7:"\<And>F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow>  is_filter R X (binary_filter_sup R X F1 F2)" and
        filter_on_lattice_bsup8:"\<And>F1 F2.  \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> (binary_filter_sup R X F1 F2) \<in> ubd (pwr X) (filters_on R X) {F1, F2}" and
        filter_on_lattice_bsup9:"\<And>G F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2;is_filter R X G; G \<in> (ubd (pwr X)  (filters_on R X) {F1, F2})\<rbrakk>  \<Longrightarrow> ((binary_filter_sup R X F1 F2), G)\<in>(pwr X)" and
        filter_on_lattice_bsup10:"\<And>F1 F2.  \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk>  \<Longrightarrow> is_sup (pwr X) (filters_on R X) {F1, F2} (binary_filter_sup R X F1 F2)" and
        filter_on_lattice_bsup11:"\<And>F1 F2.  \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> Sup (pwr X) (filters_on R X) {F1, F2} = (binary_filter_sup R X F1 F2)" 
proof-
  show P0: "\<And>a F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2; a \<in> F1\<rbrakk> \<Longrightarrow> a \<in> binary_filter_sup R X F1 F2"
  proof-
    fix a F1 F2 assume A1:"is_filter R X  F1" and A2:"is_filter R X  F2" and A3:"a \<in> F1"
    obtain y where A4:"y \<in> F2"
      using A2 is_filterD1 by fastforce
    then obtain B0:"y \<in> X" and B1:"a \<in> X"  using A1 A2 A3 is_filterD1 by blast
    then obtain B2:"(Inf R X {a, y}, a)\<in>R"
      using binf_le1 lat lattD31 por by fastforce
    then show "a \<in> binary_filter_sup R X F1 F2"
      by (meson A3 A4 B1 filter_bsup_memI1)
  qed
  show P0b:"\<And>a F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2; a \<in> F2\<rbrakk> \<Longrightarrow> a \<in> binary_filter_sup R X F1 F2"
    by (metis P0 filter_bsup_comm)
  show P1:"\<And>F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow>  F1 \<subseteq> (binary_filter_sup R X F1 F2)"
    by (simp add: P0 subsetI)
  show P1b:"\<And>F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow>  F2 \<subseteq> (binary_filter_sup R X F1 F2)"
    by (simp add: P0b subsetI)
  show P2:"\<And>F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow>  is_ord_cl X (binary_filter_sup R X F1 F2) R"
  proof-
     fix F1 F2 assume A1:"is_filter R X  F1" and A2:"is_filter R X  F2"
     show "is_ord_cl X (binary_filter_sup R X F1 F2) R"
     proof(rule is_ord_clI1)
      fix a b assume a0:"a \<in> (binary_filter_sup R X F1 F2)" and b0:"b \<in> X" and ab0:"(a,b)\<in>R"
      then obtain a1:"a \<in> X" using filter_bsup_memD1 by force
      obtain x y where x0:"x \<in> F1" and y0:"y \<in> F2" and ixy:"(Inf R X {x, y}, a)\<in>R"
        by (meson a0 filter_bsup_memD1)
      obtain x1:"x \<in> X" and y1:"y \<in> X"
        using A1 A2 is_filterD1 x0 y0 by blast 
      then  obtain xymem:"Inf R X {x,y}\<in>X"
        by (meson is_supD1 lat lattD31 por)
      then obtain ixyr:"(Inf R X {x,y}, Inf R X {x,y})\<in>R"
        by (meson por reflD2)
      then obtain ixymem:"Inf R X {x,y}\<in>(binary_filter_sup R X F1 F2)"
        by (meson filter_bsup_memI1 x0 xymem y0) 
      then obtain "(Inf R X {x,y}, b)\<in>R"
        by (meson a1 ab0 b0 ixy por trans_onD xymem)
      then show "b \<in> (binary_filter_sup R X F1 F2) "
        by (meson b0 filter_bsup_memI1 x0 y0)
    qed
  qed
  show P3:"\<And>F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow>  is_dir (binary_filter_sup R X F1 F2) (dual R)"
  proof-
    fix F1 F2 assume fil1:"is_filter R X F1" and fil2:"is_filter R X F2" let ?FC="binary_filter_sup R X F1 F2"
    show "is_dir ?FC (dual R)"
    proof(rule is_dirI1)
      fix a b assume amem1:"a \<in> ?FC" and bmem1:"b \<in> ?FC"
      then obtain amem2:"a \<in> X" and bmem2:"b \<in> X" using filter_bsup_memD1 by force
      obtain a1 a2 b1 b2 where B0:"a1 \<in> F1" and B1:"b1 \<in> F1" and B2:"a2 \<in> F2" and B3:"b2 \<in> F2" and 
                               B4:"(Inf R X {a1, a2}, a)\<in>R" and B5:"(Inf R X {b1,b2},b)\<in>R"
         by (meson amem1 bmem1 filter_bsup_memD1)
      then obtain B6:"a1 \<in> X" and B7:"a2 \<in> X" and B8:"b1 \<in> X" and B9:"b2 \<in> X"
        using fil1 fil2 is_filterD1 by blast
      obtain B10:"Inf R X {a1,b1}\<in>F1" and B11:"Inf R X {a2,b2}\<in>F2"
        by (metis B0 B1 B2 B3 fil1 fil2 filter_inf_closed2 lat latt_iff por)
      obtain B12:"Inf R X {a1,b1} \<in> X" and B13:"Inf R X {a2,b2}\<in>X"
        using B10 B11 fil1 fil2 is_filterD1 by auto
      obtain B14:"Inf R X {a1, a2} \<in> X" and B15:"Inf R X {b1, b2}\<in>X"
        by (meson B6 B7 B8 B9 is_supD1 lat lattD31 por)
      have B16:"Inf R X {Inf R X {a1,b1},Inf R X {a2,b2}} =  Inf R X {a1,b1,a2,b2}"
        by (metis B6 B7 B8 B9 lat latt_iff por semilattice_assoc_inf)
      also have B17:"... = Inf R X {a1,a2,b1,b2}"
        by (simp add: insert_commute)
      also have B18:"... = Inf R X {Inf R X {a1, a2}, Inf R X {b1, b2}}"
        by (metis B6 B7 B8 B9 lat latt_iff por semilattice_assoc_inf)
      obtain B19:"(Inf R X {Inf R X {a1, a2}, Inf R X {b1, b2}},a)\<in>R "
        by (metis B14 B15 B4 le_infI1 amem2 lat latt_iff por)
      then obtain B20:"(Inf R X {Inf R X {a1, b1}, Inf R X {a2, b2}},a)\<in>R"
        using B16 B17 B18 by presburger
      obtain B21:"(Inf R X {Inf R X {a1, a2}, Inf R X {b1, b2}},b)\<in>R "
        by (metis B14 B15 B5 le_infI2 bmem2 lat latt_iff por)
      then obtain B22:"(Inf R X {Inf R X {a1, b1}, Inf R X {a2, b2}},b)\<in>R"
        using B16 B17 B18 by presburger
      have B23:"Inf R X {Inf R X {a1, b1}, Inf R X {a2, b2}} \<in> (binary_filter_sup R X F1 F2)"
        by (meson B10 B11 B12 B13 filter_bsup_memI1 is_supD1 lat lattD31 por reflD2)
      show "\<exists>c \<in> ?FC. (a,c)\<in>(dual R)\<and>(b,c)\<in>(dual R)"
        using B18 B19 B21 B23 calculation by auto
    qed
  qed
  show P4:"\<And>F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow>  binary_filter_sup R X F1 F2 \<noteq> {}"
    by (metis P1 empty_subsetI equalityI is_filterD1) 
  show P5:"\<And>F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow>  binary_filter_sup R X F1 F2 \<subseteq> X"
    by (meson filter_bsup_memD1 subsetI)
  show P6:"\<And>F1 F2. \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow>  is_filter R X (binary_filter_sup R X F1 F2)"
  proof-
    fix F1 F2 assume fil1:"is_filter R X F1" and fil2:"is_filter R X F2" let ?FC="binary_filter_sup R X F1 F2"
    show "is_filter R X ?FC"
    proof(rule is_filterI1)
      show "?FC \<noteq> {}"
        by (simp add: P4 fil1 fil2)
      show "?FC \<subseteq> X"
        by (simp add: P5 fil1 fil2)
      show "is_dir ?FC (dual R)"
         by (simp add: P3 fil1 fil2)
      show "is_ord_cl X ?FC R"
         by (simp add: P2 fil1 fil2)
    qed
  qed
  show P7:"\<And>F1 F2.  \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> (binary_filter_sup R X F1 F2) \<in> ubd (pwr X) (filters_on R X) {F1, F2}"
  proof-
    fix F1 F2 assume fil1:"is_filter R X F1" and fil2:"is_filter R X F2" let ?FC="binary_filter_sup R X F1 F2"
    show "?FC \<in>ubd (pwr X) (filters_on R X) {F1, F2}"
    proof(rule ubdI)
      show "?FC \<in> filters_on R X"
        by (simp add: P6 fil1 fil2 filters_on_iff)
      show "\<And>a. a \<in> {F1, F2} \<Longrightarrow> (a, ?FC) \<in> pwr X"
        by (metis P1 P1b P5 fil1 fil2 insertE pwr_mem_iff singleton_iff)
    qed
  qed
  show P8:"\<And>G F1 F2.  \<lbrakk>is_filter R X F1; is_filter R X F2;is_filter R X G; G \<in> (ubd (pwr X)  (filters_on R X) {F1, F2})\<rbrakk> 
        \<Longrightarrow> ((binary_filter_sup R X F1 F2), G)\<in>(pwr X)"
  proof-
    fix G F1 F2 
    assume fil0:"is_filter R X G" and fil1:"is_filter R X F1" and fil2:"is_filter R X F2" and
               gubd: "G \<in> (ubd (pwr X)  (filters_on R X) {F1, F2})" 
     let ?FC="binary_filter_sup R X F1 F2"
    have "?FC \<subseteq> G"
    proof
      fix x assume A4:"x \<in> ?FC"
      obtain a1 a2 where B0:"a1 \<in> F1" and B1:"a2 \<in> F2" and B2:"(Inf R X {a1, a2},x)\<in>R"
        by (meson A4 filter_bsup_memD1)
      then obtain B3:"a1 \<in> G" and B4:"a2 \<in> G"
        by (metis gubd insertCI insert_Diff insert_subset powrel8 ubdD1)
      then obtain B4:"Inf R X {a1, a2} \<in> G"
        by (metis fil0 filter_inf_closed2 lat latt_iff por)
      show "x \<in> G"
        by (meson A4 B2 B4 fil0 filter_bsup_memD1 is_filterD1 is_ord_clE1)
    qed
    then show "(?FC,G)\<in>(pwr X)"
      by (meson fil0 is_filterD1 pwr_memI)
  qed
  show P9:"\<And>F1 F2.  \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk>  \<Longrightarrow> is_sup (pwr X) (filters_on R X) {F1, F2} (binary_filter_sup R X F1 F2)"
    by (meson P7 P8 converseI filters_on_iff greatestI2 is_sup_def subsetD ubd_sub)
  show P10:"\<And>F1 F2.  \<lbrakk>is_filter R X F1; is_filter R X F2\<rbrakk> \<Longrightarrow> Sup (pwr X) (filters_on R X) {F1, F2} = (binary_filter_sup R X F1 F2)"
  by (simp add: P9 antisym_on_def pwr_mem_iff subset_antisym sup_equality)
qed

  
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
          by (simp add: A1 A2 A3 A4 A5 A6 B01 lattice_filters_isl7 lattice_filters_isl8)
        obtain B3:"z \<in> ?sfg" and B4:"z \<in> ?sfh" using B2 A7 by blast 
        then obtain x1 y where B5:"x1 \<in> f" and B6:" y \<in> g"  and B7:"(Inf R X {x1, y},z)\<in>R"
          by (metis A1 A2 A3 A4 A5 B01 filter_bsup_memD1 filter_on_lattice_bsup11 filters_on_iff)
        obtain x2 t where B8:"x2 \<in> f" and B9:"t \<in> h" and B10:"(Inf R X {x2,t},z)\<in>R"
          by (metis A1 A2 A3 A4 A6 B01 B4 filter_bsup_memD1 filter_on_lattice_bsup11 filters_on_iff)
        then obtain B11:"x1 \<in> X" and B12:"y \<in> X" and B13:"x2 \<in> X" and B14:"t \<in> X"
          by (meson A4 A5 A6 B5 B6 filters_on_iff is_filterD1 subsetD)
        then obtain B15:"Sup R X {x1,Inf R X {x2,t}}\<in>f"
          by (meson A1 A3 A4 B01 B5 bsup_ge1 filters_on_iff is_filterD1 is_ord_clD1 is_supD1 lattD31 lattD42 ssupD4)
        then obtain B16:"Sup R X {y,x2}\<in>f"
          by (meson A1 A3 A4 B01 B12 B13 B8 bsup_ge2 filters_on_iff is_filterD1 is_ord_clE1 lattD42 ssupD4)
        then obtain B17:"Sup R X {y,t} \<in> g"
          by (meson A1 A3 A5 B01 B12 B14 B6 bsup_ge1 filters_on_iff is_filterD1 is_ord_clE1 lattD42 ssupD4)
        then obtain B18:"Sup R X {y, t} \<in> h"
          by (meson A1 A3 A6 B01 B12 B14 B9 bsup_ge2 filters_on_iff is_filterD1 is_ord_clE1 lattD42 ssupD4)
        have B19:"Inf R X {Sup R X {x1, Inf R X {x2, t}}, Sup R X {y, x2}} \<in> f"
          using A1 A4 B01 B15 B16 filter_inf_closed2 filters_on_iff lattD4 by fastforce
        have B20:"Inf R X {Sup R X {y, x2}, Sup R X {y, t}} = Sup R X {y, Inf R X {x2, t}}"
          by (simp add: A0 B12 B13 B14 distr_latticeD1)
        then obtain B21:
        "Inf R X {Sup R X {x1, Inf R X {x2, t}}, Inf R X {Sup R X {y, x2}, Sup R X {y, t}}} =  
                        Inf R X {Sup R X {x1, Inf R X {x2, t}},  Sup R X {y, Inf R X {x2, t}}}"
          by simp
        have B22:"... = Sup R X {Inf R X {x1, y}, Inf R X {x2, t}}"
          by (metis A0 A1 B01 B11 B12 B13 B14 distr_latticeD2 is_supD1 lattD31)
        obtain B23:"Inf R X {x1,y}\<in>X" and B24:"Inf R X {x2,t}\<in>X" and B25:"Inf R X {x2,t}\<in>X" and 
               B26:"Sup R X {y,x2}\<in>X" and B27:"Sup R X {y,t}\<in>X"
               by (meson A1 B01 B11 B12 B13 B14 is_supD1 lattD31 lattD42 ssupD4)
        have B28:"Sup R X {Inf R X {x1, y}, Inf R X {x2, t}} = 
                  Inf R X {Sup R X {x1, Inf R X {x2, t}}, Inf R X {Sup R X {y, x2}, Sup R X {y, t}}} "
                  by (simp add: B22 B21)
        have B29:"... =  Inf R X {Inf R X {Sup R X {x1, Inf R X {x2, t}}, Sup R X {y, x2}}, Sup R X {y, t}}"
          using binf_assoc2 latt_iff ssupD4 A1 A3 B01 B11 B25 B26 B27 by metis
        obtain B30:"(Inf R X {x1, y},z)\<in>R" and B31:"(Inf R X {x2,t},z)\<in>R" and B32:"z \<in> X"
          by (metis A1 A2 A3 A4 A6 B01 B10 B4 B7 filter_bsup_memD1 filter_on_lattice_bsup11 filters_on_iff)
        have B33:"(Sup R X {Inf R X {x1, y}, Inf R X {x2, t}}, z)\<in>R"
          by (simp add: A1 A2 A3 B01 B23 B25 B31 B32 B7 leq_sup) 
        have B34:"(Inf R X {Inf R X {Sup R X {x1, Inf R X {x2, t}}, Sup R X {y, x2}}, Sup R X {y, t}},z)\<in>R"
          using B21 B22 B29 B33 by presburger
        have B35:"Inf R X {Sup R X {x1, Inf R X {x2, t}}, Sup R X {y, x2}} \<in> f"
          using B19 by blast
        have B36:"Sup R X {y, t} \<in> Inf ?R ?F {g, h}"
          by (simp add: A1 A2 A3 A5 A6 B01 B17 B18 lattice_filters_isl7)
        have B37:"z \<in> binary_filter_sup R X f ?igh"
          by (meson B32 B34 B35 B36 filter_bsup_memI1)
        have B38:" binary_filter_sup R X f ?igh = Sup ?R ?F {f, ?igh}"
          by (metis A1 A2 A3 A4 A5 A6 B01 filter_on_lattice_bsup11 filters_on_iff is_supD1 lattice_filters_isl1 lattice_filters_isl7)
        then show "z \<in> Sup ?R ?F {f, ?igh}"
          using B37 by presburger 
       qed
      have B39:"Inf ?R ?F {?sfg, ?sfh} \<subseteq> X"
        by (metis A1 A2 A3 A4 A5 A6 B01 filter_on_lattice_bsup11 filter_on_lattice_bsup7 filters_on_iff inf.coboundedI1 is_filterD1 lattice_filters_isl7)
      have B40:"Sup ?R ?F {f, ?igh} \<subseteq> X"
        by (metis A1 A2 A3 A4 A5 A6 B01 filter_on_lattice_bsup11 filter_on_lattice_bsup6 filters_on_iff lattice_filters_isl0 lattice_filters_isl7)  
      show "(Inf ?R ?F {?sfg, ?sfh}, Sup ?R ?F {f, ?igh}) \<in> ?R"
        by (simp add: B40 D0 pwr_memI) 
    qed
    have P:" \<And>x y z. \<lbrakk>x \<in> ?F;  y \<in>?F; z \<in> ?F\<rbrakk> \<Longrightarrow> (Inf ?R ?F {Sup ?R ?F {x, y}, Sup ?R ?F {x, z}}, Sup ?R ?F {x, Inf ?R ?F {y, z}}) \<in> (pwr X)"
      using B1 by blast
    show "distributive_lattice ?R ?F"
    proof(rule distr_latticeI1)
      show "pord ?R ?F"
        by (meson PowI filters_on_iff is_filterD1 powrel6 powrel7 pwr_memI refl_def subsetI)
      show " is_lattice ?R ?F"
        using B02 by blast
      show "\<And>x y z. \<lbrakk>x \<in> ?F; y \<in> ?F; z \<in> ?F\<rbrakk> \<Longrightarrow>  (Inf ?R ?F {Sup ?R ?F {x, y}, Sup ?R ?F {x, z}}, Sup ?R ?F {x, Inf ?R ?F {y, z}}) \<in> (pwr X)"
        using P by blast
    qed
qed

section SpecialElements
subsection Primality

lemma sup_primeD1:
  "\<lbrakk>sup_prime R X A; a \<in> X; b \<in> X; Sup R X {a, b} \<in> A\<rbrakk> \<Longrightarrow> a \<in> A \<or> b \<in> A"
  by (simp add:sup_prime_def)

lemma inf_primeD1:
  "\<lbrakk>inf_prime R X A; a \<in> X; b \<in> X; Inf R X {a, b} \<in> A\<rbrakk> \<Longrightarrow> a \<in> A \<or> b \<in> A"
  by (simp add: Sup_def sup_prime_def)

lemma sup_primeI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; Sup R X {a, b} \<in> A\<rbrakk> \<Longrightarrow> (a \<in> A \<or> b \<in> A)) \<Longrightarrow> sup_prime R X A"
  by (simp add:sup_prime_def)

lemma sup_primeI2:
  "(\<And>a b. \<lbrakk>a \<in> X;b \<in> X; Sup R X {a, b} \<in> A;  a \<notin> A\<rbrakk> \<Longrightarrow> b \<in> A) \<Longrightarrow> sup_prime R X A"
  using sup_prime_def by blast

lemma inf_primeI1:
  "(\<And>a b. \<lbrakk>a \<in> X; b \<in> X; Inf R X {a, b} \<in> A\<rbrakk> \<Longrightarrow> (a \<in> A \<or> b \<in> A)) \<Longrightarrow> inf_prime R X A"
  by (simp add:sup_prime_def Sup_def)

lemma inf_primeI2:
  "(\<And>a b. \<lbrakk>a \<in> X;b \<in> X; Inf R X {a, b} \<in> A;  a \<notin> A\<rbrakk> \<Longrightarrow> b \<in> A) \<Longrightarrow> inf_prime R X A"
  by (meson inf_primeI1)

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
  "\<lbrakk>x \<in> X; elem_sup_prime R X x\<rbrakk> \<Longrightarrow> sup_prime R X (lcro R X x)"
  by (metis elem_sup_prime_def lcroD1 lcroI1 sup_prime_def)       

lemma elem_inf_primeE1:
  "\<lbrakk>x \<in> X; elem_inf_prime R X x\<rbrakk> \<Longrightarrow> inf_prime R X (lorc R X x)"
  by (simp add: elem_sup_primeE1)

lemma elem_sup_primeI2:
  assumes A0:"x\<in>X" and A1:"sup_prime R X (lcro R X x)" and A2:"pord R X" and A3:"is_sup_semilattice R X"
  shows "elem_sup_prime R X x "
  proof(rule elem_sup_primeI1)
    fix a b assume A4:"a \<in> X" and A5:"b \<in> X" and A6:"(x, Sup R X {a, b})\<in>R" 
    show "(x, a) \<in> R \<or> (x, b) \<in> R"
    by (metis A1 A2 A3 A4 A5 A6 is_supD1 lcroD1 lcroI1 ssupD3 sup_primeD1)
qed

lemma elem_inf_primeI2:
  assumes A0:"x\<in>X" and A1:"inf_prime R X (lorc R X x)" and A2:"pord R X" and A3:"is_inf_semilattice R X"
  shows "elem_inf_prime R X x"
  by (simp add: A0 A1 A2 A3 elem_sup_primeI2 is_sup_semilattice_def refl_iff)

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
  assumes A0:"pord R X" and A1:"distributive_lattice R X" and A2:"x\<in>X" and A3:"elem_sup_prime R X x"
  shows "fin_sup_irr R X x"
proof(rule fin_sup_irrI1)
  fix a b assume A4:"a\<in>X" and A5:"b\<in>X"  and A6:"x = Sup R X {a, b}" 
  show "x = a \<or> x = b"
  by (metis A0 A1 A2 A3 A4 A5 A6 antisym_onD bsup_ge1 bsup_ge2 distr_latticeD5 elem_sup_prime_def latt_iff)
qed


lemma fin_inf_irrE1:
  assumes A0:"pord R X" and A1:"distributive_lattice R X" and A2:"x\<in>X" and A3:"elem_inf_prime R X x"
  shows "fin_inf_irr R X x"
proof(rule fin_inf_irrI1)
  fix a b assume A4:"a\<in>X" and A5:"b\<in>X"  and A6:"x = Inf R X {a, b}" 
  show "x = a \<or> x = b"
  by (metis A0 A1 A2 A3 A4 A5 A6 antisym_onD binf_le1 binf_le2 distr_latticeD5 elem_inf_primeD1 latt_iff reflD2)
qed



lemma elem_sup_primeI3:
  assumes A0:"distributive_lattice R X" and A1:"x \<in> X" and A2: "fin_sup_irr R X x" and A3:"pord R X"
  shows "elem_sup_prime R X x"
proof(rule elem_sup_primeI1)
    fix a b assume A4:"a \<in> X" and A5:"b \<in> X" and A6:"(x, Sup R X {a, b})\<in>R" 
    obtain B0:"Sup R X {a, b} \<in> X"
      by (meson A0 A3 A4 A5 distr_latticeD5 is_supD1 lattD32)
    have B1:"x = Inf R X {x, Sup R X {a, b}}"
      by (metis A0 A1 A3 A6 B0 distr_latticeD5 latt_ge_iff1 lattice_absorb2 reflD2)
    have B2:"... = Sup R X {Inf R X {x, a}, Inf R X {x, b}}"
      by (simp add: A0 A1 A3 A4 A5 distr_latticeD3)
    have B3:"x = Inf R X {x, a} \<or> x = Inf R X {x, b}"
      by (metis A0 A1 A2 A3 A4 A5 B1 B2 distr_latticeD5 fin_sup_irr_def is_supD1 lattD31)
    show "(x, a) \<in> R \<or> (x, b) \<in> R"
      by (metis A0 A1 A3 A4 A5 B3 binf_le2 distr_latticeD5 latt_iff)
qed

lemma sup_inf_dual:
  assumes A0:"\<exists>s. is_sup R X A s" and A1:"antisym R X"
  shows sup_inf_dual1:"Sup R X A = Inf (dual R) X A" and
        sup_inf_dual2:"Inf R X A = Sup (dual R) X A"
proof-
  show "Sup R X A = Inf (dual R) X A" 
    by (simp add: Sup_def)
  show "Inf R X A = Sup (dual R) X A"
   by (simp add: Sup_def)
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
  "\<lbrakk>distributive_lattice R X; pord R X; x \<in> X\<rbrakk> \<Longrightarrow> (elem_sup_prime R X x \<longleftrightarrow> fin_sup_irr R X x)"
  by (metis elem_sup_primeI3 fin_sup_irrE1)

lemma inf_prime_iff:
  "\<lbrakk>distributive_lattice R X; pord R X; x \<in> X\<rbrakk> \<Longrightarrow> (elem_inf_prime R X x \<longleftrightarrow> fin_inf_irr R X x)"
  by (metis elem_inf_primeI3 fin_inf_irrE1)

lemma fin_sup_irrI2:
  "\<lbrakk>distributive_lattice R X;pord R X;x \<in> X;  sup_prime R X (lcro R X x)\<rbrakk> \<Longrightarrow> fin_sup_irr R X x"
  by (simp add: distributive_lattice_def elem_sup_primeI2 fin_sup_irrE1 lattD42)
  
lemma fin_inf_irrI2:
  "\<lbrakk>distributive_lattice R X; x \<in> X;  antisym R X; refl R X; trans R X;inf_prime R X (lorc R X x)\<rbrakk> \<Longrightarrow> fin_inf_irr R X x"
  by (simp add: distributive_lattice_dualization fin_sup_irrI2)

lemma sup_primeI4:
  "\<lbrakk>distributive_lattice R X; x \<in> X; pord R X;fin_sup_irr R X x\<rbrakk> \<Longrightarrow> sup_prime R X (lcro R X x)"
  by (simp add: elem_sup_primeE1 elem_sup_primeI3)

  lemma inf_primeI4:
  "\<lbrakk>distributive_lattice R X; x \<in> X;  pord R X;fin_inf_irr R X x\<rbrakk> \<Longrightarrow> inf_prime R X (lorc R X x)"
  by (simp add: elem_inf_primeE1 elem_inf_primeI3)

lemma sup_prime_pfilterD1:
  "\<lbrakk>sup_prime R X A; is_pfilter R X A;  pord R X\<rbrakk> \<Longrightarrow> (\<And>a b. \<lbrakk>a \<in> X; b \<in> X;  (Sup R X {a, b}) \<in> A\<rbrakk> \<Longrightarrow> (a \<in> A \<or> b \<in> A))"
  by (simp add: sup_prime_def)

lemma sup_prime_pfilterD:
  assumes lat:"is_lattice R X" and por:"pord R X" and spp:"sup_prime R X F" and pfil:"is_pfilter R X F"
  shows sup_prime_pfilterD2:"\<And>a b.  \<lbrakk>a \<in> X; b \<in> X; (a \<in> F \<or> b \<in> F)\<rbrakk> \<Longrightarrow> (Sup R X {a, b}) \<in> F" and
        sup_prime_pfilterD3:"\<And>F1 F2. \<lbrakk>is_filter R X  F1; is_filter R X  F2; \<not>(F1 \<subseteq> F); \<not>(F2 \<subseteq> F)\<rbrakk> \<Longrightarrow> \<not>(F1 \<inter> F2 \<subseteq> F)" and
        sup_prime_pfilterD4:"\<And>F1 F2. \<lbrakk>is_filter R X  F1; is_filter R X  F2;  F1 \<inter> F2 \<subseteq> F\<rbrakk> \<Longrightarrow> (F1 \<subseteq> F) \<or> (F2 \<subseteq> F)"
proof-
  show P0:"(\<And>a b.  \<lbrakk>a \<in> X; b \<in> X; (a \<in> F \<or> b \<in> F)\<rbrakk> \<Longrightarrow> (Sup R X {a, b}) \<in> F)"
    by (meson bsup_ge1 bsup_ge2 is_filterD1 is_ord_clE1 is_pfilterD1 lat lattD42 pfil por ssupD4)
  show P1:"(\<And>F1 F2. \<lbrakk>is_filter R X  F1; is_filter R X  F2; \<not>(F1 \<subseteq> F); \<not>(F2 \<subseteq> F)\<rbrakk> \<Longrightarrow> \<not>(F1 \<inter> F2 \<subseteq> F))" 
  proof-
    fix F1 F2 assume fil1:"is_filter R X F1" and fil2:"is_filter R X F2" and nf1:"\<not>(F1\<subseteq>F)" and nf2:"\<not>(F2 \<subseteq> F)"
    show "\<not>(F1 \<inter> F2 \<subseteq> F)"
    proof-
      obtain f1 f2 where A0:"f1 \<in> F1" and A1:"f1 \<notin> F" and A2:"f2 \<in> F2" and A3:"f2 \<notin> F"
        using nf1 nf2 by blast
      obtain B0:"f1 \<in> X" and B1:"f2 \<in> X"
        using A0 A2 fil1 fil2 is_filterD1 by blast
      obtain B2:"Sup R X {f1,f2}\<in> F1" and B3:"Sup R X {f1,f2}\<in>F2"
        by (meson A0 A2 B0 B1 bsup_ge1 bsup_ge2 fil1 fil2 is_filterD1 is_ord_clE1 lat lattD42 por ssupD4)
      then obtain B4:"Sup R X {f1,f2}\<in> F1 \<inter> F2" by blast
      obtain B5:"Sup R X {f1,f2}\<notin> F"
        by (meson A1 A3 B0 B1 spp sup_primeD1)
      then show "\<not>(F1 \<inter> F2 \<subseteq> F)" using B4 by auto
    qed
  qed
  show P2:"\<And>F1 F2. \<lbrakk>is_filter R X  F1; is_filter R X  F2;  F1 \<inter> F2 \<subseteq> F\<rbrakk> \<Longrightarrow> (F1 \<subseteq> F) \<or> (F2 \<subseteq> F)"
    using P1 by blast
qed


lemma lorc_sup_filter_subset:
  assumes lat:"is_lattice R X" and por:"pord R X"  and fil:"is_filter R X F" and
          spp:"(\<And>F1 F2. \<lbrakk> is_filter R X  F1; is_filter R X  F2; F1 \<inter> F2 \<subseteq> F\<rbrakk> \<Longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F)"
  shows "\<And>a b. \<lbrakk>a \<in> X; b \<in> X; (Sup R X {a, b}) \<in> F\<rbrakk>\<Longrightarrow> (a \<in> F \<or> b \<in> F)" 
proof-
    fix a b assume A6:"a \<in> X" and A7:"b \<in> X" and A8:"(Sup R X {a, b}) \<in> F" 
    let ?F1="(lcro R X a)" let ?F2="(lcro R X b)"
    have B1:"?F1 \<inter> ?F2 \<subseteq> F" 
    proof
      fix x assume A9: "x \<in> ?F1 \<inter> ?F2"
      then obtain B10:"(a, x) \<in> R" and B11:"(b, x) \<in> R"
        by (simp add: lcro_eq_upbd ubd_singleton_mem)
      then obtain B11:"(Sup R X {a, b}, x) \<in> R"
        by (metis A6 A7 A9 IntD1 bsup_ge3 lat lattD42 lcroD1 por)  
      then show "x \<in> F"
      by (metis A8 A9 Int_iff fil is_filterD1 is_ord_clE1 lcroD1) 
    qed
    obtain B2:"is_filter R X  ?F1" and B3:"is_filter R X ?F2"
      by (simp add: A6 A7 lcro_filter por)   
    then obtain B4:"?F1 \<subseteq> F \<or> ?F2 \<subseteq> F"
      by (simp add: B1 spp)  
    then show "(a \<in> F \<or> b \<in> F)"
      by (meson A6 A7 lcro_memI1 por subsetD)
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
  assumes A0:"is_lattice R X" and A1:"is_filter R X F" and A2:"a \<in> X" and A3:"pord R X"
  defines "G \<equiv> {x \<in> X. \<exists>y \<in> F. (Inf R X {a, y}, x)\<in>R}"
  shows "is_filter R X G"
proof(rule is_filterI1)
  show P0:"G \<noteq> {}"
  proof-
    obtain f where B70:"f \<in> F"
      using A1 is_filterD1 by fastforce 
    then obtain B71:"f \<in> X"
      using A1 is_filterD1 by blast
    then obtain B71:"(Inf R X {a, f}, a) \<in>R"
      using A0 A2 A3 binf_le1 lattD31 by fastforce
    then have "a \<in> G"
      using A2 B70 G_def by blast
    then show ?thesis by auto
  qed
  show P1:"G \<subseteq> X"
    using G_def by fastforce
  show P2:"is_dir G (dual R)"
  proof(rule is_dirI1)
    fix x1 x2 assume A4:"x1 \<in> G" and A5:"x2 \<in> G"
    obtain B30:"x1 \<in> X" and B31:"x2 \<in> X"
      using A4 A5 P1 by blast 
    obtain y1 y2 where B20:"y1 \<in> F" and B21:"(Inf R X {a, y1}, x1)\<in>R" and
                       B22:"y2 \<in> F" and B23:"(Inf R X {a, y2}, x2)\<in>R"
                       using A4 A5 G_def by blast 
    obtain B32:"y1 \<in> X" and B33:"y2 \<in> X"
      using A1 B20 B22 is_filterD1 by blast    
    have B3:"Inf R X {y1, y2} \<in> F"
      using A0 A1 A3 B20 B22 B33 filter_inf_closed2 lattD21 by fastforce  
    obtain B34:"Inf R X {x1, x2} \<in> X" and B35:"Inf R X {a, y1} \<in> X" and 
           B36:"Inf R X {a, y2} \<in> X" and B36b:"Inf R X {y1,y2} \<in> X"
      by (meson A0 A2 A3 B30 B31 B32 B33 is_supD1 lattD31)  
    have B4:"(Inf R X {Inf R X {a, y1}, Inf R X {a, y2}},Inf R X {x1, x2})\<in>R"
      by (metis A0 A3 B21 B23 B30 B31 B35 B36 inf_iso latt_iff)
    have B5:"Inf R X {Inf R X {a, y1}, Inf R X {a, y2}} = Inf R X {a,y1, a,y2}"
      using semilattice_assoc_inf[of X R a y1 a y2] A0 A2 A3 B32 B33 by (simp add:latt_iff) 
    have B6:"... = Inf R X {y1, y2,a}"
      by (simp add: insert_commute)
    have B7:"... = Inf R X {Inf R X {y1, y2}, a}"
      using binf_assoc[of X R y1 y2 a] A0 A2 A3 B32 B33 by (simp add:latt_iff) 
    have B8:"... = Inf R X {a, Inf R X {y1,y2}} "
      by (simp add: insert_commute)
    then obtain B9:"Inf R X {Inf R X {a, y1}, Inf R X {a, y2}}  = Inf R X {a, Inf R X {y1, y2}}"
      by (simp add: B5 B6 B7) 
    have B10:"(Inf R X {Inf R X {y1, y2}, a},Inf R X {x1, x2})\<in>R"
      using B4 B5 B6 B7 by force
    have B11:"\<exists>y \<in> F. (Inf R X {a, y},Inf R X {x1, x2})\<in>R"
      using B10 B3 B8 by auto
    have B12:"Inf R X {x1, x2} \<in> G"
      using B11 B34 G_def by blast
    then show "\<exists>c\<in>G. (x1, c) \<in> dual R \<and> (x2, c) \<in> dual R"
      by (metis A0 A3 B30 B31 binf_le1 binf_le2 converse_iff latt_iff)
  qed
  show "is_ord_cl X G R"
  proof(rule is_ord_clI1)
     fix x g assume A8:"g \<in> G" and A9:"x \<in> X" and A10:"(g,x)\<in>R"
     obtain y where B60:"y \<in> F" and B61:"(Inf R X {a, y}, g)\<in>R"  
        using A8 G_def by blast 
     obtain B62:"g \<in> X"  and B62:"Inf R X {a, y} \<in> X"
        by (metis A0 A1 A2 A3 A8 B60 P1 dual_lattice Sup_def antisym_on_converse is_filterD1 lattD42 ssupD4 subsetD)
     then have B63:"(Inf R X {a, y}, x) \<in> R"
        by (meson A10 A3 A9 B61 trans_onD)
     then show "x \<in> G"
      using A9 B60 G_def by blast
  qed
qed
lemma primefilterI1:
  "\<lbrakk>is_lattice R X;pord R X; is_pfilter R X A; (\<forall>a b. (a \<in> A \<or> b \<in> A) \<longleftrightarrow> ((Sup R X {a, b}) \<in> A)) \<rbrakk> \<Longrightarrow> sup_prime R X A"
  by (simp add: sup_prime_def)

lemma primefilter_iff1:
  "\<lbrakk>is_lattice R X; pord R X\<rbrakk> \<Longrightarrow>
   ( sup_prime R X A \<and> is_pfilter R X A) \<longleftrightarrow> (is_pfilter R X A \<and>  (\<forall>a \<in> X. \<forall>b \<in> X. (a \<in> A \<or> b \<in> A) \<longleftrightarrow> ((Sup R X {a, b}) \<in> A)))"
  by (metis sup_primeD1 sup_primeI1 sup_prime_pfilterD2)

lemma prime_filter_iff2:
  "\<lbrakk>is_lattice R X; pord R X\<rbrakk> \<Longrightarrow>
    (sup_prime R X F \<and> is_pfilter R X F)  \<longleftrightarrow>  (is_pfilter R X F \<and> (\<forall>F1 F2. is_filter R X  F1 \<and> is_filter R X  F2 \<and> F1 \<inter> F2 \<subseteq> F \<longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F))"
  by (metis sup_prime_pfilterD3 sup_prime_pfilterI2)

lemma prime_filter_fin_irr1:
  "\<lbrakk>is_lattice R X; pord R X; sup_prime R X F; is_pfilter R X F; G \<in> filters_on R X; H \<in> filters_on R X; G \<inter> H = F\<rbrakk> \<Longrightarrow> G=F \<or> H=F"
  by (meson filters_on_iff inf_le1 inf_le2 order_refl subset_antisym sup_prime_pfilterD4)

lemma prime_filter_fin_irr2:
  "\<lbrakk>is_lattice R X; sup_prime R X F; pord R X; is_pfilter R X F; G \<in> filters_on R X; H \<in> filters_on R X; Inf (pwr X) (filters_on R X) {G, H} = F\<rbrakk> \<Longrightarrow> G=F \<or> H=F"
  by (simp add: lattice_filters_isl7 prime_filter_fin_irr1)

lemma prime_filter_irr3:
  "\<lbrakk>is_lattice R X; sup_prime R X F;pord R X; is_pfilter R X F\<rbrakk> \<Longrightarrow> fin_inf_irr (pwr X) (filters_on R X) F"
  by (metis fin_sup_irr_def prime_filter_fin_irr2 Sup_def)

lemma proper_principal_prime:
  "\<lbrakk>is_pfilter R X (lcro R X a); (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; (a, Sup R X {x, y})\<in>R\<rbrakk> \<Longrightarrow> (a, x) \<in> R \<or> (a,y)\<in>R)\<rbrakk> \<Longrightarrow> sup_prime R X (lcro R X a)"
  by (metis lcroD1 lcroI1 sup_prime_def)

lemma proper_principal_prime2:
  "\<lbrakk>is_lattice R X;pord R X;is_pfilter R X (lorc R X a); (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; (a, Sup R X {x, y})\<in>R\<rbrakk> \<Longrightarrow> (a, x) \<in> R \<or> (a,y)\<in>R)\<rbrakk> \<Longrightarrow> (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; a = Sup R X {x, y}\<rbrakk> \<Longrightarrow> a =x \<or> a=y)"
  by (metis antisym_onD bsup_ge1 bsup_ge2 lattD42 ssupD4)

lemma proper_principal_fin_irr:
  "\<lbrakk>is_lattice R X; pord R X;is_pfilter R X (lcro R X a); (\<And>x y. \<lbrakk>x \<in> X; y \<in> X; (a, Sup R X {x, y})\<in>R\<rbrakk> \<Longrightarrow> (a, x) \<in> R \<or> (a,y)\<in>R)\<rbrakk> \<Longrightarrow>fin_inf_irr (pwr X) (filters_on R X) (lcro R X a)"
  by (simp add: prime_filter_irr3 proper_principal_prime)

lemma fin_irr_filter_prime:
  assumes dis:"distributive_lattice R X" and por:"pord R X" and pfil:"is_pfilter R X F" and
          fii:"fin_inf_irr (pwr X) (filters_on R X) F"
  shows "inf_prime R X F"
proof(rule inf_primeI1)
  fix a b assume A0:"a\<in>X" and A1:"b\<in>X" and A2:"Inf R X {a, b} \<in> F"
  obtain lat:"is_lattice R X" using distr_latticeD5 dis by blast
  obtain glb:"is_inf R X {a,b}(Inf R X {a, b})" using A0 A1 por lat lattD31[of X R a b] by auto
  show "a \<in> F \<or> b \<in> F" by (meson A0 A2 converse_iff glb insertCI is_filterD1 is_ord_clE1 is_pfilterD1 is_supD1 pfil)
qed

lemma distr_lattice_maximal_prime:
  assumes dis:"distributive_lattice R X" and por:"pord R X" and ult:"is_maximal (pwr X) (pfilters_on R X) F"
  shows "sup_prime R X F"
proof(rule sup_primeI2)
  fix a b assume A0:"a \<in> X" and A1:"b\<in>X" and A2:"Sup R X {a, b} \<in> F" and  A3:"a \<notin> F"
  then obtain A4:"Sup R X {a,b}\<in>X" and A5:"lcro R X a \<in> filters_on R X" and A6:"F \<in> pfilters_on R X"
    by (meson dis distr_latticeD5 filters_on_iff is_supD1 lattD32 lcro_filter maximalD1 por ult)
  then obtain A7:"is_filter R X F" and A8:"is_filter R X(lcro R X a)"
    by (simp add: filters_on_iff is_pfilterD1 pfilters_on_iff)
  obtain A9:"is_lattice R X"
    by (simp add: dis distr_latticeD5)
  have dpor:"pord (dual R) X"
    by (simp add: por refl_dualI)
  let ?sab="Sup R X {a,b}" let ?Fa="binary_filter_sup R X F (lcro R X a)" let ?upa="lcro R X a"
  obtain A10:"lcro R X a \<subseteq> ?Fa" and A11:"F \<subseteq> ?Fa" and A12:"is_filter R X ?Fa"
      using  por A7 A8 A9 filter_on_lattice_bsup2b[of X R F ?upa] filter_on_lattice_bsup2a[of X R F ?upa] 
            filter_on_lattice_bsup7[of X R F ?upa] by fastforce 
  obtain B1:"a \<in> ?Fa - F"
    by (meson A0 A10 A3 DiffI lcro_memI1 por subsetD)
  then obtain B2:"F \<subset> ?Fa"
    using A11 by blast 
  then obtain B3:"?Fa \<notin> pfilters_on R X"
    by (metis A7 A8 A9 filter_on_lattice_bsup6 maximalD2 por psubset_eq pwr_memI ult) 
  obtain B4:"?Fa \<in> filters_on R X" and B5:"?Fa = X" and  B6:"b \<in> ?Fa"
    by (metis A1 A12 B3 filters_on_iff is_pfilter_def pfilters_on_iff) 
  obtain f c where A13:"f \<in>F" and A14:"c \<in> ?upa" and A15:"(Inf R X {f, c}, b)\<in>R"
    by (meson B6 filter_bsup_memD1)
  then obtain A16:"f\<in>X" and A17:"c\<in>X"
    by (metis B2 B5 lcroD1 psubsetD)
  let ?ifc="Inf R X {f, c}" let ?sbf="Sup R X {b,f}" let ?sbc="Sup R X {b,c}" let ?sba="Sup R X {b, a}" let ?ifa="Inf R X{f,a}"
  obtain A18:"?ifc\<in>X"  and A19:"?sbf\<in>X" and A20:"?sbc\<in>X" and A21:"?sba\<in>X" and A21b:"?ifa\<in>X"
    by (meson A0 A1 A16 A17 A9 is_supD1 lattD31 lattD42 por ssupD4)
  have B8:"b = Sup R X {b, ?ifc}"
    by (metis A1 A15 A18 A9 latt_ge_iff2 por reflD2)
  have B9:"... = Inf R X {?sbf, ?sbc}"
    by (simp add: A1 A16 A17 dis distr_latticeD1)
  let ?i_sbf_sbc="Inf R X {?sbf,?sbc}"
  obtain A22:"?i_sbf_sbc \<in> X"
    using A1 B8 B9 by presburger 
  obtain B10a:"?sbf \<in>F"
    by (meson A1 A13 A16 A19 A7 A9 bsup_ge2 is_filterD1 is_ord_clE1 lattD42 por)
  obtain B10b:"?sbc \<in>?upa"
    by (meson A0 A1 A14 A20 A9 bsup_ge2 lattD42 lcroD1 lcroI1 por trans_onD)
  obtain B10c:"b=?i_sbf_sbc"
    using B8 B9 by presburger
  have B11:"(a, ?sbc) \<in> R"
    by (meson B10b lcroD1)
  let ?s_b_sbf=" Sup R X {b, ?sbf}" let ?s_b_sbc="Sup R X {b, ?sbc}"
  obtain A23:"?s_b_sbf \<in> X" and A24:"?s_b_sbc \<in> X"
    by (meson A1 A19 A20 A9 latt_iff por ssupD4) 
  have B12:"(?sbf, ?s_b_sbf)\<in>R"
    by (simp add: A1 A19 A9 bsup_ge2 lattD42 por)
  have B13:"(?sba,?s_b_sbc) \<in>R"
    by (meson A0 A1 A20 A9 B11 lattD42 por reflD2 sup_iso)
  have B14:"b = Sup R X {b, ?i_sbf_sbc}"
    using A1 B10c por sup_singleton2 by fastforce
  have B15:"... = Inf R X {?s_b_sbf, ?s_b_sbc}"
    by (simp add: A1 A19 A20 dis distr_latticeD1)
  let ?ib="Inf R X {?s_b_sbf, ?s_b_sbc}"
  obtain A25:"b=?ib"
    using B14 B15 by presburger
  let ?i_sbf_sba="Inf R X {?sbf, ?sba}"
  have A26:"?i_sbf_sba \<in>X" using A19 A21 A9 por is_supD1 by (metis lattD31)
  have B16:"?i_sbf_sba=Sup R X {b,?ifa}"
    by (simp add: A0 A1 A16 dis distr_latticeD1)
  have B17:"(Inf R X {?sbf, ?sba}, Inf R X {?s_b_sbf, ?s_b_sbc}) \<in>R"
    by (metis A1 A17 A19 A20 A21 A25 A9 B10c B13 B14 bsup_assoc2 inf_iso latt_iff por refl_def)
  have B18:"Inf R X {?sbf, ?sba} \<in> F"
    by (smt (verit, del_insts) A2 A7 A9 B10a filter_inf_closed2 insert_commute latt_iff por)
  have B19:"(Inf R X {?sbf, ?sba}, b)\<in>R"
    using A25 B17 by presburger
  then show "b \<in> F"
    by (meson A1 A7 B18 is_filterD1 is_ord_clE1)
qed




lemma finite_ind_fil:
  assumes por:"pord R X" and ind1:"finite I" and ind2:"I \<noteq> {}" and top:"is_greatest R X m" and 
          fil:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X (f i))"
  shows finite_ind_fil1:"is_inf_semilattice R X \<Longrightarrow> is_inf (pwr X) (filters_on R X) (f`I) (\<Inter>(f`I))" and
        finite_ind_fil2:"is_lattice R X \<Longrightarrow> is_inf (pwr X) (filters_on R X) (f`I) (\<Inter>(f`I))" 
proof-
  show P0:"is_inf_semilattice R X \<Longrightarrow> is_inf (pwr X) (filters_on R X) (f`I) (\<Inter>(f`I))"
  proof-
    assume isl:"is_inf_semilattice R X"
    obtain "(f`I) \<in> Pow_ne (filters_on R X)"
      by (simp add: fil filters_on_iff image_subsetI ind2)
    then show "is_inf (pwr X) (filters_on R X) (f`I) (\<Inter>(f`I))"
      using isl por top filters_inf_semilattice_inf[of X R m "f`I"] by blast
  qed
  show P1:"is_lattice R X \<Longrightarrow> is_inf (pwr X) (filters_on R X) (f`I) (\<Inter>(f`I))"
  by (simp add: P0 latt_iff)
qed 


lemma finite_ind_fil3:
  fixes f::"'b \<Rightarrow> 'a set" and x::"'b \<Rightarrow> 'a" and I::"'b set"
  assumes A0:"is_lattice R X" and
          A1: "is_greatest R X top" and 
          A2:"finite I" and
          A3:"I \<noteq> {}" and
          A4:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X  (f i))" and
          A5:"(\<And>i. i \<in> I \<Longrightarrow> (x i) \<in> (f i))" and
          A6:"is_sup R X (x` I) s" and 
          A7:"pord R X"
  shows "s \<in> (\<Inter>(f` I))"
proof-
  have B0:"\<And>i. i \<in> I \<Longrightarrow> s \<in> f i"
  proof-
    fix i assume A10:"i \<in> I"
    obtain B0:"(x i) \<in> (f i)" and B1:"(x i) \<in> (x` I)" and B2:"is_filter R X (f i)"
      by (simp add: A10 A4 A5)
    obtain B3:"is_ord_cl X (f i) R"
      by (simp add: B2 is_filterD1)
    obtain B4:"s \<in> X"  by (meson A6 is_supD1) 
    obtain B5:"(x i, s)\<in>R" by (meson A6 B1 is_supD1)
    show "s \<in> f i"
      by (meson B0 B3 B4 B5 is_ord_clE1)  
  qed
  show "s \<in>  (\<Inter>(f` I))"   
    using B0 by blast
qed

lemma finite_ind_fil4:
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
  proof(rule is_supI1)
    show P0:"s \<in> X"
      using A2 A3 A4 A5 is_filterD1 by fastforce
    show "\<And>a. a \<in> x ` I \<Longrightarrow> (a, s) \<in> R"
      using A6 P0 refl_def x_def by fastforce
    show "\<And>b. b \<in> X \<Longrightarrow> (\<And>a. a \<in> x ` I \<Longrightarrow> (a, b) \<in> R) \<Longrightarrow> (s, b) \<in> R"
      using A3 x_def by blast
  qed
  have B1:" (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))"  
    using A5 x_def by blast
  show ?thesis 
     using B0 B1 by auto
qed

lemma finite_ind_fil5:
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
  have B1:"?F \<subseteq> X"
    by (meson A4 A5 image_subset_iff is_filterD1 subsetD)      
  have B2:"is_sup R X ?F ?s"
    by (simp add: A0 A3 A6 A7 A8 B0 B1 l_finsup sup_equality2)  
  then show ?thesis
    by (metis A0 A1 A2 A3 A4 A5 A6 A7 A8 finite_ind_fil3) 
qed

lemma finite_ind_fil6:
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
  by (auto, metis A0 A1 A2 A3 A4 A5 A6 A7 A8 finite_ind_fil4 sup_equality)

lemma finite_ind_fil7:
  fixes f::"'b \<Rightarrow> 'a set" and x::"'b \<Rightarrow> 'a" and I::"'b set"
  assumes A0:"is_lattice R X" and 
          A1:"is_greatest R X top" and 
          A2:"finite I" and 
          A3:"I \<noteq> {}" and
          A4:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X  (f i))" and
          A5:"refl R X" and 
          A6:"antisym R X" and 
          A7:"trans R X"
  shows "\<Inter>(f`I) = {Sup R X (x` I)|x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))}" (is "?LHS=?RHS")
proof
  show "?LHS \<subseteq> ?RHS"
  proof
    fix a assume "a \<in> ?LHS"
    then show "a \<in> ?RHS" 
    using finite_ind_fil4[of R X top I f a] A0 A1 A2 A3 A4 A5 A6 A7 sup_equality by fastforce 
  qed
  next
  show "?RHS \<subseteq> ?LHS"
  proof
    fix a assume "a \<in> ?RHS"
    then obtain x where "\<And>i. i \<in> I \<Longrightarrow> (x i) \<in> (f i)" and "a=Sup R X (x` I)" by blast
    then show "a \<in> ?LHS" using finite_ind_fil5[of R X top I f x] 
      using A0 A1 A2 A3 A4 A5 A6 A7 sup_equality by fastforce
  qed
qed

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
proof-
  let ?F1="\<Inter>(f`I)" let ?F2=" {Sup R X (x` I)|x. (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i))}"
  have B0:"?F1 = ?F2" using finite_ind_fil7[of R X top I] assms by presburger
  have B1:"is_inf (pwr X) (filters_on R X) (f`I) ?F1" by (metis A0 A1 A2 A3 A4 A5 A6 A7 finite_ind_fil2)
  then obtain B2:"is_inf (pwr X)  (filters_on R X) (f`I) ?F2"
    by (simp add: B0)
  have B3:"is_clattice (pwr X) (filters_on R X)"
    by (meson A0 A1 A5 A6 A7 lattice_filters_complete)
  have B4:"(f`I) \<subseteq>(filters_on R X) "
    by (simp add: A4 filters_on_iff image_subsetI)
  have B5:"antisym (pwr X) (filters_on R X)"
    by (simp add: antisym_on_def powrel8 set_eq_subset)
  have B6:"Inf (pwr X) (filters_on R X) (f`I) = ?F1" 
    using B1 B5 inf_equality[of "pwr X" "filters_on R X" " (f`I)" ?F1] by fastforce
  also have B7:"... = ?F2" using B0 by blast
  finally show ?thesis by blast
qed

lemma finite_ind_fil8:
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
  have B0:"?A \<noteq> {}"   
    using A2 A3 is_filterD1 by fastforce
  have B1:"is_inf_semilattice R X"
    using A0 latt_iff by auto
  have B2:"f`I \<in> Pow_ne (filters_on R X)"
    by (simp add: A2 A3 filters_on_iff image_subsetI)
  have B3:"Sup (pwr X) (filters_on R X) (f`I) = filter_closure R X (?A)"
    using A4 A5 A6 B1 B2 semilat_filters_isl2 by auto
  also have B4:"... = {x \<in> X. \<exists>F \<subseteq> ?A. finite F \<and> F \<noteq> {} \<and> (Inf R X F, x)\<in>R} " 
      unfolding filter_closure using B0 by (simp add: filter_closure_def)
  also have B3:"... = {x \<in> X. \<exists>F \<in> Fpow_ne ?A.  (Inf R X F, x)\<in>R}"  
      by blast
  finally show ?thesis
   by blast 
qed

lemma inf_comp:
  assumes por:"pord R X" and sub1:"A1 \<subseteq> X" and sub2:"A2 \<subseteq> X" and gbl1:"is_inf R X A1 i1" and
          glc2:"is_inf R X A2 i2" and sbd:"\<And>a2. a2 \<in> A2 \<Longrightarrow> (\<exists>a1 \<in> A1. (a1,a2)\<in>R)"
  shows "(i1,i2)\<in>R"
proof-
  have B0:"\<And>a2. a2 \<in> A2 \<Longrightarrow> (i1,a2)\<in>R"
    by (meson converse_iff gbl1 is_supD1 por sbd sub1 sub2 subsetD trans_onD)
  then show ?thesis
  by (meson converseD converseI gbl1 glc2 is_supD1)
qed

lemma finite_ind_fil9:
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
  have B2:"\<And>i. i \<in> I \<Longrightarrow> (x i) \<in> (f i)"
  proof-
    fix i assume A6:"i \<in> I"
    show "x i \<in> f i"
    proof(cases " G``{i} \<noteq> {}")
      case True
      have B3:"x i =  Inf R X (G``{i})"  by (simp add: True x_def)
      have B4:"G``{i} \<subseteq> (f i)"   using A6 P by blast
      have B5:"finite (G``{i})" by (meson A5 A6 B0 Fpow_ne_iff True finite_subset)  
      have B6:" Inf R X (G``{i}) \<in> (f i)"
        by (metis A0 A10 A4 A6 A9 B4 B5 True filter_inf_closed3 latt_iff)  
      then show ?thesis  
        by (simp add: B3)
    next
      case False
      then show ?thesis  by (metis A6 assms(5) ex_in_conv is_filterD1 someI2_ex x_def)
    qed
  qed
  have B7:"\<And>z. z \<in> F \<Longrightarrow> (\<exists>w \<in> (x` I). (w, z)\<in>R)"
  proof-
    fix z assume A7:"z \<in> F"
    obtain i where B8:"i \<in> I \<and> z \<in> (f i)"
      using A5 A7 by blast  
    have B9:"G``{i} \<noteq> {}" using A7 B8 by(auto simp add:G_def)
    have B10:"x i =  Inf R X (G``{i})" by (simp add: B9 x_def)
    have B11:"z \<in> G``{i}" by (simp add: A7 B8 G_def)
    have B12:"finite (G``{i}) \<and> (G``{i}) \<subseteq> X"
      by (meson A4 A5 B0 B8 B9 Fpow_ne_iff P finite_subset is_filterD1 subsetD subsetI)  
    have B13:"(Inf R X (G``{i}), z)\<in>R"
      by (metis A0 A10 A8 A9 B11 B12 B9 converse_iff inf_equality is_supD3 l_fininf)
    show " (\<exists>w \<in> (x` I). (w, z)\<in>R)"
      by (metis B10 B13 B8 imageI)
  qed
  have B14:"finite (x` I) \<and> (x` I) \<subseteq> X"
    using B2 assms(3) assms(5) is_filterD1 by fastforce 
  have B15:"\<And>i. i \<in> I \<Longrightarrow> (f i) \<subseteq> X"
    using A4 is_filterD1 by blast  
  have B16:"\<Union>(f`I) \<subseteq> X"   by (simp add: B15 UN_least)
  have B17:"finite F \<and> F \<subseteq> X \<and> F \<noteq> {}"
    using A5 B16 by blast 
  have B18:"(Inf R X (x` I), Inf R X F)\<in>R"
    apply(rule_tac ?X="X" and ?A1.0="x` I" and ?A2.0="F" in inf_comp)
    apply (simp add: A8)
    apply (simp add: A9)
    apply (simp add: A10)
    apply (simp add: B14)
    apply (simp add: B17)
    apply (metis A0 A10 A3 A8 A9 B14 antisym_on_converse image_is_empty is_sup_unique l_fininf the_equality)
    apply (metis A0 A10 A8 A9 B17 inf_equality2 l_fininf)
    using B7 by blast
  have B19:"Inf R X (x` I) \<in> X"
    by (metis A0 A10 A3 A8 A9 B14 image_is_empty inf_equality is_supD1 l_fininf)
  have B20:" Inf R X F \<in> X"
    by (meson A0 A10 A8 A9 B17 inf_equality2 is_supD1 l_fininf)
  have B21:"(Inf R X (x` I), y)\<in>R"
    by (meson A10 A6 A7 B18 B19 B20 trans_onD)
  show ?thesis
    using B2 B21 by blast
qed


lemma finite_ind_fil10:
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
  obtain F where B0:"F \<in> Fpow_ne (\<Union>(f`I)) \<and> (Inf R X F, z)\<in>R" 
    using A0 A1 A2 A4 A5 A6 A7 A8 finite_ind_fil8[of R X top I] by fastforce
  have B1:"(f`I) \<noteq> {}" 
    by (simp add: A2) 
  have B2:"z \<in> X"
    by (metis A0 A3 A4 A5 A6 A7 A8 B1 Fpow_ne_iff filter_bsup_memD1 filter_on_lattice_bsup1b filters_on_iff finite_imageI image_subsetI lattice_filters_isl8) 
  have B3:"F \<in> Fpow_ne (\<Union>(f`I)) \<and> (Inf R X F, z)\<in>R  \<and> z \<in> X"
    using B0 B2 by auto   
  obtain x where B4:"(\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> (Inf R X (x` I), z)\<in>R"
    using finite_ind_fil9[of R X top I f]  by (metis A0 A1 A2 A3 A4 A5 A6 A7 B0 B2)
  show "z \<in> ?R" using B3 B4 by auto
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
  shows "{y \<in> X. \<exists>(x::'b \<Rightarrow> 'a). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> (Inf R X (x` I), y)\<in>R} \<subseteq> Sup(pwr X) (filters_on R X) (f`I) " (is "?L \<subseteq> ?R")
proof
  fix z assume A2:"z \<in> ?L"
  obtain x where B0:"(\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> (Inf R X (x` I) ,z)\<in>R" using A2 by auto
  have B1:"(x` I) \<in> Fpow_ne (\<Union>(f`I))"  by(auto simp add:Fpow_ne_def Fpow_def B0 assms)
  show "z \<in> ?R" using assms B0 B1 A2 finite_ind_fil8[of R X top I] by auto
qed

lemma finite_ind_fil12:
  fixes f::"'b \<Rightarrow> 'a set" and I::"'b set"
  assumes A0:"is_lattice R X"and 
          A1:"is_greatest R X top" and 
          A2:"I \<noteq> {}" and 
          A3:"finite I" and
          A4:"(\<And>i. i \<in> I \<Longrightarrow> is_filter R X  (f i))" and
          A5:"refl R X" and 
          A6:"antisym R X" and 
          A7:"trans R X"
    shows "Sup (pwr X) (filters_on R X) (f`I) = {y \<in> X. \<exists>(x::'b \<Rightarrow> 'a). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> (Inf R X (x` I), y)\<in>R}" (is "?L = ?R")
proof(rule order.antisym)
  show "?L \<subseteq> ?R" 
    using finite_ind_fil10[of R X top I f]  A0 A1 A2 A3 A4 A5 A6 A7 by fastforce
  show "?R \<subseteq> ?L"
    using finite_ind_fil11[of R X top I f]  A0 A1 A2 A3 A4 A5 A6 A7 by fastforce
qed

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
  using finite_ind_fil12[of R X top I f] assms by(auto)

lemma finite_ind_fil13:
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
  have B00:"finite (x` I)"   
    by (simp add: A3) 
  have B01:"x` I \<subseteq> X"  
    using A4 A6 is_filterD1 by fastforce 
  have B02:"x` I \<noteq> {}"  
    by (simp add: A2) 
  have B03:"finite (x1 ` I)"   
    by (simp add: A3) 
  have B04:"(x1 ` I) \<subseteq> X"
    by (metis A0 A5 A9 B01 distr_latticeD5 image_subset_iff lattD4 ssupD4 x1_def)  
  have B05:"(x1 ` I) \<noteq> {}"  
    using A2 by force
  have B06:"is_lattice R X" 
    by (simp add: A0 distr_latticeD5)
  have B07:"Inf R X (x` I) \<in> X"  
    by (metis A0 A10 A8 A9 B00 B01 B02 Sup_def antisym_on_converse distr_latticeD5 is_supD1 l_fininf sup_equality)
  have B0:"y = Sup R X {y, Inf R X (x` I)}"
    by (metis A0 A10 A5 A7 A8 A9 B07 distr_latticeD5 latt_ge_iff2 reflD2)   
  have B1:"... = Inf R X {Sup R X {y,a}|a.  a \<in> (x` I)}" 
    using fin_distr1[of R X "x`I" "y"] A0 A10 A5 A8 A9 B00 B01 B02 by fastforce
  have B2:"... = Inf R X {Sup R X {y, x i}|i. i \<in> I}"
    by (smt (verit, best) Collect_cong imageE image_eqI) 
  have B3:"... = Inf R X {x1 i|i. i \<in> I}"  
    using x1_def by auto
  have B4:"... = Inf R X (x1 ` I)"  
    by (simp add: Setcompr_eq_image)
  have B5:"Inf R X (x1 ` I) = y"  
    using B0 B1 B2 B3 B4 by presburger
  have B6:"\<And>i. i \<in> I \<Longrightarrow>  (x1 i) \<in> (f i)"
    by (smt (verit, ccfv_threshold) A10 A4 A5 A6 A9 B06 bsup_ge1 insert_commute is_filterD1 is_ord_clE1 lattD4 ssupD4 subsetD x1_def)  
  show ?thesis  using B5 B6 by blast
qed

lemma finite_ind_fil14:
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
  fix y assume A8:"y \<in> ?L"
  have B0:"is_lattice R X" 
    by (simp add: A0 distr_latticeD5)
  have B1:"is_clattice (pwr X) (filters_on R X)"
    using A1 A5 A6 A7 B0 lattice_filters_complete by fastforce
  have B2:"(f`I) \<subseteq> (filters_on R X)"
    using A4 filters_on_iff by blast
  have B3:"?L \<subseteq> X"
    by (metis A2 A3 A5 A6 A7 B0 B2 Fpow_ne_iff empty_is_image filters_on_iff filters_on_lattice_inf_semilattice1(9) finite_imageI is_filterD1)
  have B4:"y \<in> X"
    using A8 B3 by blast 
  obtain x where B5:"(\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and>( Inf R X (x` I), y)\<in>R"
   using finite_ind_fil11b  by (metis A1 A2 A3 A4 A5 A6 A7 A8 B0) 
  obtain x1 where B6:"(\<forall>i. i \<in> I \<longrightarrow> (x1 i) \<in> (f i)) \<and> Inf R X (x1` I) =y" 
    using finite_ind_fil13[of R X top I f y x]  A0 A1 A2 A3 A4 A5 A6 A7 B4 B5 by presburger 
  show "y \<in> ?R"
    using B4 B6 by blast
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
  shows "{y \<in> X. \<exists>(x::'b \<Rightarrow> 'a). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> Inf R X (x` I) = y} \<subseteq> Sup (pwr X) (filters_on R X) (f`I) " (is "?L \<subseteq> ?R")
proof
  fix y assume A8:"y \<in> ?L"
  have B0:"is_lattice R X" 
    by (simp add: A0 distr_latticeD5)
  have B1:"y \<in> X"  
    using A8 by blast
  obtain x1 where B3:"(\<forall>i. i \<in> I \<longrightarrow> (x1 i) \<in> (f i)) \<and> Inf R X (x1` I) =y" 
    using A8 by blast
  have B4:"(\<forall>i. i \<in> I \<longrightarrow> (x1 i) \<in> (f i)) \<and> (Inf R X (x1` I), y)\<in>R"  
    using A5 B1 B3 reflE1 by auto  
  have B5:"y \<in> {y \<in> X. \<exists>(x::'b \<Rightarrow> 'a). (\<forall>i. i \<in> I \<longrightarrow> (x i) \<in> (f i)) \<and> (Inf R X (x` I), y)\<in>R}"   
     using B1 B4 by blast 
  show "y \<in> ?R"  using finite_ind_fil11[of R X top I f]  A1 A2 A3 A4 A5 A6 A7 B0 B5 by blast
qed

lemma finite_ind_fil16:
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
  using finite_ind_fil14[of R X top I f] finite_ind_fil15[of R X top I f] A0 A1 A2 A3 A4 A5 A6 A7 by fastforce 


lemma maximalI2:
  "\<lbrakk>antisym R X; A \<subseteq> X;x \<in> A; \<not>(\<exists>a \<in> A. (x, a)\<in>R \<and> x \<noteq> a)\<rbrakk> \<Longrightarrow> is_maximal R A x"
  by (metis maximalI1)

lemma maximalI3:
  "\<lbrakk>antisym R X;A \<subseteq> X;is_greatest R A x\<rbrakk> \<Longrightarrow> is_maximal R A x"
  by (meson antisym_onD antisym_on_subset greatestD is_maximal_def)

lemma mredI1:
  "\<lbrakk>A \<in> Pow_ne X; x \<notin> A; is_inf R X A x\<rbrakk> \<Longrightarrow> meet_reducible R X x"
  by (meson meet_reducible_def)

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
  obtain A where B0:"A \<in> Pow_ne X" and B1:"x \<notin> A" and B2:"is_inf R X A x" 
     by (meson A1 mredD1) 
  have B3:"A \<subseteq> X"
    using B0 by blast  
  obtain a where B4:"a \<in> A"  
    using B0 by fastforce  
  have B3:"(x, a) \<in> R \<and> x \<noteq> a"
    using B1 B2 B4 is_supD1 by fastforce  
  show "\<not>(is_greatest R X x)" 
  proof(rule ccontr)
   assume A1:"\<not>(\<not>(is_greatest R X x))" then obtain B30:"is_greatest R X x" by simp
  then have B31:"(a, x) \<in> R"
    by (meson B0 B4 Pow_ne_iff greatestD subsetD)
  have B32:"a \<in> X"
    using B0 B4 by blast
  have B33:"(x, a) \<in>R"
    by (simp add: B3)
  then have B34:"a = x"
    by (meson A0 B30 B32 antisym_onD greatestD)
  then show False
    using B3 by auto
  qed
qed


lemma mredD3:
  "\<lbrakk>m \<in> X; antisym R X; refl R X; trans R X; is_clattice R X;  \<not>(is_greatest R X m)\<rbrakk> \<Longrightarrow> {x \<in> X. (m, x)\<in>R \<and> m \<noteq> x} \<noteq> {}"
  using clatD41 is_supD1 sup_maxI1 by fastforce

lemma mredD4:
  assumes A0:"is_clattice R X" and A1:"m \<in> X" and A2:"\<not>(is_greatest R X m)" and A3:"\<not>((m, Inf R X {x \<in> X. (m, x)\<in>R \<and> m \<noteq> x}) \<in> R \<and> m \<noteq> Inf R X {x \<in> X. (m, x)\<in>R \<and> m \<noteq> x})" and
          A4:"antisym R X" and A5:"trans R X" and A6:"refl R X"
  shows "meet_reducible R X m"
proof-
  let ?A="{x \<in> X. (m, x)\<in>R \<and> m \<noteq> x}"
  obtain B0:"?A \<subseteq> X" and B1:"?A \<noteq> {}" 
    by (metis (no_types, lifting) A0 A1 A2 A4 A5 A6 Collect_empty_eq mem_Collect_eq mredD3 subsetI) 
  have B2:"(m, Inf R X ?A)\<in>R"
    by (metis (no_types, lifting) A0 A1 A4 A5 B0 B1 cinfD61 clatD2 converseI mem_Collect_eq ubdI) 
  have B3:"m = Inf R X ?A"   
     using A3 B2 by blast  
  have B4:"?A \<in> Pow_ne X"
    using B1 by blast  
  have B5:"m \<notin> ?A"  by simp
  have B6:"is_inf R X ?A m"   
    by (metis (no_types, lifting) A0 A4 A5 B0 B1 B3 cinfD4 clatD2) 
  show "meet_reducible R X m"
    by (meson B4 B5 B6 mredI1)  
qed

lemma filter_compl1:
  "\<lbrakk>antisym R X; trans R X; refl R X; is_lattice R X; is_pfilter R X F\<rbrakk> \<Longrightarrow> (X -  F) \<noteq> {}"
  using is_filterD1 is_pfilter_def by fastforce

lemma filter_compl2: 
  "\<lbrakk>antisym R X; trans R X; refl R X;is_lattice R X; is_pfilter R X F\<rbrakk> \<Longrightarrow> (X - F \<noteq> X)"
  by (metis Diff_Diff_Int Diff_cancel PosetsRel2.is_filter_def inf_absorb2 is_pfilterD1)
lemma pfilter_compl3: 
  "\<lbrakk>antisym R X; trans R X; refl R X;is_lattice R X; is_pfilter R X F; x \<in> (X-F); y \<in> X; (y, x)\<in>R\<rbrakk> \<Longrightarrow>y \<in> (X-F)"
  by (metis Diff_iff is_filterD1 is_ord_clE1 is_pfilterD1)

lemma pfilter_compl4:
   "\<lbrakk>antisym R X; trans R X; refl R X;is_lattice R X; is_pfilter R X F\<rbrakk> \<Longrightarrow> is_ord_cl X (X-F) (dual R)"
   by (meson converseD is_ord_cl_def pfilter_compl3)

lemma prime_filter_compl5:
   "\<lbrakk>antisym R X; trans R X; refl R X; is_lattice R X; is_pfilter R X F; sup_prime R X F; x \<in> (X-F); y \<in> (X-F)\<rbrakk> \<Longrightarrow> Sup R X {x, y} \<in> (X-F)"
   by (metis Diff_iff  l_sup_closed primefilterD1)

lemma prime_filter_compl6:
   "\<lbrakk>antisym R X; trans R X; refl R X;is_lattice R X; is_pfilter R X F; sup_prime R X F\<rbrakk> \<Longrightarrow> is_dir (X-F) R"
   by (smt (verit) DiffD1 DiffD2 DiffI Diff_eq_empty_iff bsup_ge1 bsup_ge2 diff_shunt_var is_dirI1 is_pfilterD1 lattD42 ssupD4 sup_prime_def)


lemma prime_filter_compl7: 
  "\<lbrakk>antisym R X; trans R X; refl R X;is_lattice R X; is_pfilter R X F; sup_prime R X F; x \<in> X; y \<in> X; Inf R X {x, y} \<in> (X-F)\<rbrakk> \<Longrightarrow> (x \<in> (X-F)) \<or> (y \<in> (X-F))"
  by (metis DiffD2 DiffI filter_inf_closed1 is_pfilterD1 lattD31)  

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
  have B0:"F=a \<inter> b"
    by (simp add: A0 A1 A2 A3 A6 A7 A8 lattice_filters_isl7) 
  have B1:"a \<subseteq> F \<or> b \<subseteq> F" 
    using B0 A0 A1 A2 A3 A4 B0 A5 A6 A7 sup_prime_pfilterD4[of R X F a b] filters_on_iff by auto
  have B2:"\<not>(a \<subseteq> F) \<longrightarrow> b = F" 
    using B0 B1 by blast
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
  have B0:"?K \<subseteq> X" 
     by (simp add: compact_elements_sub)
  have B1:"?Kd \<subseteq> X" 
    using B0 by blast
  have B2:"Kx \<subseteq> ?Kd" 
      using A6 A7 is_supD1 by fastforce
  have B3:"(Sup R X ?Kd, Sup R X Kx)\<in>R"
    by (metis (no_types, lifting) A0 A3 A4 A7 B1 CollectD clatD21 is_supD1 sup_equality) 
  have B4:" Sup R X Kx = x"   
    by (simp add: A3 A7 sup_equality) 
  have B6:"(x, Sup R X ?Kd)\<in>R"  
     using A0 A3 A4 B1 B2 B4 sup_iso1 by blast 
  show ?thesis 
    using B3 B4 B6 by (metis (no_types, lifting) A0 A2 A3 A4 B1 B2 antisym_onD bot.extremum_uniqueI clatD31)
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
  by (meson A1 A2 A3 A4 PowD compactly_generatedD1 is_supD1 subset_iff)

lemma meet_reduction1:
  assumes A0:"is_clattice R X" and
          A1:"antisym R X" and
          A2:"trans R X" and
          A3:"refl R X" and
          A4:"m \<in> X" and
          A5:"meet_reducible R X m"
  shows " m \<in> lbd R X {x \<in> X. (m, x)\<in>R \<and> m \<noteq> x}"
  using A4 ubdI by fastforce


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
    fix x assume A6:"x \<in> A"  show "(m, x)\<in>R \<and> m \<noteq> x"  
      using A6 B1 B2 is_supD1  by fastforce
  qed
  obtain B2:"A \<subseteq> ?A"
  using B0 Ball_Collect \<open>\<And>thesis::bool. ((\<And>x::'a::type. x \<in> (A::'a::type set) \<Longrightarrow> (m::'a::type, x) \<in> (R::('a::type \<times> 'a::type) set) \<and> m \<noteq> x) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by auto 
  have B3:"?A \<subseteq> X"  by simp
  have B4:"?A \<noteq> {}"
    using B0 B2 by force  
  have B5:"(m, Inf R X ?A)\<in>R"
    by (metis (no_types, lifting) A0 A1 A2 A4 B3 B4 cinfD61 clatD2 converseI mem_Collect_eq ubdI)   
  have B6:"(Inf R X ?A,Inf R X A)\<in>R"  
     by (simp add: A0 A1 A2 B2 inf_anti1) 
  have B7:"(Inf R X ?A, m)\<in>R"
    by (smt (verit, del_insts) A0 A1 A2 B3 B4 Pow_ne_iff \<open>\<And>thesis::bool. (\<And>A::'a::type set. \<lbrakk>A \<in> Pow_ne (X::'a::type set); (m::'a::type) \<notin> A; is_inf (R::('a::type \<times> 'a::type) set) X A m\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> cinfD4 clatD2 converse_iff is_supD1 mem_Collect_eq subsetD)
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
    fix x assume A6:"x \<in> A"  show "(m, x)\<in>R \<and> m \<noteq> x"  
    using A6 B1 B2 is_supD1 by fastforce
  qed
  obtain B2:"A \<subseteq> ?A"
    using B0 Ball_Collect \<open>\<And>thesis::bool. ((\<And>x::'a::type. x \<in> (A::'a::type set) \<Longrightarrow> (m::'a::type, x) \<in> (R::('a::type \<times> 'a::type) set) \<and> m \<noteq> x) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by auto  
  have B3:"?A \<subseteq> X" 
     by simp
  have B4:"?A \<noteq> {}"
    using B0 B2 by force
  have B5:"(m, Inf R X ?A)\<in>R"
    by (metis (no_types, lifting) A0 A1 A2 A4 B3 B4 cinfD61 clatD2 converseI mem_Collect_eq ubdI) 
  have B6:"(Inf R X ?A,Inf R X A)\<in>R"   
    by (simp add: A0 A1 A2 B2 inf_anti1) 
  have B7:"(Inf R X ?A, m)\<in>R"
    by (smt (verit) A0 A1 A2 Pow_ne_iff \<open>\<And>thesis::bool. (\<And>A::'a::type set. \<lbrakk>A \<in> Pow_ne (X::'a::type set); (m::'a::type) \<notin> A; is_inf (R::('a::type \<times> 'a::type) set) X A m\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> converseD inf_anti1 inf_equality is_supD1 mem_Collect_eq subsetD subsetI)
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
  obtain j where B1:"is_sup R X D j" 
    by (meson A0 A12 A13 A9 B0 clatD21 dual_order.trans)
  have B2:"j \<in> X"
    by (meson B1 is_supD1) 
  have B3:"\<forall>d. d \<in> D \<longrightarrow> (a,d)\<in>R"   
    using A9 by blast
  have B4:"a \<in> lbd R X D"  
    by (simp add: A2 B3 ubdI)
  have B5:"(a, j)\<in>R"
    by (meson A11 A13 A2 A9 B0 B1 B3 bot.extremum_uniqueI is_supD1 subset_eq trans_onD) 
  have B6:"\<not> ((k,j)\<in>R)"
  proof(rule ccontr)
    assume P0:"\<not>(\<not> ((k,j)\<in>R))" 
    obtain P1:"(k,j)\<in>R"  
      using P0 by auto
    have B7:"(k,Sup R X D)\<in>R"   
        using B1 P1 sup_equality A12 by fastforce
    have B8:"D \<in> Pow_ne X"
      using A11 A9 by blast 
    have B9:"is_sup_semilattice R X"   
       by (simp add: A0 clatD1 csup_fsup)
    obtain d where B10:"d \<in> D \<and> (k,d)\<in>R"
      by (meson A10 A12 A13 A14 A5 B7 B8 B9 compactD3)
    show False   
      using A9 B10 by blast
  qed
  have B11:"j \<in> ?Q"   
    by (simp add: B2 B5 B6)
  show "Sup R X D \<in> ?Q" 
    using B1 B11 sup_equality using A12 by fastforce
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
        then show ?thesis  
          using A2 A7 A10 reflE1 by force
      next
        case False
        have B3:"C \<noteq> {}"   by (simp add: False)
        have B4:"\<And>x y. x \<in> C \<and> y \<in> C \<longrightarrow> (\<exists>z \<in> C. (x,z)\<in>R \<and> (y, z)\<in>R)"
        proof
          fix x y assume A10:"x \<in> C \<and>  y \<in> C"
          have B1:"(x, y) \<in> relation_of ((\<lambda>x y. (x, y) \<in> R)) ?Q \<or> (y, x) \<in> relation_of ((\<lambda>x y. (x, y) \<in> R)) ?Q" 
            using Chains_def[of " relation_of ((\<lambda>x y. (x, y) \<in> R)) ?Q"] A8 A10 by auto
          have B2:"(x, y)\<in>R \<or> (y, x)\<in>R" 
              using B1 relation_of_def[of "((\<lambda>x y. (x, y) \<in> R))" "?Q"] by blast
          show "(\<exists>z \<in> C. (x,z)\<in>R \<and> (y, z)\<in>R)"  
            using A10 B2 by (meson B0 assms(11) reflE1 subset_iff) 
        qed
        have B5:"is_dir C R" 
          by (simp add: B4 is_dirI1)
        have B6:"C \<subseteq> ?Q"   
           using A8 Chains_relation_of by blast
        have B7:"Sup R X C \<in> ?Q"
           using A0 A1 A2 A3 A4 A5 A6 A7 B3 B5 B6  mirred_temp1[of R X a b k C]  A10 A9 assms(9) by fastforce 
        have B8:"\<forall>c  \<in> C. (c, Sup R X C)\<in>R"
          by (meson A0 A9 B0 False assms(9) clatD41 is_supD1)  
        then show ?thesis   
           using B7 by blast 
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
  obtain P1:"meet_reducible R X m"  
    using P by auto
  have B0:"\<And>x. x \<in> X \<and> (m, x)\<in>R \<and> (m \<noteq> x) \<longrightarrow> (k,x)\<in>R"
  proof
    fix x assume A9: "x \<in> X \<and> (m, x)\<in>R \<and> (m \<noteq> x)"
    have B01:"x \<notin> ?Q" 
      using A8 A9 nless_le by blast 
    have B02:"(a, x) \<in> R"  
       using A8 A9  by (metis (mono_tags, lifting) A10 A2 mem_Collect_eq trans_onD) 
    show "(k,x)\<in>R" 
       using A9 B01 B02 by blast
  qed
  have B1:"m=Inf R X {x \<in> X. (m,x)\<in>R \<and> (m \<noteq> x)}"  
      using A0 A8 P meet_reduction2  A10 A11 A9 by fastforce 
  have B2:"k \<in> lbd R X {x \<in> X.(m,x)\<in>R \<and> (m \<noteq> x)}"   
      by (metis (mono_tags, lifting) A5 B0 compactD2 converseI mem_Collect_eq ubdI) 
  obtain B20:"m \<in> X"   
     using A8 by blast 
  obtain B21:"is_inf R X  {x \<in> X. (m,x)\<in>R \<and> (m \<noteq> x)} m" 
       by (simp add: A0 A10 A11 A9 B20 P1 meet_reduction3)
  have B3:"(k, m)\<in>R"
    by (meson B2 B21 converseD is_supD2)  
  show False 
     using A8 B3 by blast
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
  obtain k where B0:"k \<in> compact_elements R X" and  B1:"(k, b)\<in>R" and B2: "\<not> ((k,a)\<in>R)" 
     using A0 A1 A2 A3 A4 compactly_generated_meets by (metis A5 A6 A7)
  have B0b:"is_compact R X k" 
    using B0 compact_elements_mem_iff1   by fastforce
  obtain m where B3:"m \<in> {q \<in> X. (a,q)\<in>R \<and> \<not> ((k,q)\<in>R)} \<and> (\<forall>q \<in> {q \<in> X. (a,q)\<in>R \<and> \<not> ((k,q)\<in>R)}.  (m,q)\<in>R \<longrightarrow> q = m)" 
    using A0 A1 A2 A3 A4 B0b B1 B2 mirred_temp2b[of R X a b k]  A5 A6 A7 by blast
  have B4:"\<not>(meet_reducible R X m)" 
    using mirred_temp2c[of R X a b  k m] A0 A1 A2 A3 A4 B0b B1 B2 B3 A5 A6 A7 by blast
  show ?thesis  using B1 B3 B4  
     by (metis (mono_tags, lifting) A3 A6 B0b compactD2 mem_Collect_eq that trans_onD) 
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
  obtain top where top:"is_greatest R X top"
     using A0 clatD1 csupD3 by blast
  obtain B0:"?M \<subseteq> X" and B1:"top \<in> ?M" and B2:"?M \<noteq> {}" 
    by (metis (no_types, lifting) A2 A3 empty_iff greatestD  mem_Collect_eq mredD2 subsetI top) 
  obtain b where idef:"is_inf R X ?M b"  
    using A0 B0 clatD22  A3 A4 by blast 
  have B4:"(a, b)\<in>R"
    using A2 idef is_supD1 by force 
  have B5: "\<not>((a,b)\<in>R \<and> a \<noteq> b)"
  proof(rule ccontr)
    assume B5dneg:"\<not> \<not> ((a,b)\<in>R \<and> a \<noteq> b)" obtain B5neg:"(a,b)\<in>R \<and> a \<noteq> b"  
      using B5dneg by auto
    obtain m where B50:"m \<in> X" and B51:"meet_irr R X m" and  B52:"(a, m)\<in>R" and B53:"\<not> ((b, m)\<in>R)"   
      by (meson A0 A1 A2 A3 A4 A5 B5neg antisym_onD idef is_supD1 mirred_temp2d) 
    have B54:"m \<in> ?M"   
      by (simp add: B50 B51 B52)
    have B55:"(b, m)\<in>R"   
      using B54 idef is_supD1 by fastforce 
    show False
      using B53 B55 by auto
  qed
  have "a = b"  
    using B4 B5 nless_le by blast
  show ?thesis  
    using A3 B4 B5 idef inf_equality by fastforce
qed

lemma lattice_equality_sup:
  assumes A0:"is_lattice R X" and A1:" antisym R X"  and A2:"trans R X" and A3:"refl R X" and A4:"F \<subseteq>X" and A5:"finite F" and A6:"F \<noteq> {}" and A7:"Sup R X F = s"
  shows "is_sup R X F s"
  by (metis A0 A1 A2 A4 A5 A6 A7 Fpow_ne_iff lattD42 sup_semilattice_fsup)

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
    have B1:" {a, b} \<in> Pow_ne X"
      by (simp add: A6)  
    have B10:"{a, b} \<subseteq> X"  
      using B1 by blast
    have B11:"finite {a, b}" 
      by simp
    have B12:"{a,b} \<noteq> {}" 
      by auto
    have B2:"is_inf R X {a, b} m" 
      using lattice_equality_inf[of R X "{a,b}" m]   by (simp add: A1 A2 A3 A4 A6)
    have B3:"m \<in> {a, b}"   
       by (metis A5 B1 B2 mredI1) 
    show "m = a \<or> m = b"  
      using B3 by fastforce
  qed
  show "fin_inf_irr R X m"
    by (meson B0 fin_inf_irrI1)
qed

lemma pfilter_meet_of_primes:
  assumes A0:"distributive_lattice R X" and 
          A1:"is_greatest R X top" and
          A2:"F \<in> pfilters_on R X" and
          por:"pord R X"
  obtains M where "\<forall>Fm. Fm \<in> M \<longrightarrow> Fm \<in> filters_on R X \<and> meet_irr (pwr X) (filters_on R X) Fm " 
                  and "F = Inf (pwr X) (filters_on R X) M"
proof-
  let ?FX="(filters_on R X)" let ?RX="pwr X"
  have B0:"compactly_generated ?RX ?FX"
    by (meson A0 A1 distr_latticeD5 filters_on_lattice_compactgen por) 
  have B1:"is_clattice ?RX ?FX"
    by (meson A0 A1 distr_latticeD5 lattice_filters_complete por) 
  have B2:"F \<in> ?FX"
    using A2 filters_on_iff is_pfilterD1 pfilters_on_iff by blast
  have B3:"F = Inf ?RX ?FX {Fm \<in> ?FX. meet_irr ?RX ?FX Fm \<and> (F, Fm)\<in>?RX}" 
    using mirred_temp3[of ?RX ?FX F] B0 B1 B2  by (metis PowI filters_on_def is_filterD1 mem_Collect_eq powrel6 powrel7 pwr_memI refl_def subsetI)
  have B4:"\<forall>Fm.  Fm \<in> {Fm \<in> ?FX. meet_irr ?RX ?FX Fm \<and> (F,Fm)\<in>?RX} \<longrightarrow> Fm \<in> ?FX \<and> meet_irr ?RX ?FX Fm "  
    by fastforce
  then show ?thesis  
    using B3 that by blast
qed



lemma sup_prime_pfilterI3:
  assumes A0:"distributive_lattice R X" and 
          A1:"pord R X" and
          A2:"fin_inf_irr (pwr X) (filters_on R X) F" and 
          A3:"is_pfilter R X F"
  shows "sup_prime R X F"
proof-
  let ?R="pwr X" let ?X="filters_on R X" 
  obtain C1:"antisym ?R ?X" and C2:"refl ?R ?X" and C3:"trans ?R ?X"
    by (meson PowI filters_on_iff is_filterD1 powrel3 powrel6 powrel7 reflI1 refl_onD subsetI)  
  obtain C4:"F \<in> ?X"
    by (simp add: A3 filters_on_iff is_pfilterD1)  
  obtain C5:"distributive_lattice ?R ?X"    
    by (simp add: A0 A1 A2 A3 lattice_filters_distr)
  have B0:"elem_inf_prime ?R ?X F"
    by (simp add: A2 C1 C2 C3 C4 C5 elem_inf_primeI3) 
  have B1:"(\<And>F1 F2. \<lbrakk>F1 \<in> ?X; F2 \<in> ?X; (Inf ?R ?X {F1, F2}, F)\<in>(pwr X)\<rbrakk> \<Longrightarrow> (F1, F)\<in>?R \<or> (F2, F)\<in>?R)" 
    by (meson B0 elem_inf_primeD1)
  have B2:"(\<And>F1 F2. \<lbrakk>is_filter R X  F1; is_filter R X  F2; F1 \<inter> F2 \<subseteq> F\<rbrakk> \<Longrightarrow> F1 \<subseteq> F \<or> F2 \<subseteq> F)"
    by (metis A0 A1 B1 C2 C4 distr_latticeD5 filters_on_iff lattice_filters_isl7 pwr_mem_iff reflD2)  
  show ?thesis
    by (simp add: A0 A1 A3 B2 distr_latticeD5 sup_prime_pfilterI2) 
qed

lemma prime_filter_irr3_converse:
  "\<lbrakk>distributive_lattice R X; antisym R X; trans R X; refl R X; fin_inf_irr (pwr X) (filters_on R X) F; is_pfilter R X F\<rbrakk> \<Longrightarrow> sup_prime R X F"  
  by (simp add: is_pfilterI1 sup_prime_pfilterI3)


lemma pfilters_meet_of_primes2:
  assumes A0:"distributive_lattice R X" and
          A1:"is_greatest R X top" and
          A2:"F \<in> pfilters_on R X" and
          por:"pord R X"
  obtains M where "\<forall>Fm. Fm \<in> M \<longrightarrow> Fm \<in> filters_on R X \<and> sup_prime R X Fm " and 
                  "F = Inf (pwr X) (filters_on R X) M"
proof-
  let ?FX="(filters_on R X)" let ?RX="pwr X"
  have B0:"compactly_generated ?RX ?FX"
    by (meson A0 A1 distr_latticeD5 filters_on_lattice_compactgen por)  
  obtain C1:"antisym ?RX ?FX" and C2:"refl ?RX ?FX" and C3:"trans ?RX ?FX"
    by (meson PowI antisym_on_def filters_on_iff is_filterD1 powrel3 powrel7 powrel8 refl_def refl_on_def subsetI subset_antisym)  
  obtain C4:"distributive_lattice ?RX ?FX"
    by (simp add: A0 lattice_filters_distr por)  
  have B1:"is_clattice ?RX ?FX"
    by (meson A0 A1 distr_latticeD5 lattice_filters_complete por)  
  have B2:"F \<in> ?FX"
    using A2 filters_on_iff is_pfilterD1 pfilters_on_iff by blast 
  have B3:"F = Inf ?RX ?FX {Fm \<in> ?FX. meet_irr ?RX ?FX Fm \<and> (F, Fm)\<in>?RX}"
    by (simp add: B0 B1 B2 C1 C2 C3 mirred_temp3) 
  have B4:"\<And>Fm.  Fm \<in> {Fm \<in> ?FX. meet_irr ?RX ?FX Fm \<and> (F, Fm)\<in>?RX} \<Longrightarrow> Fm \<in> ?FX \<and> sup_prime R X Fm " 
  proof-
    fix Fm assume A6:"Fm \<in> {Fm \<in> ?FX. meet_irr ?RX ?FX Fm \<and>(F, Fm)\<in>?RX}" 
    have B40:"Fm \<in> ?FX \<and> meet_irr ?RX ?FX Fm"  
      using A6 by blast
    have B41:"fin_inf_irr ?RX ?FX Fm"
      by (simp add: B1 B40 C1 C2 C3 clat_lattice meet_irr_imp_fmeet_irr)
    have B43:"is_greatest ?RX ?FX X"  
    proof-
      have B430:"X \<in> ?FX"
        by (metis A0 CollectI bot_filters1 distr_latticeD5 filters_on_def lattD41)   
      have B431:"X \<in> ubd ?RX ?FX ?FX"  
         by (meson B430 C2 pwr_mem_iff reflD2 ubdI)
      show ?thesis   
        by (simp add: B431 is_greatest_def)
    qed
    have B44:"sup_prime R X Fm"
    proof(cases "is_pfilter R X Fm")
      case True then show ?thesis
        by (simp add: A0 B41 por sup_prime_pfilterI3)
    next
      case False obtain B45:"Fm = X"
        using B40 False filters_on_iff is_pfilter_def by blast 
      then show ?thesis
        by (simp add: sup_primeI1) 
    qed
    show "Fm \<in> ?FX \<and> sup_prime R X Fm" 
       by (simp add: B40 B44)
  qed
  then show ?thesis  
    using B3 that by blast
qed



lemma principal_filters_compact:
  assumes A0:"is_lattice R X" and A1:"is_greatest R X top" and A2:"X \<noteq> {}" and A3:"F \<in> filters_on R X" and  por:"pord R X"
  shows "is_compact (pwr X) (filters_on R X) F \<longleftrightarrow> (\<exists>x \<in> X. F = (lcro R X x))" (is "?L \<longleftrightarrow> ?R")
proof-                             
  let ?A="{lcro R X x|x. x \<in>F}" let ?U="\<Union>?A"
  obtain C0:"?A \<in> Pow(Pow X)" and C1:"?U \<in> Pow X"
    using lcroD1 by fastforce
  obtain C5:"pord (pwr X) (Pow X)" and C6:"pord (pwr X) (filters_on R X)"
    by (meson PowI filters_on_iff is_filterD1 powrel3 powrel6 powrel7 refl_def refl_onD subsetI)
  have C2:"\<And>f. f \<in> ?A \<Longrightarrow> is_filter R X f"
    using A3 filters_on_iff is_filterD1 lcro_filter por by fastforce
  have B0:"F \<subseteq> X"
    by (meson A3 filters_on_iff is_filterD1) 
  have B1:"\<And>x. x \<in> F \<Longrightarrow> x \<in> lcro R X x"
    by (meson B0 lcro_memI1 por subsetD) 
  have B3:"{lcro R X x|x. x \<in>F} \<in> Pow_ne (filters_on R X)"
    using A1 A3 B0 filters_on_iff lcro_filter por top_filters1 by fastforce 
  obtain s where iss:"is_sup (pwr X) (filters_on R X) ?A s"
    by (metis (mono_tags, lifting) A0 B3 Pow_ne_iff lattice_filters_isl4 por)
  have B2:"F \<subseteq>?U" 
    using B0 B1 by blast
  have C3:"?U \<subseteq> X"
    using C1 by fastforce
  have C4:"?U \<subseteq> s"
    by (metis (no_types, lifting) Sup_le_iff is_supD3 iss pwr_mem_iff)
  have B21:"((\<Union>?A),s)\<in>pwr X"
    by (metis (no_types, lifting) C4 Collect_mono_iff is_sup_iso1 iss pwr_memD pwr_memI)
  have B22:"s = Sup (pwr X) (filters_on R X) ?A"
    using C6 iss sup_equality by fastforce
  have B4:"(F, s)\<in>(pwr X)"
    by (meson B2 B21 order.trans pwr_mem_iff)
  have B5:"s \<in> (filters_on R X)"
    by (meson is_supD1 iss)
  have B6:"is_dir s (dual R)"
    by (meson B5 is_filter_def filters_on_iff)
  have B7:" (\<exists>x \<in> X.  lcro R X x = F ) \<Longrightarrow> is_compact (pwr X) (filters_on R X) F "
  proof-
    assume "(\<exists>x \<in> X. lcro R X x = F)" then obtain x where xmem:"x \<in> X" and B40:"lcro R X x = F"  by auto
    let ?C="filters_on R X"
    have B42:"is_compact (pwr X) ?C (cl_from_clr (pwr X) ?C {x})"
      using singleton_closure_compact[of X ?C]
    by (metis A0 A1 A2 filters_on_lattice_compactgen01 filters_on_lattice_compactgen02 filters_on_lattice_compactgen03 por xmem)
    have B42:"lcro R X x \<in> ubd (pwr X) (filters_on R X) {{x}}"
      by (metis A3 B0 B40 empty_subsetI insert_subset lcroI1 lcro_eq_upbd lcro_memI1 por pwr_memI xmem)
   have B43:"is_least (pwr X) (ubd (pwr X) (filters_on R X) {{x}}) (lcro R X x)"
   proof-
    have D0:"lcro R X x \<in> filters_on R X"
      by (simp add: filters_on_iff lcro_filter por xmem)
    have D1:"({x}, lcro R X x) \<in> pwr X"
      by (metis D0 empty_subsetI filters_on_iff insert_subset is_filterD1 lcro_memI1 por pwr_memI xmem)
    have D2:"\<And>a. a \<in> filters_on R X \<Longrightarrow> ({x}, a) \<in> pwr X \<Longrightarrow> (lcro R X x, a) \<in> pwr X"
    proof-
      fix a assume E0:"a \<in> filters_on R X" and E1:"({x},a)\<in>pwr X" 
      then obtain E2:"x \<in> a" and E3:"is_ord_cl X a R"
        by (simp add: filters_on_def is_filterD1 pwr_mem_iff)
      then obtain "(lcro R X x) \<subseteq> a"
        by (meson is_ord_clE1 lcroD1 subsetI)
      then show "(lcro R X x,a)\<in>pwr X"
        by (meson E1 pwr_mem_iff)
   qed
   show ?thesis
    by (metis D0 D1 D2 converseI greatestI2 ubd_singleton_mem)
  qed
  have B44:"cl_from_clr (pwr X) ?C {x} = lcro R X x"
    by (meson A0 A1 A2 B43 clr_equality filters_on_lattice_compactgen01 por powrel1)
  have B45:"... = F"
    by (simp add: B40)
  then show "is_compact (pwr X) (filters_on R X) F"
    by (metis A0 A1 A2 B44 filters_on_lattice_compactgen01 filters_on_lattice_compactgen02 filters_on_lattice_compactgen03 por singleton_closure_compact xmem)
  qed
  have B3:"is_compact (pwr X) (filters_on R X) F \<Longrightarrow>  (\<exists>x \<in> X.  lcro R X x = F )"
  proof-
    assume B3A0:"is_compact (pwr X) (filters_on R X) F"  
    obtain A0 where B31:"A0 \<in> Fpow_ne ?A " and B32:"(F, Sup (pwr X)(filters_on R X) A0)\<in>pwr X"
      by (metis (no_types, lifting) B22 B3 B3A0 B4 compactD)
    have B33:"\<And>Ai. Ai \<in> A0 \<Longrightarrow> (\<exists>x. is_least R Ai x)"
    proof-
      fix Ai assume "Ai \<in> A0" then obtain x where "x \<in> F" and "Ai = lcro R X x"
        using B31 by blast 
      then obtain "is_least R Ai x"
        by (meson B1 converseI greatestI2 lcroD1) 
      then show "(\<exists>x. is_least R Ai x)" 
        by blast
    qed
    define S where "S \<equiv> (\<lambda>Ai. THE x. x \<in> F \<and> is_least R Ai x)"
    have B34:"\<And>Ai. Ai \<in> A0 \<Longrightarrow> (S Ai) \<in> F \<and> is_least R Ai (S Ai) \<and> lcro R X (S Ai) = Ai" 
    proof-
      fix Ai assume "Ai \<in> A0" then obtain x where B340:"x \<in> F" and B34A0:"Ai = lcro R X x"
        using B31 by blast  
      then obtain B341:"is_least R Ai x"
        by (meson B1 converseI greatestI2 lcroD1) 
      then obtain B342: "(S Ai) \<in>F" and B343:"is_least R Ai (S Ai)" unfolding S_def
        by (smt (verit, del_insts) B1 B340 B34A0 antisym_on_converse antisym_on_subset greatest_equality3 is_filterD1 lcroD1 lcro_filter por the1I2)
       obtain "lcro R X (S Ai) = Ai"
        by (metis B1 B340 B341 B343 B34A0 antisym_on_converse antisym_on_subset greatest_equality3 is_filterD1 lcroD1 lcro_filter por) 
      then show "(S Ai) \<in> F \<and> is_least R Ai (S Ai) \<and> lcro R X (S Ai) = Ai"
         using B342 B343 by blast
    qed
    then obtain B35:"(S`A0) \<subseteq> F" and B36:"finite (S`A0)"
      using B31 by blast 
    then obtain B37:"Inf R X (S`A0) \<in> F"
      by (metis (no_types, lifting) A0 A3 B31 Fpow_ne_iff filter_inf_closed3 filters_on_iff image_is_empty latt_iff por) 
    then obtain B38:"lcro R X (Inf R X (S`A0)) \<subseteq> F "
      by (meson A3 filters_on_iff is_filterD1 is_ord_clD1 lcroD1 subsetI)
    have B39:"\<And>Ai. Ai \<in> {lcro R X f|f. f \<in>  (S`A0)} \<Longrightarrow> Ai \<in> A0" 
      using B34 by force
    have B40:"\<And>Ai. Ai \<in> A0 \<Longrightarrow>  Ai \<in> {lcro R X f|f. f \<in>  (S`A0)} " 
      using B34 by force
    have B41:"A0 =  {lcro R X f|f. f \<in>  (S`A0)}"
      using B39 B40 by blast 
    have B41b:"(S`A0) \<in> Fpow_ne X"
      using B0 B31 B35 by auto
    obtain B42:"lcro R X (Inf R X (S`A0)) = Sup (pwr X) (filters_on R X) A0" 
      using A0 B41 B41b por lcro_inter2[of R X "(S`A0)"] S_def by presburger
    then show " (\<exists>x \<in> X.  lcro R X x = F )"
      by (metis B0 B32 B37 B38 powrel8 subsetD subset_antisym)
  qed
  then show ?thesis
    using B7 by blast
qed 



section FilterOfSets

lemma setfilters0:
  "is_filter (pwr X) (Pow X) EF \<Longrightarrow> F \<in> EF \<Longrightarrow> F \<subseteq> X"
  using is_filterD1 by blast

lemma setfilters1:
  assumes A0:"is_filter (pwr X) (Pow X) EF" and A1:"F1 \<in> EF" and A2:"F2 \<in> EF"
  shows "F1 \<inter> F2 \<in> EF"
proof-
  obtain A3:"F1 \<in> Pow X" and A4:"F2 \<in> Pow X"
    using A0 A1 A2 is_filterD1 by blast
  have B0:"is_inf (pwr X) (Pow X) {F1, F2} (F1 \<inter> F2)"
    by (metis A3 A4 Inf_insert Inter_empty empty_subsetI inf_top.right_neutral insert_not_empty insert_subsetI powrel4b)
  then show "(F1 \<inter> F2) \<in> EF"
    by (meson A0 A1 A2 filter_inf_closed1) 
qed
       

lemma setfilters2:
  assumes A0:"is_filter (pwr X) (Pow X) EF" and A1:"A \<in> EF" and A2:"B \<in> Pow X" and A3:"A \<subseteq> B"
  shows "B \<in> EF"
  by (meson A0 A1 A2 A3 PowD is_filterD1 is_ord_clE1 pwr_memI)

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
  proof(rule is_pfilterI1)
  show "is_filter (pwr X) (Pow X) F"
  proof(rule is_filterI1)
    show "F \<noteq> {}"
      by (simp add: A1)
    show  "F \<subseteq> Pow X"
      by (simp add: A0)
    show "is_dir F (dual (pwr X))"
    proof(rule is_dirI1)
      fix a b assume "a \<in> F" and "b \<in> F" 
      then show "\<exists>c \<in> F. (a,c)\<in>(dual (pwr X)) \<and> (b,c)\<in>(dual (pwr X))"
        by (meson A0 A3 PowD converseI in_mono inf.cobounded1 inf.cobounded2 pwr_mem_iff)
    qed
    show "is_ord_cl (Pow X) F (pwr X)"
      by (meson A4 is_ord_clI1 powrel8)
  qed
  show "Pow X \<noteq> F"
    using A2 by auto 
qed

lemma sets_pfilter:
  assumes "is_pfilter (pwr X) (Pow X) F"
  shows sets_pfilter1:"F \<noteq> {}" and
        sets_pfilter2:"F \<noteq> Pow X" and
        sets_pfilter3:"(\<And>A B. \<lbrakk>A \<in> F; B \<in> F\<rbrakk> \<Longrightarrow> A \<inter> B \<in> F)" and
        sets_pfilter4:"(\<And>A B. \<lbrakk>A \<in> F; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> B \<in> F)" and
        sets_pfilter5:"{} \<notin> F" and
        sets_pfilter6:"F \<subseteq> Pow X"
proof-
  show P0:"F \<noteq> {}"
    using assms is_filterD1 is_pfilterD1 by blast
  show P1:"F \<noteq> Pow X"
    using assms is_pfilterD2 by blast
  show P2:"(\<And>A B. \<lbrakk>A \<in> F; B \<in> F\<rbrakk> \<Longrightarrow> A \<inter> B \<in> F)"
    using assms is_pfilterD1 setfilters1 by blast 
  show P3:"(\<And>A B. \<lbrakk>A \<in> F; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> B \<in> F)"
    using assms is_pfilterD1 setfilters2 by blast
  show "{} \<notin> F"
  proof(rule ccontr)
    assume "\<not>({} \<notin> F)" then obtain contr:"{} \<in> F" by simp
    then obtain sub1:"F \<subseteq> Pow X" and sub2:"\<And>A. A \<in> Pow X \<Longrightarrow> A \<in> F"
      by (metis PowD Pow_bottom assms is_filterD1 is_pfilterD1 setfilters2)
    then obtain sub3:"F=Pow X" 
      by blast
    then show False
      by (simp add: P1)
  qed
  show "F \<subseteq> Pow X"
    using assms is_filterD1 is_pfilterD1 by blast
qed

 
lemma pfilter_sets_comp:
  assumes A0:"is_pfilter (pwr X) (Pow X) F" and A1:"(X-A) \<in> F"
  shows "A \<notin> F"
proof(rule ccontr)
  assume "\<not>(A \<notin> F)" then have  "A \<in> F" by simp
  then have "(X-A) \<inter> A \<in> F"
    using A0 A1 sets_pfilter3 by blast 
  then have "{} \<in> F"  
    by (simp add: Int_commute)
  then show False
    using A0 sets_pfilter5 by blast
qed
    
lemma pfilters_sets_comp2:
   "is_pfilter (pwr X) (Pow X) F \<Longrightarrow> A \<in> F \<Longrightarrow> (X-A) \<notin> F"
  using pfilter_sets_comp by blast

lemma pfilters_sets_comp3:
   "\<lbrakk>is_pfilter (pwr X) (Pow X) F; A \<subseteq> X; \<exists>U \<in> F. U \<inter> (X-A) = {}\<rbrakk> \<Longrightarrow> A \<in> F"
  by (metis Diff_Diff_Int Diff_mono Diff_triv PowI inf.absorb_iff2 order.order_iff_strict setfilters0 setfilters2 setfilters3)


lemma principal_filter_sets:
  "x \<in> X \<Longrightarrow> is_filter (pwr X) (Pow X) (lcro (pwr X) (Pow X) {x})"
  by (simp add: lcro_filter powrel1 powrel2 pwr_memI refl_def)

lemma principal_pfilter_sets:
  "x \<in> X \<Longrightarrow> is_pfilter (pwr X) (Pow X) (lcro (pwr X) (Pow X) {x})"
  by (metis Pow_bottom empty_iff insert_subset lcroD1 powrel8 principal_filter_sets setfilters3)


lemma pmb_filters2:
  assumes A0:"is_pfilter (pwr X) (Pow X) F" and
          A1:"\<And>x. x \<in> (Pow X) \<Longrightarrow> (x \<in> F \<or> (X-x) \<in> F) \<and> \<not>(x \<in> F \<and> (X-x) \<in> F)"
  shows "is_maximal (pwr (Pow X)) (pfilters_on (pwr X) (Pow X)) F"
proof-
  let ?X="Pow X" let ?R="(pwr X)"
  have B0:"F \<in> pfilters_on ?R ?X"
    by (simp add: A0 pfilters_on_iff) 
  have B1:"\<And>G. \<lbrakk>G \<in> filters_on ?R ?X;  F \<subset> G \<rbrakk> \<Longrightarrow> G = ?X"
  proof-
    fix G assume A2:"G \<in> filters_on ?R ?X" and A3:"F \<subset> G"
    obtain z where B10: "z \<in> G - F"  
      using A3 by auto
    have B11:"z \<notin> F" 
      using B10 by blast 
    have B12:"X-z \<in> F"
      by (meson A1 A2 B10 B11 DiffD1 filters_on_iff in_mono is_filterD1) 
    have B13:"X-z \<in> G \<and> z \<in> G"  
      using A3 B10 B12 by blast
    have B14:"is_filter ?R ?X G"  
       using A2 filters_on_iff by auto
    show "G=?X"  
      using B13 B14  is_pfilterI1 pfilters_sets_comp2 by blast 
  qed
  have B2:"\<And>G. \<lbrakk>G \<in> pfilters_on ?R ?X;  F \<subseteq> G \<rbrakk> \<Longrightarrow> G = F"
    by (metis B1 filters_on_iff is_pfilterD1 is_pfilterD2 pfilters_on_iff psubsetI)
  show ?thesis
    by (simp add: B0 B2 maximalI1 powrel8)
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
    proof(rule is_filterI1)
      show P0:"H \<noteq> {}"
        using A0 H_def is_filterD1 is_pfilterD1 by fastforce
      show P1:"H \<subseteq> Pow X"
        using H_def by blast
      show P2:"is_dir H (dual (pwr X))"
      proof(rule is_dirI1)
        fix a b assume A3:"a \<in> H" and A4:"b \<in> H"
        obtain aB bB where B0:"aB \<in> F" and B1:"bB \<in> F" and B2:"A \<inter> aB \<subseteq> a" and B3:"A \<inter> bB \<subseteq> b"
          using A3 A4 H_def by auto 
        obtain B4:"aB \<inter> bB \<in> F"
          using A0 B0 B1 sets_pfilter3 by blast 
        obtain B5:"A \<inter> aB \<inter> bB \<in> H"
          using A4 B3 B4 H_def inf.absorb_iff2 by fastforce 
        also have B6:"A \<inter> aB \<inter> bB \<subseteq> a \<and> A \<inter> aB \<inter> bB \<subseteq> b"  
          using B2 B3 by blast
        then show " \<exists>c\<in>H. (a, c) \<in> dual (pwr X) \<and> (b, c) \<in> dual (pwr X)"
          by (meson A3 A4 P1 PowD calculation converseI pwr_memI subset_eq)  
        qed
      show "is_ord_cl (Pow X) H (pwr X)"
      proof(rule is_ord_clI1)
        fix a b assume B0:"a \<in>H" and B1:"b \<in> Pow X" and B2:"(a,b)\<in>pwr X"
        then obtain aB where B3:"aB \<in> F" and B4:"A \<inter> aB \<subseteq> a" using H_def by blast
        then obtain B5:"A \<inter> aB \<subseteq> b"
          using B2 powrel8 by fastforce
        then show "b \<in> H"
          using B1 B3 H_def by blast
      qed
    qed
    show "Pow X \<noteq> H"
    proof-
      have B7:"{} \<notin> H"   
        by (simp add: H_def Int_commute local.A2)
      then show ?thesis by blast
    qed
  qed
  show "F \<subseteq> H"
  proof
    fix f assume A4:"f \<in> F"
    have B8:"X \<in> F"
      using A0 A4 pfilters_sets_comp3 by auto
    also have B9:"X \<inter> f \<subseteq> f" 
      by simp
    then show "f \<in> H"
      using A0 A4 H_def is_pfilterD1 setfilters0 by fastforce 
  qed
qed

lemma principal_ufilter_sets:
  "x \<in> X \<Longrightarrow> is_maximal (pwr (Pow X)) (pfilters_on (pwr X) (Pow X)) (lcro (pwr X) (Pow X) {x})"
proof(rule pmb_filters2)
    show " x \<in> X \<Longrightarrow> is_pfilter (pwr X) (Pow X) (lcro (pwr X) (Pow X) {x})"
      by (simp add: principal_pfilter_sets)
    show "\<And>xa. x \<in> X \<Longrightarrow> xa \<in> Pow X \<Longrightarrow> (xa \<in> lcro (pwr X) (Pow X) {x} \<or> X - xa \<in> lcro (pwr X) (Pow X) {x}) \<and> \<not> (xa \<in> lcro (pwr X) (Pow X) {x} \<and> X - xa \<in> lcro (pwr X) (Pow X) {x})"
      by (simp add: lcro_def pwr_mem_iff)
qed

lemma galois_connD1:
  "galois_conn f Rx X g Ry Y \<Longrightarrow> (f`X \<subseteq> Y) \<and> (g`Y \<subseteq> X)"
  by (simp add:galois_conn_def)

lemma galois_connD2:
  "galois_conn f Rx X g Ry Y \<Longrightarrow> (\<And>x y. \<lbrakk>x\<in>X;y\<in>Y\<rbrakk>\<Longrightarrow>((x,g y)\<in>Rx \<longleftrightarrow> (y,f x)\<in>Ry))"
  by (simp add:galois_conn_def)

lemma galois_connD3:
  "galois_conn f Rx X g Ry Y \<Longrightarrow> (\<And>x y. \<lbrakk>x\<in>X;y\<in>Y;(x,g y)\<in>Rx\<rbrakk> \<Longrightarrow> (y,f x)\<in>Ry)"
  by (simp add:galois_conn_def)        

lemma galois_connD4:
  "galois_conn f Rx X g Ry Y \<Longrightarrow> (\<And>x y. \<lbrakk>x\<in>X;y\<in>Y;(y,f x)\<in>Ry\<rbrakk> \<Longrightarrow> (x,g y)\<in>Rx)"
  by (simp add:galois_conn_def)

lemma galois_connD5:
  "galois_conn f Rx X g Ry Y \<Longrightarrow> x \<in> X \<Longrightarrow> f x \<in> Y"
  using galois_connD1 by blast     

lemma galois_connD6:
  "galois_conn f Rx X g Ry Y \<Longrightarrow> y \<in> Y \<Longrightarrow> g y \<in> X"
  using galois_connD1 by blast

lemma gc_props1:
  assumes is_gc:"galois_conn f Rx X g Ry Y" and prx:"pord Rx X" and pry:"pord Ry Y"
  shows gc_ext1:"\<And>x. x \<in> X \<Longrightarrow> (x, g (f x))\<in>Rx" and
        gc_ext2:"\<And>y. y \<in> Y \<Longrightarrow> (y,f (g y))\<in>Ry" and
        gc_ant1:"\<And>x1 x2. \<lbrakk>x1 \<in> X; x2 \<in> X; (x1,x2)\<in>Rx\<rbrakk> \<Longrightarrow> (f x2, f x1)\<in>Ry" and
        gc_ant2:"\<And>y1 y2. \<lbrakk>y1 \<in> Y; y2 \<in> Y; (y1,y2)\<in>Ry\<rbrakk> \<Longrightarrow> (g y2, g y1)\<in>Rx" and
        gc_ext3:"extensive Rx X (g\<circ>f)" and 
        gc_ext4:"extensive Ry Y (f\<circ>g)" and
        gc_ant3:"antitone Rx X Ry f" and 
        gc_ant4:"antitone Ry Y Rx g" and 
        gc_ide1:"\<And>x. x \<in> X \<Longrightarrow> f (g (f x)) = f x" and
        gc_ide2:"\<And>y. y\<in> Y \<Longrightarrow> g (f (g y)) = g y"
proof-
  show P0:"\<And>x. x \<in> X \<Longrightarrow> (x, g (f x))\<in>Rx" 
  proof-
    fix x assume A0:"x \<in> X"
    then obtain B0:"f x \<in> Y"
      using galois_connD1 is_gc by blast
    then obtain B1:"(f x, f x) \<in> Ry"
      by (meson pry reflD2)
    then show "(x,g (f x))\<in>Rx"
      by (meson A0 B0 galois_connD2 is_gc)
  qed
  show P1:"\<And>y. y \<in> Y \<Longrightarrow> (y,f (g y))\<in>Ry" 
  proof-
    fix y assume A0:"y \<in> Y"
    then obtain B0:"g y \<in> X"
      using galois_connD1 is_gc by blast
    then obtain B1:"(g y, g y) \<in> Rx"
      by (meson prx reflD2)
    then show "(y,f (g y))\<in>Ry"
      by (meson A0 B0 galois_connD3 is_gc)
  qed
  show P2:"\<And>x1 x2. \<lbrakk>x1 \<in> X; x2 \<in> X; (x1,x2)\<in>Rx\<rbrakk> \<Longrightarrow> (f x2, f x1)\<in>Ry"
    by (meson P0 galois_connD3 galois_connD5 galois_connD6 is_gc prx trans_onD) 
  show P3:"\<And>y1 y2. \<lbrakk>y1 \<in> Y; y2 \<in> Y; (y1,y2)\<in>Ry\<rbrakk> \<Longrightarrow> (g y2, g y1)\<in>Rx"
    by (meson P1 galois_connD4 galois_connD5 galois_connD6 is_gc pry trans_onD)
  show P4:"extensive Rx X (g\<circ>f)"
    by (simp add: P0 extensive_def) 
  show P5:"extensive Ry Y (f\<circ>g)" 
    by (simp add: P1 extensive_def) 
  show P6:"antitone Rx X Ry f"
    by (simp add: P2 isotone_def)  
  show P7:"antitone Ry Y Rx g"
    by(simp add:P3 isotone_def)
  show P8:"\<And>x. x \<in> X \<Longrightarrow> f (g (f x)) = f x"
    by (meson P0 P1 P2 antisym_on_def galois_connD5 galois_connD6 is_gc pry)
  show P9:"\<And>y. y \<in> Y \<Longrightarrow> g (f (g y)) = g y"
    by (meson P0 P1 P3 antisym_on_def galois_connD5 galois_connD6 is_gc prx)
qed

lemma gcI:
  assumes ant1:"antitone Rx X Ry f" and ant2:"antitone Ry Y Rx g" and
          ext1:"extensive Rx X (g\<circ>f)" and ext2:"extensive Ry Y (f\<circ>g)" and
          map1:"f`X \<subseteq> Y" and map2:"g`Y \<subseteq> X" and 
          prx:"pord Rx X" and pry:"pord Ry Y"
  shows "galois_conn f Rx X g Ry Y"
proof-
  have B0:"\<And>x y. \<lbrakk>x \<in> X; y \<in> Y\<rbrakk> \<Longrightarrow>  ((x, g y) \<in> Rx) \<longleftrightarrow> ((y, f x) \<in> Ry)"
  proof-
    fix x y assume A0:"x \<in> X" and A1:"y \<in> Y"
    then obtain B01:"f x \<in> Y" and B02:"g y \<in> X"
      using map1 map2 by fastforce
    then obtain B03:"g (f x)\<in>X" and B04:"f (g y)\<in>Y"
      using map1 map2 by blast
    have B05:"(y,f x)\<in>Ry \<Longrightarrow> (x, g y)\<in>Rx"
    proof-
      assume A2:"(y, f x)\<in> Ry"
      then obtain C0:"(g (f x), g y) \<in> Rx"
        by (meson A1 B01 ant2 converseD isotoneD1)
      then obtain C1:"(x, g (f x))\<in> Rx" and C2:"(g (f x), g y)\<in> Rx"
        using A0 ext1 extensiveD1 by fastforce
      then show "(x, g y)\<in> Rx"
        by (meson A0 B02 B03 prx trans_onD)
    qed
    also have B06:"(x, g y)\<in>Rx\<Longrightarrow>(y,f x)\<in>Ry"
    proof-
      assume A3:"(x, g y)\<in> Rx"
      then obtain C3:"(f (g y), f x) \<in> Ry"
        by (meson A0 B02 ant1 converse.simps isotoneD1)
      then obtain C4:"(y, f (g y))\<in> Ry" and C5:"(f (g y), f x)\<in> Ry"
        using A1 ext2 extensiveD1 by fastforce
      then show "(y, f x)\<in> Ry"
        by (meson A1 B01 B04 pry trans_onD)
    qed
    then show "(x, g y) \<in> Rx \<longleftrightarrow> (y, f x) \<in> Ry"
      using calculation by blast
  qed
  then show ?thesis
  by (simp add: galois_conn_def map1 map2)
qed


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
  assumes fam:"EF \<in> (Pow (Pow X))" and A1:"A \<in> Pow X" and up:"is_ord_cl (Pow X) EF (pwr X)"
  shows mesh_up1:"\<not>(A \<in> EF \<and> {X-A}#EF)"  and
        mesh_up2:"\<not>(A \<in> EF) \<or> \<not>({X-A}#EF)" and
        mesh_up3:"A \<in> EF \<Longrightarrow> \<not>({X-A}#EF)" 
        using mesh_singleE by fastforce+

lemma pfilter_mesh1:
  assumes pfil1:"EF \<in> pfilters_on (pwr X) (Pow X)" and pfil2:"GF \<in> pfilters_on (pwr X) (Pow X)" and finer:"EF \<subseteq> GF"
  shows "EF#GF"
proof(rule ccontr)
  assume c:"\<not>(EF#GF)" then obtain F G where fmem:"F \<in> EF" and gmem:"G \<in> GF" and dis:"F \<inter> G={}" by (meson meshI)
  from  pfil1 pfil2 obtain "is_pfilter (pwr X) (Pow X) EF" and  pfil:"is_pfilter (pwr X) (Pow X) GF"
    by (simp add: pfilters_on_iff) 
  then obtain "EF \<subseteq> Pow X" and  "GF \<subseteq> Pow X"  and  "is_ord_cl (Pow X) GF (pwr X)"
    using is_filterD1 is_pfilterD1 by blast 
  also have "F \<in> EF" using fmem by auto
  then obtain "F \<in> GF" and "G \<in> GF" and "F \<inter> G \<in> GF"
    using finer gmem pfil sets_pfilter3 by blast 
  then obtain "{} \<in> GF" 
    using dis by auto
  then show False
    using pfil sets_pfilter5 by blast 
qed


lemma upcl_meet:
  assumes fam:"A \<in> Pow( Pow X)" and
           upcl:"is_ord_cl (Pow X) A (pwr X)" and 
          bsub:"b \<in> Pow X" and 
          notin:"b \<notin> A" and
          ain:"a \<in> A "
  shows "a \<inter> (X-b) \<noteq>{}"
proof(rule ccontr)
  assume  "\<not> (a \<inter> (X-b) \<noteq> {})" then obtain "a \<inter> (X-b) = {}" 
    by auto 
  then have "a \<subseteq> b" 
    using fam ain by fastforce 
  then have "b \<in> A"
    by (meson PowD ain bsub is_ord_clE1 pwr_mem_iff upcl) 
  then show False 
    using notin by auto
qed


lemma isotone_mesh:
  assumes fam:"A \<in> Pow(Pow X)" and upcl:"is_ord_cl (Pow X) A (pwr X)" and st:"E \<in> Pow X"  
  shows isotone_mesh1:"E \<notin> A \<longleftrightarrow> {X-E}#A" and
        isotone_mesh2:"E \<in> A \<longleftrightarrow> \<not> ({X-E}#A)"
proof-
  show "E \<notin> A \<longleftrightarrow> {X-E}#A"
  proof
    assume ena:"E \<notin> A"  show "{X-E}#A" 
    proof(rule mesh_singleI)
      fix a assume ana:"a \<in> A" show "(X - E) \<inter> a \<noteq> {}" 
        using fam upcl st ena ana upcl_meet[of A X E a] by auto
    qed
   next
    assume cms:"{X-E}#A" then show "E \<notin> A"
      using fam mesh_up3 st upcl by blast  
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
  shows "A#B \<longleftrightarrow> B \<subseteq> grill (Pow X) A"
  by (metis fam1 fam2 mesh_iff_grill1 mesh_sym)  

lemma grill_reform:
  assumes fam:"A \<in> Pow( Pow X)" and upcl:"is_ord_cl (Pow X) A (pwr X)" and 
          st:"E \<in> Pow X"  
  shows grill_reform1:"(X-E) \<notin> grill (Pow X) A \<longleftrightarrow> E \<in> A " and 
        grill_reform2:"(X-E) \<in> grill (Pow X) A \<longleftrightarrow> E \<notin> A"  and
        grill_reform3:"E \<in> grill (Pow X) A \<longleftrightarrow> (X-E) \<notin> A" and
        grill_reform4:"E \<notin> grill (Pow X) A \<longleftrightarrow> (X-E) \<in> A"
proof-
  obtain st2:"(X-E) \<in> Pow X" by simp
  show P0:"(X-E) \<notin> grill (Pow X) A \<longleftrightarrow> E \<in> A " 
  proof-
    have "(X-E) \<notin> grill (Pow X) A \<longleftrightarrow> \<not>({X-E}#A)"   
      by (simp add: grill_def)
    then show ?thesis 
      using  isotone_mesh2 fam st upcl by blast 
  qed
  show P1:"(X-E) \<in> grill (Pow X) A \<longleftrightarrow> E \<notin> A"
    using P0 by blast
  show P2:"E \<in> grill (Pow X) A \<longleftrightarrow> (X-E) \<notin> A"
    by (metis (no_types, lifting) Diff_Diff_Int PowD fam grill_def inf.absorb_iff2 isotone_mesh2 mem_Collect_eq st st2 upcl)
  show P3:"E \<notin> grill (Pow X) A \<longleftrightarrow> (X-E) \<in> A"
    by (simp add: P2)  
qed

lemma grill_reform5:
  assumes fam:"A \<in> Pow( Pow X)" and upcl:"is_ord_cl (Pow X) A (pwr X)" 
  shows "grill (Pow X) A = {E \<in> Pow X. (X-E) \<notin> A}"
  using assms grill_def[of "Pow X" A] grill_reform3[of A X] by auto        


lemma grill_anti1:
  "\<lbrakk>A \<in> Pow (Pow X); B \<in> Pow (Pow X); A \<subseteq> B\<rbrakk> \<Longrightarrow> grill (Pow X) B \<subseteq> grill (Pow X) A"
  by (simp add: grill_def mesh_single_iff subset_eq)
  
lemma grill_anti2:
  assumes anx:"A \<in> Pow (Pow X)" and bnx:"B \<in> Pow (Pow X)" and
          up1:"is_ord_cl (Pow X) A (pwr X)" and up2:"is_ord_cl (Pow X) B (pwr X)" and 
          sub:"grill (Pow X) B \<subseteq> grill (Pow X) A"
  shows "A \<subseteq> B"
proof
  fix a assume a0:"a \<in> A"  then obtain a1:"a \<in> Pow X" using anx by blast
  then obtain "(X-a) \<notin>  grill (Pow X) A" using grill_reform2[of A X a] a0 anx up1 by blast
  then obtain "(X-a) \<notin>  grill (Pow X) B" using sub by blast
  then show "a \<in> B" using grill_reform1[of B X a] bnx up2 a1  by fastforce
qed

lemma grill_upcl:
  assumes anx:"A \<in> Pow (Pow X)" shows "is_ord_cl (Pow X) (grill (Pow X) A) (pwr X)"
proof(rule is_ord_clI1)
  fix a b assume a0:"a \<in> grill (Pow X) A"  and b0:"b \<in> Pow X" and ab:"(a,b)\<in>pwr X" 
  then obtain C0:"a \<subseteq> b"
    using powrel8 by blast
  then show "b \<in> grill (Pow X) A"
  by (metis (no_types, lifting) CollectD CollectI a0 assms b0 grill_def mesh_sub) 
qed

lemma double_grill1:
  assumes anx:"A \<in> (Pow (Pow X))" 
  shows "grill (Pow X) (grill (Pow X) A) = {E \<in> Pow X. \<exists>a \<in> A. a \<subseteq>E}"
proof-
  let ?G1="grill (Pow X) A" let ?G2="grill (Pow X) ?G1" let ?R="{E \<in> Pow X. \<exists>a \<in> A. a \<subseteq> E}"
  have up1:"is_ord_cl (Pow X) ?G1 (pwr X)" 
    using grill_upcl assms by blast
  have gnx:"?G1 \<in> Pow (Pow X)"  
    by simp
  have "\<And>E. E \<in> Pow X \<Longrightarrow> E \<in> ?G2 \<longleftrightarrow> E \<in> ?R"
  proof-
    fix E assume enx:"E \<in> Pow X"
    have "E \<in> ?G2 \<longleftrightarrow> (X-E) \<notin> ?G1" 
      using grill_reform3[of ?G1 X E] gnx up1 enx by fastforce
    also have "... \<longleftrightarrow> \<not>({X-E}#A)"  
      by (simp add: grill_def)
    also have "... \<longleftrightarrow> (\<exists>a \<in> A. a \<subseteq> E)" 
      using anx mesh_single_iff by fastforce
    also have "... \<longleftrightarrow> E \<in> ?R"
       using enx by blast
    finally show "E \<in> ?G2 \<longleftrightarrow> E \<in> ?R"
    by blast
  qed
  then show ?thesis
    unfolding grill_def by blast
qed

lemma grill_of_filter:
  assumes A0:"\<F> \<in> pfilters_on (pwr X) (Pow X)"
  shows "\<F> \<subseteq> grill (Pow X) \<F>"
  by (meson Pow_iff assms dual_order.refl is_filterD1 mesh_iff_grill1 pfilter_mesh1 pfilters_on_iff setfilters3)


lemma double_grill2:
  assumes anx:"A \<in> (Pow (Pow X))" 
  shows "grill (Pow X) (grill (Pow X) A) = A \<longleftrightarrow> is_ord_cl (Pow X) A (pwr X)" (is "?L \<longleftrightarrow> ?R")
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
  assumes anx:"A \<in> (Pow (Pow X))"  and upcl:"is_ord_cl (Pow X) A (pwr X)"
  shows "grill (Pow X) (grill (Pow X) A) = A" 
  using assms double_grill2 by blast 

lemma grill_union_inter1:
  assumes A0:"\<AA> \<in> Pow (Pow (Pow X))" and A1:"\<AA> \<noteq> {}" and A2:"\<And>\<A>. \<A> \<in> \<AA> \<Longrightarrow> is_ord_cl (Pow X) \<A> (pwr X)"
  shows "grill (Pow X) (\<Inter>\<AA>) = \<Union>{grill (Pow X) \<A>|\<A>. \<A> \<in> \<AA>}" (is "?L = ?R")
proof-
  let ?I ="\<Inter>\<AA>"
  have B0:"?I \<in> (Pow (Pow X))" using A0 A1 by blast
  have B1:"?R \<subseteq> ?L" 
  proof-
    have B10:"\<And>\<A>. \<A> \<in> \<AA> \<Longrightarrow> grill (Pow X) \<A> \<subseteq> grill (Pow X) ?I"
    proof-
      fix \<A> assume A3:"\<A> \<in> \<AA>" 
      then obtain B100:"\<A> \<in> Pow (Pow X)" and B101:"is_ord_cl (Pow X) \<A> (pwr X)"  and B103:"?I \<subseteq> \<A>"  
        using A0 A2 by auto
      then show "grill (Pow X) \<A> \<subseteq> grill (Pow X) ?I"
      by (simp add: grill_anti1)
    qed
    then show ?thesis
      by blast
  qed
  have B2:"\<And>A. \<lbrakk>A \<in> Pow X; A \<notin> ?R\<rbrakk> \<Longrightarrow> A \<notin> ?L "
  proof-
    fix A assume B2A0:"A \<in> Pow X" and B2A1:"A \<notin> ?R"
    then obtain B22:"\<And>\<A>. \<A> \<in> \<AA> \<Longrightarrow> A \<notin> grill (Pow X) \<A>" 
      by blast
    then obtain B23:"\<And>\<A>. \<A> \<in>\<AA> \<Longrightarrow> (\<exists>B. B \<in> \<A> \<and> B \<inter> A = {})" 
      unfolding grill_def mesh_def using  B2A0 by fastforce
    define f where "f \<equiv> (\<lambda>\<A>. SOME B. B \<in> \<A> \<and> B \<inter> A = {})"
    have B24:"\<And>\<A>. \<A> \<in> \<AA> \<Longrightarrow> (f \<A>) \<in> \<A>  \<and> (f \<A>) \<inter> A = {}"
    proof-
      fix \<A> assume B24A0:"\<A> \<in> \<AA>" then obtain "(\<exists>B. B \<in> \<A> \<and> B \<inter> A = {})" 
        using B23 B24A0 by auto
      then show "(f \<A>) \<in> \<A>  \<and> (f \<A>) \<inter> A = {}" 
        unfolding f_def using someI_ex[of "\<lambda>B. B \<in> \<A> \<and> B \<inter> A = {}"] by blast
    qed
    have B25:"(\<Union>{f \<A> |\<A> . \<A>  \<in> \<AA>}) \<in> Pow X" 
      using B24 A0 by blast
    have B26:"\<And>\<A>. \<A> \<in> \<AA> \<Longrightarrow> (\<Union>{f \<A> |\<A> . \<A>  \<in> \<AA>}) \<in> \<A>"
    proof-
      fix \<A> assume B26A0:"\<A> \<in> \<AA>"  
      then obtain B260:"is_ord_cl (Pow X) \<A> (pwr X)"  
        using A2 by auto
      also obtain B261:"f \<A> \<in> \<A>" and B262:"f \<A> \<subseteq> (\<Union>{f \<A> |\<A> . \<A>  \<in> \<AA>})"  
         using B24 B26A0 by auto  
      then show "(\<Union>{f \<A> |\<A> . \<A>  \<in> \<AA>}) \<in> \<A>"
        using B25 calculation is_ord_clE1 pwr_memI by fastforce  
    qed
    then obtain B27:"(\<Union>{f \<A> |\<A> . \<A>  \<in> \<AA>}) \<in> (\<Inter>\<AA>)" and B28:"A \<inter> (\<Union>{f \<A> |\<A> . \<A>  \<in> \<AA>}) = {}"  
      using B24 by blast
    then show "A \<notin> ?L" 
      unfolding grill_def mesh_def by auto
  qed
  have B3:"?R \<subseteq> Pow X"   
    using grill_space by blast
  from B2 B3 have B4:"?L \<subseteq> ?R" 
    unfolding grill_def mesh_def by blast
  from B1 B4 show ?thesis 
    by blast
qed

lemma grill_union_inter:
  assumes A0:"\<AA> \<in> Pow (Pow (Pow X))" and A1:"\<AA> \<noteq> {}"
  shows "grill (Pow X) (\<Union>\<AA>) = \<Inter>{grill (Pow X) \<A>|\<A>. \<A> \<in> \<AA>}" (is "?L =?R")
  unfolding grill_def using assms apply(auto, simp add: mesh_single_iff)
  unfolding mesh_def using assms apply(auto) by(blast)

lemma ideals_filter_grill:
  assumes A0:"\<G> \<in> (Pow (Pow X))"  and A1:"\<G> \<noteq> {}" and A2:"{} \<notin> \<G>"
  shows "(\<exists>\<F> \<in> pfilters_on (pwr X) (Pow X). \<G> = grill (Pow X) \<F>) \<longleftrightarrow>   (\<forall>A \<in> Pow X. \<forall>B \<in> Pow X. A \<union> B \<in> \<G> \<longrightarrow> A \<in> \<G> \<or> B \<in> \<G>) \<and> is_ord_cl (Pow X) \<G> (pwr X)"
  (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L then obtain F where B0:"F \<in> pfilters_on (pwr X) (Pow X)" and B1:" \<G> = grill (Pow X) F" by auto
  from B0 have B2:"F \<in> Pow (Pow X)"
    using grill_of_filter in_mono by fastforce
  from B1 B2 obtain B3:" is_ord_cl (Pow X) \<G> (pwr X)" 
    using grill_upcl[of F X] by blast
  have B4:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X; A \<notin> \<G>; B \<notin> \<G>\<rbrakk> \<Longrightarrow> A \<union> B \<notin> \<G>"
  proof-
    fix A B assume B4A0:"A \<in> Pow X" and B4A1:"B \<in> Pow X" and B4A2:"A \<notin> \<G>" and B4A3:"B \<notin> \<G>"
    then obtain B40:"A \<notin> grill (Pow X) F" and B41:"B \<notin> grill (Pow X) F" 
      using B1 by auto
    then obtain Fa Fb where B42:"Fa \<in> F" and B43:"Fb \<in> F" and B44:"Fa \<inter> A = {}" and B45:"Fb \<inter> B = {}"
      by (metis B0 B2 B4A0 B4A1 Diff_disjoint grill_reform4 inf_commute is_filterD1 pfilters_on_iff setfilters3)
    then obtain "Fa \<inter> Fb \<in> F" and "(Fa \<inter> Fb) \<inter> (A \<union> B) = {}"
      by (metis B0 boolean_algebra.de_Morgan_disj inf_mono inf_shunt pfilters_on_iff sets_pfilter3)
    then obtain "A \<union> B \<notin> grill (Pow X) F" 
       by (metis A0 B1 B2 Int_absorb inf.absorb_iff2 mesh_def mesh_iff_grill2)
    then show "A \<union> B \<notin> \<G>" 
      using B1 by auto
  qed
  then have B5:"(\<forall>A \<in> Pow X. \<forall>B \<in> Pow X. A \<union> B \<in> \<G> \<longrightarrow> A \<in> \<G> \<or> B \<in> \<G>)" by blast
  then show ?R  
    using B3 by blast
next
  assume R:?R then obtain B0:"\<G> = grill (Pow X) (grill (Pow X) \<G>)" 
    using A0 double_grill21[of \<G> X] by auto
  let ?F="grill (Pow X) \<G>"
  have B1:"is_pfilter (pwr X) (Pow X) ?F"
  proof(rule is_pfilterI1)
    show "is_filter (pwr X) (Pow X) ?F"
    proof(rule is_filterI1)
      show P0:"?F \<noteq> {}"
        by (metis A0 A2 B0 Pow_bottom empty_iff grill_reform3 grill_upcl)
      show P1:"?F \<subseteq> Pow X" 
        by simp
      show P2:"is_ord_cl (Pow X) ?F (pwr X)"
        using A0 grill_upcl by blast 
      show "is_dir ?F (dual (pwr X))"
      proof(rule is_dirI1)
        fix a b assume amem:"a \<in> ?F" and bmem:"b \<in> ?F" 
        then obtain B2:"is_ord_cl (Pow X) ?F (pwr X)" and B3:"a \<in> Pow X" and B4:"b \<in> Pow X"
          using P1 P2 by blast 
        then obtain B5:"(X-a) \<notin> \<G>" and B6:"(X-b) \<notin> \<G>"
          by (metis A0 R amem bmem grill_reform4)
        then obtain B7:"(X-a) \<union> (X-b) \<notin> \<G>"   
          using R by blast
        then obtain B8:"(X-((X-a) \<union> (X-b))) \<in> grill (Pow X) \<G>"
          by (meson A0 Diff_subset PowI R Un_least grill_reform1)
        then obtain B9:"a \<inter> b \<in> ?F" 
           by (metis B3 B4 Diff_Diff_Int Diff_Un PowD inf.absorb2)
        then show "\<exists>c \<in> ?F. (a, c) \<in> dual (pwr X) \<and> (b, c) \<in> dual (pwr X)"
          by (meson B3 B4 PowD converse.simps inf_le2 inf_sup_ord(1) pwr_mem_iff) 
      qed
    qed
    show "Pow X \<noteq> grill (Pow X) \<G>"
      using A1 grill_def mesh_single_iff by fastforce
  qed
  then show ?L 
  using B0 pfilters_on_iff by blast
qed

lemma maybe_tho:
  assumes A0:"is_lattice R X" and A1:"is_greatest R X top" and A2:"is_filter R X F" and A3:"pord R X"
  shows "F = Sup (pwr X) (filters_on R X) {(lcro R X f)|f. f \<in>F}"
proof-
  from A0 A1 A3 obtain B0:"is_clattice (pwr X) (filters_on R X)" and B1:"compactly_generated (pwr X)(filters_on R X)" 
    using lattice_filters_complete[of X R top] filters_on_lattice_compactgen[of X R top] by blast
  obtain por1:"pord (pwr X) (filters_on R X)" and por2:"pord (pwr X) ( (Pow X))"
    by (meson Pow_iff filters_on_iff is_filterD1 powrel6 powrel7 pwr_memI refl_def subsetI)
  have B2:"F= Sup (pwr X) (filters_on R X) {k \<in> compact_elements (pwr X) (filters_on R X). (k, F)\<in>pwr X}" 
    using A2 B0 B1 compact_dense[of "pwr X" "filters_on R X" F] por1 filters_on_iff by blast
  have B3:"\<And>f. f \<in> compact_elements (pwr X) (filters_on R X) \<Longrightarrow> f \<in> {lcro R X x|x. x \<in> X}"
  proof-
    fix f assume C0:"f \<in> compact_elements (pwr X) (filters_on R X)" 
   then obtain "is_filter R X f"
    by (meson compact_element_memD2 filters_on_iff) 
   then obtain x where "lcro R X x = f"  using A0 A1 principal_filters_compact
    by (metis A3 C0 compact_element_memD1 compact_element_memD2 lattD1)
  then show  "f \<in> {lcro R X x|x. x \<in> X}"
    using A0 A1 A3 C0 compact_element_memD1 compact_element_memD2 lattD1 principal_filters_compact by fastforce
  qed
  have B4:"\<And>f.  f \<in> {lcro R X x|x. x \<in> X} \<Longrightarrow> f \<in> compact_elements(pwr X) (filters_on R X) "
     using A0 A1 principal_filters_compact[of R X top]  compact_elements_mem_iff1 A3 filters_on_def lcro_filter by fastforce 
  have B5:" {lcro R X x|x. x \<in> X} =  compact_elements (pwr X  )(filters_on R X)" 
    using B3 B4 by blast
  have B7:"\<And>z. \<lbrakk>z \<in> X; (lcro R X z, F)\<in>pwr X\<rbrakk> \<Longrightarrow> z \<in> F"
    by (meson A3 in_mono lcro_memI1 powrel8)
  have B7b:"\<And>z. \<lbrakk>z \<in> X; lcro R X z \<subseteq> F\<rbrakk> \<Longrightarrow> z \<in> F"
    by (simp add: A3 lcro_memI1 subsetD)
  have B8:"\<And>z. \<lbrakk>z \<in> X; z \<in> F\<rbrakk> \<Longrightarrow> (lcro R X z, F)\<in>pwr X "
    by (meson A2 is_filterD1 is_ord_clE1 lcroD1 pwr_mem_iff subsetI)
  have B8b:"\<And>z. \<lbrakk>z \<in>X; z \<in> F\<rbrakk>\<Longrightarrow>lcro R X z \<subseteq> F"
    using B8 powrel8 by blast
  have B9:"{lcro R X x|x. x \<in> X}  \<subseteq> Pow X"
    using lcroD1 by fastforce
  have B10:"{k \<in>{lcro R X x|x. x \<in> X}. (k,F)\<in>pwr X}  \<subseteq> Pow X"
    using pwr_memD by fastforce
  have B10b:"{k \<in>{lcro R X x|x. x \<in> X}. k \<subseteq> F} \<subseteq> Pow X"
    using B9 by blast
  have B11:"{k \<in>{lcro R X x|x. x \<in> X}. (k,F)\<in>pwr X} \<subseteq> {lcro R X x|x. x \<in> F}"
    using B7 by blast
  have B12:"F \<subseteq> X"
    using A2 is_filterD1 by blast  
  have B13:"{lcro R X x|x. x \<in> F} \<subseteq> {k \<in>{lcro R X x|x. x \<in> X}. (k,F)\<in>pwr X} "
    using B12 B8 by auto
  have B14:"{lcro R X x|x. x \<in> F} = {k \<in>{lcro R X x|x. x \<in> X}. (k,F)\<in>pwr X}" 
    using B11 B13 by auto
  have B15:"F= Sup (pwr X) (filters_on R X) {k \<in>{lcro R X x|x. x \<in> X}. (k,F)\<in>pwr X}" 
     using B2 B5 by presburger
  also have B16:"... = Sup (pwr X )(filters_on R X)  {(lcro R X f)|f. f \<in>F}"
     using B14 by auto
  finally show ?thesis
    by simp
qed

lemma filter_on_set_ne:
  "\<F> \<in> pfilters_on (pwr X) (Pow X) \<Longrightarrow> {} \<notin> \<F>"
  by (simp add: pfilters_on_iff sets_pfilter5)

lemma filter_mem_mesh:
  "\<lbrakk>\<F> \<in> pfilters_on (pwr X) (Pow X); A \<in> \<F>\<rbrakk> \<Longrightarrow> {A}#\<F>"
  by (meson dual_order.refl mesh_def mesh_singleI pfilter_mesh1)


lemma Cl_to_Nhoods1:
  assumes A0:"x \<in> X" 
  shows "(NCl Cl X)``{x} = (grill (Pow X) ((converse Cl)``{x}))"
  unfolding NCl_def grill_def using assms by auto

lemma Cl_to_Nhoods2:
    assumes A0:"x \<in> X" 
    shows "(converse (ClN N X))``{x} = grill (Pow X) (N``{x})"
    unfolding ClN_def grill_def using assms by auto
  
lemma Nhoods_to_Adh0:
  assumes A0:"\<E> \<in> pfilters_on (pwr X) (Pow X)" and A1:"x \<in> X" and A2:"\<And>x V. (x, V) \<in> N \<Longrightarrow> x \<in> X \<and> V \<in> Pow X"
  shows "x \<in> (AdhN N X)``{\<E>} \<longleftrightarrow> (N``{x})#\<E> " 
  unfolding AdhN_def mesh_def using assms by auto

lemma Nhoods_to_Adh1a: 
  assumes A0:"x \<in> X" and A1:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in>pfilters_on (pwr X) (Pow X)" and A2:"Adh \<noteq> {}"
  shows "(NAdh Adh X)``{x} \<subseteq> \<Inter>{grill (Pow X) \<E>|\<E>. (\<E>, x) \<in> Adh}"
  unfolding NAdh_def grill_def mesh_def using assms by blast
  
lemma Nhoods_to_Adh1b: 
  assumes A0:"x \<in> X" and A1:"A \<in> Pow X" and A2:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in> pfilters_on (pwr X) (Pow X)" and A3:"Adh \<noteq> {}" and
          A4:"(x, A) \<in> (NAdh Adh X)"
  shows " (\<And>\<E>. \<lbrakk>\<E> \<in> Pow (Pow X); (\<E>, x) \<in> Adh\<rbrakk> \<Longrightarrow> {A}#\<E>)"
  unfolding NAdh_def mesh_def using assms by(auto,metis (no_types, lifting) A2 CollectD NAdh_def case_prodD mesh_singleE) 

  
lemma Nhoods_to_Adh1c: 
  assumes A0:"x \<in> X" and A1:"A \<in> Pow X" and A2:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in> Pow (Pow X)" and A3:"Adh \<noteq> {}" and
          A4:"(\<And>\<E>. \<lbrakk>\<E> \<in> Pow (Pow X); (\<E>, x) \<in> Adh\<rbrakk> \<Longrightarrow> {A}#\<E>)"
  shows "(x, A) \<in> (NAdh Adh X)"
  unfolding NAdh_def mesh_def using assms by(simp add:mesh_def)

lemma Nhoods_to_Adh1d: 
  assumes A0:"x \<in> X" and A1:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in> pfilters_on (pwr X) (Pow X)" and A2:"Adh \<noteq> {}"
  shows "\<And>E.  \<lbrakk>E \<in> Pow X; E \<notin> (NAdh Adh X)``{x}\<rbrakk> \<Longrightarrow> E \<notin>  \<Inter>{grill (Pow X) \<E>|\<E>. (\<E>, x) \<in> Adh}"
  unfolding NAdh_def grill_def mesh_def using assms by(auto, smt (verit, ccfv_SIG) mem_Collect_eq)

lemma Nhoods_to_Adh1: 
  assumes A0:"x \<in> X" and A1:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in>pfilters_on (pwr X) (Pow X)" and A2:"Adh \<noteq> {}" and A3:"(converse Adh)``{x} \<noteq> {}"
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
  assumes A0:"\<E> \<in>pfilters_on (pwr X) (Pow X)" and A1:"x \<in> X" and A2:"\<And>x V. (x, V) \<in> N \<Longrightarrow> x \<in> X \<and> V \<in> Pow X"
  shows "x \<in> (LimN N X)``{\<E>} \<longleftrightarrow> (N``{x}) \<subseteq> \<E> " 
  unfolding LimN_def mesh_def using assms by auto


lemma Nhoods_to_Lim1: 
  assumes A0:"x \<in> X" and A1:"\<And>x \<E>. (\<E>, x) \<in>Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> pfilters_on (pwr X) (Pow X)" and A2:"Lim \<noteq> {}" and A3:"(converse Lim)``{x} \<noteq> {}"
  shows "(NLim Lim X)``{x} = (\<Inter>{\<E>. (\<E>, x) \<in> Lim})" (is "?L = ?R")
proof 
  show "?L \<subseteq> ?R" unfolding NLim_def using assms by(auto)
next
  show "?R \<subseteq> ?L" 
  proof-
    have B0:"\<And>A. \<lbrakk>A \<in> Pow X; A \<notin> ?L\<rbrakk> \<Longrightarrow> A \<notin> ?R"
       unfolding NLim_def using assms by auto
    have B1:"?L \<subseteq> Pow X" 
      unfolding NLim_def using assms by(auto)
    obtain ne:"{\<E>. (\<E>, x) \<in> Lim} \<noteq> {}" 
      using A3 by blast
    then obtain B2:"?R \<subseteq> Pow X" 
      using A1 pfilters_on_iff sets_pfilter6 by fastforce 
    from B1 B2 B0 show ?thesis  
       by (meson subset_eq)
    qed
qed



lemma Nhoods_to_Lim1_via_cl: 
  assumes A0:"x \<in> X" and 
          A1:"\<And>x \<E>. (\<E>, x) \<in>Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> pfilters_on (pwr X) (Pow X)" and 
          A2:"Lim \<noteq> {}" and 
          A3:"(converse Lim)``{x} \<noteq> {}"
  shows "\<And>V. \<lbrakk>V \<in> Pow X\<rbrakk> \<Longrightarrow> (x, V) \<in> (NLim Lim X) \<longleftrightarrow> (X-V, x) \<notin> (ClLim Lim X) "
proof-
  fix V assume vmem:"V \<in> Pow X"
  have lfil:"\<And>\<F>. \<F> \<in> converse (Lim)``{x} \<Longrightarrow>  \<F>  \<in> Pow (Pow X) \<and> is_ord_cl (Pow X)  \<F> (pwr X)"
    by (meson A1 Image_singleton_iff PowI converse.cases is_filterD1 pfilters_on_iff setfilters3)
  have B0:"(x, V) \<in> (NLim Lim X) \<longleftrightarrow> (\<forall>\<F> \<in> converse (Lim)``{x}. V \<in> \<F>)" 
    unfolding NLim_def using A0 vmem A1 by blast
  also have B1:"...                   \<longleftrightarrow> (\<forall>\<F> \<in> converse (Lim)``{x}. (X-(X-V)) \<in> \<F>)" 
    using double_diff vmem by fastforce
  also have B2:"...                   \<longleftrightarrow> \<not>(\<exists>\<F> \<in> converse (Lim)``{x}. (X-(X-V)) \<notin> \<F>)"  
    by blast
  also have B3:"...                   \<longleftrightarrow> \<not>(\<exists>\<F> \<in> converse (Lim)``{x}. (X-(X-(X-V))) \<in> grill (Pow X) \<F>)"
    by (metis Diff_subset PowI grill_reform2 lfil)  
  also have B4:"...                   \<longleftrightarrow> \<not>(\<exists>\<F> \<in> converse (Lim)``{x}. (X-V) \<in> grill (Pow X) \<F>)" 
    by (simp add: double_diff)  
  also have B5:"...                   \<longleftrightarrow> \<not>(\<exists>\<F> \<in> converse (Lim)``{x}. {(X-V)}#\<F>)" 
    by (simp add: grill_def) 
  also have B6:"...                   \<longleftrightarrow> (X-V, x) \<notin> (ClLim Lim X)" 
    unfolding ClLim_def using A0 A1 vmem by blast
  finally show "(x, V) \<in> (NLim Lim X) \<longleftrightarrow> (X-V, x) \<notin> (ClLim Lim X)" 
    by blast
qed


lemma Cl_to_Adh1:
  assumes A0:"\<And>A x. (A, x) \<in> Cl \<Longrightarrow> A \<in> Pow X \<and> x \<in> X" and A1:"\<F> \<in> pfilters_on (pwr X) (Pow X)"
  shows "(AdhCl Cl X)``{\<F>} = \<Inter>{Cl``{A}|A. A \<in> \<F>}"
  unfolding AdhCl_def using assms apply(auto)
  apply (meson pfilters_on_iff setfilters0 setfilters3)
  apply (metis Image_singleton_iff equals0I is_filterD1 is_pfilterD1 pfilters_on_iff)
  by blast

lemma Cl_to_Adh2:
  assumes A0:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (pwr X) (Pow X))"  and A1:"A \<in> Pow X"
  shows "(ClAdh Adh X)``{A} = \<Union>{Adh``{\<F>}|\<F>. \<F> \<in> pfilters_on (pwr X) (Pow X) \<and> A \<in> \<F>}"
  unfolding ClAdh_def using assms by auto
   
  
lemma Cl_to_Lim1:
  assumes A0:"\<And>A x. (A, x) \<in> Cl \<Longrightarrow> A \<in> Pow X \<and> x \<in> X" and A1:"\<F> \<in> pfilters_on (pwr X) (Pow X)"
  shows "(LimCl Cl X)``{\<F>} = \<Inter>{Cl``{A}|A. A \<in> Pow X \<and> {A}#\<F>}"
  unfolding LimCl_def mesh_def using assms apply(auto)
  apply (metis Image_singleton_iff empty_subsetI filter_on_set_ne pfilters_on_iff setfilters0 setfilters3 sets_pfilter3)
  by blast 
    
  
lemma Cl_to_Lim2:
  assumes A0:"\<And>x \<E>. (\<E>, x) \<in> Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (pwr X) (Pow X))"  and A1:"A \<in> Pow X"
  shows "(ClLim Lim X)``{A} = \<Union>{Lim``{\<F>}|\<F>. \<F> \<in> pfilters_on (pwr X) (Pow X) \<and> {A}#\<F>}"
  unfolding ClLim_def using assms by(auto)

lemma Adh_to_Lim1:
  assumes A0:"\<And>x \<E>. (\<E>, x) \<in> Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (pwr X) (Pow X))"  and A1:"\<F> \<in> pfilters_on (pwr X) (Pow X)"
  shows "(AdhLim Lim X)``{\<F>} = \<Union>{Lim``{\<G>}|\<G>. \<G> \<in>  pfilters_on (pwr X) (Pow X) \<and> \<G>#\<F>}"
  unfolding AdhLim_def using assms by(auto)


lemma Adh_to_Lim2:
  assumes A0:"\<And>x \<E>. (\<E>, x) \<in> Adh \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (pwr X) (Pow X))"  and A1:"\<F> \<in> pfilters_on (pwr X) (Pow X)"
  shows "(LimAdh Adh X)``{\<F>} = \<Inter>{Adh``{\<G>}|\<G>. \<G> \<in>  pfilters_on (pwr X) (Pow X) \<and> \<G>#\<F>}"
  unfolding LimAdh_def using assms by(auto,metis ImageE pfilter_mesh1 subset_refl)

lemma cl_nh_mono1:
  assumes is_cl:"\<And>A x. (A, x) \<in> Cl \<Longrightarrow> A \<in> Pow X \<and> x \<in> X"  and  iso:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow> Cl``{A} \<subseteq> Cl``{B}" 
  shows "\<And>x A. \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow> (A, x) \<in> (ClN (NCl Cl X) X) \<longleftrightarrow> (A, x) \<in> Cl"
proof-
  fix x A assume xmem:"x \<in> X" and amem:"A \<in> Pow X"
  have B0:"(NCl Cl X)``{x} = (grill (Pow X) ((converse Cl)``{x}))" 
     by (simp add: Cl_to_Nhoods1 xmem)
  have B1:"(converse (ClN (NCl Cl X) X))``{x} = grill (Pow X) ((NCl Cl X)``{x})" 
    by (simp add:Cl_to_Nhoods2 xmem)
  have B2:"(converse (ClN (NCl Cl X) X))``{x} = grill (Pow X) ((grill (Pow X) ((converse Cl)``{x})))" 
     by (simp add: B1 Cl_to_Nhoods1 xmem)
  have B3:"\<And>A1 A2. \<lbrakk>A2 \<in> Pow X; A1 \<in> ((converse Cl)``{x}); A1 \<subseteq> A2\<rbrakk> \<Longrightarrow> A2 \<in> ((converse Cl)``{x})"
  proof-
    fix A1 A2 assume B30:"A2 \<in> Pow X" and B31:"A1 \<in> ((converse Cl)``{x})" and B32:"A1 \<subseteq> A2"
    from B31 is_cl obtain B33:"(A1, x) \<in> Cl" and B34:"A1 \<in> Pow X"   
      by blast
    then obtain B35:"Cl``{A1} \<subseteq> Cl``{A2}" 
      using iso B34 B32 B30  by force 
    then obtain "(A2, x) \<in> Cl"  
      using  B33 by blast
    then show "A2 \<in> ((converse Cl)``{x})" 
      by simp
  qed
  then obtain B4:"is_ord_cl (Pow X) ((converse Cl)``{x}) (pwr X)"
    by (meson is_ord_cl_def powrel8) 
  have B5:"grill (Pow X) ((grill (Pow X) ((converse Cl)``{x}))) = (converse Cl)``{x}" 
    using double_grill2 xmem  by (metis B4 Image_singleton_iff Pow_iff converseD is_cl subsetI)
  have B6:"(x, A) \<in> (converse (ClN (NCl Cl X) X)) \<longleftrightarrow> (x, A) \<in> converse Cl"  
    using B2 B5 by blast
  then show "(A, x) \<in> (ClN (NCl Cl X) X) \<longleftrightarrow> (A, x) \<in> Cl" 
    by simp
qed

lemma cl_nh_mono2:
  assumes is_nh:"\<And>x V. (x, V) \<in> N \<Longrightarrow> x \<in> X \<and> V \<in> Pow X"  and  upcl:"\<And>x A B. \<lbrakk>(x, A) \<in> N ; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow>(x, B) \<in> N" 
  shows "\<And>x A. \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow> (x, A) \<in> (NCl (ClN N X) X) \<longleftrightarrow> (x, A) \<in> N"
proof-
  fix x A assume xmem:"x \<in> X" and amem:"A \<in> Pow X"
  have ordcl:"is_ord_cl (Pow X) (N``{x}) (pwr X)"
    by (meson Image_singleton_iff is_ord_cl_def powrel8 upcl) 
  have B0:"(converse (ClN N X))``{x} = grill (Pow X) (N``{x})"  
    by (simp add: Cl_to_Nhoods2 xmem)
  have B1:"(NCl (ClN N X) X)``{x} = grill (Pow X) ((converse (ClN N X))``{x})" 
    by (simp add: Cl_to_Nhoods1 xmem)
  also have B2:"...               = grill (Pow X) (grill (Pow X) (N``{x}))" 
     using B1 B0 by auto 
  also have B3:"...               = N``{x}" 
    using ordcl double_grill2 by (metis Image_singleton_iff Pow_iff is_nh subsetI)
  finally show "(x, A) \<in> (NCl (ClN N X) X) \<longleftrightarrow> (x, A) \<in> N" 
     by blast
qed

lemma nh_lim_prtp1:
  assumes is_prtp:"\<And>x. x \<in> X \<Longrightarrow> (N``{x}) \<in> pfilters_on (pwr X) (Pow X)" 
  shows "\<And>x A. \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow> (x, A) \<in> NLim (LimN N X) X \<longleftrightarrow> (x, A) \<in> N"
proof-
  fix x A assume xmem:"x \<in> X" and amem:"A \<in> Pow X"
  show "(x, A) \<in> NLim (LimN N X) X \<longleftrightarrow> (x, A) \<in> N" (is "?L \<longleftrightarrow> ?R")
  proof
    assume L:?L then show ?R 
    unfolding NLim_def LimN_def using xmem amem is_prtp by auto
  next
    assume R:?R then show ?L 
    unfolding NLim_def LimN_def using xmem amem is_prtp by auto
  qed
qed

lemma nh_lim_prtp2:
  assumes centered:"\<And>x. x \<in> X \<Longrightarrow> (lcro (pwr X) (Pow X) {x}, x) \<in> Lim" and
          upclosed:"\<And>\<G> \<F> x. \<lbrakk>\<G> \<in> pfilters_on (pwr X) (Pow X); (\<F>, x) \<in> Lim;  \<F> \<subseteq> \<G>\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> Lim" and
          vicinity:"\<And>x. x \<in> X \<Longrightarrow> (\<Inter>{\<F>. (\<F>, x) \<in> Lim}, x) \<in> Lim " and  
          is_limit:"\<And>x \<E>. (\<E>, x) \<in> Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (pwr X) (Pow X))" 
  shows "\<And>\<F> x. \<lbrakk>\<F> \<in> pfilters_on (pwr X) (Pow X); x \<in> X\<rbrakk> \<Longrightarrow>(\<F>, x) \<in> LimN (NLim Lim X) X \<longleftrightarrow> (\<F>, x) \<in> Lim"
proof-
  fix \<F> x assume pfil:"\<F> \<in> pfilters_on (pwr X) (Pow X)" and xmem:"x \<in> X" 
  show "(\<F>, x) \<in> LimN (NLim Lim X) X \<longleftrightarrow> (\<F>, x) \<in> Lim" (is "?L \<longleftrightarrow> ?R")
  proof
    assume L:"(\<F>, x) \<in> LimN (NLim Lim X) X"
    from vicinity xmem obtain smallest:"(\<Inter>{\<F>. (\<F>, x) \<in> Lim}, x) \<in> Lim" 
      by auto
    from L have B0:"(\<And>A. \<lbrakk>A \<in>  Pow X; (x, A) \<in> (NLim Lim X)\<rbrakk> \<Longrightarrow> A \<in> \<F>)" 
      unfolding LimN_def by auto
    have B1:"\<Inter>{\<F>. (\<F>, x) \<in> Lim} = (NLim Lim X)``{x}"
      unfolding NLim_def using is_limit vicinity pfil B0 xmem centered
      proof -
        have ?thesis
        by (metis Image_singleton_iff Nhoods_to_Lim1 all_not_in_conv assms(4) converse_iff smallest)
        then show "\<Inter> {A. (A, x) \<in> Lim} = {(a, A). A \<in> Pow X \<and> a \<in> X \<and> (\<forall>Aa. Aa \<in> pfilters_on (pwr X) (Pow X) \<and> (Aa, a) \<in> Lim \<longrightarrow> A \<in> Aa)} `` {x}"
        by (simp add: NLim_def)
      qed
    also have B2:"... \<subseteq> \<F>" 
      unfolding NLim_def using B1 B0 L is_limit  by blast
    finally show "(\<F>, x) \<in> Lim" 
      using upclosed smallest pfil by blast 
  next
    assume R:"(\<F>, x) \<in> Lim" then show "?L" 
    unfolding LimN_def NLim_def using pfil xmem by auto
  qed
qed


lemma lorc_pfilter:
  assumes A0:"x \<in> X" and A1:"\<not>(is_least R X x)" and A2:"pord R X"
  shows "is_pfilter R X (lcro R X x)"
proof(rule is_pfilterI1)
  show "is_filter R X (lcro R X x)"
    by (simp add: A0 A2 lcro_filter) 
  show "X \<noteq> (lcro R X x)"
    by (metis A0 A1 converseI greatestI2 lcroD1)
qed


lemma lorc_set_pfilter:
  assumes A0:"A \<in> Pow X" and A1:"A \<noteq> {}" 
  shows "is_pfilter (pwr X) (Pow X) (lcro (pwr X) (Pow X) A)"
  by (metis A0 A1 Pow_bottom bot.extremum_uniqueI lcroD1 lcro_filter powrel1 powrel2 powrel3 powrel8 refl_def refl_onD setfilters3)


lemma adh_nh_mono2:
  assumes is_nh:"\<And>x V. (x, V) \<in> N \<Longrightarrow> x \<in> X \<and> V \<in> Pow X \<and> V \<noteq> {}"  and 
          upcl:"\<And>x A B. \<lbrakk>(x, A) \<in> N ; B \<in> Pow X; A \<subseteq> B\<rbrakk> \<Longrightarrow>(x, B) \<in> N" and
          ntr:"\<And>x. x \<in> X \<Longrightarrow> N``{x} \<noteq> {}"
  shows "\<And>x A. \<lbrakk>x \<in> X; A \<in> Pow X\<rbrakk> \<Longrightarrow> (x, A) \<in> (NAdh (AdhN N X) X) \<longleftrightarrow> (x, A) \<in> N"
proof-
  fix x A assume xmem:"x \<in> X" and amem:"A \<in> Pow X" 
  have "(x, A) \<in> (NAdh (AdhN N X) X) \<longleftrightarrow> (\<forall>\<F> \<in> pfilters_on (pwr X) (Pow X). (\<F>, x) \<in> (AdhN N X) \<longrightarrow> {A}#\<F>)"
    unfolding NAdh_def using amem xmem by blast
  also have "... \<longleftrightarrow>  (\<forall>\<F> \<in> pfilters_on (pwr X) (Pow X). (\<forall>V \<in> Pow X. (x, V) \<in> N \<longrightarrow> {V}#\<F>) \<longrightarrow> {A}#\<F>)"
    unfolding AdhN_def using amem xmem by auto
  also have "... \<longleftrightarrow> (\<forall>\<F> \<in> pfilters_on (pwr X) (Pow X). (N``{x})#\<F> \<longrightarrow> {A}#\<F>)"
    by (metis Image_singleton_iff is_nh mesh_def singletonD singletonI)
  finally have P0:"(x, A) \<in> (NAdh (AdhN N X) X) \<longleftrightarrow> (\<forall>\<F> \<in> pfilters_on (pwr X) (Pow X). (N``{x})#\<F> \<longrightarrow> {A}#\<F>)"  by blast
  show "(x, A) \<in> (NAdh (AdhN N X) X) \<longleftrightarrow> (x, A) \<in> N" (is "?L \<longleftrightarrow> ?R")
  proof
    assume R:?R 
    have B0:"\<And>\<F>. \<lbrakk>\<F> \<in> pfilters_on (pwr X) (Pow X); (\<F>, x) \<in> (AdhN N X)\<rbrakk> \<Longrightarrow> {A}#\<F>"
    proof-
      fix \<F> assume fmem:"\<F> \<in> pfilters_on (pwr X) (Pow X)" and fadh:"(\<F>, x) \<in> (AdhN N X)"
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
      then obtain B2:"{(X-A)}#(N``{x}) "
        by (smt (verit, best) Diff_Int2 Diff_Int_distrib2 Diff_eq_empty_iff Image_singleton_iff Int_absorb1 PowD is_nh mesh_singleI) 
      then have B3:"(lcro (pwr X) (Pow X) (X-A))#(N``{x})"
        unfolding mesh_def lcro_def  using powrel8 by fastforce 
      have B4:"\<not>((lcro (pwr X) (Pow X) (X-A))#{A})"
        by (meson Diff_disjoint Diff_subset Pow_iff lcroI1 mesh_def mesh_sym powrel3 refl_onD singletonI) 
      obtain B5:"(X-A) \<in> Pow X" and B6:"(X-A) \<noteq> {}" 
         by (metis B2 Diff_disjoint Diff_empty Diff_subset Pow_iff ex_in_conv mesh_singleE ntr xmem) 
      then obtain B7:"(lcro (pwr X) (Pow X) (X-A)) \<in> pfilters_on (pwr X) (Pow X)"
        by (simp add: lorc_set_pfilter pfilters_on_iff)
      from B7 B3 B4 have B8:"\<not>(\<forall>\<F> \<in> pfilters_on (pwr X) (Pow X). (N``{x})#\<F> \<longrightarrow> {A}#\<F>)"
         using mesh_sym by blast  
      then show "\<not>(?L)" 
      using P0 by blast
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
    then obtain \<F> where f1:"\<F> \<in> pfilters_on (pwr X) (Pow X)" and f2:"A \<in> \<F>" and f3:"(\<F>, x) \<in> AdhCl Cl X" 
      unfolding ClAdh_def using xmem amem L  by blast
    have f4:"\<And>B. B \<in> \<F> \<Longrightarrow> B \<in> Pow X"
      using f1 pfilters_on_iff sets_pfilter6 by blast  
    have f5:"\<And>B. B \<in> \<F> \<Longrightarrow> (B, x) \<in> Cl" using f3 unfolding AdhCl_def using xmem f1 f4  by fastforce
    then show ?R using f2  by auto
  next
    assume R:?R
    let ?F="lcro (pwr X) (Pow X) A"
    have B0:"?F \<in> pfilters_on (pwr X) (Pow X)" 
       by (metis Image_singleton_iff R amem cl_emp equals0D lorc_set_pfilter pfilters_on_iff)
    have B1:"\<And>B. B \<in> ?F \<Longrightarrow> (B, x) \<in> Cl"
      by (meson Image_singleton_iff R is_cl is_iso lcroD1 powrel8 subsetD)
    have B2:"(?F, x) \<in>  (AdhCl Cl X)"  
      by (simp add: AdhCl_def B0 B1 xmem)
    have B3:"A \<in> ?F"
      by (meson amem lcroI1 powrel3 refl_onD) 
    have B4:"(\<exists>\<F> \<in> pfilters_on (pwr X) (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> (AdhCl Cl X))"  
      using B0 B2 B3 by blast
    show ?L 
      using B4 xmem amem unfolding ClAdh_def by blast
  qed
qed


lemma cl_lim_prtp2:
  assumes centered:"\<And>x. x \<in> X \<Longrightarrow> (lcro (pwr X) (Pow X) {x}, x) \<in> Lim" and
          upclosed:"\<And>\<G> \<F> x. \<lbrakk>\<G> \<in> pfilters_on (pwr X) (Pow X); (\<F>, x) \<in> Lim;  \<F> \<subseteq> \<G>\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> Lim" and
          vicinity:"\<And>x. x \<in> X \<Longrightarrow> (\<Inter>{\<F>. (\<F>, x) \<in> Lim}, x) \<in> Lim " and  
          is_limit:"\<And>x \<E>. (\<E>, x) \<in> Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (pwr X) (Pow X))" 
  shows "\<And>\<F> x. \<lbrakk>\<F> \<in> pfilters_on (pwr X) (Pow X); x \<in> X\<rbrakk> \<Longrightarrow> (\<F>, x) \<in> Lim \<longleftrightarrow> (\<F>, x) \<in> LimCl (ClLim Lim X) X"
proof-
  fix \<F> x assume pfil:"\<F> \<in> pfilters_on (pwr X) (Pow X)" and xmem:"x \<in> X" 
  show "(\<F>, x) \<in> Lim \<longleftrightarrow> (\<F>, x) \<in> LimCl (ClLim Lim X) X" (is "?L \<longleftrightarrow> ?R")
proof
  assume L:?L
  have L0:"\<And>A. \<lbrakk>A \<in> Pow X; {A}#\<F>\<rbrakk> \<Longrightarrow> (\<exists>\<G> \<in>  pfilters_on (pwr X) (Pow X). (\<G>, x) \<in> Lim \<and> {A}#\<G>)"
  proof-
    fix A assume amem:"A \<in> Pow X" and amesh:"{A}#\<F>"
    obtain is_pfil:"is_pfilter (pwr X) (Pow X) \<F>" and amesh_unfold:"\<forall>B \<in> \<F>. A \<inter> B \<noteq> {}" 
      using amesh mesh_singleE pfil pfilters_on_iff by blast
    define \<H> where  "\<H> \<equiv> {E \<in> Pow X. \<exists>B \<in> \<F>. A \<inter> B \<subseteq> E}" 
    then obtain hpfil:"is_pfilter (pwr X) (Pow X) \<H>" and fsub:"\<F>\<subseteq> \<H>" 
      using is_pfil amesh_unfold amem finer_proper_filter[of X \<F> A]  by (simp add: Int_commute)
    obtain gmem:"\<H> \<in> pfilters_on (pwr X) (Pow X)" and rassum:"(\<F>, x) \<in> Lim"  and fsubh:"\<F> \<subseteq> \<H>"
      using L fsub hpfil pfilters_on_iff by blast 
    then obtain hlim:"(\<H>, x) \<in> Lim" 
      using upclosed by blast
    also obtain hmesh:"{A}#\<H>" 
      unfolding \<H>_def mesh_def using amesh_unfold by fastforce
    then show "(\<exists>\<G> \<in>  pfilters_on (pwr X) (Pow X). (\<G>, x) \<in> Lim \<and> {A}#\<G>)"   
      using gmem hlim by blast
  qed
  then show ?R 
    unfolding LimCl_def ClLim_def using pfil xmem by (smt (verit, best) CollectI case_prodI)
next
  assume R:?R
  then obtain R0:"\<And>F. \<lbrakk>F \<in> Pow X; {F}#\<F>\<rbrakk> \<Longrightarrow>  (\<exists>\<G> \<in>  pfilters_on (pwr X) (Pow X). (\<G>, x) \<in> Lim \<and> {F}#\<G>)" 
    unfolding LimCl_def ClLim_def using pfil xmem by blast
  have R1:"\<And>F. \<lbrakk>F \<in> Pow X; {F}#\<F>\<rbrakk> \<Longrightarrow>  (\<exists>\<G> \<in>  pfilters_on (pwr X) (Pow X). (\<G>, x) \<in> Lim \<and> F \<in> \<G>)"
  proof-
    fix F assume fmem:"F \<in> Pow X" and fmesh:"{F}#\<F>" 
    then obtain \<G> where gfil:"\<G> \<in> pfilters_on (pwr X) (Pow X)" and gx:"(\<G>, x) \<in> Lim" and fg:"{F}#\<G>"  using R0 by auto
    then obtain is_pfil:"is_pfilter (pwr X) (Pow X) \<G>"  and fmesh_unfold:"\<forall>B \<in> \<G>. F \<inter> B \<noteq> {}" using fmesh mesh_singleE pfil pfilters_on_iff by blast
    define \<H> where  "\<H> \<equiv> {E \<in> Pow X. \<exists>B \<in>  \<G>. F \<inter> B \<subseteq> E}" 
    then obtain hpfil:"is_pfilter (pwr X) (Pow X) \<H>" and gsub:" \<G>\<subseteq> \<H>"
      using is_pfil fmesh_unfold fmem finer_proper_filter[of X  \<G> F] by (simp add: Int_commute)
    obtain hmem:"\<H> \<in> pfilters_on (pwr X) (Pow X)"
      by (simp add: hpfil pfilters_on_iff)  
    obtain fmem2:"F \<in> \<H>"  
      using \<H>_def fmem is_pfil sets_pfilter1 by fastforce
    obtain hlim:"(\<H>, x) \<in> Lim" 
      using gsub hmem gx upclosed   by blast
    then show "(\<exists>\<G> \<in>  pfilters_on (pwr X) (Pow X). (\<G>, x) \<in> Lim \<and> F \<in>\<G>)" 
      using hmem fmem2 by blast
  qed
  let ?N="\<Inter>{\<F>. (\<F>, x) \<in> Lim}"
  have R2:"?N \<subseteq>\<F>"
  proof(rule ccontr)
    assume contr1:"\<not>(?N \<subseteq> \<F>)" then obtain F where f1:"F \<in> ?N" and f2:"F \<notin> \<F>" by blast
    from pfil obtain f3:"\<F>  \<in> Pow (Pow X)" and  f4:"is_ord_cl (Pow X)  \<F> (pwr X)"
      by (simp add: is_filterD1 is_pfilterD1 pfilters_on_iff sets_pfilter6) 
    from f2 f3 f4 obtain "(X-F) \<in> grill (Pow X) \<F>"
      by (metis InterE centered f1 grill_reform1 lcroD1 mem_Collect_eq xmem) 
    then obtain "{X-F}#\<F>" 
      by (simp add: grill_def)
    then obtain \<G> where gfil:"\<G> \<in> pfilters_on (pwr X) (Pow X)" and gx:"(\<G>, x) \<in> Lim" and fg:"(X-F) \<in> \<G>" 
      by (meson Diff_subset PowI R1)
    from f1 have "F \<in> \<G>"  
      using gx by blast
    then obtain "{} \<in> \<G>"
      by (metis Diff_disjoint fg gfil pfilters_on_iff sets_pfilter3) 
    then show False
      using gfil pfilters_on_iff sets_pfilter5 by blast
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
  assumes centered:"\<And>x. x \<in> X \<Longrightarrow> (lcro (pwr X) (Pow X) {x}, x) \<in> Lim" and
          upclosed:"\<And>\<G> \<F> x. \<lbrakk>\<G> \<in> pfilters_on (pwr X) (Pow X); (\<F>, x) \<in> Lim;  \<F> \<subseteq> \<G>\<rbrakk> \<Longrightarrow> (\<G>, x) \<in> Lim" and
          vicinity:"\<And>x. x \<in> X \<Longrightarrow> (\<Inter>{\<F>. (\<F>, x) \<in> Lim}, x) \<in> Lim " and  
          is_limit:"\<And>x \<E>. (\<E>, x) \<in> Lim \<Longrightarrow> x \<in> X \<and> \<E> \<in> (pfilters_on (pwr X) (Pow X))" 
  shows prtp_lim_cleq:"(ClLim Lim X) = {(A, x). A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F> \<in> pfilters_on (pwr X) (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> Lim)}" and
        prtp_lim_ccl0:"(ClLim Lim X)``{{}}={}" and
        prtp_lim_ccl1:"\<And>A. A \<in> Pow X \<Longrightarrow> A \<subseteq>(ClLim Lim X)``{A}" and
        prtp_lim_ccl2:"\<And>A B. \<lbrakk>A \<in> Pow X; B \<in> Pow X\<rbrakk> \<Longrightarrow> (ClLim Lim X)``{A \<union> B}=(ClLim Lim X)``{A} \<union> (ClLim Lim X)``{B}"
proof-
  show Q0:"(ClLim Lim X) = {(A, x). A \<in> Pow X \<and> x \<in> X \<and> (\<exists>\<F> \<in> pfilters_on (pwr X) (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> Lim)}"
  proof-
     have P0:"\<And>A x. \<lbrakk>A \<in> Pow X; x \<in> X\<rbrakk> \<Longrightarrow> (A, x) \<in> (ClLim Lim X) \<longleftrightarrow>  (\<exists>\<F> \<in> pfilters_on (pwr X) (Pow X). {A}#\<F> \<and> (\<F>, x) \<in> Lim)" 
        unfolding ClLim_def  by blast
     then have P1:"\<And>A x. \<lbrakk>A \<in> Pow X; x \<in> X\<rbrakk> \<Longrightarrow> (A, x) \<in> (ClLim Lim X) \<longleftrightarrow>  (\<exists>\<F> \<in> pfilters_on (pwr X) (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> Lim)"
     proof-
      fix A x assume A0:"A \<in> Pow X" and x0:"x \<in> X" 
      show "(A, x) \<in> (ClLim Lim X) \<longleftrightarrow>  (\<exists>\<F> \<in> pfilters_on (pwr X) (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> Lim)" (is "?L \<longleftrightarrow> ?R")
      proof
        assume L:?L then obtain \<F> where f1:"\<F> \<in> pfilters_on (pwr X) (Pow X)" and f2:"{A}#\<F>"  and F3:"(\<F>, x) \<in> Lim" 
          using P0 A0 x0 by blast
        then obtain is_pfil:"is_pfilter (pwr X) (Pow X) \<F>"  and fmesh_unfold:"\<forall>B \<in> \<F>. A \<inter> B \<noteq> {}" 
          using f2 mesh_singleE f1 pfilters_on_iff by blast
        define \<H> where  "\<H> \<equiv> {E \<in> Pow X. \<exists>B \<in> \<F>. A \<inter> B \<subseteq> E}" 
        then obtain hpfil:"is_pfilter (pwr X) (Pow X) \<H>" and gsub:"\<F>\<subseteq> \<H>"  
          using is_pfil fmesh_unfold A0 finer_proper_filter[of X \<F> A] by (simp add: Int_commute)
        obtain hmem:"\<H> \<in> pfilters_on (pwr X) (Pow X)"
          by (simp add: hpfil pfilters_on_iff) 
        obtain fmem2:"A \<in> \<H>"  using \<H>_def A0 is_pfil
          by (simp add: ex_in_conv sets_pfilter1)
        obtain hlim:"(\<H>, x) \<in> Lim" 
          using gsub hmem F3 upclosed by blast
        then show "?R" 
          using hmem fmem2 by auto
      next
        assume R:?R  then obtain \<F> where f1:"\<F> \<in> pfilters_on (pwr X) (Pow X)" and f2:"A \<in>\<F>"  and F3:"(\<F>, x) \<in> Lim" 
          using P0 A0 x0 by blast
        also obtain f4:"{A}#\<F>"
          using f1 f2 filter_mem_mesh by auto
        then show ?L 
          using A0 F3 P0 f1 x0 by auto
      qed
    qed
    from P1 have  P2:"\<And>A x. (A, x) \<in> (ClLim Lim X) \<Longrightarrow>  (\<exists>\<F> \<in> pfilters_on (pwr X) (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> Lim)"
      by (metis (no_types, lifting) ClLim_def CollectD case_prodD)
    from P1 have P3: "\<And>A x.   (\<exists>\<F> \<in> pfilters_on (pwr X) (Pow X). A \<in> \<F> \<and> (\<F>, x) \<in> Lim) \<Longrightarrow> (A, x) \<in> (ClLim Lim X)"
      by (meson PowI is_limit pfilters_on_iff setfilters0 setfilters3)  
    from P2 P3 show ?thesis
      unfolding ClLim_def by blast
  qed
  show Q1:"(ClLim Lim X)``{{}}={}"
  proof-
    have P0:"\<And>x. x \<in> X \<Longrightarrow> ({}, x) \<notin> (ClLim Lim X)" 
      using CollectD Q0 filter_on_set_ne by auto 
    then show ?thesis  
      by (simp add: Q0)
  qed
  show Q2:"\<And>A. A \<in> Pow X \<Longrightarrow> A \<subseteq>(ClLim Lim X)``{A}"
  proof-
    fix A assume amem:"A \<in> Pow X"
    have "\<And>x. x \<in> A \<Longrightarrow> x \<in> (ClLim Lim X)``{A}"
    proof-
      fix x assume xa:"x \<in> A"
      then obtain B0:"(lcro (pwr X) (Pow X) {x}) \<in> pfilters_on (pwr X) (Pow X)" and B1:"{A}#(lcro (pwr X) (Pow X) {x})" and B2:"(lcro (pwr X) (Pow X) {x}, x) \<in> Lim"
        by (meson PowD Pow_bottom amem centered filter_mem_mesh insert_subset lcroI1 pfilters_on_iff principal_pfilter_sets pwr_memI subsetD)
      then show "x \<in> (ClLim Lim X)``{A}" 
        unfolding ClLim_def using Image_singleton_iff amem case_prodI is_limit by auto 
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
        obtain G where B2:"G \<in> pfilters_on (pwr X) (Pow X)" and  B3:"(G, x) \<in> Lim \<and> A \<union> B \<in> G" using ClLim_def L  Q0 by auto 
        have B4:"x \<notin> (ClLim Lim X)``{A} \<Longrightarrow> x \<in> (ClLim Lim X)``{B}"
        proof-
          assume A5:"x \<notin> (ClLim Lim X)``{A}"
          then obtain B5:"A \<notin> G"   
            using B2 B3 ClLim_def L Q0 by auto
          have B6:"\<forall>g \<in> G. g \<inter> (X-A) \<noteq> {}"
            by (meson B2 B5 PowD amem pfilters_on_iff pfilters_sets_comp3) 
          have B7:"is_pfilter (pwr X) (Pow X) G"
            using B2 pfilters_on_iff by blast  
          have B8:"(X-A) \<in> Pow X" 
            by simp
          define H where "H \<equiv> {E \<in> Pow X. \<exists>g \<in> G. (X-A) \<inter> g \<subseteq> E}" 
          obtain B9:"is_pfilter (pwr X) (Pow X) H"  
            using finer_proper_filter[of X G "(X-A)"] B6 B7 B8 H_def by blast
          obtain B10:"G \<subseteq> H"  
            using finer_proper_filter[of X G "(X-A)"] B6 B7 B8 H_def by blast
          have B11:"(X - A) \<inter> (A \<union> B) \<subseteq> B" 
            by blast
          have B12:"(X - A) \<inter> (A \<union> B) \<in> H"  
            using B3 H_def by blast
          have B13:"B \<in> H"
            using B12 B9 bmem sets_pfilter4 by blast   
          have B14a:"H \<in> pfilters_on (pwr X) (Pow X) \<and>  (G, x) \<in> Lim \<and> G \<subseteq> H"   
             by (simp add: B10 B3 B9 pfilters_on_iff)
          then have B14:"(H, x) \<in> Lim"  
            using upclosed by blast 
          show "x \<in> (ClLim Lim X)``{B}"  
            using B13 B14 B14a ClLim_def Q0 bmem is_limit by fastforce
        qed
        have B15:"x \<in>  (ClLim Lim X)``{A} \<or> x \<in>  (ClLim Lim X)``{B}"  
          using B4 by blast
        then show "x \<in>  (ClLim Lim X)``{A} \<union>  (ClLim Lim X)``{B}"
         by simp
      qed
    next
      show "?rhs \<subseteq> ?lhs"
      proof
        fix x assume R:"x \<in> ?rhs"
        then obtain B0:"x \<in>  (ClLim Lim X)``{A} \<or> x \<in>  (ClLim Lim X)``{B}" by auto
        then obtain G where B1:"G \<in> pfilters_on (pwr X) (Pow X)" and B2:"(G, x) \<in> Lim \<and> (A \<in> G \<or>  B \<in> G)"  
          using ClLim_def Q0 Image_Collect_case_prod mem_Collect_eq singletonD by auto 
        then obtain B3:"A \<union> B \<in> G"
          using amem bmem pfilters_on_iff sets_pfilter4 by fastforce 
        then have B4:"G \<in>  pfilters_on (pwr X) (Pow X) \<and> (G, x) \<in> Lim\<and> (A \<union> B) \<in> G"
           by (simp add: B1 B2)
        then obtain B5:"\<exists>G1 \<in> pfilters_on (pwr X) (Pow X). (G1, x) \<in> Lim \<and> (A \<union>B ) \<in> G1" 
          by blast
        also obtain "x \<in> X" 
          using B0 ClLim_def Q0 by blast
        then show "x \<in> ?lhs" 
          using ClLim_def Q0 calculation Pow_iff Un_subset_iff amem bmem by auto
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
    assume R:?R then show ?L using A0 A1 is_cl apply(auto)
    by (metis (no_types, lifting) Diff_Diff_Int Diff_disjoint Pow_iff inf.absorb_iff2)
  qed
qed

  


  

lemma cl_lim_prtp1:
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
    then show ?R 
      unfolding ClLim_def LimCl_def using L A0 x0 by auto
    next
    assume R:?R
    define \<F> where "\<F> \<equiv> {V \<in> Pow X. x \<notin> Cl``{X-V}}"
    have PF0:"is_filter (pwr X) (Pow X) \<F>"
    proof(rule is_filterI1)
      show PF01:"\<F> \<noteq> {}"
        using CCl1 \<F>_def by fastforce
      show PF02:"\<F> \<subseteq> Pow X"
        using \<F>_def by blast
      show PF03:"is_dir \<F> (dual (pwr X))"
      proof(rule is_dirI1)
        fix a b assume "a \<in> \<F>" and "b \<in> \<F>" 
        then obtain amem:"a \<in> Pow X" and "x \<notin> Cl``{X-a}" and bmem:"b \<in> Pow X" and "x \<notin> Cl``{X-b}" 
          unfolding \<F>_def by fastforce
        then obtain "a \<inter> b \<in> Pow X" and "x \<notin> Cl``{X-(a \<inter> b)}" 
          by (metis CCl3 Diff_Int Diff_subset Int_Un_eq(1) Pow_iff Un_iff Un_subset_iff)
        then obtain "\<exists>c\<in>\<F>. c \<subseteq> a \<and> c \<subseteq> b"  using \<F>_def by auto
        then show " \<exists>c\<in>\<F>. (a, c) \<in> dual (pwr X) \<and> (b, c) \<in> dual (pwr X)"
          by(meson PowD amem bmem converseI pwr_memI)
      qed
      show PF04:"is_ord_cl (Pow X) \<F> (pwr X)"
      proof(rule is_ord_clI1)
        fix a b assume a0:"a \<in> \<F>" and b0:"b \<in> Pow X"  and ab0:"(a,b)\<in>pwr X" 
        then obtain a1:"a \<in> Pow X" and  ab1:"a \<subseteq> b" and x1:"x \<notin> Cl``{X-a}"
          by (simp add: \<F>_def powrel8) 
        then show "b \<in> \<F>"  
      unfolding \<F>_def using ab0 b0  by (metis (no_types, lifting) CCl3 Diff_Int Diff_subset Pow_iff Un_iff inf.absorb_iff2 mem_Collect_eq)
      qed
    qed
    have PF1:"Pow X \<noteq> \<F>"
    by (metis (no_types, lifting) CCl2 CollectD Diff_empty Pow_bottom Pow_top \<F>_def subsetD x0)
    have F0:"\<F> \<in> pfilters_on (pwr X) (Pow X)"
      by (simp add: PF0 PF1 is_pfilterI1 pfilters_on_iff)
    have F1:"{A} # \<F> " 
      unfolding \<F>_def mesh_def by (smt (verit, del_insts) CCl1 CCl2 CCl3 CollectD Image_singleton_iff Int_commute R cl_lim_prtp2b is_cl singletonD)
    have F2:"\<And>E. \<lbrakk>E \<in> Pow X; {E}#\<F>\<rbrakk> \<Longrightarrow> (E, x) \<in> Cl"
    proof-
      fix E assume E0:"E \<in> Pow X" and E1:"{E}#\<F>"
      then show "(E, x) \<in> Cl" 
        by (smt (verit, del_insts) CollectI Diff_Diff_Int Diff_disjoint Image_singleton_iff PowD Pow_def \<F>_def inf.absorb_iff2 insert_iff mesh_def)
    qed
    then show ?L
       unfolding ClLim_def LimCl_def using A0 x0 R F0 F1 F2 by auto
    qed
qed



end